import obspython as obs
import socket
import threading
import json
import time
import random
import calendar
import collections
import re
import os
import sys
import string
import site
import ssl
import base64
import subprocess
import platform
import ctypes
import ctypes.util
import tempfile
import mimetypes
import shutil
import asyncio
import hashlib
import secrets
import webbrowser
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
import http.client
from urllib.parse import urlparse, parse_qs, quote
import urllib.request
import urllib.parse
import urllib.error
from abc import ABC, abstractmethod
from datetime import datetime, timedelta
from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, List, Optional

try:
    import aiohttp
except ImportError:
    aiohttp = None

try:
    import websockets
except ImportError:
    websockets = None

try:
    # Стандартна бібліотека Python 3.9+. Потрібна, щоб коректно рахувати
    # час до опівночі Pacific Time (реальний момент скидання денної квоти
    # YouTube Data API v3, а не довільний "+1 година").
    from zoneinfo import ZoneInfo
except ImportError:
    ZoneInfo = None

# ============================================================================
# АВТОМАТИЧНИЙ ПОШУК ШЛЯХІВ ДО PYTHON БІБЛІОТЕК
# ============================================================================
def add_python_paths():
    paths_added = []
    try:
        for path in site.getsitepackages():
            if os.path.exists(path) and path not in sys.path:
                sys.path.insert(0, path)
                paths_added.append(path)
    except:
        pass
    try:
        user_site = site.getusersitepackages()
        if os.path.exists(user_site) and user_site not in sys.path:
            sys.path.insert(0, user_site)
            paths_added.append(user_site)
    except:
        pass

    appdata = os.getenv('APPDATA', '').replace('Roaming', '')
    if appdata:
        possible_paths = [
            os.path.join(appdata, 'Local', 'Programs', 'Python'),
            os.path.join(appdata, 'Local', 'Programs (x86)', 'Python'),
        ]
        for base_path in possible_paths:
            if os.path.exists(base_path):
                try:
                    for folder in os.listdir(base_path):
                        lib_path = os.path.join(base_path, folder, 'lib', 'site-packages')
                        if os.path.exists(lib_path) and lib_path not in sys.path:
                            sys.path.insert(0, lib_path)
                            paths_added.append(lib_path)
                except:
                    pass

    if paths_added:
        print(f"[Python] ✅ Додано шляхів: {len(paths_added)}")

add_python_paths()

# ============================================================================
# ІМПОРТИ
# ============================================================================
TIKTOK_AVAILABLE = False
TIKTOK_WEBDEFAULTS_AVAILABLE = False
RoomUserSeqEvent = None
ShareEvent = None
TikTokWebDefaults = None
try:
    from TikTokLive import TikTokLiveClient
    try:
        from TikTokLive.events import CommentEvent, FollowEvent, GiftEvent, LikeEvent, RoomUserSeqEvent, ShareEvent
    except ImportError:
        RoomUserSeqEvent = None
        ShareEvent = None
        try:
            from TikTokLive.events import CommentEvent, FollowEvent, GiftEvent, LikeEvent, ShareEvent
        except ImportError:
            from TikTokLive.events import CommentEvent, FollowEvent, GiftEvent, LikeEvent
            ShareEvent = None
    TIKTOK_AVAILABLE = True
    print("[TikTok] ✅ TikTokLive завантажена!")
    if ShareEvent is None:
        print("[TikTok] ⚠️ ShareEvent недоступний у цій версії бібліотеки — відстеження репостів трансляції вимкнено.")
    try:
        # Дозволяє задати Euler Stream API-ключ (config["tt_sign_api_key"]) і підняти
        # ліміт анонімних підключень до Sign Server, який інакше часто віддає
        # SIGN_NOT_200 / RATE_LIMIT. Ключ береться безкоштовно на eulerstream.com.
        from TikTokLive.client.web.web_settings import WebDefaults as TikTokWebDefaults
        TIKTOK_WEBDEFAULTS_AVAILABLE = True
    except ImportError as e:
        print(f"[TikTok] ⚠️ WebDefaults недоступний у цій версії бібліотеки, ключ Euler Stream застосувати не вдасться: {e}")
except ImportError as e:
    print(f"[TikTok] ⚠️ Не знайдено: {e}")

JoinEvent = None
try:
    from TikTokLive.events import JoinEvent
except ImportError:
    JoinEvent = None

# ============================================================================
# ГЛОБАЛЬНІ ЗМІННІ
# ============================================================================
PORT = 8080
server_instance = None
server_thread = None
global_session_id = 0

# ---------------------------------------------------------------------------
# РЕЄСТР СЕСІЙ ТА СТАНІВ ПЛАТФОРМ
# ---------------------------------------------------------------------------
# Раніше всі воркери порівнювались з одним спільним global_session_id, тому
# будь-яка його зміна вбивала ОДРАЗУ ВСІ платформи, Analytics і читачі чату.
# Тепер кожна платформа має власний унікальний session_id, а множина
# active_session_ids містить лише ті, що дійсні зараз. Відкликання одного id
# зупиняє рівно одну платформу і не торкається решти.
session_registry_lock = threading.RLock()
active_session_ids = set()
_session_id_counter = 1000


def next_session_id():
    global _session_id_counter
    with session_registry_lock:
        _session_id_counter += 1
        return _session_id_counter


def session_is_current(session_id):
    """Чи ця сесія воркера ще дійсна. Замінює `sid == global_session_id`."""
    with session_registry_lock:
        return session_id in active_session_ids


# Станова машина життєвого циклу платформи.
PLATFORM_STATE_START = 'START'
PLATFORM_STATE_CONNECTED = 'CONNECTED'
PLATFORM_STATE_RUNNING = 'RUNNING'
PLATFORM_STATE_ERROR = 'ERROR'
PLATFORM_STATE_BACKOFF = 'BACKOFF'
PLATFORM_STATE_RECONNECTING = 'RECONNECTING'
PLATFORM_STATE_STOPPED = 'STOPPED'

# 5 -> 10 -> 20 -> 40 -> 120 секунд, далі стеля 120.
PLATFORM_BACKOFF_STEPS = [5, 10, 20, 40, 120]

platform_lock = threading.RLock()
platform_threads = {}
platform_sessions = {}
platform_status = {}


def platform_status_snapshot():
    with platform_lock:
        out = {}
        for name, st in platform_status.items():
            thread = platform_threads.get(name)
            entry = dict(st)
            entry['thread_alive'] = bool(thread and thread.is_alive())
            entry['session_id'] = platform_sessions.get(name)
            out[name] = entry
        return out


def platform_set_state(name, state, reason=''):
    with platform_lock:
        st = platform_status.setdefault(
            name, {"state": PLATFORM_STATE_STOPPED, "attempts": 0,
                   "reason": "", "since": 0.0, "last_error": ""})
        st['state'] = state
        st['since'] = time.time()
        if reason:
            st['reason'] = reason


def platform_mark_connected(name):
    """Воркер викликає це після успішного підключення: скидає backoff."""
    with platform_lock:
        st = platform_status.setdefault(
            name, {"state": PLATFORM_STATE_STOPPED, "attempts": 0,
                   "reason": "", "since": 0.0, "last_error": ""})
        st['attempts'] = 0
        st['state'] = PLATFORM_STATE_RUNNING
        st['since'] = time.time()
        st['last_error'] = ''


def platform_backoff_delay(name, reason=''):
    """Воркер викликає це після помилки: рахує паузу і логує ізольоване
    відновлення. Жодного глобального перезапуску тут не відбувається."""
    with platform_lock:
        st = platform_status.setdefault(
            name, {"state": PLATFORM_STATE_STOPPED, "attempts": 0,
                   "reason": "", "since": 0.0, "last_error": ""})
        st['attempts'] = int(st.get('attempts', 0)) + 1
        attempts = st['attempts']
        st['state'] = PLATFORM_STATE_BACKOFF
        st['since'] = time.time()
        if reason:
            st['last_error'] = str(reason)[:400]
    idx = min(attempts - 1, len(PLATFORM_BACKOFF_STEPS) - 1)
    delay = PLATFORM_BACKOFF_STEPS[idx]
    print("[Recovery] platform={} reason={} action=reconnect_platform_only "
          "attempt={} backoff={}s".format(
              name, (reason or 'unknown_error'), attempts, delay))
    return delay
buffer_lock = threading.Lock()
config_lock = threading.Lock()
messages_buffer = []
recent_signatures = []
message_counter = 0
user_cooldowns = {}
blocked_users = set()
blacklist_words = set()
no_tts_users = set()
custom_nicknames = {}
user_voice_assignments = {}
tiktok_like_tracker = {}
tiktok_gift_tracker = {}
repeated_message_tracker = {}
processed_comment_ids = set()
processed_gift_ids = set()
processed_like_ids = set()
processed_share_ids = set()
announced_follower_joins = set()
tiktok_recent_comment_fingerprints = {}
tiktok_recent_comment_simple_fingerprints = {}
tiktok_last_comment_ts = 0.0
tiktok_widget_events = []
tiktok_widget_event_counter = 0
platform_widget_event_queues = {}
platform_widget_event_stats = {}
tiktok_live_viewer_count = 0
tiktok_live_is_active = False
tiktok_last_viewer_update_ts = 0.0
tiktok_room_info_cache = None
tiktok_room_info_cache_username = ''
tiktok_last_room_info_refresh_ts = 0.0
tiktok_last_viewer_debug_ts = 0.0
tiktok_last_room_info_debug_ts = 0.0
twitch_app_token_cache = {"access_token": "", "expires_at": 0}
twitch_token_validation_cache = {"token": "", "payload": None, "ts": 0.0}
twitch_user_oauth_cache = {"access_token": "", "refresh_token": "", "expires_at": 0.0, "scope": []}
twitch_oauth_state_cache = {"state": "", "ts": 0.0}
TWITCH_DEFAULT_REDIRECT_URI = 'http://localhost:8080/callback/twitch'
TWITCH_EVENTSUB_SCOPES = ['moderator:read:followers', 'bits:read']
KICK_DEFAULT_REDIRECT_URI = 'http://127.0.0.1:8080/callback/kick'
kick_user_oauth_cache = {"access_token": "", "refresh_token": "", "expires_at": 0.0, "scope": ""}
processed_twitch_event_ids = set()

# ---------------------------------------------------------------------------
# ДЕДУПЛІКАЦІЯ ПОВІДОМЛЕНЬ (durable, per-platform)
# ---------------------------------------------------------------------------
# Живе на рівні модуля і НЕ очищується ні при перезапуску сервісів, ні при
# реконнекті окремої платформи, ні при перемиканні способу читання чату
# (YouTube API <-> YouTube web). Саме тому після відновлення з'єднання старі
# повідомлення більше не потрапляють у TTS повторно.
#
# Витіснення - FIFO (найстаріші ID), а НЕ .clear(): скидати весь кеш одразу
# означало б знову озвучити свіжі повідомлення на наступному ж опитуванні.
DEDUP_MAX_PER_PLATFORM = 20000
DEDUP_EVICT_CHUNK = 4000
message_dedup_lock = threading.Lock()
message_dedup_seen = {}
message_dedup_stats = {}


def dedup_is_new(platform, msg_id, kind='message'):
    """True -> повідомлення нове, обробляй далі.
    False -> вже було оброблене, повністю пропустити (Translator/TTS/буфер).

    Порожній msg_id означає, що платформа не дала ідентифікатора: тоді
    вважаємо повідомлення новим (нехай краще спрацює локальний
    fingerprint-фільтр, ніж ми загубимо справжнє повідомлення).
    """
    if not msg_id:
        return True
    key = str(msg_id)
    platform = str(platform or 'unknown')
    with message_dedup_lock:
        seen = message_dedup_seen.get(platform)
        if seen is None:
            seen = collections.OrderedDict()
            message_dedup_seen[platform] = seen
        stats = message_dedup_stats.setdefault(
            platform, {"new": 0, "duplicates": 0})
        if key in seen:
            stats["duplicates"] += 1
            print("[Dedup][{}] duplicate {} skipped: {}".format(
                platform, kind, key))
            return False
        seen[key] = time.time()
        stats["new"] += 1
        if len(seen) > DEDUP_MAX_PER_PLATFORM:
            for _ in range(DEDUP_EVICT_CHUNK):
                try:
                    seen.popitem(last=False)
                except KeyError:
                    break
    return True


def dedup_snapshot():
    """Діагностика: скільки ID тримаємо і скільки дублів відсіяли."""
    with message_dedup_lock:
        return {
            p: {
                "cached": len(message_dedup_seen.get(p, ())),
                "new": st.get("new", 0),
                "duplicates": st.get("duplicates", 0),
            }
            for p, st in message_dedup_stats.items()
        }


def dedup_reset_all():
    """Викликається ЛИШЕ при повному завантаженні скрипта (script_load),
    ніколи - при перезапуску сервісів чи реконнекті платформи."""
    with message_dedup_lock:
        message_dedup_seen.clear()
        message_dedup_stats.clear()
youtube_quota_exceeded = False
youtube_quota_reset_time = 0
youtube_active_targets = set()
youtube_active_targets_lock = threading.Lock()
# Стан лічильників YouTube (підписники каналу та лайки трансляції).
# subs:      {channel_id: last_subscriber_count}
# like_step: {video_id: last_announced_step}
youtube_stats_state = {"subs": {}, "like_step": {}}

MAX_CACHE_SIZE = 10000
MAX_TRANSLATION_CACHE_SIZE = 1000
translation_cache = {}
translation_lock = threading.Lock()

PRIORITY_MAP = {
    "donation": 100, "raid": 96, "gift": 90, "bits": 89, "points": 88, "hype": 87, "subscription": 85, "follow": 80, "alert": 70, "chat": 50, "like": 10,
    # Оголошення бота — найнижчий пріоритет: озвучується лише тоді, коли
    # в черзі TTS немає ні повідомлень глядачів, ні алертів.
    "announce": 1
}

TIKTOK_RECONNECT_DELAYS = [10, 20, 40, 60]
TIKTOK_GIFT_AGGREGATION_WINDOW = 5
TIKTOK_HISTORY_GUARD_SECONDS = 8
TIKTOK_DUPLICATE_TTL = 600
TIKTOK_SIMPLE_DUPLICATE_TTL = 90
TIKTOK_BACKLOG_SETTLE_SECONDS = 12
TIKTOK_RECONNECT_DROP_SECONDS = 12
TIKTOK_BACKLOG_TS_SLACK_SECONDS = 2
IDENTICAL_MESSAGE_WINDOW = 30
IDENTICAL_MESSAGE_LIMIT = 2
MAX_TIKTOK_TTS_LENGTH = 120
# Загальний запобіжник для звичайних чат-повідомлень у TTS (лише проти
# екстремального спаму/копіпасти) - Twitch і так обмежує повідомлення до
# 500 символів, тож це не має різати нормальні коментарі.
TTS_MAX_MESSAGE_LENGTH = 500
# Безпечний розмір одного шматка тексту для Google Translate TTS: у цього
# ендпоінту є недокументований ліміт (~200 байт у запиті) - довші фрази він
# просто обрізає, з чого й була скарга "читає половину і замовкає".
GOOGLE_TTS_CHUNK_LENGTH = 170
WIDGET_EVENT_TTL_SECONDS = 180
WIDGET_EVENT_MAX = 200
WIDGET_QUEUE_MAX_PER_TYPE = 50


threads = {
    "twitch": None, "twitch_eventsub": None, "kick": None, "youtube": None, "tiktok": None,
    "bot_timers": None,

}

analytics_manager = None
analytics_data_dir = "analytics_data"
network_monitor_manager = None

config = {
    "dock_port": 8080,
    "twitch_channel": "", "twitch_irc_login": "", "twitch_irc_oauth": "", "kick_chat_url": "", "kick_webhook_secret": "", "yt_live_id": "", "yt_api_key": "", "tt_username": "", "tt_sign_api_key": "",
    "twitch_client_id": "", "twitch_client_secret": "", "kick_client_id": "", "kick_client_secret": "",
    "tts_enabled": True, "tts_engine": "google", "tts_voice": "uk-UA", "tts_volume": 80,
    "elevenlabs_api_key": "", "elevenlabs_model": "eleven_multilingual_v2",
    "elevenlabs_voice_id": "2OXYbN1uGomXXJtv9Dq6", "elevenlabs_output_format": "mp3_44100_128",
    "elevenlabs_stability": 50, "elevenlabs_similarity": 75, "elevenlabs_debug": False,
    "tts_speed": 100, "tts_cooldown": 3, "tts_read_symbols": True, "tts_read_nicknames": True, "tts_sub_only": False,
    "tts_template": "{nickname} {comment}",
    "tts_auto_translate": False,
    "tts_translate_uk": False,
    "tts_translate_en": False,
    "anti_caps": True, "flood_control": True, "filter_badwords": True, "replace_emoji": True,
    "hide_links": True, "hide_emojis": False,
    "blacklist": "", "blacklist_action": "censor",
    "msg_timeout": 20,
    "bot_enabled": True, "ad_interval": 15, "ad_text": "Не забудьте підписатися на канал!",
    "chat_bg_image": "", "chat_msg_color": "rgba(255, 255, 255, 0.1)", "chat_font_size": 14,
    "filter_platforms": {"twitch": True, "youtube": True, "tiktok": True, "kick": True, "bot": True, "alerts": True},
    "tt_enable_chat": True, "tt_enable_follows": True, "tt_enable_likes": True, "tt_enable_gifts": True, "tt_enable_shares": True,
    "tt_follow_template": "{user} підписався на TikTok",
    "tt_follow_show_avatar": True, "tt_follow_show_nick": True,
    "tt_like_show_avatar": True,
    "tt_gift_template": "{user} відправив подарунок {gift} x{count}",
    "tt_like_template": "{user} відправив {count} лайків",
    "tt_share_template": "{user} зробив(-ла) репост трансляції!",
    "tt_follow_audio_path": "", "tt_follow_media_path": "",
    "tt_like_audio_path": "", "tt_like_media_path": "",
    "tt_gift_audio_path": "", "tt_gift_media_path": "",
    "tt_share_audio_path": "", "tt_share_media_path": "",
    "tt_like_threshold": 100,
    "tt_show_follows_in_chat": True, "tt_show_gifts_in_chat": True, "tt_show_likes_in_chat": True, "tt_show_shares_in_chat": True, "yt_show_members_in_chat": True, "tw_show_subs_in_chat": True, "tw_show_follows_in_chat": True, "tw_show_raids_in_chat": True, "tw_show_bits_in_chat": True, "tw_show_points_in_chat": True, "tw_show_hype_in_chat": True, "kk_show_follows_in_chat": True, "kk_show_subs_in_chat": True,
    "tts_output_to_stream": True, "tts_ringtone_path": "", "tts_ringtone_chat_only": True,
    "update_url": "",
    "tt_follow_voice_id": "", "tt_gift_voice_id": "", "tt_like_voice_id": "", "tt_share_voice_id": "", "yt_member_voice_id": "", "tw_sub_voice_id": "", "tw_follow_voice_id": "", "tw_raid_voice_id": "", "tw_bits_voice_id": "", "tw_points_voice_id": "", "tw_hype_voice_id": "", "kk_follow_voice_id": "", "kk_sub_voice_id": "",
    "yt_member_audio_path": "", "yt_member_media_path": "",
    "yt_enable_sub_alerts": True, "yt_enable_like_alerts": True,
    "yt_stats_poll_seconds": 60, "yt_like_threshold": 1,
    "yt_sub_template": "Новий підписник на YouTube! Всього підписників: {total}",
    "yt_like_template": "На трансляції YouTube вже {likes} лайків! Дякую!",
    "yt_sub_audio_path": "", "yt_sub_media_path": "", "yt_sub_voice_id": "", "yt_show_subs_in_chat": True,
    "yt_like_audio_path": "", "yt_like_media_path": "", "yt_like_voice_id": "", "yt_show_likes_in_chat": True,
    "tw_enable_subs": True, "tw_enable_follows": True, "tw_enable_raids": True, "tw_enable_bits": True, "tw_enable_points": True, "tw_enable_hype": True, "tw_sub_audio_path": "", "tw_sub_media_path": "", "tw_follow_audio_path": "", "tw_follow_media_path": "", "tw_raid_audio_path": "", "tw_raid_media_path": "", "tw_bits_audio_path": "", "tw_bits_media_path": "", "tw_points_audio_path": "", "tw_points_media_path": "", "tw_hype_audio_path": "", "tw_hype_media_path": "",
    "kk_enable_follows": True, "kk_enable_subs": True, "kk_follow_audio_path": "", "kk_follow_media_path": "", "kk_sub_audio_path": "", "kk_sub_media_path": "", "tw_sub_priority": 85, "tw_follow_priority": 80, "tw_raid_priority": 96, "tw_bits_priority": 89, "tw_points_priority": 88, "tw_hype_priority": 87,
    "overlay_max_messages": 20, "overlay_msg_timeout": 10, "overlay_font_size": 18,
    "overlay_bg_color": "rgba(0,0,0,0.7)", "overlay_text_color": "#ffffff",
    "overlay_rotation": 0, "overlay_offset_x": 0, "overlay_offset_y": 0,
    "overlay_plain": False, "overlay_plain_marker": "icon",
    "analytics_enabled": True,
    "analytics_update_interval": 25,
    "analytics_platforms": {"youtube": True, "tiktok": True, "twitch": True, "kick": True},
    "analytics_widget_platforms": {"youtube": True, "tiktok": True, "twitch": True, "kick": True},
    "analytics_widget_enabled": True,
    "analytics_widget_mode": "compact",
    "analytics_widget_font_size": 16,
    "analytics_widget_text_color": "#ffffff",
    "analytics_widget_bg_color": "rgba(0,0,0,0.7)",
    "top_likes_widget_title": "🏆 Топ за лайками (TikTok)",
    "top_likes_widget_limit": 10,
    "top_likes_widget_show_title": True,
    "top_likes_widget_bg_enabled": True,
    "top_likes_widget_bg_color": "rgba(20,20,28,0.85)",
    "top_likes_widget_text_color": "#ffffff",
    "top_likes_widget_row_plate": True,
    "allow_network_access": False,
    "gw_enabled": False, "gw_tg_token": "", "gw_tg_chat_id": "", "gw_prize_title": "",
    "gw_announce_text": "", "gw_img_path": "", "gw_duration_min": 15,
    "sn_enabled": False,
    "sn_stream_title": "", "sn_stream_game": "", "sn_custom_text": "", "sn_preview_path": "",
    "sn_post_image_path": "", "sn_streamer_name": "", "sn_send_delay": 0,
    "sn_tg_token": "", "sn_tg_chat_id": "", "sn_tg_delete_on_stop": False,
    "sn_dc_webhook": "", "sn_dc_mention": "none",
    "sn_url_tiktok": "", "sn_url_twitch": "", "sn_url_youtube": "", "sn_url_kick": "",
    "sn_url_discord": "", "sn_url_telegram": "", "sn_url_steamtv": "",
    "sn_url_fb_gaming": "", "sn_url_facebook": "", "sn_url_instagram": "", "sn_url_donat": "",
    "sn_btn_style_tiktok": "", "sn_btn_style_twitch": "", "sn_btn_style_youtube": "danger", "sn_btn_style_kick": "success", "sn_btn_style_discord": "", "sn_btn_style_telegram": "", "sn_btn_style_steamtv": "", "sn_btn_style_fb_gaming": "", "sn_btn_style_facebook": "", "sn_btn_style_instagram": "", "sn_btn_style_donat": "primary",
    "sn_tg_edit_on_stop": False, "sn_after_image_path": "", "sn_after_text": "",
    "sn_after_url_tiktok": False, "sn_after_url_twitch": False, "sn_after_url_youtube": False, "sn_after_url_kick": False,
    "sn_after_url_discord": False, "sn_after_url_telegram": False, "sn_after_url_steamtv": False,
    "sn_after_url_fb_gaming": False, "sn_after_url_facebook": False, "sn_after_url_instagram": False, "sn_after_url_donat": False,
    "sn_schedule_date": "", "sn_schedule_time": "",
    "netmon_enabled": False,
    "netmon_ping_host": "8.8.8.8",
    "netmon_ping_hosts": "1.1.1.1, 8.8.8.8, 9.9.9.9",
    "netmon_window_size": 60,
    "netmon_jitter_threshold": 60,
    "netmon_show_obs_frames": True,
    "netmon_ping_interval": 3,
    "netmon_loss_threshold": 20,
    "netmon_ping_threshold": 250,
    "netmon_debounce_count": 3,
    "netmon_show_in_chat": False,
    "netmon_unstable_text": "Увага, інтернет-з'єднання нестабільне",
    "netmon_stable_text": "З'єднання стабілізувалось",
    "netmon_speedtest_enabled": False,
    "netmon_speedtest_interval": 60,
    "auto_mute_enabled": False,
    "auto_mute_words": "",
    "auto_mute_announce_template": "Користувача {user} з {platform} заглушено за порушення правил",
    "tt_enable_follower_join": False,
    "tt_follower_join_template": "{user} (підписник) приєднався до ефіру!",
    "tt_follower_join_voice_id": "",
    "tt_show_follower_join_in_chat": False,
    "music_enabled": False,
    "music_folder_path": "",
    "music_duck_on_alert": True,
    "music_duck_resume_delay": 10,
    "music_duck_source_names": {},
}

ANALYTICS_ICON_DATA = {
    "youtube": "https://www.genspark.ai/api/files/s/okLeEAaQ",
    "kick": "https://www.genspark.ai/api/files/s/oWzV6ugd",
    "tiktok": "https://www.genspark.ai/api/files/s/w6w8Li1M",
    "twitch": "https://www.genspark.ai/api/files/s/v7iTB1Rw",
}

TTS_BROWSER_SOURCE_NAME = "MultiChat TTS Audio"
TTS_BROWSER_SOURCE_SIZE = 16

# ============================================================================
# UNIFIED EVENT BUS / CONFIG / OAUTH EXTENSIONS
# ============================================================================
CONFIG_DIR = os.path.join(os.path.dirname(__file__), "config")
ASSETS_DIR = os.path.join(CONFIG_DIR, "uploaded_assets")


def fs_root_listing():
    """Список коренів файлової системи: диски A:-Z: на Windows,
    домашня тека + '/' на POSIX. Використовується як стартова точка і як
    резервний варіант, коли збережений шлях більше не існує."""
    entries = []
    if os.name == "nt":
        for letter in string.ascii_uppercase:
            drive = "{}:\\".format(letter)
            try:
                if os.path.exists(drive):
                    entries.append({"name": drive, "path": drive, "is_dir": True})
            except OSError:
                continue
        return {"ok": True, "current_path": "", "parent_path": None, "entries": entries}
    home = os.path.expanduser("~")
    if os.path.isdir(home):
        entries.append({"name": home, "path": home, "is_dir": True})
    entries.append({"name": "/", "path": "/", "is_dir": True})
    return {"ok": True, "current_path": "", "parent_path": None, "entries": entries}


def browse_filesystem(req_path, only_dirs=False, ext_filter=""):
    """
    Серверний (не браузерний) огляд файлової системи. Використовується
    полями типу 'browse', які посилаються на ВЖЕ ІСНУЮЧІ файли/теки на
    диску користувача (на відміну від alert-медіа, де файл копіюється
    у папку скрипта). Оскільки сам сервер працює локально з повним доступом
    до диска (на відміну від JS у браузерному доку), огляд файлової
    системи відбувається тут і повертає СПРАВЖНІ абсолютні шляхи.
    """
    req_path = (req_path or "").strip()
    ext_list = [e.strip().lower() for e in ext_filter.split(",") if e.strip()]

    if not req_path:
        return fs_root_listing()

    # Поле може вже містити шлях до ФАЙЛУ (напр. D:/Звуки/1.mp3) — тоді
    # відкриваємо папку, в якій цей файл лежить, а не повертаємо помилку.
    try:
        if os.path.isfile(req_path):
            req_path = os.path.dirname(req_path) or req_path
    except OSError:
        pass

    if not os.path.isdir(req_path):
        # Шлях зіпсований / диск відключений — піднімаємось батьківськими
        # теками, а якщо жодна не існує, показуємо список дисків.
        probe = req_path
        found = None
        for _ in range(12):
            parent = os.path.dirname(probe.rstrip("\\/"))
            if not parent or parent == probe:
                break
            probe = parent
            try:
                if os.path.isdir(probe):
                    found = probe
                    break
            except OSError:
                break
        if not found:
            return fs_root_listing()
        req_path = found

    try:
        raw_entries = os.listdir(req_path)
    except OSError as e:
        return {"ok": False, "error": "Немає доступу до папки: {}".format(e)}

    dirs = []
    files = []
    for name in sorted(raw_entries, key=str.lower):
        full = os.path.join(req_path, name)
        try:
            is_dir = os.path.isdir(full)
        except OSError:
            continue
        if is_dir:
            dirs.append({"name": name, "path": full, "is_dir": True})
        elif not only_dirs:
            if ext_list and not any(name.lower().endswith(ext) for ext in ext_list):
                continue
            files.append({"name": name, "path": full, "is_dir": False})

    normalized = req_path.rstrip("\\/")
    if os.name == "nt" and re.match(r'^[A-Za-z]:$', normalized):
        parent_path = ""
    else:
        parent_candidate = os.path.dirname(normalized)
        parent_path = parent_candidate if parent_candidate and parent_candidate != normalized else (
            "" if os.name == "nt" else "/"
        )
        if parent_path == normalized:
            parent_path = None

    return {"ok": True, "current_path": req_path, "parent_path": parent_path, "entries": dirs + files}
OAUTH_CONFIG_FILE = os.path.join(CONFIG_DIR, "oauth.json")
PLATFORMS_CONFIG_FILE = os.path.join(CONFIG_DIR, "platforms.json")
SETTINGS_CONFIG_FILE = os.path.join(CONFIG_DIR, "settings.json")
SECRETS_CONFIG_FILE = os.path.join(CONFIG_DIR, "secrets.json")
TOKENS_CONFIG_FILE = os.path.join(CONFIG_DIR, "tokens.json")
LOG_DIR = os.path.join(os.path.dirname(__file__), "logs")
ERROR_LOG_FILE = os.path.join(LOG_DIR, "errors.log")
APP_LOG_FILE = os.path.join(LOG_DIR, "multichat.log")


class PlatformName(str, Enum):
    TIKTOK = "tiktok"
    TWITCH = "twitch"
    YOUTUBE = "youtube"
    KICK = "kick"
    DONATION = "donation"
    BOT = "bot"
    SYSTEM = "system"


class UnifiedEventType(str, Enum):
    CHAT_MESSAGE = "chat_message"
    FOLLOW = "follow"
    SUBSCRIBE = "subscribe"
    GIFTED_SUBSCRIPTION = "gifted_subscription"
    GIFT = "gift"
    LIKE = "like"
    CHEER = "cheer"
    RAID = "raid"
    VIEWER_COUNT = "viewer_count"
    STREAM_ONLINE = "stream_online"
    STREAM_OFFLINE = "stream_offline"
    CATEGORY_CHANGED = "category_changed"
    TITLE_CHANGED = "title_changed"
    MODERATOR_EVENT = "moderator_event"
    BAN = "ban"
    TIMEOUT = "timeout"
    SUPER_CHAT = "super_chat"
    SUPER_STICKER = "super_sticker"
    MEMBERSHIP = "membership"
    POLL = "poll"
    PREDICTION = "prediction"
    HYPE_TRAIN = "hype_train"
    UNKNOWN = "unknown"


@dataclass
class UnifiedEvent:
    """Internal cross-platform event format used by API routes and widgets."""

    platform: str
    event: str
    username: str = ""
    avatar: Optional[str] = None
    amount: Optional[float] = None
    currency: Optional[str] = None
    message: Optional[str] = None
    metadata: Dict[str, Any] = field(default_factory=dict)
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat() + "Z")
    id: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class OAuthToken:
    """Persisted OAuth token record with enough metadata for refresh checks."""

    platform: str
    account_id: str = "default"
    access_token: str = ""
    refresh_token: str = ""
    expires_at: float = 0.0
    scope: Any = field(default_factory=list)
    client_id_hash: str = ""
    token_type: str = "Bearer"

    def is_expiring(self, seconds: int = 300) -> bool:
        return bool(self.access_token) and time.time() >= float(self.expires_at or 0) - seconds

    def is_valid(self) -> bool:
        return bool(self.access_token) and time.time() < float(self.expires_at or 0) - 30


class JsonConfigStore:
    """Small JSON store that keeps secrets out of source code."""

    def __init__(self, base_dir: str = CONFIG_DIR):
        self.base_dir = base_dir
        self.files = {
            "oauth": OAUTH_CONFIG_FILE,
            "platforms": PLATFORMS_CONFIG_FILE,
            "settings": SETTINGS_CONFIG_FILE,
            "secrets": SECRETS_CONFIG_FILE,
            "tokens": TOKENS_CONFIG_FILE,
        }
        os.makedirs(self.base_dir, exist_ok=True)

    def read(self, name: str, default: Any = None) -> Any:
        path = self.files.get(name, name)
        if not os.path.exists(path):
            return default
        try:
            with open(path, "r", encoding="utf-8") as file:
                return json.load(file)
        except Exception as exc:
            log_error("Config", "Failed to read {}: {}".format(path, exc))
            return default

    def write(self, name: str, payload: Any) -> bool:
        path = self.files.get(name, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        tmp_path = path + ".tmp"
        try:
            with open(tmp_path, "w", encoding="utf-8") as file:
                json.dump(payload, file, indent=2, ensure_ascii=False)
            os.replace(tmp_path, path)
            return True
        except Exception as exc:
            log_error("Config", "Failed to write {}: {}".format(path, exc))
            try:
                if os.path.exists(tmp_path):
                    os.unlink(tmp_path)
            except Exception:
                pass
            return False

    def merge_into_runtime_config(self, runtime_config: Dict[str, Any]) -> None:
        settings = self.read("settings", {}) or {}
        platforms = self.read("platforms", {}) or {}
        oauth = self.read("oauth", {}) or {}
        secrets = self.read("secrets", {}) or {}
        for source in (settings, platforms, oauth, secrets):
            if not isinstance(source, dict):
                continue
            for key, value in source.items():
                if key in runtime_config and value not in (None, ""):
                    runtime_config[key] = value


class OAuthManager:
    """Persists and restores OAuth tokens for Twitch, Kick and future platforms."""

    def __init__(self, store: JsonConfigStore):
        self.store = store
        self._lock = threading.RLock()
        self.tokens: Dict[str, Dict[str, OAuthToken]] = {}
        self.restore_tokens()

    @staticmethod
    def _client_hash(client_id: str) -> str:
        return hashlib.sha256((client_id or "").encode("utf-8")).hexdigest()[:16] if client_id else ""

    def restore_tokens(self) -> None:
        payload = self.store.read("tokens", {}) or {}
        restored: Dict[str, Dict[str, OAuthToken]] = {}
        if isinstance(payload, dict):
            for platform, accounts in payload.items():
                if not isinstance(accounts, dict):
                    continue
                restored[platform] = {}
                for account_id, raw in accounts.items():
                    if isinstance(raw, dict):
                        try:
                            restored[platform][account_id] = OAuthToken(**raw)
                        except TypeError:
                            token = OAuthToken(platform=platform, account_id=account_id)
                            for key, value in raw.items():
                                if hasattr(token, key):
                                    setattr(token, key, value)
                            restored[platform][account_id] = token
        with self._lock:
            self.tokens = restored

    def save_tokens(self) -> bool:
        with self._lock:
            payload = {
                platform: {account: token.__dict__ for account, token in accounts.items()}
                for platform, accounts in self.tokens.items()
            }
        return self.store.write("tokens", payload)

    def set_token(self, platform: str, payload: Dict[str, Any], account_id: str = "default", client_id: str = "") -> OAuthToken:
        expires_in = int((payload or {}).get("expires_in", 0) or 0)
        expires_at = float((payload or {}).get("expires_at", 0) or 0)
        if not expires_at and expires_in:
            expires_at = time.time() + max(60, expires_in)
        token = OAuthToken(
            platform=(platform or "").lower(),
            account_id=account_id or "default",
            access_token=((payload or {}).get("access_token") or "").strip(),
            refresh_token=((payload or {}).get("refresh_token") or "").strip(),
            expires_at=expires_at,
            scope=(payload or {}).get("scope") or [],
            client_id_hash=self._client_hash(client_id),
            token_type=(payload or {}).get("token_type") or "Bearer",
        )
        with self._lock:
            self.tokens.setdefault(token.platform, {})[token.account_id] = token
        self.save_tokens()
        return token

    def get_token(self, platform: str, account_id: str = "default") -> Optional[OAuthToken]:
        with self._lock:
            return self.tokens.get((platform or "").lower(), {}).get(account_id or "default")

    def token_matches_client(self, token: Optional[OAuthToken], client_id: str) -> bool:
        if not token:
            return False
        expected_hash = self._client_hash(client_id)
        token_hash = (token.client_id_hash or "").strip()
        return not token_hash or not expected_hash or token_hash == expected_hash

    def status(self) -> Dict[str, Any]:
        with self._lock:
            return {
                platform: {
                    account: {
                        "has_access_token": bool(token.access_token),
                        "has_refresh_token": bool(token.refresh_token),
                        "expires_at": token.expires_at,
                        "valid": token.is_valid(),
                        "scope": token.scope,
                    }
                    for account, token in accounts.items()
                }
                for platform, accounts in self.tokens.items()
            }


class UnifiedEventBus:
    """Thread-safe event buffer for APIs, dashboards and future integrations."""

    def __init__(self, max_events: int = 1000):
        self.max_events = max_events
        self._lock = threading.RLock()
        self._events: List[UnifiedEvent] = []
        self._subscribers: List[Callable[[UnifiedEvent], None]] = []
        self._counter = 0

    def publish(self, event: UnifiedEvent) -> int:
        with self._lock:
            self._counter += 1
            event.id = self._counter
            self._events.append(event)
            if len(self._events) > self.max_events:
                self._events = self._events[-self.max_events:]
            subscribers = list(self._subscribers)
        for callback in subscribers:
            try:
                callback(event)
            except Exception as exc:
                log_error("EventBus", "Subscriber failed: {}".format(exc))
        return event.id

    def subscribe(self, callback: Callable[[UnifiedEvent], None]) -> None:
        with self._lock:
            self._subscribers.append(callback)

    def recent(self, limit: int = 100, after_id: int = 0, platform: str = "", event: str = "") -> List[Dict[str, Any]]:
        limit = max(1, min(int(limit or 100), 500))
        platform = (platform or "").lower()
        event = (event or "").lower()
        with self._lock:
            items = [
                item for item in self._events
                if item.id > int(after_id or 0)
                and (not platform or item.platform.lower() == platform)
                and (not event or item.event.lower() == event)
            ]
            return [item.to_dict() for item in items[-limit:]]

    def statistics(self) -> Dict[str, Any]:
        now = time.time()
        hour_ago = datetime.utcfromtimestamp(now - 3600).isoformat()
        stats = {
            "total_events": 0,
            "last_hour_events": 0,
            "platforms": {},
            "events": {},
            "revenue": 0.0,
            "chat_activity": 0,
        }
        with self._lock:
            for item in self._events:
                stats["total_events"] += 1
                if item.timestamp >= hour_ago:
                    stats["last_hour_events"] += 1
                stats["platforms"][item.platform] = stats["platforms"].get(item.platform, 0) + 1
                stats["events"][item.event] = stats["events"].get(item.event, 0) + 1
                if item.event == UnifiedEventType.CHAT_MESSAGE.value:
                    stats["chat_activity"] += 1
                if item.amount:
                    stats["revenue"] += float(item.amount or 0)
        stats["revenue"] = round(stats["revenue"], 2)
        return stats


class AsyncServiceRuntime:
    """Background asyncio loop for refresh tasks and optional aiohttp pooling."""

    def __init__(self):
        self.loop: Optional[asyncio.AbstractEventLoop] = None
        self.thread: Optional[threading.Thread] = None
        self.stop_event: Optional[asyncio.Event] = None
        self.session = None

    def start(self) -> None:
        if self.thread and self.thread.is_alive():
            return
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _run(self) -> None:
        self.loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self.loop)
        try:
            self.loop.run_until_complete(self._start_async_services())
            self.loop.run_until_complete(self.stop_event.wait())
        finally:
            if self.session:
                self.loop.run_until_complete(self.session.close())
            pending = asyncio.all_tasks(self.loop)
            for task in pending:
                task.cancel()
            self.loop.run_until_complete(asyncio.sleep(0))
            self.loop.close()

    async def _start_async_services(self) -> None:
        self.stop_event = asyncio.Event()
        if aiohttp:
            timeout = aiohttp.ClientTimeout(total=20)
            connector = aiohttp.TCPConnector(limit=32, ttl_dns_cache=300)
            self.session = aiohttp.ClientSession(timeout=timeout, connector=connector)
        asyncio.create_task(self._heartbeat_loop())

    async def _heartbeat_loop(self) -> None:
        while self.stop_event and not self.stop_event.is_set():
            try:
                publish_unified_event(
                    "system",
                    "heartbeat",
                    username="MultiChat",
                    metadata={
                        "aiohttp": bool(aiohttp),
                        "websockets": bool(websockets),
                        "threads": {name: bool(thread and thread.is_alive()) for name, thread in threads.items()},
                    },
                )
            except Exception:
                pass
            await asyncio.sleep(60)

    def stop(self) -> None:
        if self.loop and self.stop_event and self.thread and self.thread.is_alive():
            self.loop.call_soon_threadsafe(self.stop_event.set)
            self.thread.join(timeout=5)


def log_error(component: str, message: str) -> None:
    os.makedirs(LOG_DIR, exist_ok=True)
    line = "{} [{}] {}\n".format(datetime.now().isoformat(timespec="seconds"), component, message)
    try:
        with open(ERROR_LOG_FILE, "a", encoding="utf-8") as file:
            file.write(line)
    except Exception:
        pass
    print("[{}] {}".format(component, message))


def log_app(component: str, message: str, level: str = "INFO") -> None:
    os.makedirs(LOG_DIR, exist_ok=True)
    line = "{} {} [{}] {}\n".format(datetime.now().isoformat(timespec="seconds"), level.upper(), component, message)
    try:
        with open(APP_LOG_FILE, "a", encoding="utf-8") as file:
            file.write(line)
    except Exception:
        pass


json_config_store = JsonConfigStore()
oauth_manager = OAuthManager(json_config_store)
event_bus = UnifiedEventBus()
async_runtime = AsyncServiceRuntime()


def publish_unified_event(platform: str, event: str, username: str = "", avatar: Optional[str] = None, amount: Optional[float] = None, currency: Optional[str] = None, message: Optional[str] = None, metadata: Optional[Dict[str, Any]] = None) -> int:
    unified = UnifiedEvent(
        platform=(platform or "system").lower(),
        event=(event or UnifiedEventType.UNKNOWN.value).lower(),
        username=username or "",
        avatar=avatar,
        amount=amount,
        currency=currency,
        message=message,
        metadata=metadata or {},
    )
    return event_bus.publish(unified)


def describe_token_lifetime(expires_at) -> str:
    """Людською мовою: скільки ще живий токен."""
    try:
        expires_at = float(expires_at or 0)
    except (TypeError, ValueError):
        expires_at = 0.0
    if expires_at <= 0:
        return "термін невідомий"
    left = expires_at - time.time()
    if left <= 0:
        return "ПРОСТРОЧЕНИЙ ({})".format(time.strftime("%Y-%m-%d %H:%M", time.localtime(expires_at)))
    if left < 3600:
        return "ще {} хв".format(int(left / 60))
    return "ще {:.1f} год (до {})".format(left / 3600.0, time.strftime("%Y-%m-%d %H:%M", time.localtime(expires_at)))


def restore_external_configuration() -> None:
    json_config_store.merge_into_runtime_config(config)
    oauth_manager.restore_tokens()
    # Діагностика: показуємо ТОЧНИЙ шлях до файлу з токенами і що з нього
    # прочиталось. Раніше при будь-якій проблемі зі збереженням користувач
    # бачив лише «авторизуйтесь знову» без жодної підказки чому.
    try:
        exists = os.path.isfile(TOKENS_CONFIG_FILE)
        print("[OAuth] Файл токенів: {} ({})".format(
            TOKENS_CONFIG_FILE,
            "знайдено, {} байт".format(os.path.getsize(TOKENS_CONFIG_FILE)) if exists else "НЕ існує — токени ще не зберігались"))
        if not os.access(os.path.dirname(TOKENS_CONFIG_FILE) or ".", os.W_OK):
            print("[OAuth] ⚠️ Немає прав на запис у {} — токени не збережуться між запусками OBS!".format(CONFIG_DIR))
    except Exception as diag_err:
        print("[OAuth] Не вдалося перевірити файл токенів: {}".format(diag_err))

    twitch_client_id = (config.get("twitch_client_id", "") or "").strip()
    twitch_token = oauth_manager.get_token("twitch")
    if twitch_token and twitch_token.access_token:
        matches = oauth_manager.token_matches_client(twitch_token, twitch_client_id)
        if not matches:
            # Не викидаємо токен: Client ID могли просто перезаписати в
            # налаштуваннях. Підтягуємо його, а фактичну придатність
            # перевірить /oauth2/validate + refresh.
            print("[Twitch Auth] ⚠️ Збережений токен видано під інший Client ID. "
                  "Пробую використати його все одно; якщо Twitch відмовить — натисни авторизацію заново "
                  "(http://127.0.0.1:{}/auth/twitch/start).".format(config.get("dock_port", 8080)))
        twitch_user_oauth_cache.update({
            "access_token": twitch_token.access_token,
            "refresh_token": twitch_token.refresh_token,
            "expires_at": twitch_token.expires_at,
            "scope": twitch_token.scope or [],
        })
        config["twitch_irc_oauth"] = "oauth:" + twitch_token.access_token
        print("[Twitch Auth] Токен відновлено з диска: {}; refresh_token {}.".format(
            describe_token_lifetime(twitch_token.expires_at),
            "є" if (twitch_token.refresh_token or "").strip() else "ВІДСУТНІЙ (доведеться авторизуватись вручну)"))
    else:
        print("[Twitch Auth] Збереженого токена немає — потрібна авторизація через /auth/twitch/start")

    kick_token = oauth_manager.get_token("kick")
    if kick_token and kick_token.access_token:
        kick_user_oauth_cache.update({
            "access_token": kick_token.access_token,
            "refresh_token": kick_token.refresh_token,
            "expires_at": kick_token.expires_at,
            "scope": kick_token.scope or "",
        })
        print("[Kick Auth] Токен відновлено з диска: {}; refresh_token {}.".format(
            describe_token_lifetime(kick_token.expires_at),
            "є" if (kick_token.refresh_token or "").strip() else "ВІДСУТНІЙ"))

    # Прострочені токени оновлюємо у фоні, щоб не блокувати старт OBS.
    try:
        threading.Thread(target=oauth_refresh_on_startup, name="oauth-refresh", daemon=True).start()
    except Exception as thread_err:
        print("[OAuth] Не вдалося запустити автооновлення токенів: {}".format(thread_err))


def persist_runtime_configuration() -> None:
    safe_settings = {
        key: value for key, value in config.items()
        if "secret" not in key.lower() and "token" not in key.lower() and "oauth" not in key.lower() and "api_key" not in key.lower()
    }
    platform_settings = {
        "twitch_channel": twitch_effective_channel_login(),
        "kick_chat_url": config.get("kick_chat_url", ""),
        "yt_live_id": config.get("yt_live_id", ""),
        "tt_username": config.get("tt_username", ""),
        "analytics_platforms": config.get("analytics_platforms", {}),
        "filter_platforms": config.get("filter_platforms", {}),
    }
    oauth_settings = {
        "twitch_client_id": config.get("twitch_client_id", ""),
        "kick_client_id": config.get("kick_client_id", ""),
        "redirect_uris": {
            "twitch": TWITCH_DEFAULT_REDIRECT_URI,
            "kick": KICK_DEFAULT_REDIRECT_URI,
        },
    }
    secret_settings = {
        "elevenlabs_api_key": config.get("elevenlabs_api_key", ""),
        "yt_api_key": config.get("yt_api_key", ""),
        "tt_sign_api_key": config.get("tt_sign_api_key", ""),
        "twitch_client_secret": config.get("twitch_client_secret", ""),
        "kick_client_secret": config.get("kick_client_secret", ""),
        "kick_webhook_secret": config.get("kick_webhook_secret", ""),
        "gw_tg_token": config.get("gw_tg_token", ""),
        "sn_tg_token": config.get("sn_tg_token", ""),
        "sn_dc_webhook": config.get("sn_dc_webhook", ""),
        "sn_twitch_client_secret": config.get("sn_twitch_client_secret", ""),
    }
    json_config_store.write("settings", safe_settings)
    json_config_store.write("platforms", platform_settings)
    json_config_store.write("oauth", oauth_settings)
    json_config_store.write("secrets", secret_settings)


def get_platform_status_payload() -> Dict[str, Any]:
    status = {}
    with buffer_lock:
        active_threads = {name: bool(thread and thread.is_alive()) for name, thread in threads.items()}
    for platform in ("tiktok", "twitch", "youtube", "kick"):
        status[platform] = {
            "enabled": bool(config.get("filter_platforms", {}).get(platform, True)),
            "thread_alive": active_threads.get(platform, False) or active_threads.get("{}_eventsub".format(platform), False),
            "configured": bool(
                (platform == "tiktok" and config.get("tt_username"))
                or (platform == "twitch" and twitch_effective_channel_login())
                or (platform == "youtube" and config.get("yt_live_id"))
                or (platform == "kick" and config.get("kick_chat_url"))
            ),
        }
    return status


def get_viewer_payload() -> Dict[str, Any]:
    if analytics_manager:
        stats = analytics_manager.get_current_stats()
    else:
        stats = {"status": "offline", "total_viewers": 0, "platforms": {}}
    stats.setdefault("tiktok_live_viewer_count", int(tiktok_live_viewer_count or 0))
    return stats


def set_youtube_active_targets(targets):
    normalized = set()
    for item in targets or []:
        value = str(item or '').strip()
        if value:
            normalized.add(value)
    with youtube_active_targets_lock:
        youtube_active_targets.clear()
        youtube_active_targets.update(normalized)


def youtube_target_is_active(target):
    value = str(target or '').strip()
    if not value:
        return False
    with youtube_active_targets_lock:
        if not youtube_active_targets:
            return True
        return value in youtube_active_targets


def parse_multivalue_input(raw_value):
    values = []
    for part in re.split(r'[\n\r,;|]+', str(raw_value or '')):
        item = str(part or '').strip()
        if item and item not in values:
            values.append(item)
    return values


def get_youtube_input_sources(raw_value):
    return parse_multivalue_input(raw_value)


def generate_simple_widget_html(widget_name: str) -> str:
    endpoint = {
        "chat": "/api/chat",
        "dashboard": "/api/status",
        "viewers": "/api/viewers",
    }.get(widget_name, "/api/events")
    title = {
        "chat": "MultiChat",
        "dashboard": "Dashboard",
        "viewers": "Viewers",
    }.get(widget_name, "Events")
    return """<!DOCTYPE html><html lang="uk"><head><meta charset="UTF-8"><style>
*{box-sizing:border-box}body{margin:0;background:transparent;color:#fff;font-family:Segoe UI,Arial,sans-serif;overflow:hidden}.panel{width:100vw;min-height:100vh;padding:10px;background:rgba(12,14,18,.72)}h1{margin:0 0 8px;font-size:16px;font-weight:700}.row{display:flex;align-items:center;gap:8px;padding:6px 0;border-bottom:1px solid rgba(255,255,255,.1);font-size:14px}.platform{text-transform:uppercase;font-size:11px;opacity:.75;min-width:58px}.text{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.metric{font-size:28px;font-weight:800}
</style></head><body><div class="panel"><h1>__TITLE__</h1><div id="content"></div></div><script>
const endpoint='__ENDPOINT__';async function load(){try{const r=await fetch(endpoint);const d=await r.json();const c=document.getElementById('content');if(endpoint.includes('chat')){const rows=(d.messages||d||[]).slice(-12).map(m=>`<div class="row"><span class="platform">${m.platform||''}</span><strong>${m.displayName||m.username||''}</strong><span class="text">${m.text||m.message||''}</span></div>`).join('');c.innerHTML=rows||'<div class="row">No messages</div>';}else if(endpoint.includes('viewers')){const p=d.platforms||{};const rows=Object.keys(p).map(k=>`<div class="row"><span class="platform">${k}</span><span class="metric">${(p[k]&&p[k].current)||p[k]||0}</span></div>`).join('');c.innerHTML=`<div class="row"><span class="platform">total</span><span class="metric">${d.total_viewers||0}</span></div>${rows}`;}else{c.innerHTML=Object.keys(d.platforms||d||{}).map(k=>`<div class="row"><span class="platform">${k}</span><span class="text">${JSON.stringify((d.platforms||d)[k])}</span></div>`).join('');}}catch(e){}}load();setInterval(load,2500);
</script></body></html>""".replace("__TITLE__", title).replace("__ENDPOINT__", endpoint)


def handle_generic_webhook(platform: str, headers: Any, payload: Dict[str, Any]) -> bool:
    event_name = pick_first_non_empty(
        headers.get("X-Event-Type", ""),
        headers.get("Twitch-Eventsub-Message-Type", ""),
        headers.get("YouTube-Event-Type", ""),
        payload.get("event") if isinstance(payload, dict) else "",
        payload.get("type") if isinstance(payload, dict) else "",
        "unknown",
    )
    data = payload.get("event") if isinstance(payload.get("event"), dict) else payload.get("data") if isinstance(payload.get("data"), dict) else payload
    user_obj = (data or {}).get("user") or (data or {}).get("chatter") or (data or {}).get("from_broadcaster_user_name") or {}
    username = pick_first_non_empty(
        user_obj.get("login") if isinstance(user_obj, dict) else "",
        user_obj.get("name") if isinstance(user_obj, dict) else "",
        (data or {}).get("username"),
        (data or {}).get("user_name"),
        (data or {}).get("chatter_user_name"),
        platform,
    )
    message = pick_first_non_empty((data or {}).get("message"), (data or {}).get("text"), (data or {}).get("content"), "")
    amount = None
    try:
        amount_value = (data or {}).get("amount") or (data or {}).get("value")
        amount = float(amount_value) if amount_value not in (None, "") else None
    except Exception:
        amount = None
    publish_unified_event(platform, str(event_name).replace(".", "_"), username=username, amount=amount, currency=(data or {}).get("currency"), message=message or None, metadata={"payload": payload})
    return True


# ============================================================================
# LIVE ANALYTICS MODULE
# ============================================================================
class PlatformAdapter(ABC):
    def __init__(self, platform_name: str, config: dict):
        self.platform_name = platform_name
        self.config = config
        self.is_connected = False
        self.viewer_count = 0
        self.is_live = False

    @abstractmethod
    def connect(self) -> bool:
        pass

    @abstractmethod
    def disconnect(self):
        pass

    @abstractmethod
    def get_viewer_count(self) -> int:
        pass

    @abstractmethod
    def is_stream_live(self) -> bool:
        pass

    def get_status(self) -> dict:
        return {"platform": self.platform_name, "connected": self.is_connected, "live": self.is_live, "viewers": self.viewer_count}


class YouTubeAdapter(PlatformAdapter):
    def __init__(self, config: dict):
        super().__init__("YouTube", config)
        self.api_key = config.get("yt_api_key", "")
        self.channel_name = config.get("yt_live_id", "")
        self.video_ids = []

    def connect(self) -> bool:
        if not self.api_key:
            print("[Analytics] YouTube API key не вказано")
            return False
        if not obs.obs_frontend_streaming_active():
            print("[Analytics] YouTube API активується тільки після натискання кнопки 'Почати трансляцію'")
            return False
        self.video_ids = []
        self.viewer_count = 0
        self.is_live = False
        self.is_connected = True
        return True

    def find_active_streams(self):
        if not self.api_key:
            return []
        result = []
        for source in get_youtube_input_sources(self.channel_name):
            for video_id in youtube_expand_live_targets(source, self.api_key):
                if len(str(video_id or '')) == 11 and video_id not in result:
                    result.append(video_id)
        self.video_ids = result
        return result

    def get_viewer_count(self) -> int:
        if not self.is_connected or not self.api_key:
            return 0
        if not obs.obs_frontend_streaming_active():
            self.is_live = False
            self.viewer_count = 0
            return 0
        if not self.video_ids:
            self.find_active_streams()
        if not self.video_ids:
            self.is_live = False
            self.viewer_count = 0
            return 0

        total_viewers = 0
        live_found = False
        refreshed_ids = []
        for video_id in list(self.video_ids):
            url = "https://www.googleapis.com/youtube/v3/videos?part=liveStreamingDetails&id={}&key={}".format(video_id, self.api_key)
            try:
                req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
                with urllib.request.urlopen(req, timeout=10) as response:
                    data = json.loads(response.read().decode('utf-8'))
                if not data.get('items'):
                    continue
                live_details = data['items'][0].get('liveStreamingDetails', {}) or {}
                if live_details:
                    live_found = True
                    refreshed_ids.append(video_id)
                concurrent_viewers = live_details.get('concurrentViewers', 0)
                total_viewers += int(concurrent_viewers or 0)
            except Exception as e:
                print(f"[Analytics] YouTube API error ({video_id}): {e}")
        self.video_ids = refreshed_ids or self.video_ids
        self.viewer_count = int(total_viewers or 0)
        self.is_live = bool(live_found or self.viewer_count > 0)
        return self.viewer_count

    def is_stream_live(self) -> bool:
        self.get_viewer_count()
        return self.is_live

    def disconnect(self):
        self.is_connected = False
        self.is_live = False
        self.viewer_count = 0
        self.video_ids = []


class TikTokAdapter(PlatformAdapter):
    def __init__(self, config: dict):
        super().__init__("TikTok", config)
        self.username = config.get("tt_username", "").lstrip('@')

    def connect(self) -> bool:
        if not self.username:
            print("[Analytics] TikTok username не вказано")
            return False
        if not TIKTOK_AVAILABLE:
            print("[Analytics] TikTokLive бібліотека недоступна для analytics")
            return False
        self.is_connected = True
        return True

    def get_viewer_count(self) -> int:
        global tiktok_live_viewer_count, tiktok_live_is_active, tiktok_last_viewer_update_ts, tiktok_last_room_info_debug_ts
        if not self.is_connected or not self.username:
            self.viewer_count = 0
            self.is_live = False
            return 0

        now = time.time()
        cached_viewers = int(tiktok_live_viewer_count or 0)
        last_update = float(tiktok_last_viewer_update_ts or 0)
        if last_update and now - last_update <= 180:
            self.viewer_count = cached_viewers
            self.is_live = bool(tiktok_live_is_active or self.viewer_count > 0)
            if now - float(tiktok_last_room_info_debug_ts or 0) >= 30:
                tiktok_last_room_info_debug_ts = now
                print('[TikTok Analytics] cached viewer_count={} | is_live={} | last_update_age={:.1f}s'.format(self.viewer_count, self.is_live, max(0.0, now - last_update)))
            return self.viewer_count

        room_info = tiktok_try_retrieve_room_info(self.username, min_refresh_interval=45)
        if isinstance(room_info, dict) and room_info:
            try:
                status = int(room_info.get('status', 0) or 0)
            except Exception:
                status = 0
            try:
                user_count = int(room_info.get('user_count', 0) or 0)
            except Exception:
                user_count = 0
            try:
                total_user = int(((room_info.get('stats') or {}).get('total_user', 0)) or 0)
            except Exception:
                total_user = 0
            try:
                like_count = int(((room_info.get('stats') or {}).get('like_count', 0)) or 0)
            except Exception:
                like_count = 0
            print('[TikTok Analytics] room_info fallback | username=@{} | status={} | user_count={} | total_user={} | like_count={}'.format(self.username, status, user_count, total_user, like_count))
            self.viewer_count = max(0, user_count)
            self.is_live = status == 2 or self.viewer_count > 0
            tiktok_live_viewer_count = self.viewer_count
            tiktok_live_is_active = self.is_live
            if self.viewer_count > 0:
                tiktok_last_viewer_update_ts = now
            return self.viewer_count

        if tiktok_live_is_active and last_update and now - last_update <= 300:
            self.viewer_count = cached_viewers
            self.is_live = True
            return self.viewer_count

        self.viewer_count = cached_viewers
        self.is_live = bool(tiktok_live_is_active or self.viewer_count > 0)
        return self.viewer_count

    def is_stream_live(self) -> bool:
        self.get_viewer_count()
        return self.is_live

    def disconnect(self):
        self.is_connected = False


class TwitchAdapter(PlatformAdapter):
    def __init__(self, config: dict):
        super().__init__("Twitch", config)
        self.channel = twitch_effective_channel_login()
        self.client_id = config.get("twitch_client_id", "")
        self.client_secret = config.get("twitch_client_secret", "")

    def connect(self) -> bool:
        if not self.channel:
            return False
        self.is_connected = True
        return True

    def _get_app_access_token(self):
        global twitch_app_token_cache
        if not self.client_id or not self.client_secret:
            return None
        now = time.time()
        cached_token = twitch_app_token_cache.get("access_token") or ""
        expires_at = float(twitch_app_token_cache.get("expires_at") or 0)
        if cached_token and expires_at - now > 60:
            return cached_token
        try:
            data = urllib.parse.urlencode({
                'client_id': self.client_id,
                'client_secret': self.client_secret,
                'grant_type': 'client_credentials'
            }).encode('utf-8')
            req = urllib.request.Request('https://id.twitch.tv/oauth2/token', data=data, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=10) as response:
                payload = json.loads(response.read().decode('utf-8'))
            token = payload.get('access_token') or ''
            expires_in = int(payload.get('expires_in') or 0)
            if token:
                twitch_app_token_cache['access_token'] = token
                twitch_app_token_cache['expires_at'] = now + max(0, expires_in)
                return token
        except Exception as e:
            print(f"[Analytics] Twitch token error: {e}")
        return None

    def _get_viewer_count_via_api(self):
        token = self._get_app_access_token()
        if not token or not self.client_id:
            return None
        channel = self.channel.strip().lstrip('@').strip('/')
        url = f'https://api.twitch.tv/helix/streams?user_login={urllib.parse.quote(channel)}'
        headers = {
            'User-Agent': 'Mozilla/5.0',
            'Authorization': f'Bearer {token}',
            'Client-Id': self.client_id
        }
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=10) as response:
                data = json.loads(response.read().decode('utf-8'))
            items = data.get('data') or []
            if items:
                self.viewer_count = int(items[0].get('viewer_count', 0) or 0)
                self.is_live = True
                return self.viewer_count
            self.viewer_count = 0
            self.is_live = False
            return 0
        except Exception as e:
            print(f"[Analytics] Twitch Helix error: {e}")
            return None

    def _get_viewer_count_via_fallback_parse(self):
        channel = self.channel.strip().lstrip('@').strip('/')
        urls = [
            f'https://www.twitch.tv/{urllib.parse.quote(channel)}',
            f'https://www.twitch.tv/popout/{urllib.parse.quote(channel)}/chat?popout='
        ]
        headers = {
            'User-Agent': 'Mozilla/5.0',
            'Accept-Language': 'en-US,en;q=0.9',
            'Accept': 'text/html,application/json;q=0.9,*/*;q=0.8'
        }
        patterns = [
            r'"viewersCount":\s*([0-9]+)',
            r'"viewerCount":\s*([0-9]+)',
            r'"viewer_count":\s*([0-9]+)',
            r'"streamViewersCount":\s*([0-9]+)'
        ]
        for url in urls:
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=10) as response:
                    html = response.read().decode('utf-8', 'ignore')
                for pattern in patterns:
                    match = re.search(pattern, html)
                    if match:
                        self.viewer_count = int(match.group(1) or 0)
                        self.is_live = self.viewer_count > 0
                        return self.viewer_count
            except Exception as e:
                print(f"[Analytics] Twitch parse error: {e}")
        return None

    def get_viewer_count(self) -> int:
        if not self.is_connected or not self.channel:
            return 0
        api_value = self._get_viewer_count_via_api()
        if api_value is not None:
            return api_value
        parsed_value = self._get_viewer_count_via_fallback_parse()
        if parsed_value is not None:
            return parsed_value
        self.viewer_count = 0
        self.is_live = False
        return 0

    def is_stream_live(self) -> bool:
        self.get_viewer_count()
        return self.is_live

    def disconnect(self):
        self.is_connected = False


class KickAdapter(PlatformAdapter):
    def __init__(self, config: dict):
        super().__init__("Kick", config)
        self.channel_url = config.get("kick_chat_url", "")
        self.client_id = config.get("kick_client_id", "")
        self.client_secret = config.get("kick_client_secret", "")
        self.slug = None
        self.channel_page_url = ""
        self._last_error_log = 0.0

    def connect(self) -> bool:
        if not self.channel_url:
            return False
        self.slug = extract_kick_slug(self.channel_url)
        self.slug = (self.slug or '').strip('/').lower()
        if not self.slug:
            return False
        self.channel_page_url = "https://kick.com/{}".format(self.slug)
        self.is_connected = True
        return True

    def get_viewer_count(self) -> int:
        if not self.slug:
            return 0

        has_official_credentials = bool((self.client_id or '').strip() and (self.client_secret or '').strip())
        official_data = kick_fetch_public_channel(self.slug, self.client_id, self.client_secret, timeout=10, log_errors=False)
        if official_data:
            try:
                stream = official_data.get('stream') or official_data.get('livestream') or {}
                viewer_value = (
                    stream.get('viewer_count')
                    if isinstance(stream, dict) and stream.get('viewer_count') is not None
                    else official_data.get('viewer_count')
                )
                self.viewer_count = int(viewer_value or 0)
                is_live_value = stream.get('is_live') if isinstance(stream, dict) else None
                if is_live_value is None:
                    is_live_value = official_data.get('is_live') or official_data.get('live')
                self.is_live = bool(is_live_value or self.viewer_count > 0)
                return self.viewer_count
            except Exception as e:
                now = time.time()
                if now - self._last_error_log >= 60:
                    print(f"[Analytics] Kick official API parse error: {e}")
                    self._last_error_log = now
        elif has_official_credentials:
            now = time.time()
            if now - self._last_error_log >= 60:
                print("[Analytics] Kick official API returned no channel data for slug='{}'. Check that Kick Client ID/Secret are saved and the app has channel:read scope.".format(self.slug))
                self._last_error_log = now
            self.viewer_count = 0
            self.is_live = False
            return 0

        url = "https://kick.com/api/v2/channels/{}".format(urllib.parse.quote(self.slug))
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
            'Accept': 'application/json',
            'Origin': 'https://kick.com',
            'Referer': self.channel_page_url or 'https://kick.com/'
        }
        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=10) as response:
                data = json.loads(response.read().decode('utf-8'))
                livestream = data.get('livestream') or {}
                self.viewer_count = int(livestream.get('viewer_count', 0) or 0)
                self.is_live = bool(livestream)
                return self.viewer_count
        except Exception as e:
            now = time.time()
            if now - self._last_error_log >= 60:
                print(f"[Analytics] Kick API error: {e}")
                if not ((self.client_id or '').strip() and (self.client_secret or '').strip()):
                    print("[Analytics] Kick hint: заповніть Kick Client ID/Secret, щоб analytics бралася з офіційного API /public/v1/channels замість нестабільного website v2 endpoint.")
                self._last_error_log = now
            self.is_live = False
        return 0

    def is_stream_live(self) -> bool:
        self.get_viewer_count()
        return self.is_live

    def disconnect(self):
        self.is_connected = False


# ---------------------------------------------------------------------------
# СЕСІЯ СТРИМУ (окремо від стану підключення платформ)
# ---------------------------------------------------------------------------
# Раніше стан "чи йде стрим" жив ВИКЛЮЧНО в екземплярі ObsStreamStateManager,
# який створювався заново на кожен run_services(). Після будь-якого
# перезапуску сервісів is_streaming=False, і перший же тік монітора бачив
# "OBS стримить, а я про це не знав" -> _on_stream_started() -> у Telegram/
# Discord знову летіло "ТРАНСЛЯЦІЮ РОЗПОЧАТО!", а статистика стриму
# починалась з нуля, хоча трансляція не переривалась.
# Тепер сесія стриму живе на рівні модуля і переживає перезапуск сервісів.
STREAM_SESSION_OFFLINE_CONFIRMATIONS = 3  # скільки тіків підряд OBS має казати "офлайн"

stream_session_lock = threading.RLock()
_stream_session_counter = 0
stream_session = {
    "id": 0,
    "active": False,
    "start_time": None,
    "record": None,
    "peak_viewers": 0,
    "reason": None,
}


def stream_session_is_active():
    with stream_session_lock:
        return bool(stream_session.get("active"))


def stream_session_begin(reason='obs_stream_started'):
    """Створює НОВУ сесію стриму. Викликається лише коли OBS реально
    почав нову трансляцію (а не коли перезапустились сервіси)."""
    global _stream_session_counter
    with stream_session_lock:
        _stream_session_counter += 1
        stream_session.update({
            "id": _stream_session_counter,
            "active": True,
            "start_time": time.time(),
            "record": None,
            "peak_viewers": 0,
            "reason": reason,
        })
        return dict(stream_session)


def stream_session_end(reason='obs_stream_stopped'):
    with stream_session_lock:
        finished = dict(stream_session)
        stream_session.update({
            "active": False,
            "start_time": None,
            "record": None,
            "peak_viewers": 0,
            "reason": reason,
        })
        return finished


def stream_session_attach_record(record):
    """Прив'язує до сесії запис статистики, щоб він пережив перестворення
    LiveStatisticsStorage під час перезапуску сервісів."""
    with stream_session_lock:
        stream_session["record"] = record


def stream_session_set_peak(value):
    with stream_session_lock:
        if value and value > (stream_session.get("peak_viewers") or 0):
            stream_session["peak_viewers"] = value


def stream_session_snapshot():
    with stream_session_lock:
        snap = dict(stream_session)
    snap.pop("record", None)
    snap["uptime"] = (time.time() - snap["start_time"]) if snap.get("start_time") else 0
    return snap


class LiveStatisticsStorage:
    def __init__(self, data_dir: str):
        self.data_dir = data_dir
        self.current_stream = None
        self.stream_history = []
        self.viewer_history = []
        self.peak_viewers = 0
        self.stream_start_time = None
        os.makedirs(data_dir, exist_ok=True)
        self._load_history()
        self._adopt_active_session()

    def _adopt_active_session(self):
        """Якщо сесія стриму вже активна (сервіси перезапустились посеред
        живого стриму) — підхоплюємо існуючий запис, а не починаємо з нуля."""
        with stream_session_lock:
            record = stream_session.get("record")
            if stream_session.get("active") and record:
                self.current_stream = record
                self.stream_start_time = stream_session.get("start_time") or record.get("start_time")
                self.peak_viewers = stream_session.get("peak_viewers") or 0
                print("[Stream] Відновлено активну сесію стриму #{} після перезапуску сервісів".format(
                    stream_session.get("id")))

    def start_stream(self):
        with stream_session_lock:
            record = stream_session.get("record")
            if stream_session.get("active") and record:
                # Сесія вже існує — це перезапуск сервісів, а не новий стрим.
                self.current_stream = record
                self.stream_start_time = stream_session.get("start_time") or record.get("start_time")
                self.peak_viewers = stream_session.get("peak_viewers") or 0
                print("[Stream] OBS still LIVE → preserving current stream session #{}".format(
                    stream_session.get("id")))
                return
        self.stream_start_time = time.time()
        self.current_stream = {
            "start_time": self.stream_start_time,
            "start_datetime": datetime.now().isoformat(),
            "platforms": {},
            "peak_viewers": 0,
            "avg_viewers": 0,
            "viewer_samples": []
        }
        self.viewer_history.clear()
        self.peak_viewers = 0
        stream_session_attach_record(self.current_stream)
        print("[Analytics] 🔴 Новий стрим розпочато")

    def end_stream(self):
        if not self.current_stream:
            return
        end_time = time.time()
        duration = end_time - self.stream_start_time
        samples = self.current_stream["viewer_samples"]
        if samples:
            avg = sum(samples) / len(samples)
            self.current_stream["avg_viewers"] = round(avg, 2)

        self.current_stream.update({
            "end_time": end_time,
            "end_datetime": datetime.now().isoformat(),
            "duration_seconds": duration,
            "peak_viewers": self.peak_viewers
        })
        self.stream_history.append(self.current_stream)
        self._save_history()
        print(f"[Analytics] ⚫ Стрим завершено. Тривалість: {duration/60:.1f} хв, Пік: {self.peak_viewers}, Середній: {self.current_stream['avg_viewers']}")
        self.current_stream = None
        stream_session_attach_record(None)

    def update_viewer_count(self, platform: str, count: int, total: int):
        if not self.current_stream:
            return
        if platform not in self.current_stream["platforms"]:
            self.current_stream["platforms"][platform] = {"current": 0, "peak": 0, "samples": []}

        plat_data = self.current_stream["platforms"][platform]
        plat_data["current"] = count
        plat_data["peak"] = max(plat_data["peak"], count)
        plat_data["samples"].append(count)

    def finalize_viewer_cycle(self, total: int, platform_stats: dict):
        if not self.current_stream:
            return
        timestamp = time.time()
        self.current_stream["viewer_samples"].append(total)
        self.peak_viewers = max(self.peak_viewers, total)
        stream_session_set_peak(self.peak_viewers)
        self.viewer_history.append({"timestamp": timestamp, "total": total, "platforms": dict(platform_stats or {})})

    def get_current_stats(self) -> dict:
        if not self.current_stream:
            return {"status": "offline", "total_viewers": 0, "peak_viewers": 0, "platforms": {}, "duration": 0}

        duration = time.time() - self.stream_start_time
        platforms = {}
        total = 0
        for platform, data in self.current_stream["platforms"].items():
            platforms[platform] = {"current": data["current"], "peak": data["peak"]}
            total += data["current"]

        return {"status": "live", "duration": duration, "total_viewers": total, "peak_viewers": self.peak_viewers, "platforms": platforms, "start_time": self.stream_start_time}

    def _save_history(self):
        history_file = os.path.join(self.data_dir, "stream_history.json")
        try:
            with open(history_file, 'w', encoding='utf-8') as f:
                json.dump(self.stream_history, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"[Analytics] Error saving history: {e}")

    def _load_history(self):
        history_file = os.path.join(self.data_dir, "stream_history.json")
        if os.path.exists(history_file):
            try:
                with open(history_file, 'r', encoding='utf-8') as f:
                    self.stream_history = json.load(f)
                print(f"[Analytics] Завантажено історію: {len(self.stream_history)} стримів")
            except Exception as e:
                print(f"[Analytics] Error loading history: {e}")


class ObsStreamStateManager:
    def __init__(self):
        self.is_streaming = False
        self.is_recording = False
        self.stream_start_time = None
        self._offline_ticks = 0
        self._first_tick = True
        self._monitor_thread = None
        self._stop_event = threading.Event()
        self._callbacks = {'stream_started': [], 'stream_ended': [], 'recording_started': [], 'recording_stopped': []}

    def start_monitoring(self):
        if self._monitor_thread and self._monitor_thread.is_alive():
            return
        self._stop_event.clear()
        self._monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self._monitor_thread.start()
        print("[Analytics] 🔍 OBS Stream State Monitor запущено")

    def stop_monitoring(self):
        self._stop_event.set()
        if self._monitor_thread:
            self._monitor_thread.join(timeout=2)
        print("[Analytics] ⚫ OBS Stream State Monitor зупинено")

    def _monitor_loop(self):
        while not self._stop_event.is_set():
            try:
                current_streaming = obs.obs_frontend_streaming_active()
                current_recording = obs.obs_frontend_recording_active()

                if self._first_tick:
                    # Перший тік після (пере)запуску: синхронізуємось із OBS
                    # МОВЧКИ. Якщо трансляція вже йде і сесія активна — це
                    # перезапуск сервісів, а не новий стрим.
                    self._first_tick = False
                    self.is_streaming = current_streaming
                    self.is_recording = current_recording
                    self._offline_ticks = 0
                    if current_streaming and stream_session_is_active():
                        snap = stream_session_snapshot()
                        self.stream_start_time = snap.get("start_time")
                        print("[Stream] OBS still LIVE → preserving current stream session #{}".format(
                            snap.get("id")))
                    elif current_streaming:
                        self._on_stream_started()
                    elif stream_session_is_active():
                        # Сервіси перезапустились уже після завершення стриму.
                        print("[Stream] OBS is offline → closing stale stream session")
                        self._on_stream_ended()
                    time.sleep(1)
                    continue

                if current_streaming and not self.is_streaming:
                    self._offline_ticks = 0
                    self._on_stream_started()
                elif not current_streaming and self.is_streaming:
                    # Дебаунс: одне «офлайн» від OBS API не закриває сесію,
                    # інакше блимання дає LIVE→STOP→LIVE і повторне
                    # "ТРАНСЛЯЦІЮ РОЗПОЧАТО!".
                    self._offline_ticks += 1
                    if self._offline_ticks < STREAM_SESSION_OFFLINE_CONFIRMATIONS:
                        print("[Stream] OBS reports offline ({}/{}) → waiting for confirmation".format(
                            self._offline_ticks, STREAM_SESSION_OFFLINE_CONFIRMATIONS))
                        self.is_recording = current_recording
                        time.sleep(1)
                        continue
                    self._on_stream_ended()
                    self.is_streaming = False
                    self._offline_ticks = 0
                else:
                    self._offline_ticks = 0
                    self.is_streaming = current_streaming

                if current_recording and not self.is_recording:
                    self._on_recording_started()
                if not current_recording and self.is_recording:
                    self._on_recording_stopped()
                self.is_recording = current_recording
            except Exception as e:
                print(f"[Analytics] Monitor error: {e}")
            time.sleep(1)

    def _on_stream_started(self):
        if stream_session_is_active():
            # Захист від подвійного старту: сесія вже є, нового стриму немає.
            snap = stream_session_snapshot()
            self.stream_start_time = snap.get("start_time")
            self.is_streaming = True
            print("[Stream] OBS still LIVE → preserving current stream session #{}".format(
                snap.get("id")))
            return
        info = stream_session_begin('obs_stream_started')
        self.stream_start_time = info.get("start_time")
        self.is_streaming = True
        print("[Stream] New stream detected → creating new stream session #{}".format(info.get("id")))
        print("[Analytics] 🔴 ТРАНСЛЯЦІЮ РОЗПОЧАТО!")
        self._trigger_callbacks('stream_started')

    def _on_stream_ended(self):
        if not stream_session_is_active():
            self.stream_start_time = None
            self.is_streaming = False
            return
        snap = stream_session_snapshot()
        duration = time.time() - self.stream_start_time if self.stream_start_time else snap.get("uptime", 0)
        print("[Stream] Stream session #{} closed reason=obs_stream_stopped".format(snap.get("id")))
        print(f"[Analytics] ⚫ ТРАНСЛЯЦІЮ ЗАВЕРШЕНО! Тривалість: {duration/60:.1f} хв")
        self._trigger_callbacks('stream_ended')
        stream_session_end('obs_stream_stopped')
        self.stream_start_time = None
        self.is_streaming = False

    def _on_recording_started(self):
        print("[Analytics] 🔴 ЗАПИС РОЗПОЧАТО")
        self._trigger_callbacks('recording_started')

    def _on_recording_stopped(self):
        print("[Analytics] ⚫ ЗАПИС ЗАВЕРШЕНО")
        self._trigger_callbacks('recording_stopped')

    def on_stream_started(self, callback):
        self._callbacks['stream_started'].append(callback)

    def on_stream_ended(self, callback):
        self._callbacks['stream_ended'].append(callback)

    def _trigger_callbacks(self, event: str):
        for callback in self._callbacks.get(event, []):
            try:
                callback()
            except Exception as e:
                print(f"[Analytics] Callback error for {event}: {e}")

    def get_status(self) -> dict:
        return {"streaming": self.is_streaming, "recording": self.is_recording,
                "stream_session": stream_session_snapshot(), "stream_start_time": self.stream_start_time, "uptime": time.time() - self.stream_start_time if self.stream_start_time else 0}


class LiveAnalyticsManager:
    def __init__(self, config: dict):
        self.config = config
        self.is_running = False
        self._update_thread = None
        self._stop_event = threading.Event()

        data_dir = os.path.join(tempfile.gettempdir(), analytics_data_dir)
        print(f"[Analytics] Data dir: {data_dir}")
        self.storage = LiveStatisticsStorage(data_dir)
        self.obs_monitor = ObsStreamStateManager()
        self.adapters = {}

        self._init_adapters()
        self._setup_obs_callbacks()
        print("[Analytics] ✅ LiveAnalyticsManager ініціалізовано")

    def _init_adapters(self):
        analytics_config = self.config.get("analytics_platforms", {})
        if analytics_config.get("youtube", False):
            self.adapters["youtube"] = YouTubeAdapter(self.config)
            print("[Analytics] ✅ YouTube adapter ініціалізовано")
        if analytics_config.get("tiktok", False):
            self.adapters["tiktok"] = TikTokAdapter(self.config)
            print("[Analytics] ✅ TikTok adapter ініціалізовано")
        if analytics_config.get("twitch", False):
            self.adapters["twitch"] = TwitchAdapter(self.config)
            print("[Analytics] ✅ Twitch adapter ініціалізовано")
        if analytics_config.get("kick", False):
            self.adapters["kick"] = KickAdapter(self.config)
            print("[Analytics] ✅ Kick adapter ініціалізовано")

    def _setup_obs_callbacks(self):
        self.obs_monitor.on_stream_started(self._on_stream_started)
        self.obs_monitor.on_stream_ended(self._on_stream_ended)

    def start(self):
        if self.is_running:
            print("[Analytics] ⚠️ LiveAnalytics вже запущено")
            return
        self.is_running = True
        self._stop_event.clear()
        self.obs_monitor.start_monitoring()
        self._update_thread = threading.Thread(target=self._update_loop, daemon=True)
        self._update_thread.start()
        if stream_session_is_active():
            self._resume_stream_session()
        else:
            print("[Analytics] 📊 LiveAnalytics запущено (очікування початку стриму)")

    def _resume_stream_session(self):
        """Сервіси перезапустились посеред живого стриму: підключаємо
        адаптери і продовжуємо ту саму сесію. НЕ публікуємо STREAM_ONLINE,
        щоб у Telegram/Discord не летіло повторне повідомлення про початок."""
        snap = stream_session_snapshot()
        print("[Stream] OBS still LIVE → preserving current stream session #{} (analytics resumed)".format(
            snap.get("id")))
        self.obs_monitor.is_streaming = True
        self.obs_monitor.stream_start_time = snap.get("start_time")
        for platform, adapter in self.adapters.items():
            try:
                if adapter.connect():
                    print("[Analytics] ✅ {} перепідключено".format(platform))
            except Exception as e:
                print("[Analytics] ❌ {} помилка перепідключення: {}".format(platform, e))

    def stop(self):
        if not self.is_running:
            return
        self.is_running = False
        self._stop_event.set()
        self.obs_monitor.stop_monitoring()
        for adapter in self.adapters.values():
            try:
                adapter.disconnect()
            except Exception as e:
                print(f"[Analytics] Error disconnecting adapter: {e}")
        print("[Analytics] ⚫ LiveAnalytics зупинено")

    def _on_stream_started(self):
        print("[Analytics] 🔴 Стрим розпочато - активую збір статистики")
        publish_unified_event("system", UnifiedEventType.STREAM_ONLINE.value, username="OBS", metadata={"source": "obs_frontend"})
        for platform, adapter in self.adapters.items():
            try:
                if adapter.connect():
                    print(f"[Analytics] ✅ {platform} підключено")
            except Exception as e:
                print(f"[Analytics] ❌ {platform} помилка підключення: {e}")
        self.storage.start_stream()

    def _on_stream_ended(self):
        print("[Analytics] ⚫ Стрим завершено - зберігаю статистику")
        publish_unified_event("system", UnifiedEventType.STREAM_OFFLINE.value, username="OBS", metadata={"source": "obs_frontend"})
        self.storage.end_stream()
        for platform, adapter in self.adapters.items():
            try:
                adapter.disconnect()
                print(f"[Analytics] ⚫ {platform} відключено")
            except Exception as e:
                print(f"[Analytics] ⚠️ {platform} помилка відключення: {e}")

    def _update_loop(self):
        update_interval = self.config.get("analytics_update_interval", 5)
        while not self._stop_event.is_set():
            try:
                if self.obs_monitor.is_streaming:
                    self._update_statistics()
                else:
                    time.sleep(2)
                    continue
            except Exception as e:
                print(f"[Analytics] Update loop error: {e}")
            time.sleep(update_interval)

    def _update_statistics(self):
        total_viewers = 0
        platform_stats = {}
        for platform, adapter in self.adapters.items():
            try:
                count = adapter.get_viewer_count()
                platform_stats[platform] = count
                total_viewers += count
                self.storage.update_viewer_count(platform, count, total_viewers)
                publish_unified_event(platform, UnifiedEventType.VIEWER_COUNT.value, metadata={"viewer_count": count})
            except Exception as e:
                print(f"[Analytics] {platform} update error: {e}")

        self.storage.finalize_viewer_cycle(total_viewers, platform_stats)
        if total_viewers > 0:
            stats_str = " | ".join(["{}: {}".format(p, c) for p, c in platform_stats.items()])
            print(f"[Analytics] 📊 Онлайн: {total_viewers} | {stats_str}")

    def get_current_stats(self) -> dict:
        return self.storage.get_current_stats()

    def get_stream_history(self) -> list:
        return self.storage.stream_history

    def get_widget_html(self) -> str:
        mode = self.config.get("analytics_widget_mode", "compact")
        font_size = self.config.get("analytics_widget_font_size", 16)
        text_color = self.config.get("analytics_widget_text_color", "#ffffff")
        bg_color = self.config.get("analytics_widget_bg_color", "rgba(0,0,0,0.7)")
        widget_platforms = self.config.get("analytics_widget_platforms", {}) or {}
        ordered_platforms = [p for p in ("youtube", "tiktok", "twitch", "kick") if widget_platforms.get(p, True)]
        if not ordered_platforms:
            ordered_platforms = ["youtube", "tiktok", "twitch", "kick"]
        meta = {
            "youtube": {"id": "yt", "label": "YouTube", "abbr": "YT", "icon": ANALYTICS_ICON_DATA.get("youtube", "")},
            "tiktok": {"id": "tt", "label": "TikTok", "abbr": "TT", "icon": ANALYTICS_ICON_DATA.get("tiktok", "")},
            "twitch": {"id": "tw", "label": "Twitch", "abbr": "TW", "icon": ANALYTICS_ICON_DATA.get("twitch", "")},
            "kick": {"id": "kick", "label": "Kick", "abbr": "KK", "icon": ANALYTICS_ICON_DATA.get("kick", "")},
        }
        compact_mode = str(mode or "compact") == "compact"
        html = """<!DOCTYPE html>
<html lang="uk">
<head><meta charset="UTF-8"><style>
*{margin:0;padding:0;box-sizing:border-box}body{font-family:'Segoe UI',sans-serif;background:transparent;color:__TEXT_COLOR__;overflow:hidden;font-size:__FONT_SIZE__px}.widget-container{display:flex;flex-wrap:wrap;gap:8px;padding:__PADDING__;background:__BG_COLOR__;border-radius:12px;align-items:center;min-width:__MIN_WIDTH__}.platform-item,.platform-stat{display:flex;align-items:center;gap:8px;padding:6px 10px;background:rgba(255,255,255,0.08);border-radius:10px}.platform-item{justify-content:center;min-width:72px}.platform-stat{justify-content:space-between;width:100%}.platform-label{display:flex;align-items:center;gap:8px;font-weight:600}.platform-icon,.platform-fallback{display:inline-flex;align-items:center;justify-content:center;width:24px;height:24px;flex:0 0 24px}.platform-icon img{width:24px;height:24px;display:block;object-fit:contain;border-radius:6px}.platform-fallback{border-radius:6px;background:rgba(255,255,255,0.16);font-size:.72em;font-weight:700}.viewer-count{font-weight:700;font-size:1.05em;min-width:20px;text-align:right}.total-stats{width:100%;margin-top:4px;padding-top:8px;border-top:2px solid rgba(255,255,255,0.25);text-align:center;font-weight:bold}.total-viewers{font-size:1.5em;color:#ffd700}.peak-viewers{font-size:0.85em;opacity:0.8}
</style></head>
<body><div class="widget-container" id="widget"></div>
<script>
const compactMode=__COMPACT__;
const selectedPlatforms=__PLATFORMS__;
const meta=__META__;
function iconHtml(p){const m=meta[p]||{};return m.icon?`<span class="platform-icon"><img src="${m.icon}" alt="${m.label||p}"></span>`:`<span class="platform-fallback">${m.abbr||String(p).slice(0,2).toUpperCase()}</span>`;}
function buildLayout(){const root=document.getElementById('widget');if(compactMode){root.innerHTML=selectedPlatforms.map(p=>{const m=meta[p]||{};return `<div class="platform-item">${iconHtml(p)}<span class="viewer-count" id="${m.id||p}-viewers">0</span></div>`;}).join('');}else{root.innerHTML=selectedPlatforms.map(p=>{const m=meta[p]||{};return `<div class="platform-stat"><span class="platform-label">${iconHtml(p)}${m.label||p}</span><span id="${m.id||p}-viewers">0</span></div>`;}).join('')+`<div class="total-stats"><div class="total-viewers"><span id="total">0</span> 👁️</div><div class="peak-viewers">Пік: <span id="peak">0</span></div></div>`;}}
async function updateStats(){try{const res=await fetch('/analytics/stats');const data=await res.json();const p=(data&&data.platforms)||{};selectedPlatforms.forEach(platform=>{const m=meta[platform]||{};const el=document.getElementById(`${m.id||platform}-viewers`);if(el){el.textContent=((p[platform]&&p[platform].current)||0);}});const total=document.getElementById('total');if(total){total.textContent=data.total_viewers||0;}const peak=document.getElementById('peak');if(peak){peak.textContent=data.peak_viewers||0;}}catch(e){console.error(e);}}
buildLayout();updateStats();setInterval(updateStats,3000);
</script></body></html>"""
        html = html.replace('__TEXT_COLOR__', str(text_color))
        html = html.replace('__FONT_SIZE__', str(font_size))
        html = html.replace('__BG_COLOR__', str(bg_color))
        html = html.replace('__COMPACT__', 'true' if compact_mode else 'false')
        html = html.replace('__PLATFORMS__', json.dumps(ordered_platforms, ensure_ascii=False))
        html = html.replace('__META__', json.dumps(meta, ensure_ascii=False))
        html = html.replace('__PADDING__', '6px 10px' if compact_mode else '10px')
        html = html.replace('__MIN_WIDTH__', 'auto' if compact_mode else '220px')
        return html


# ============================================================================
# МОНІТОРИНГ ІНТЕРНЕТ-З'ЄДНАННЯ (ping / packet loss / download / upload)
# ============================================================================
NETMON_STATE_UNKNOWN = "unknown"
NETMON_STATE_STABLE = "stable"
NETMON_STATE_UNSTABLE = "unstable"


# Статистика OBS (пропущені кадри). ЧИТАЄТЬСЯ ЛИШЕ З ГОЛОВНОГО ПОТОКУ через
# obs.timer_add у script_load - звертатись до obspython з робочих потоків
# заборонено (саме це раніше валило OBS на кнопці розіграшу).
obs_stream_stats = {
    "streaming": False,
    "dropped": None,
    "total": None,
    "percent": None,
    "fps": None,
    "updated": 0.0,
}


# Список джерел OBS для чекбоксів вибору джерела дакінгу музики.
# ЧИТАЄТЬСЯ ЛИШЕ З ГОЛОВНОГО ПОТОКУ через obs.timer_add у script_load -
# HTTP-обробники лише читають вже наповнений список, самі obspython не кличуть.
obs_sources_cache = {
    "names": [],
    "updated": 0.0,
}


def obs_sources_list_tick():
    """Оновлює кеш назв джерел OBS. Викликається таймером OBS."""
    try:
        names = []
        sources = obs.obs_enum_sources() or []
        try:
            for src in sources:
                try:
                    name = obs.obs_source_get_name(src)
                    if name:
                        names.append(name)
                except Exception:
                    continue
        finally:
            try:
                obs.source_list_release(sources)
            except Exception:
                pass
        names.sort(key=lambda s: s.lower())
        obs_sources_cache["names"] = names
        obs_sources_cache["updated"] = time.time()
    except Exception as e:
        print("[MultiChat] [OBS] Не вдалося оновити список джерел: {}".format(e))


def netmon_obs_stats_tick():
    """Знімає статистику вихідного потоку OBS. Викликається таймером OBS."""
    try:
        output = None
        try:
            output = obs.obs_frontend_get_streaming_output()
        except Exception:
            output = None
        if not output:
            obs_stream_stats["streaming"] = False
            obs_stream_stats["dropped"] = None
            obs_stream_stats["total"] = None
            obs_stream_stats["percent"] = None
        else:
            try:
                dropped = obs.obs_output_get_frames_dropped(output)
                total = obs.obs_output_get_total_frames(output)
                dropped = int(dropped or 0)
                total = int(total or 0)
                obs_stream_stats["streaming"] = True
                obs_stream_stats["dropped"] = dropped
                obs_stream_stats["total"] = total
                obs_stream_stats["percent"] = round(dropped * 100.0 / total, 2) if total > 0 else 0.0
            finally:
                try:
                    obs.obs_output_release(output)
                except Exception:
                    pass
        try:
            fps = obs.obs_get_active_fps()
            obs_stream_stats["fps"] = round(float(fps), 1) if fps else None
        except Exception:
            obs_stream_stats["fps"] = None
        obs_stream_stats["updated"] = time.time()
    except Exception as e:
        print("[NetMon] Помилка читання статистики OBS: {}".format(e))


class NetworkMonitorManager:
    """
    Фоновий моніторинг якості інтернет-з'єднання під час стріму: періодичний
    ping (затримка + втрата пакетів) і, опційно, разовий speedtest
    (download/upload). Поточний стан віддається через /api/netmon для панелі
    адміністратора (нижня панель), а перехід stable<->unstable озвучується
    через TTS тим самим механізмом, що й інші алерти (add_to_buffer()).

    Логіка виміру ping/parsing перенесена з окремого допоміжного OBS-скрипта
    користувача (netmon_obs.py) майже без змін - вона вже перевірена в бою.
    """

    def __init__(self, cfg):
        self.config = cfg
        self.is_running = False
        self._stop_event = threading.Event()
        self._ping_thread = None
        self._lock = threading.Lock()

        self._state = {
            "enabled": True,
            "ping": None,
            "loss": None,
            "jitter": None,
            "targets": [],
            "obs": {},
            "download": None,
            "upload": None,
            "status": NETMON_STATE_UNKNOWN,
            "speedtest_running": False,
            "speedtest_updated": None,
            "updated_at": 0.0,
        }

        self._consecutive_bad = 0
        self._consecutive_good = 0
        self._last_speed_time = 0.0
        # Ковзні вікна проб по кожній цілі: {host: deque([rtt_ms або None, ...])}
        self._windows = {}

    # ------------------------------------------------------------------
    # Життєвий цикл
    # ------------------------------------------------------------------
    def start(self):
        if self.is_running:
            print("[NetMon] ⚠️ Вже запущено")
            return
        self.is_running = True
        self._stop_event.clear()
        self._consecutive_bad = 0
        self._consecutive_good = 0
        self._last_speed_time = 0.0
        self._windows = {}
        with self._lock:
            self._state["status"] = NETMON_STATE_UNKNOWN
        self._ping_thread = threading.Thread(target=self._ping_loop, daemon=True)
        self._ping_thread.start()
        print("[NetMon] 📡 Моніторинг інтернету запущено")

    def stop(self):
        if not self.is_running:
            return
        self.is_running = False
        self._stop_event.set()
        print("[NetMon] ⚫ Моніторинг інтернету зупинено")

    def get_state(self):
        with self._lock:
            data = dict(self._state)
        data["enabled"] = self.is_running
        return data

    # ------------------------------------------------------------------
    # Головний цикл
    # ------------------------------------------------------------------
    def _ping_loop(self):
        while not self._stop_event.is_set():
            try:
                self._tick()
            except Exception as e:
                print("[NetMon] Помилка тіку: {}".format(e))
            interval = max(2, int(self.config.get("netmon_ping_interval", 3) or 3))
            self._stop_event.wait(interval)

    def _tick(self):
        ping_val, loss_val, jitter_val, targets = self._measure_ping()
        obs_snapshot = {}
        if self.config.get("netmon_show_obs_frames", True):
            obs_snapshot = dict(obs_stream_stats)
        with self._lock:
            self._state["ping"] = ping_val
            self._state["loss"] = loss_val
            self._state["jitter"] = jitter_val
            self._state["targets"] = targets
            self._state["obs"] = obs_snapshot
            self._state["updated_at"] = time.time()

        self._evaluate_stability(ping_val, loss_val, jitter_val, targets)

        if self.config.get("netmon_speedtest_enabled", False):
            now = time.time()
            interval = max(30, int(self.config.get("netmon_speedtest_interval", 60) or 60))
            with self._lock:
                already_running = self._state.get("speedtest_running")
            if now - self._last_speed_time >= interval and not already_running:
                self._last_speed_time = now
                threading.Thread(target=self._measure_speed, daemon=True).start()

    # ------------------------------------------------------------------
    # Ping + packet loss
    # ------------------------------------------------------------------
    def _ping_hosts(self):
        """Список цілей пінгу. Одна ціль - це завжди лотерея: публічні DNS
        ріжуть ICMP і дають фантомні втрати. Тому їх декілька."""
        raw = (self.config.get("netmon_ping_hosts") or "").strip()
        if not raw:
            raw = (self.config.get("netmon_ping_host") or "8.8.8.8").strip()
        hosts = []
        for part in raw.replace(";", ",").split(","):
            host = part.strip()
            if host and host not in hosts:
                hosts.append(host)
        return hosts[:5] or ["1.1.1.1"]

    def _probe_host(self, host):
        """ОДНА проба до цілі. Повертає RTT у мс або None (втрата).

        Раніше робилось 4 пінги за раз: на Windows це ~4 секунди, що інколи
        перевищувало timeout=15 разом з іншими цілями і давало хибне
        "нестабільно", а роздільність втрат була всього 0/25/50/75/100%.
        """
        is_win = platform.system() == "Windows"
        try:
            if is_win:
                cmd = ["ping", "-n", "1", "-w", "2000", host]
            else:
                cmd = ["ping", "-c", "1", "-W", "2", host]
            result = subprocess.run(
                cmd,
                capture_output=True,
                timeout=6,
                creationflags=subprocess.CREATE_NO_WINDOW if is_win else 0
            )
            raw = result.stdout or b""
            for enc in ("cp866", "utf-8", "latin-1"):
                try:
                    out = raw.decode(enc)
                    break
                except Exception:
                    out = ""
            if result.returncode != 0 and "TTL" not in out.upper() and "time" not in out.lower():
                return None
            m = re.search(r"(?:time|час)[=<]\s*([\d.,]+)\s*(?:ms|мс)", out, flags=re.IGNORECASE)
            if not m:
                m = re.search(r"=\s*([\d.,]+)\s*(?:ms|мс)", out, flags=re.IGNORECASE)
            if not m:
                return None
            return float(m.group(1).replace(",", "."))
        except Exception:
            return None

    def _window_stats(self, samples):
        """Втрати / середній ping / джитер по ковзному вікну проб."""
        total = len(samples)
        if not total:
            return None, None, None
        rtts = [x for x in samples if x is not None]
        loss = round((total - len(rtts)) * 100.0 / total, 1)
        if not rtts:
            return None, loss, None
        avg = round(sum(rtts) / len(rtts))
        jitter = None
        if len(rtts) >= 2:
            diffs = [abs(rtts[k] - rtts[k - 1]) for k in range(1, len(rtts))]
            jitter = round(sum(diffs) / len(diffs), 1)
        return avg, loss, jitter

    def _measure_ping(self):
        """Опитує всі цілі паралельно і рахує статистику по ковзному вікну."""
        hosts = self._ping_hosts()
        try:
            window = max(10, min(300, int(self.config.get("netmon_window_size", 60) or 60)))
        except Exception:
            window = 60

        results = {}

        def worker(h):
            results[h] = self._probe_host(h)

        threads = []
        for host in hosts:
            t = threading.Thread(target=worker, args=(host,), daemon=True)
            t.start()
            threads.append(t)
        for t in threads:
            t.join(timeout=8)

        for host in list(self._windows.keys()):
            if host not in hosts:
                self._windows.pop(host, None)

        targets = []
        for host in hosts:
            buf = self._windows.get(host)
            if buf is None or buf.maxlen != window:
                buf = collections.deque(list(buf or [])[-window:], maxlen=window)
                self._windows[host] = buf
            buf.append(results.get(host))
            avg, loss, jitter = self._window_stats(buf)
            targets.append({
                "host": host,
                "ping": avg,
                "loss": loss,
                "jitter": jitter,
                "samples": len(buf),
                "bad": self._target_is_bad(avg, loss, jitter),
            })

        alive = [t for t in targets if t["ping"] is not None]
        if alive:
            best = min(alive, key=lambda t: (t["loss"] if t["loss"] is not None else 100, t["ping"]))
            return best["ping"], best["loss"], best["jitter"], targets
        return None, 100.0, None, targets

    def _target_is_bad(self, ping_val, loss_val, jitter_val):
        try:
            loss_threshold = int(self.config.get("netmon_loss_threshold", 20) or 0)
            ping_threshold = int(self.config.get("netmon_ping_threshold", 250) or 0)
            jitter_threshold = int(self.config.get("netmon_jitter_threshold", 60) or 0)
        except Exception:
            loss_threshold, ping_threshold, jitter_threshold = 20, 250, 60
        if ping_val is None:
            return True
        if loss_threshold > 0 and (loss_val or 0) >= loss_threshold:
            return True
        if ping_threshold > 0 and ping_val >= ping_threshold:
            return True
        if jitter_threshold > 0 and jitter_val is not None and jitter_val >= jitter_threshold:
            return True
        return False

    # ------------------------------------------------------------------
    # Speedtest (download/upload) - лише якщо явно увімкнено в налаштуваннях
    # ------------------------------------------------------------------
    def _measure_speed(self):
        with self._lock:
            self._state["speedtest_running"] = True
        try:
            # Cloudflare - основне джерело: анікаст, є всюди, без 307-редиректів.
            # Український speedtest-kv.ukrtelecom.ua віддавав HTTP 307 і завжди падав.
            dl_servers = [
                "https://speed.cloudflare.com/__down?bytes=10000000",
                "https://speed.cloudflare.com/__down?bytes=5000000",
                "http://speedtest.kpi.ua:8080/download?size=5000000",
            ]
            headers = {"User-Agent": "Mozilla/5.0"}
            dl_mbps = None

            for dl_url in dl_servers:
                try:
                    req = urllib.request.Request(dl_url, headers=headers)
                    start = time.time()
                    downloaded = 0
                    with urllib.request.urlopen(req, timeout=15) as resp:
                        while True:
                            chunk = resp.read(65536)
                            if not chunk:
                                break
                            downloaded += len(chunk)
                    elapsed = time.time() - start
                    if elapsed > 0 and downloaded > 100000:
                        dl_mbps = round((downloaded * 8) / (elapsed * 1000000), 1)
                        break
                except Exception as e:
                    print("[NetMon] dl server failed: {} {}".format(dl_url.split('/')[2], e))
                    continue

            if dl_mbps is not None:
                with self._lock:
                    self._state["download"] = dl_mbps

            ul_servers = [
                "https://speed.cloudflare.com/__up",
                "http://speedtest.kpi.ua:8080/upload",
            ]
            payload = os.urandom(2000000)
            ul_mbps = None

            for ul_url in ul_servers:
                try:
                    req = urllib.request.Request(ul_url, data=payload, method="POST")
                    req.add_header("Content-Type", "application/octet-stream")
                    req.add_header("User-Agent", "Mozilla/5.0")
                    start = time.time()
                    with urllib.request.urlopen(req, timeout=15) as resp:
                        resp.read()
                    elapsed = time.time() - start
                    if elapsed > 0:
                        ul_mbps = round((len(payload) * 8) / (elapsed * 1000000), 1)
                        break
                except Exception as e:
                    print("[NetMon] ul server failed: {} {}".format(ul_url.split('/')[2], e))
                    continue

            if ul_mbps is not None:
                with self._lock:
                    self._state["upload"] = ul_mbps

            with self._lock:
                self._state["speedtest_updated"] = time.strftime("%H:%M")

        except Exception as e:
            print("[NetMon] Помилка speedtest: {}".format(e))
        finally:
            with self._lock:
                self._state["speedtest_running"] = False

    # ------------------------------------------------------------------
    # Визначення стабільності + TTS-сповіщення на переході стану
    # ------------------------------------------------------------------
    def _evaluate_stability(self, ping_val, loss_val, jitter_val=None, targets=None):
        debounce = max(1, int(self.config.get("netmon_debounce_count", 3) or 3))

        # Вердикт по БІЛЬШОСТІ цілей: якщо погана лише одна з трьох - це
        # проблема тієї цілі (ICMP-тротлінг, локальний збій), а не інтернету.
        targets = targets or []
        if targets:
            bad_count = sum(1 for t in targets if t.get("bad"))
            is_bad_reading = bad_count * 2 > len(targets)
        else:
            is_bad_reading = self._target_is_bad(ping_val, loss_val, jitter_val)

        with self._lock:
            current_status = self._state.get("status")

        if is_bad_reading:
            self._consecutive_bad += 1
            self._consecutive_good = 0
        else:
            self._consecutive_good += 1
            self._consecutive_bad = 0

        new_status = current_status
        if current_status != NETMON_STATE_UNSTABLE and self._consecutive_bad >= debounce:
            new_status = NETMON_STATE_UNSTABLE
        elif current_status in (NETMON_STATE_UNSTABLE, NETMON_STATE_UNKNOWN) and self._consecutive_good >= debounce:
            new_status = NETMON_STATE_STABLE

        if new_status != current_status:
            with self._lock:
                self._state["status"] = new_status
            # Перший перехід з "unknown" в "stable" - це щойно запущений
            # моніторинг увійшов у норму, а не "відновлення після збою".
            # Озвучувати його не потрібно.
            if current_status != NETMON_STATE_UNKNOWN:
                self._announce_transition(new_status, ping_val, loss_val, jitter_val)

    def _announce_transition(self, new_status, ping_val, loss_val, jitter_val=None):
        if new_status == NETMON_STATE_UNSTABLE:
            template = (self.config.get("netmon_unstable_text") or "").strip()
            label = "⚠️ Інтернет нестабільний"
            print("[NetMon] ⚠️ Стан змінено: НЕСТАБІЛЬНО (ping={} loss={}%)".format(ping_val, loss_val))
        else:
            template = (self.config.get("netmon_stable_text") or "").strip()
            label = "✅ Інтернет стабілізувався"
            print("[NetMon] ✅ Стан змінено: СТАБІЛЬНО (ping={} loss={}%)".format(ping_val, loss_val))

        if not template:
            return  # порожній шаблон = цю подію не озвучувати

        tts_text = template.replace("{ping}", str(ping_val if ping_val is not None else "-")) \
                            .replace("{loss}", str(loss_val if loss_val is not None else "-")) \
                            .replace("{jitter}", str(jitter_val if jitter_val is not None else "-"))

        try:
            add_to_buffer(
                "bot", "Мережа", tts_text, tts_text,
                is_alert=True, subtitle=label,
                show_in_chat=bool(self.config.get("netmon_show_in_chat", False)),
            )
        except Exception as e:
            print("[NetMon] Помилка постановки сповіщення в чергу: {}".format(e))



# ============================================================================
# ІСТОРІЯ ГЛЯДАЧІВ TIKTOK (заходи, повідомлення, подарунки, час на ефірі)
# ============================================================================
TIKTOK_VIEWER_HISTORY_FILE = os.path.join(os.path.dirname(__file__), "tiktok_viewer_history.json")
tiktok_viewer_history = {}
_tiktok_viewer_history_lock = threading.Lock()
_tiktok_viewer_history_last_save = 0.0


def tiktok_extract_avatar_url(user_obj):
    for attr in ('avatar_thumb', 'avatar_medium', 'avatar_large'):
        img = getattr(user_obj, attr, None)
        url_list = getattr(img, 'url_list', None) if img is not None else None
        if url_list:
            try:
                return url_list[0]
            except Exception:
                continue
    return ''


def load_tiktok_viewer_history():
    global tiktok_viewer_history
    try:
        if os.path.exists(TIKTOK_VIEWER_HISTORY_FILE):
            with open(TIKTOK_VIEWER_HISTORY_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                tiktok_viewer_history = data
                print("[TikTok History] Завантажено {} глядачів".format(len(tiktok_viewer_history)))
    except Exception as e:
        print("[TikTok History] Помилка завантаження: {}".format(e))
        tiktok_viewer_history = {}


def save_tiktok_viewer_history(force=False):
    global _tiktok_viewer_history_last_save
    now = time.time()
    if not force and now - _tiktok_viewer_history_last_save < 30:
        return
    _tiktok_viewer_history_last_save = now
    try:
        with _tiktok_viewer_history_lock:
            snapshot = dict(tiktok_viewer_history)
        tmp_path = TIKTOK_VIEWER_HISTORY_FILE + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(snapshot, f, ensure_ascii=False)
        os.replace(tmp_path, TIKTOK_VIEWER_HISTORY_FILE)
    except Exception as e:
        print("[TikTok History] Помилка збереження: {}".format(e))


TIKTOK_DETAIL_LIMIT = 100


def record_tiktok_viewer(unique_id, nickname, avatar_url, event_type, gift_diamonds=0,
                        message_text='', gift_name='', gift_count=0, like_count=0):
    unique_id = (unique_id or "").strip()
    if not unique_id:
        return
    now = time.time()
    today_str = time.strftime("%Y-%m-%d", time.localtime(now))
    with _tiktok_viewer_history_lock:
        entry = tiktok_viewer_history.setdefault(unique_id, {
            "nickname": nickname or unique_id,
            "avatar_url": avatar_url or "",
            "message_count": 0,
            "gift_count": 0,
            "gift_diamonds": 0,
            "first_seen": now,
            "last_seen": now,
            "days": {},
        })
        if nickname:
            entry["nickname"] = nickname
        if avatar_url:
            entry["avatar_url"] = avatar_url
        entry["last_seen"] = now
        entry.setdefault("days", {})
        day_bucket = entry["days"].setdefault(today_str, {"messages": 0, "gifts": 0, "diamonds": 0})
        # Будь-яка активність (вхід, лайк, репост, підписка) робить глядача
        # "активним за цей день" — раніше в історію попадали лише ті, хто
        # написав у чат.
        for extra_key in ("likes", "shares", "joins", "follows", "events"):
            day_bucket.setdefault(extra_key, 0)
        day_bucket["events"] += 1
        for extra_key in ("like_count", "share_count", "join_count", "follow_count"):
            entry.setdefault(extra_key, 0)
        entry.setdefault("messages", [])
        entry.setdefault("gifts", [])
        if event_type == "message":
            entry["message_count"] = int(entry.get("message_count", 0) or 0) + 1
            day_bucket["messages"] += 1
            if (message_text or "").strip():
                entry["messages"].append({
                    "ts": now,
                    "date": today_str,
                    "text": (message_text or "").strip()[:400],
                })
                if len(entry["messages"]) > TIKTOK_DETAIL_LIMIT:
                    del entry["messages"][:-TIKTOK_DETAIL_LIMIT]
        elif event_type == "gift":
            entry["gift_count"] = int(entry.get("gift_count", 0) or 0) + 1
            entry["gift_diamonds"] = int(entry.get("gift_diamonds", 0) or 0) + int(gift_diamonds or 0)
            day_bucket["gifts"] += 1
            day_bucket["diamonds"] += int(gift_diamonds or 0)
            entry["gifts"].append({
                "ts": now,
                "date": today_str,
                "name": (gift_name or "Подарунок").strip()[:80],
                "count": int(gift_count or 1),
                "diamonds": int(gift_diamonds or 0),
            })
            if len(entry["gifts"]) > TIKTOK_DETAIL_LIMIT:
                del entry["gifts"][:-TIKTOK_DETAIL_LIMIT]
        elif event_type == "like":
            added = max(1, int(like_count or 1))
            entry["like_count"] = int(entry.get("like_count", 0) or 0) + added
            day_bucket["likes"] += added
        elif event_type == "share":
            entry["share_count"] = int(entry.get("share_count", 0) or 0) + 1
            day_bucket["shares"] += 1
        elif event_type == "join":
            entry["join_count"] = int(entry.get("join_count", 0) or 0) + 1
            day_bucket["joins"] += 1
        elif event_type == "follow":
            entry["follow_count"] = int(entry.get("follow_count", 0) or 0) + 1
            day_bucket["follows"] += 1
        # Захист від безмежного росту: тримаємо не більше MAX_CACHE_SIZE
        # глядачів, першими викидаємо тих, кого давно не було видно.
        if len(tiktok_viewer_history) > MAX_CACHE_SIZE:
            stale = sorted(tiktok_viewer_history.items(),
                           key=lambda kv: (kv[1].get("last_seen") or 0))
            for stale_id, _ in stale[:len(tiktok_viewer_history) - MAX_CACHE_SIZE]:
                tiktok_viewer_history.pop(stale_id, None)
    save_tiktok_viewer_history()


def clear_tiktok_viewer_history():
    """Повністю очищає історію глядачів TikTok (усі дні, усі користувачі)."""
    global tiktok_viewer_history
    with _tiktok_viewer_history_lock:
        removed = len(tiktok_viewer_history)
        tiktok_viewer_history = {}
    save_tiktok_viewer_history(force=True)
    print("[TikTok History] Історію очищено повністю, видалено глядачів: {}".format(removed))
    return removed


def clear_tiktok_day_history(date_str):
    """Очищає список активних глядачів за один конкретний день (усі інші дні лишаються)."""
    global tiktok_viewer_history
    date_str = (date_str or "").strip()
    if not date_str:
        return 0
    removed_viewers = 0
    with _tiktok_viewer_history_lock:
        for unique_id in list(tiktok_viewer_history.keys()):
            entry = tiktok_viewer_history.get(unique_id) or {}
            days = entry.get("days") or {}
            if date_str in days:
                days.pop(date_str, None)
                entry["days"] = days
                removed_viewers += 1
                if not days:
                    tiktok_viewer_history.pop(unique_id, None)
                else:
                    tiktok_viewer_history[unique_id] = entry
    save_tiktok_viewer_history(force=True)
    print("[TikTok History] Очищено активних глядачів за {}: {}".format(date_str, removed_viewers))
    return removed_viewers


def get_tiktok_days_available():
    with _tiktok_viewer_history_lock:
        days = set()
        for entry in tiktok_viewer_history.values():
            days.update((entry.get("days") or {}).keys())
    return sorted(days, reverse=True)


def get_tiktok_day_summary(date_str):
    with _tiktok_viewer_history_lock:
        snapshot = {k: dict(v) for k, v in tiktok_viewer_history.items()}
    roster = []
    for unique_id, entry in snapshot.items():
        day = (entry.get("days") or {}).get(date_str)
        if not day:
            continue
        activity = (int(day.get("messages", 0) or 0) + int(day.get("gifts", 0) or 0)
                    + int(day.get("likes", 0) or 0) + int(day.get("shares", 0) or 0)
                    + int(day.get("joins", 0) or 0) + int(day.get("follows", 0) or 0)
                    + int(day.get("events", 0) or 0))
        if activity <= 0:
            continue
        roster.append({
            "unique_id": unique_id,
            "nickname": entry.get("nickname") or unique_id,
            "avatar_url": entry.get("avatar_url") or "",
            "message_count": int(day.get("messages", 0) or 0),
            "gift_count": int(day.get("gifts", 0) or 0),
            "gift_diamonds": int(day.get("diamonds", 0) or 0),
            "like_count": int(day.get("likes", 0) or 0),
            "share_count": int(day.get("shares", 0) or 0),
            "join_count": int(day.get("joins", 0) or 0),
            "follow_count": int(day.get("follows", 0) or 0),
        })
    roster.sort(key=lambda x: -(x["message_count"] * 100 + x["gift_count"] * 100
                                + x["like_count"] + x["share_count"] + x["join_count"]))
    return roster


def get_tiktok_viewer_top(metric, limit=5):
    with _tiktok_viewer_history_lock:
        snapshot = dict(tiktok_viewer_history)
    items = []
    for unique_id, entry in snapshot.items():
        value = int(entry.get(metric, 0) or 0)
        if value <= 0:
            continue
        items.append({
            "unique_id": unique_id,
            "nickname": entry.get("nickname") or unique_id,
            "avatar_url": entry.get("avatar_url") or "",
            "value": value,
        })
    items.sort(key=lambda x: -x["value"])
    return items[:limit]


def get_tiktok_user_detail(unique_id):
    unique_id = (unique_id or "").strip()
    if not unique_id:
        return None
    with _tiktok_viewer_history_lock:
        entry = tiktok_viewer_history.get(unique_id)
        if not entry:
            # tolerate case differences
            lowered = unique_id.lower()
            for key, value in tiktok_viewer_history.items():
                if (key or "").lower() == lowered:
                    entry = value
                    unique_id = key
                    break
        if not entry:
            return None
        messages = [dict(m) for m in (entry.get("messages") or [])]
        gifts = [dict(g) for g in (entry.get("gifts") or [])]
        payload = {
            "unique_id": unique_id,
            "nickname": entry.get("nickname") or unique_id,
            "avatar_url": entry.get("avatar_url") or "",
            "profile_url": "https://www.tiktok.com/@" + unique_id.lstrip("@"),
            "message_count": int(entry.get("message_count", 0) or 0),
            "gift_count": int(entry.get("gift_count", 0) or 0),
            "gift_diamonds": int(entry.get("gift_diamonds", 0) or 0),
            "like_count": int(entry.get("like_count", 0) or 0),
            "share_count": int(entry.get("share_count", 0) or 0),
            "join_count": int(entry.get("join_count", 0) or 0),
            "follow_count": int(entry.get("follow_count", 0) or 0),
            "first_seen": entry.get("first_seen", 0),
            "last_seen": entry.get("last_seen", 0),
        }
    messages.sort(key=lambda x: -(x.get("ts") or 0))
    gifts.sort(key=lambda x: -(x.get("ts") or 0))
    payload["messages"] = messages
    payload["gifts"] = gifts
    return payload


# ============================================================================
# МУЗИЧНИЙ ПЛЕЄР (фонова музика: сканування папки, синхронізований стан
# відтворення між доком і Browser Source, приглушення під час TTS/алертів)
# ============================================================================
MUSIC_AUDIO_EXTENSIONS = ('.mp3', '.wav', '.ogg', '.m4a', '.flac', '.aac')

music_state = {
    "track_index": 0,
    # anchor_time: момент часу (time.time()), який відповідає позиції 0
    # ПОТОЧНОГО треку, якщо рахувати без урахування пауз. Реальна позиція
    # в треку = (now - anchor_time), або позиція на момент паузи, якщо
    # зараз на паузі. Такий підхід дозволяє будь-якому браузерному
    # інстансу (dock чи Source) самостійно порахувати, де зараз має бути
    # відтворення, без постійної синхронізації по мережі.
    "anchor_time": 0.0,
    "paused": True,
    "pause_started_at": 0.0,
    "manual_pause": True,  # користувач явно натиснув паузу - ducking не має це перебивати
    "playlist_signature": "",
}
_music_state_lock = threading.Lock()

# Гучність плеєра та останній трек/позиція - зберігаються на диск,
# щоб після перезапуску OBS відтворення продовжилось з того ж місця.
music_runtime_state = {
    "volume": 0.7,
    "track_name": "",
    "position": 0.0,
    "paused": True,
}
_music_runtime_lock = threading.Lock()
_music_runtime_last_save = 0.0

audio_ducking_state = {"active_count": 0, "last_deactivated_at": 0.0}
_audio_ducking_lock = threading.Lock()


MUSIC_RUNTIME_STATE_FILE = os.path.join(os.path.dirname(__file__), "music_player_state.json")
# Треки, які користувач прибрав з плейлиста. Файли на диску НЕ видаляються -
# просто ігноруються під час сканування папки. {folder_key: [filename, ...]}
MUSIC_REMOVED_TRACKS_FILE = os.path.join(os.path.dirname(__file__), "music_removed_tracks.json")
music_removed_tracks = {}
_music_removed_lock = threading.Lock()
MUSIC_PLAYLIST_ORDER_FILE = os.path.join(os.path.dirname(__file__), "music_playlist_order.json")
music_playlist_order = {}   # {folder_lower: [filename, ...]}
_music_order_lock = threading.Lock()


def load_music_playlist_order():
    """Завантажує збережений порядок треків (зберігається між перезапусками OBS)."""
    global music_playlist_order
    try:
        if os.path.exists(MUSIC_PLAYLIST_ORDER_FILE):
            with open(MUSIC_PLAYLIST_ORDER_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                cleaned = {}
                for folder_key, names in data.items():
                    if isinstance(names, list):
                        cleaned[str(folder_key)] = [str(n) for n in names if isinstance(n, str)]
                with _music_order_lock:
                    music_playlist_order = cleaned
    except Exception as e:
        print("[Music] Не вдалося прочитати порядок плейлиста: {}".format(e))


def save_music_playlist_order():
    try:
        with _music_order_lock:
            snapshot = {k: list(v) for k, v in music_playlist_order.items()}
        tmp_path = MUSIC_PLAYLIST_ORDER_FILE + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(snapshot, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, MUSIC_PLAYLIST_ORDER_FILE)
    except Exception as e:
        print("[Music] Не вдалося зберегти порядок плейлиста: {}".format(e))


def load_music_removed_tracks():
    global music_removed_tracks
    try:
        if not os.path.exists(MUSIC_REMOVED_TRACKS_FILE):
            return
        with open(MUSIC_REMOVED_TRACKS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return
        cleaned = {}
        for folder_key, names in data.items():
            if isinstance(names, list):
                cleaned[str(folder_key)] = [str(n) for n in names if isinstance(n, str)]
        with _music_removed_lock:
            music_removed_tracks = cleaned
    except Exception as e:
        print("[Music] Не вдалося прочитати список прибраних треків: {}".format(e))


def save_music_removed_tracks():
    try:
        with _music_removed_lock:
            snapshot = {k: list(v) for k, v in music_removed_tracks.items() if v}
        tmp_path = MUSIC_REMOVED_TRACKS_FILE + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(snapshot, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, MUSIC_REMOVED_TRACKS_FILE)
    except Exception as e:
        print("[Music] Не вдалося зберегти список прибраних треків: {}".format(e))


def music_get_removed(folder_key=None):
    if folder_key is None:
        folder_key = music_folder_key()
    with _music_removed_lock:
        return list(music_removed_tracks.get(folder_key, []))


def music_remove_track(name):
    """Прибирає трек з плейлиста (файл лишається на диску)."""
    name = (name or "").strip()
    if not name:
        return {"ok": False, "error": "Не вказано назву треку"}
    folder_key = music_folder_key()
    if not folder_key:
        return {"ok": False, "error": "Папку з треками не задано"}
    with _music_removed_lock:
        current = list(music_removed_tracks.get(folder_key, []))
        if name not in current:
            current.append(name)
        music_removed_tracks[folder_key] = current
    save_music_removed_tracks()
    print("[Music] Трек прибрано з плейлиста (файл на диску залишився): {}".format(name))
    playlist = music_scan_playlist()
    music_ensure_state_matches_playlist(playlist)
    return {"ok": True, "removed_count": len(current), "tracks": playlist}


def music_restore_removed():
    """Повертає всі прибрані треки поточної папки назад у плейлист."""
    folder_key = music_folder_key()
    with _music_removed_lock:
        count = len(music_removed_tracks.pop(folder_key, []))
    save_music_removed_tracks()
    playlist = music_scan_playlist()
    music_ensure_state_matches_playlist(playlist)
    return {"ok": True, "restored": count, "tracks": playlist}


def load_music_runtime_state():
    """Читає збережені гучність / останній трек / позицію відтворення."""
    global music_runtime_state
    try:
        if not os.path.exists(MUSIC_RUNTIME_STATE_FILE):
            return
        with open(MUSIC_RUNTIME_STATE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return
        with _music_runtime_lock:
            try:
                music_runtime_state["volume"] = max(0.0, min(1.0, float(data.get("volume", 0.7))))
            except (TypeError, ValueError):
                music_runtime_state["volume"] = 0.7
            music_runtime_state["track_name"] = str(data.get("track_name", "") or "")
            try:
                music_runtime_state["position"] = max(0.0, float(data.get("position", 0.0)))
            except (TypeError, ValueError):
                music_runtime_state["position"] = 0.0
            music_runtime_state["paused"] = bool(data.get("paused", True))
    except Exception as e:
        print("[Music] Не вдалося прочитати стан плеєра: {}".format(e))


def save_music_runtime_state(force=False):
    """Пише стан плеєра на диск (не частіше ніж раз на 5 с, якщо не force)."""
    global _music_runtime_last_save
    now = time.time()
    if not force and (now - _music_runtime_last_save) < 5.0:
        return
    _music_runtime_last_save = now
    try:
        with _music_runtime_lock:
            snapshot = dict(music_runtime_state)
        tmp_path = MUSIC_RUNTIME_STATE_FILE + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(snapshot, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, MUSIC_RUNTIME_STATE_FILE)
    except Exception as e:
        print("[Music] Не вдалося зберегти стан плеєра: {}".format(e))


def music_get_volume():
    with _music_runtime_lock:
        return float(music_runtime_state.get("volume", 0.7))


def music_set_volume(value):
    try:
        value = max(0.0, min(1.0, float(value)))
    except (TypeError, ValueError):
        return music_get_volume()
    with _music_runtime_lock:
        music_runtime_state["volume"] = value
    save_music_runtime_state(force=True)
    return value


def music_remember_playback(playlist=None, position=None, paused=None, force=False):
    """Запам'ятовує поточний трек (за іменем) і позицію в ньому."""
    try:
        with _music_state_lock:
            idx = music_state["track_index"]
        name = ""
        if playlist and 0 <= idx < len(playlist):
            name = playlist[idx]
        with _music_runtime_lock:
            if name:
                music_runtime_state["track_name"] = name
            if position is not None:
                music_runtime_state["position"] = max(0.0, float(position))
            if paused is not None:
                music_runtime_state["paused"] = bool(paused)
        save_music_runtime_state(force=force)
    except Exception:
        pass


_music_restored_once = False


def music_restore_last_session(force=False):
    """
    Після запуску OBS ставить плеєр на той самий трек і ту саму позицію,
    на яких його зупинили минулого разу.

    Викликається двічі: один раз при імпорті (коли config ще порожній —
    тоді просто нічого не знаходить) і ще раз із script_load()/
    script_update() уже ПІСЛЯ відновлення налаштувань. Прапорець
    _music_restored_once гарантує, що успішне відновлення не перезапише
    те, що користувач уже слухає.
    """
    global _music_restored_once
    if _music_restored_once and not force:
        return
    playlist = music_scan_playlist()
    if not playlist:
        return
    with _music_runtime_lock:
        name = music_runtime_state.get("track_name") or ""
        position = float(music_runtime_state.get("position", 0.0) or 0.0)
        paused = bool(music_runtime_state.get("paused", True))
    if not name or name not in playlist:
        return
    index = playlist.index(name)
    _music_restored_once = True
    now = time.time()
    with _music_state_lock:
        music_state["track_index"] = index
        music_state["anchor_time"] = now - position
        music_state["paused"] = paused
        music_state["manual_pause"] = paused
        music_state["pause_started_at"] = now if paused else 0.0
    print("[Music] Відновлено: {} з позиції {:.1f} с ({})".format(
        name, position, "пауза" if paused else "відтворення"))


def music_folder_key(folder=None):
    if folder is None:
        folder = (config.get('music_folder_path') or '').strip()
    return os.path.normcase(os.path.normpath(folder)) if folder else ""


def music_apply_saved_order(files, folder_key):
    """Ставить треки у збережений користувачем порядок; нові файли - у кінець."""
    with _music_order_lock:
        saved = list(music_playlist_order.get(folder_key, []))
    if not saved:
        return files
    present = set(files)
    ordered = [n for n in saved if n in present]
    ordered_set = set(ordered)
    ordered.extend([f for f in files if f not in ordered_set])
    return ordered


def music_scan_playlist():
    folder = (config.get('music_folder_path') or '').strip()
    if not folder or not os.path.isdir(folder):
        return []
    try:
        removed = set(music_get_removed(music_folder_key(folder)))
        files = sorted(
            [f for f in os.listdir(folder)
             if f.lower().endswith(MUSIC_AUDIO_EXTENSIONS)
             and f not in removed
             and os.path.isfile(os.path.join(folder, f))],
            key=str.lower
        )
        return music_apply_saved_order(files, music_folder_key(folder))
    except Exception as e:
        print("[Music] Помилка сканування папки: {}".format(e))
        return []


def music_set_order(new_order):
    """Зберігає новий порядок треків і, якщо музика грає, лишає поточний трек
    активним (індекс перераховується під новий порядок, без перезапуску)."""
    folder = (config.get('music_folder_path') or '').strip()
    if not folder or not os.path.isdir(folder):
        return {"ok": False, "error": "Папку з треками не задано"}
    try:
        existing = [f for f in os.listdir(folder)
                    if f.lower().endswith(MUSIC_AUDIO_EXTENSIONS) and os.path.isfile(os.path.join(folder, f))]
    except Exception as e:
        return {"ok": False, "error": "Не вдалося прочитати папку: {}".format(e)}
    present = set(existing)
    seen = set()
    cleaned = []
    for name in (new_order or []):
        if isinstance(name, str) and name in present and name not in seen:
            seen.add(name)
            cleaned.append(name)
    if not cleaned:
        return {"ok": False, "error": "Порожній або некоректний порядок"}
    leftovers = sorted([f for f in existing if f not in seen], key=str.lower)
    cleaned.extend(leftovers)

    old_playlist = music_scan_playlist()
    with _music_state_lock:
        current_name = old_playlist[music_state["track_index"]] if 0 <= music_state["track_index"] < len(old_playlist) else ""

    folder_key = music_folder_key(folder)
    with _music_order_lock:
        music_playlist_order[folder_key] = list(cleaned)
    save_music_playlist_order()

    with _music_state_lock:
        music_state["playlist_signature"] = music_playlist_signature(cleaned)
        if current_name and current_name in cleaned:
            music_state["track_index"] = cleaned.index(current_name)
        elif music_state["track_index"] >= len(cleaned):
            music_state["track_index"] = 0
            music_state["anchor_time"] = time.time()
    return {"ok": True, "tracks": cleaned}


def music_playlist_signature(playlist):
    return "|".join(playlist)


def music_ensure_state_matches_playlist(playlist):
    """Якщо плейлист змінився (папку пересканували, файли додали/прибрали) і
    поточний track_index вийшов за межі - безпечно скидаємо на початок."""
    global music_state
    sig = music_playlist_signature(playlist)
    with _music_state_lock:
        if music_state["playlist_signature"] != sig:
            music_state["playlist_signature"] = sig
            if music_state["track_index"] >= len(playlist):
                music_state["track_index"] = 0
                music_state["anchor_time"] = time.time()


def music_get_state():
    playlist = music_scan_playlist()
    music_ensure_state_matches_playlist(playlist)
    now = time.time()
    with _music_state_lock:
        state = dict(music_state)
    ducked = music_should_be_ducked()
    effectively_paused = state["paused"] or ducked
    if state["paused"]:
        position = max(0.0, state["pause_started_at"] - state["anchor_time"])
    else:
        position = max(0.0, now - state["anchor_time"])
    if playlist:
        music_remember_playback(playlist, position=position, paused=state["paused"])
    return {
        "enabled": bool(config.get("music_enabled", False)),
        "folder_path": config.get("music_folder_path", "") or "",
        "tracks": playlist,
        "track_count": len(playlist),
        "track_index": state["track_index"] if playlist else 0,
        "position": position,
        "duration": 0.0,
        "paused": effectively_paused,
        "manual_pause": state["manual_pause"],
        "ducked": ducked,
        "volume": music_get_volume(),
        "removed_count": len(music_get_removed()),
    }


def music_control(action, from_index=None):
    global music_state
    playlist = music_scan_playlist()
    music_ensure_state_matches_playlist(playlist)
    now = time.time()
    with _music_state_lock:
        if not playlist:
            return
        if action == "play":
            if music_state["paused"]:
                paused_span = now - music_state["pause_started_at"] if music_state["pause_started_at"] else 0.0
                music_state["anchor_time"] += paused_span
            music_state["paused"] = False
            music_state["manual_pause"] = False
        elif action == "pause":
            if not music_state["paused"]:
                music_state["pause_started_at"] = now
            music_state["paused"] = True
            music_state["manual_pause"] = True
        elif action == "next":
            music_state["track_index"] = (music_state["track_index"] + 1) % len(playlist)
            music_state["anchor_time"] = now
            music_state["pause_started_at"] = now
        elif action == "prev":
            music_state["track_index"] = (music_state["track_index"] - 1) % len(playlist)
            music_state["anchor_time"] = now
            music_state["pause_started_at"] = now
        elif action == "goto":
            try:
                target = int(from_index)
            except (TypeError, ValueError):
                target = None
            if target is not None and 0 <= target < len(playlist):
                music_state["track_index"] = target
                music_state["anchor_time"] = now
                music_state["pause_started_at"] = now
                music_state["paused"] = False
                music_state["manual_pause"] = False
        elif action == "seek":
            try:
                target_pos = max(0.0, float(from_index))
            except (TypeError, ValueError):
                target_pos = None
            if target_pos is not None:
                music_state["anchor_time"] = now - target_pos
                music_state["pause_started_at"] = now
        elif action == "advance":
            # Клієнт повідомив, що поточний трек природно дограв до кінця.
            # Захист від подвійного просування, якщо і dock, і source
            # одночасно надішлють "advance" для того самого треку -
            # застосовуємо лише якщо індекс ще збігається з очікуваним.
            if from_index is None or from_index == music_state["track_index"]:
                music_state["track_index"] = (music_state["track_index"] + 1) % len(playlist)
                music_state["anchor_time"] = now
                music_state["pause_started_at"] = now
    music_remember_playback(playlist, force=True)


def music_should_be_ducked():
    if not config.get("music_duck_on_alert", True):
        return False
    with _audio_ducking_lock:
        active = audio_ducking_state["active_count"] > 0
        last_deactivated_at = audio_ducking_state["last_deactivated_at"]
    if active:
        return True
    if last_deactivated_at <= 0:
        return False
    delay = max(0, int(config.get("music_duck_resume_delay", 10) or 10))
    return (time.time() - last_deactivated_at) < delay


def audio_ducking_begin():
    with _audio_ducking_lock:
        audio_ducking_state["active_count"] += 1


def audio_ducking_end():
    with _audio_ducking_lock:
        audio_ducking_state["active_count"] = max(0, audio_ducking_state["active_count"] - 1)
        if audio_ducking_state["active_count"] == 0:
            audio_ducking_state["last_deactivated_at"] = time.time()


# ============================================================================
# ЕКСПЕРИМЕНТАЛЬНО: відстеження реального рівня звуку обраних джерел OBS
# (щоб приглушувати музику саме тоді, коли конкретне джерело - напр. віджет
# Donatik - реально видає звук, а не за фіксованим таймером). Штатний
# obspython НЕ надає доступу до рівня звуку джерела - доводиться напряму
# зв'язуватися з бібліотекою OBS через ctypes (obs_volmeter_* функції).
# Це неофіційний, платформозалежний прийом (підтверджений робочим кодом
# спільноти на форумі OBS), який НЕ гарантовано працює на кожній збірці
# OBS/ОС. Усе загорнуто в try/except - якщо щось не спрацює, ця функція
# просто тихо вимикається.
# ============================================================================

class SourceAudioDuckMonitor:
    SILENCE_DB_THRESHOLD = -40.0  # нижче цього рівня (дБ) вважаємо тишею - можна підлаштувати дослідно
    HANGOVER_SECONDS = 0.8        # скільки тиші поспіль треба, щоб зняти ducking для джерела
    STALE_SECONDS = 2.0           # якщо колбек не оновлював рівень довше - вважаємо джерело неактивним

    def __init__(self):
        self.available = False
        self.is_running = False
        self._lib = None
        self._sources = {}
        self._volmeters = {}
        self._callbacks = {}
        self._levels = {}
        self._levels_lock = threading.Lock()
        self._active_names = set()
        self._poll_thread = None
        self._stop_event = threading.Event()

        class _Source(ctypes.Structure):
            pass

        class _Volmeter(ctypes.Structure):
            pass

        self._Source = _Source
        self._Volmeter = _Volmeter
        self._volmeter_callback_t = ctypes.CFUNCTYPE(
            None, ctypes.c_void_p,
            ctypes.POINTER(ctypes.c_float),
            ctypes.POINTER(ctypes.c_float),
            ctypes.POINTER(ctypes.c_float),
        )

    def _wrap(self, funcname, restype, argtypes):
        func = getattr(self._lib, funcname)
        func.restype = restype
        func.argtypes = argtypes
        return func

    def start(self):
        if self.is_running:
            return
        names_cfg = config.get("music_duck_source_names")
        if isinstance(names_cfg, dict):
            # Формат чекбоксів: {"назва джерела": True/False}.
            names = [n.strip() for n, enabled in names_cfg.items() if enabled and n and n.strip()]
        elif isinstance(names_cfg, str):
            # Зворотна сумісність зі старим текстовим форматом (через кому).
            names = [n.strip() for n in names_cfg.split(",") if n.strip()]
        else:
            names = []
        if not names:
            return

        try:
            if platform.system() == "Windows":
                self._lib = ctypes.CDLL("obs")
            else:
                lib_path = ctypes.util.find_library("obs")
                if not lib_path:
                    raise RuntimeError("бібліотеку obs не знайдено (find_library)")
                self._lib = ctypes.CDLL(lib_path)

            get_source_by_name = self._wrap("obs_get_source_by_name", ctypes.POINTER(self._Source), [ctypes.c_char_p])
            self._source_release = self._wrap("obs_source_release", None, [ctypes.POINTER(self._Source)])
            self._volmeter_create = self._wrap("obs_volmeter_create", ctypes.POINTER(self._Volmeter), [ctypes.c_int])
            self._volmeter_attach_source = self._wrap("obs_volmeter_attach_source", ctypes.c_bool, [ctypes.POINTER(self._Volmeter), ctypes.POINTER(self._Source)])
            self._volmeter_add_callback = self._wrap("obs_volmeter_add_callback", None, [ctypes.POINTER(self._Volmeter), self._volmeter_callback_t, ctypes.c_void_p])
            self._volmeter_remove_callback = self._wrap("obs_volmeter_remove_callback", None, [ctypes.POINTER(self._Volmeter), self._volmeter_callback_t, ctypes.c_void_p])
            self._volmeter_destroy = self._wrap("obs_volmeter_destroy", None, [ctypes.POINTER(self._Volmeter)])

            found_any = False
            missing = []
            for name in names:
                src = get_source_by_name(name.encode("utf-8"))
                if not src:
                    missing.append(name)
                    continue
                volmeter = self._volmeter_create(0)  # OBS_PEAK_METER_TYPE_SAMPLE_PEAK_METER
                if not volmeter:
                    self._source_release(src)
                    missing.append(name)
                    continue
                if not self._volmeter_attach_source(volmeter, src):
                    self._volmeter_destroy(volmeter)
                    self._source_release(src)
                    missing.append(name)
                    continue

                def make_callback(source_name):
                    def _cb(param, magnitude, peak, input_peak):
                        try:
                            db = float(peak[0])
                            with self._levels_lock:
                                self._levels[source_name] = (db, time.time())
                        except Exception:
                            pass
                    return self._volmeter_callback_t(_cb)

                cb = make_callback(name)
                self._volmeter_add_callback(volmeter, cb, None)

                self._sources[name] = src
                self._volmeters[name] = volmeter
                self._callbacks[name] = cb
                found_any = True

            if missing:
                print("[Music Duck] ⚠️ Не знайдено джерела OBS: {} (перевірте точні назви у списку 'Джерела')".format(", ".join(missing)))

            if not found_any:
                print("[Music Duck] Жодне джерело не вдалося підключити - експериментальне відстеження звуку вимкнено")
                self._cleanup()
                return

            self.available = True
            self.is_running = True
            self._stop_event.clear()
            self._poll_thread = threading.Thread(target=self._poll_loop, daemon=True)
            self._poll_thread.start()
            print("[Music Duck] 🔊 Відстеження звуку джерел активовано: {}".format(", ".join(self._sources.keys())))

        except Exception as e:
            print("[Music Duck] Не вдалося активувати відстеження звуку джерел (це очікувано на деяких системах): {}".format(e))
            self._cleanup()

    def _poll_loop(self):
        while not self._stop_event.is_set():
            try:
                now = time.time()
                with self._levels_lock:
                    levels_snapshot = dict(self._levels)
                for name in list(self._sources.keys()):
                    db, updated_at = levels_snapshot.get(name, (-999.0, 0.0))
                    is_loud = db > self.SILENCE_DB_THRESHOLD and (now - updated_at) < self.STALE_SECONDS
                    was_active = name in self._active_names
                    if is_loud and not was_active:
                        self._active_names.add(name)
                        audio_ducking_begin()
                    elif not is_loud and was_active and (now - updated_at) > self.HANGOVER_SECONDS:
                        self._active_names.discard(name)
                        audio_ducking_end()
            except Exception:
                pass
            self._stop_event.wait(0.2)

    def _cleanup(self):
        for name in list(self._volmeters.keys()):
            try:
                cb = self._callbacks.get(name)
                if cb:
                    self._volmeter_remove_callback(self._volmeters[name], cb, None)
                self._volmeter_destroy(self._volmeters[name])
            except Exception:
                pass
        for name in list(self._sources.keys()):
            try:
                self._source_release(self._sources[name])
            except Exception:
                pass
        self._sources.clear()
        self._volmeters.clear()
        self._callbacks.clear()
        self._levels.clear()

    def stop(self):
        if not self.is_running:
            return
        self.is_running = False
        self._stop_event.set()
        if self._poll_thread:
            self._poll_thread.join(timeout=2)
        # Якщо на момент зупинки якісь джерела вважалися "гучними" -
        # знімаємо ducking, який вони утримували, інакше лічильник "зависне".
        for name in list(self._active_names):
            try:
                audio_ducking_end()
            except Exception:
                pass
        self._active_names.clear()
        self._cleanup()
        print("[Music Duck] Відстеження звуку джерел зупинено")


source_audio_duck_monitor = SourceAudioDuckMonitor()


# ============================================================================
# ЗБЕРЕЖЕННЯ / ЗАВАНТАЖЕННЯ СПИСКІВ МОДЕРАЦІЇ
# ============================================================================
MODERATION_DATA_FILE = os.path.join(os.path.dirname(__file__), "moderation_data.json")


def load_moderation_data():
    global blocked_users, no_tts_users, custom_nicknames, user_voice_assignments
    if os.path.exists(MODERATION_DATA_FILE):
        try:
            with open(MODERATION_DATA_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if isinstance(data, dict):
                blocked_list = data.get("blocked_users", [])
                no_tts_list = data.get("no_tts_users", [])
                custom_map = data.get("custom_nicknames", {})
                voice_map = data.get("user_voice_assignments", {})
                blocked_users = set(name.lower().strip() for name in blocked_list if name)
                no_tts_users = set(name.lower().strip() for name in no_tts_list if name)
                custom_nicknames = {}
                user_voice_assignments = {}
                if isinstance(custom_map, dict):
                    for key, value in custom_map.items():
                        if not key:
                            continue
                        if isinstance(value, str):
                            alias = value.strip()
                            if alias:
                                custom_nicknames[str(key).strip().lower()] = alias
                        elif isinstance(value, dict):
                            alias = str(value.get("nickname", "")).strip()
                            if alias:
                                custom_nicknames[str(key).strip().lower()] = alias
                if isinstance(voice_map, dict):
                    for key, value in voice_map.items():
                        voice_id = str(value or "").strip()
                        if key and voice_id:
                            user_voice_assignments[str(key).strip().lower()] = voice_id
                print(f"[Модерація] Завантажено {len(blocked_users)} заблокованих, {len(no_tts_users)} без TTS, {len(custom_nicknames)} кастомних ніків та {len(user_voice_assignments)} голосових призначень")
        except Exception as e:
            print(f"[Модерація] Помилка завантаження: {e}")
            blocked_users = set()
            no_tts_users = set()
            custom_nicknames = {}
            user_voice_assignments = {}
    else:
        blocked_users = set()
        no_tts_users = set()
        custom_nicknames = {}
        user_voice_assignments = {}
        print("[Модерація] Файл не знайдено, створено порожні списки")


def save_moderation_data():
    try:
        data = {
            "blocked_users": list(blocked_users),
            "no_tts_users": list(no_tts_users),
            "custom_nicknames": dict(sorted(custom_nicknames.items())),
            "user_voice_assignments": dict(sorted(user_voice_assignments.items()))
        }
        with open(MODERATION_DATA_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        print(f"[Модерація] Збережено {len(blocked_users)} заблокованих, {len(no_tts_users)} без TTS, {len(custom_nicknames)} кастомних ніків та {len(user_voice_assignments)} голосових призначень")
    except Exception as e:
        print(f"[Модерація] Помилка збереження: {e}")


# ============================================================================
# АКТИВНІСТЬ КОРИСТУВАЧІВ (для "Топ активних" у меню чату)
# ============================================================================
USER_ACTIVITY_FILE = os.path.join(os.path.dirname(__file__), "user_activity.json")
ACTIVITY_RETENTION_DAYS = 35  # трохи більше за 30-денне вікно про запас
ACTIVITY_SAVE_INTERVAL = 30  # секунд між автозбереженнями на диск

user_activity = {}
_user_activity_lock = threading.Lock()
_last_activity_save = 0.0


def load_user_activity():
    global user_activity
    try:
        if os.path.exists(USER_ACTIVITY_FILE):
            with open(USER_ACTIVITY_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            user_activity = data if isinstance(data, dict) else {}
            print("[Активність] Завантажено дані по {} користувачах".format(len(user_activity)))
        else:
            user_activity = {}
    except Exception as e:
        print("[Активність] Помилка завантаження: {}".format(e))
        user_activity = {}


def save_user_activity():
    try:
        with _user_activity_lock:
            data = json.dumps(user_activity, ensure_ascii=False)
        with open(USER_ACTIVITY_FILE, 'w', encoding='utf-8') as f:
            f.write(data)
    except Exception as e:
        print("[Активність] Помилка збереження: {}".format(e))


def clear_user_activity():
    """Повністю очищає крос-мережеву активність ('🌐 Топ глядачів усіх мереж').

    Це окреме сховище (user_activity.json) від історії глядачів TikTok:
    воно рахує повідомлення по всіх платформах одразу, тож очищення
    TikTok-історії його не зачіпає і потребує власної кнопки/точки очищення.
    """
    global user_activity
    with _user_activity_lock:
        removed = len(user_activity)
        user_activity = {}
    save_user_activity()
    print("[Активність] Крос-мережеву активність очищено повністю, видалено записів: {}".format(removed))
    return removed


def record_user_activity(platform, username, display_name):
    global _last_activity_save
    key_username = (username or display_name or "").strip().lower()
    if not key_username:
        return
    platform_key = (platform or "").strip().lower()
    today = time.strftime("%Y-%m-%d")

    with _user_activity_lock:
        key = "{}:{}".format(platform_key, key_username)
        entry = user_activity.get(key)
        if entry is None:
            entry = {"platform": platform_key, "username": username or display_name, "display_name": display_name or username, "total": 0, "days": {}}
            user_activity[key] = entry
        entry["display_name"] = display_name or entry.get("display_name") or username
        entry["total"] = int(entry.get("total", 0) or 0) + 1
        days = entry.setdefault("days", {})
        days[today] = int(days.get(today, 0) or 0) + 1

        # Старі добові кошики вже враховані у "total" - для рольового 30-денного
        # вікна тримати їх довше немає сенсу, обрізаємо, щоб файл не ріс вічно.
        if len(days) > ACTIVITY_RETENTION_DAYS + 5:
            cutoff = time.time() - ACTIVITY_RETENTION_DAYS * 86400
            for d in list(days.keys()):
                try:
                    d_ts = time.mktime(time.strptime(d, "%Y-%m-%d"))
                except Exception:
                    continue
                if d_ts < cutoff:
                    del days[d]

    now = time.time()
    if now - _last_activity_save >= ACTIVITY_SAVE_INTERVAL:
        _last_activity_save = now
        save_user_activity()


def get_top_active(limit_all_time=10, limit_last_30_days=5):
    now = time.time()
    cutoff_30d = now - 30 * 86400
    all_time_list = []
    last30_list = []

    with _user_activity_lock:
        snapshot = {k: dict(v, days=dict(v.get("days", {}) or {})) for k, v in user_activity.items()}

    for entry in snapshot.values():
        total = int(entry.get("total", 0) or 0)
        if total <= 0:
            continue
        last30_total = 0
        for d, cnt in (entry.get("days", {}) or {}).items():
            try:
                d_ts = time.mktime(time.strptime(d, "%Y-%m-%d"))
            except Exception:
                continue
            if d_ts >= cutoff_30d:
                last30_total += int(cnt or 0)
        platform = entry.get("platform") or ""
        username = entry.get("username") or ""
        display_name = entry.get("display_name") or username
        item = {
            "platform": platform,
            "display_name": display_name,
            "username": username,
            "nickname": get_custom_nickname(platform, username, display_name),
        }
        all_time_list.append(dict(item, count=total))
        if last30_total > 0:
            last30_list.append(dict(item, count=last30_total))

    all_time_list.sort(key=lambda x: -x["count"])
    last30_list.sort(key=lambda x: -x["count"])
    return {"all_time": all_time_list[:limit_all_time], "last_30_days": last30_list[:limit_last_30_days]}


def get_top_likes(limit=10):
    """Топ глядачів TikTok за накопиченими лайками (дані лише з TikTok - інші
    платформи не надають лайки на рівні окремого глядача через їхні публічні API)."""
    with _tiktok_viewer_history_lock:
        snapshot = dict(tiktok_viewer_history)

    items = []
    for unique_id, entry in snapshot.items():
        like_count = int(entry.get("like_count", 0) or 0)
        if like_count <= 0:
            continue
        nickname = entry.get("nickname") or unique_id
        items.append({
            "platform": "tiktok",
            "username": unique_id,
            "display_name": nickname,
            "nickname": get_custom_nickname("tiktok", unique_id, nickname),
            "avatar_url": entry.get("avatar_url") or "",
            "count": like_count,
        })

    items.sort(key=lambda x: -x["count"])
    return {"top_likes": items[:limit]}


def make_user_keys(platform, username, display_name=""):
    keys = []
    platform_key = (platform or "").strip().lower()
    username_key = (username or "").strip().lower()
    display_key = (display_name or "").strip().lower()

    if platform_key and username_key:
        keys.append(f"{platform_key}:{username_key}")
    if username_key:
        keys.append(username_key)
    if platform_key and display_key:
        keys.append(f"{platform_key}:{display_key}")
    if display_key:
        keys.append(display_key)

    unique_keys = []
    for key in keys:
        if key and key not in unique_keys:
            unique_keys.append(key)
    return unique_keys


def get_custom_nickname(platform, username, display_name=""):
    for key in make_user_keys(platform, username, display_name):
        nickname = custom_nicknames.get(key)
        if nickname:
            return nickname
    return ""


def resolve_display_name(platform, username, display_name):
    nickname = get_custom_nickname(platform, username, display_name)
    return nickname if nickname else ((display_name or username or "Глядач").strip())


def set_custom_nickname(platform, username, display_name, nickname):
    global custom_nicknames
    nickname = (nickname or "").strip()
    keys = make_user_keys(platform, username, display_name)
    if not keys:
        return False

    primary_key = keys[0]
    for key in keys:
        if key in custom_nicknames and key != primary_key:
            custom_nicknames.pop(key, None)

    if not nickname:
        removed = False
        for key in keys:
            if key in custom_nicknames:
                custom_nicknames.pop(key, None)
                removed = True
        if removed:
            save_moderation_data()
            print(f"[Модерація] Видалено кастомний нік для {platform}:{username or display_name}")
        return removed

    custom_nicknames[primary_key] = nickname
    save_moderation_data()
    print(f"[Модерація] Задано кастомний нік для {platform}:{username or display_name} -> {nickname}")
    return True


def remove_custom_nickname(platform, username, display_name=""):
    return set_custom_nickname(platform, username, display_name, "")


def get_custom_nicknames_list():
    items = []
    for key in sorted(custom_nicknames.keys()):
        alias = custom_nicknames.get(key, "")
        if not alias:
            continue
        if ':' in key:
            platform, username = key.split(':', 1)
        else:
            platform, username = '', key
        items.append({
            "key": key,
            "platform": platform,
            "username": username,
            "nickname": alias
        })
    return items


def resolve_local_path(base_dir, raw_path):
    raw_path = (raw_path or "").strip()
    if not raw_path:
        return ""
    if os.path.isabs(raw_path):
        return raw_path
    if base_dir:
        return os.path.normpath(os.path.join(base_dir, raw_path))
    return raw_path


SUPPORTED_TTS_ENGINES = ("google", "browser", "elevenlabs")
LEGACY_TTS_ENGINES = ("piper", "edge")

# Каталог голосів ElevenLabs, які має користувач у своєму акаунті.
# id = voice_id з панелі ElevenLabs (Voices -> ID).
ELEVENLABS_VOICES = [
    {"id": "2OXYbN1uGomXXJtv9Dq6", "title": "Mariya Maro"},
    {"id": "WtDqMP4cPOGB6kDiLZgi", "title": "Did Vishchun"},
    {"id": "yFdwk1Wl0Sy2695aoxng", "title": "Hector Surovy"},
    {"id": "gMAK1IqiD8ZPJyBK3jvF", "title": "Yaroslav"},
    {"id": "4nLP0u2B3yI0lyzATFnN", "title": "Anton"},
    {"id": "JTlYtJrcTzPC71hMLOxo", "title": "Yuki"},
    {"id": "iwP1PxYYSTdHA1qXlwFe", "title": "Sandra Squirrel"},
    {"id": "nDJIICjR9zfJExIFeSCN", "title": "Emmaline"},
    {"id": "agL69Vji082CshT65Tcy", "title": "Blackwood"},
]

ELEVENLABS_MODELS = [
    {"value": "eleven_multilingual_v2", "label": "eleven_multilingual_v2 (найкраща якість, укр. мова)"},
    {"value": "eleven_turbo_v2_5", "label": "eleven_turbo_v2_5 (швидкий, дешевший)"},
    {"value": "eleven_flash_v2_5", "label": "eleven_flash_v2_5 (найшвидший, ~75 мс)"},
]


def elevenlabs_known_voice_ids():
    return set(voice["id"] for voice in ELEVENLABS_VOICES)


def looks_like_elevenlabs_voice_id(value):
    """ID голосу ElevenLabs — це рядок ~20 символів [A-Za-z0-9].

    Значення типу 'uk-UA', 'google', порожній рядок — це НЕ ID голосу,
    їх не можна надсилати в ElevenLabs (буде HTTP 400/404).
    """
    value = (value or "").strip()
    if len(value) < 15 or len(value) > 40:
        return False
    if "-" in value or "_" in value or " " in value:
        return False
    return value.isalnum()


def resolve_elevenlabs_voice_id(candidate=""):
    """Повертає гарантовано валідний ID голосу ElevenLabs."""
    candidate = (candidate or "").strip()
    known = elevenlabs_known_voice_ids()
    if candidate in known:
        return candidate
    if looks_like_elevenlabs_voice_id(candidate):
        return candidate
    fallback = (config.get("elevenlabs_voice_id") or "").strip()
    if fallback in known or looks_like_elevenlabs_voice_id(fallback):
        if candidate and config.get("elevenlabs_debug"):
            print("[TTS] ElevenLabs: '{}' не є ID голосу — беру голос за замовчуванням {}".format(
                candidate, fallback))
        return fallback
    if candidate:
        print("[TTS] ElevenLabs: '{}' не є ID голосу і в налаштуваннях теж немає валідного — беру {}".format(
            candidate, ELEVENLABS_VOICES[0]["id"]))
    return ELEVENLABS_VOICES[0]["id"]


GOOGLE_TTS_LANGS = [
    ("uk-UA", "Google: українська (uk-UA)"),
    ("en-US", "Google: англійська США (en-US)"),
    ("en-GB", "Google: англійська Британія (en-GB)"),
    ("pl-PL", "Google: польська (pl-PL)"),
    ("de-DE", "Google: німецька (de-DE)"),
    ("fr-FR", "Google: французька (fr-FR)"),
    ("es-ES", "Google: іспанська (es-ES)"),
    ("it-IT", "Google: італійська (it-IT)"),
    ("cs-CZ", "Google: чеська (cs-CZ)"),
    ("ja-JP", "Google: японська (ja-JP)"),
]


def build_voice_options():
    """Список варіантів для всіх полів вибору голосу у веб-панелі.

    Спочатку — порожній варіант (голос за замовчуванням рушія),
    далі всі голоси ElevenLabs, далі мовні коди Google TTS.
    """
    options = [{"value": "", "label": "— голос за замовчуванням —"}]
    for voice in ELEVENLABS_VOICES:
        options.append({"value": voice["id"],
                        "label": "ElevenLabs: {}".format(voice["title"])})
    for code, label in GOOGLE_TTS_LANGS:
        options.append({"value": code, "label": label})
    return options


def normalize_tts_engine(engine=None):
    """
    Приводить значення рушія TTS до підтримуваного.
    Piper та Microsoft Edge видалені — старі збережені конфіги
    автоматично мігрують на google, інакше озвучка мовчала б.
    """
    value = (engine if engine is not None else config.get("tts_engine")) or "google"
    value = str(value).strip().lower()
    if value == "elevenlabs" and not (config.get("elevenlabs_api_key") or "").strip():
        print("[TTS] Обрано ElevenLabs, але API-ключ не введено — використовую Google TTS")
        return "google"
    if value in LEGACY_TTS_ENGINES or value not in SUPPORTED_TTS_ENGINES:
        if value in LEGACY_TTS_ENGINES:
            print("[TTS] Рушій '{}' більше не підтримується — перемикаю на google".format(value))
            try:
                if (config.get("tts_engine") or "").strip().lower() == value:
                    config["tts_engine"] = "google"
                    save_config()
            except Exception:
                pass
        return "google"
    return value


def get_available_voice_profiles():
    """
    Список індивідуальних голосових профілів для призначення користувачам
    (контекстне меню чату -> «Голос»). Наповнюється голосами ElevenLabs;
    якщо ключ ElevenLabs не введено — список порожній, бо Google TTS
    індивідуальних голосів не має.
    """
    if not (config.get("elevenlabs_api_key") or "").strip():
        return []
    return [{"id": voice["id"], "title": voice["title"]} for voice in ELEVENLABS_VOICES]


def get_user_voice_assignment(platform, username, display_name=""):
    for key in make_user_keys(platform, username, display_name):
        voice_id = user_voice_assignments.get(key)
        if voice_id:
            return voice_id
    return ""


def set_user_voice_assignment(platform, username, display_name, voice_id):
    global user_voice_assignments
    voice_id = (voice_id or "").strip()
    keys = make_user_keys(platform, username, display_name)
    if not keys:
        return False
    primary_key = keys[0]
    for key in keys:
        if key in user_voice_assignments and key != primary_key:
            user_voice_assignments.pop(key, None)
    if not voice_id:
        return remove_user_voice_assignment(platform, username, display_name)
    user_voice_assignments[primary_key] = voice_id
    save_moderation_data()
    print(f"[Модерація] Голосовий профіль для {platform}:{username or display_name} -> {voice_id}")
    return True


def remove_user_voice_assignment(platform, username, display_name=""):
    global user_voice_assignments
    removed = False
    for key in make_user_keys(platform, username, display_name):
        if key in user_voice_assignments:
            user_voice_assignments.pop(key, None)
            removed = True
    if removed:
        save_moderation_data()
        print(f"[Модерація] Видалено голосовий профіль для {platform}:{username or display_name}")
    return removed


def resolve_user_tts_profile(platform, username, display_name=""):
    engine = normalize_tts_engine(config.get("tts_engine"))
    voice = (config.get("tts_voice") or "uk-UA").strip()
    if engine == "elevenlabs":
        # Персональний голос користувача (якщо призначений) має пріоритет
        # над загальним голосом ElevenLabs із налаштувань.
        assigned = (get_user_voice_assignment(platform, username, display_name) or "").strip()
        voice = assigned or (config.get("elevenlabs_voice_id") or "").strip() or ELEVENLABS_VOICES[0]["id"]
    return engine, voice


load_moderation_data()
load_user_activity()
load_tiktok_viewer_history()
load_music_playlist_order()
load_music_removed_tracks()
load_music_runtime_state()
music_restore_last_session()

# ============================================================================
# АВТОМАТИЧНИЙ ПЕРЕКЛАД
# ============================================================================
UA_SPECIFIC_CHARS = set('іїєґІЇЄҐ')
RU_SPECIFIC_CHARS = set('ыъэЫЪЭ')

# Часті слова-маркери для випадків, коли в тексті немає літер,
# унікальних для однієї з мов (напр. "дякую", "спасибо").
UA_MARKER_WORDS = frozenset((
    'та', 'що', 'як', 'де', 'бо', 'чи', 'був', 'була', 'було', 'були', 'дякую',
    'вітаю', 'добре', 'гарно', 'треба', 'зараз', 'дуже', 'тут', 'там', 'зробив',
    'зробити', 'подивись', 'подивитись', 'давай', 'знову', 'ще', 'вже', 'нехай',
    'слава', 'україна', 'україні', 'український', 'українською', 'привіт', 'будь',
    'ласка', 'жарт', 'молодець', 'потужно', 'радий', 'тримай', 'нарешті', 'трохи',
    'гра', 'грати', 'граєш', 'стрім', 'стріму', 'глядач', 'підписка', 'нагорода',
))
RU_MARKER_WORDS = frozenset((
    'что', 'как', 'где', 'потому', 'или', 'был', 'была', 'было', 'были', 'спасибо',
    'привет', 'хорошо', 'нужно', 'сейчас', 'очень', 'здесь', 'там', 'сделал',
    'сделать', 'посмотри', 'посмотреть', 'давай', 'опять', 'еще', 'уже', 'пусть',
    'сегодня', 'завтра', 'который', 'она', 'они', 'тоже', 'если', 'когда', 'почему',
    'молодец', 'ничего', 'немного', 'играть', 'играешь', 'стрим', 'стрима',
    'зритель', 'подписка', 'награда', 'пожалуйста', 'конечно',
))


def detect_cyrillic_lang(text):
    """Повертає 'uk', 'ru' або 'other' (латиниця/інше)."""
    if not text:
        return 'other'
    if not re.search(r'[А-Яа-яЁёІіЇїЄєҐґ]', text):
        return 'other'
    if any(ch in UA_SPECIFIC_CHARS for ch in text):
        return 'uk'
    if any(ch in RU_SPECIFIC_CHARS for ch in text):
        return 'ru'
    words = set(re.findall(r"[а-яёіїєґ']+", text.lower()))
    ua_hits = len(words & UA_MARKER_WORDS)
    ru_hits = len(words & RU_MARKER_WORDS)
    if ru_hits > ua_hits:
        return 'ru'
    if ua_hits > ru_hits:
        return 'uk'
    # Неоднозначно: вважаємо українською, щоб не перекладати вже український текст
    return 'uk'


def text_is_ukrainian(text):
    return detect_cyrillic_lang(text) == 'uk'


_CJK_RANGE_RE = re.compile(
    r'[\一-\鿿\㐀-\䶿\぀-\ヿ\가-\힣\豈-\﫿]'
)


def _contains_cjk(text):
    """True, якщо у тексті є китайські/японські/корейські символи."""
    if not text:
        return False
    return bool(_CJK_RANGE_RE.search(text))


def detect_source_lang_hint(text):
    """
    Грубе визначення мови-джерела для MyMemory (кирилиця / CJK / інше).
    Повертає код мови на кшталт 'uk', 'ru', 'zh-CN', 'ja', 'ko' або 'en'.
    """
    if not text:
        return 'en'
    detected = detect_cyrillic_lang(text)
    if detected in ('uk', 'ru'):
        return detected
    if re.search(r'[\぀-\ヿ]', text):
        return 'ja'
    if re.search(r'[\가-\힣]', text):
        return 'ko'
    if re.search(r'[\一-\鿿\㐀-\䶿\豈-\﫿]', text):
        return 'zh-CN'
    return 'en'


def _looks_like_target(text, target_lang):
    """Груба перевірка, чи текст уже мовою призначення."""
    if not text:
        return False
    if target_lang == 'uk':
        return detect_cyrillic_lang(text) == 'uk'
    if target_lang == 'en':
        # немає ані кирилиці, ані CJK-символів (кит./яп./кор.) ->
        # вважаємо, що це вже латиниця/англійська
        if _contains_cjk(text):
            return False
        return not re.search(r'[А-Яа-яЁёІіЇїЄєҐґ]', text)
    return False


def get_tts_translate_target():
    """
    Повертає 'uk', 'en' або '' (переклад вимкнено).
    Два перемикачі взаємовиключні: якщо якимось чином увімкнені обидва,
    пріоритет має українська.
    """
    if config.get("tts_translate_uk", False):
        return 'uk'
    if config.get("tts_translate_en", False):
        return 'en'
    # сумісність зі старим одиночним перемикачем
    if config.get("tts_auto_translate", False):
        return 'uk'
    return ''


def translate_text_to(text, target_lang='uk'):
    if not text or len(text.strip()) < 2:
        return text
    if target_lang not in ('uk', 'en'):
        return text
    if _looks_like_target(text, target_lang):
        print("[Translator] Текст уже {} — переклад не потрібен: {}...".format(target_lang, text[:30]))
        return text

    cache_key = "auto|{}|{}".format(target_lang, text)
    with translation_lock:
        if cache_key in translation_cache:
            return translation_cache[cache_key]

    translated = None

    # ---------- 1. MyMemory ----------
    try:
        source_lang = detect_source_lang_hint(text)
        if source_lang != target_lang:
            url = "https://api.mymemory.translated.net/get?q={}&langpair={}|{}".format(
                quote(text), source_lang, target_lang)
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=5) as response:
                data = json.loads(response.read().decode('utf-8'))
                if 'responseData' in data and 'translatedText' in data['responseData']:
                    candidate = data['responseData']['translatedText']
                    if candidate and _looks_like_target(candidate, target_lang):
                        translated = candidate
                        print("[Translator] MyMemory ({}): {}... -> {}...".format(
                            target_lang, text[:30], translated[:30]))
    except Exception as e:
        print("[Translator] MyMemory помилка: {}".format(e))

    # ---------- 2. Google Translate (unofficial), з короткими повторними спробами ----------
    if translated is None:
        gurl = "https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl={}&dt=t&q={}".format(
            target_lang, quote(text))
        _google_attempts = 2
        for _attempt in range(_google_attempts):
            try:
                req = urllib.request.Request(gurl, headers={'User-Agent': 'Mozilla/5.0'})
                with urllib.request.urlopen(req, timeout=5) as response:
                    data = json.loads(response.read().decode('utf-8'))
                    candidate = data[0][0][0] if data and data[0] and data[0][0] else None
                    if candidate and _looks_like_target(candidate, target_lang):
                        translated = candidate
                        print("[Translator] Google ({}): {}... -> {}...".format(
                            target_lang, text[:30], translated[:30]))
                break
            except Exception as e:
                print("[Translator] Google помилка (спроба {}/{}): {}".format(
                    _attempt + 1, _google_attempts, e))
                if _attempt + 1 < _google_attempts:
                    time.sleep(0.6)

    if translated is None:
        print("[Translator] Переклад не вдався, лишаємо оригінал: {}...".format(text[:30]))
        translated = text

    with translation_lock:
        translation_cache[cache_key] = translated
        if len(translation_cache) > MAX_TRANSLATION_CACHE_SIZE:
            oldest_key = next(iter(translation_cache))
            del translation_cache[oldest_key]

    return translated


def translate_comment_only(text, target_lang=None):
    """Сумісність зі старим кодом: за замовчуванням перекладає українською."""
    return translate_text_to(text, target_lang or 'uk')


# ============================================================================
# ОБРОБКА ТЕКСТУ ТА МОДЕРАЦІЯ
# ============================================================================
def clean_nickname_for_tts(nickname):
    nickname = (nickname or "").replace('_', ' ').strip()
    if config["tts_read_symbols"]:
        cleaned = re.sub(r'[^a-zA-Z0-9а-яА-ЯёЁіїєІЇЄҐ\s-]', ' ', nickname)
        cleaned = re.sub(r'\s+', ' ', cleaned).strip()
        return cleaned if cleaned else (nickname or "Глядач")
    return nickname if nickname else "Глядач"


def clamp_tiktok_tts_text(text, max_length=MAX_TIKTOK_TTS_LENGTH):
    text = (text or "").strip()
    if len(text) <= max_length:
        return text
    return text[:max_length - 3].rstrip() + "..."

def format_tiktok_text(template, **kwargs):
    safe_kwargs = {k: ("" if v is None else str(v)) for k, v in kwargs.items()}
    try:
        rendered = template.format(**safe_kwargs)
    except Exception:
        rendered = template
        for key, value in safe_kwargs.items():
            rendered = rendered.replace("{" + key + "}", value)
    return clamp_tiktok_tts_text(rendered)


def normalize_tts_text(text):
    text = "" if text is None else str(text)
    if not text:
        return ""

    text = text.replace('\r', ' ').replace('\n', ' ').replace('_', ' ')
    text = re.sub(r'(?i)https?://[^\s]+|www.[^\s]+', ' посилання ', text)
    text = re.sub(r'(?<!\w)@([A-Za-zА-Яа-яЁёїІіЄєҐ0-9_.-]+)', r' \1 ', text)
    text = re.sub(r'(?<!\w)#([A-Za-zА-Яа-яЁёїІіЄєҐ0-9_.-]+)', r' \1 ', text)

    symbol_map = {'&': ' і ', '+': ' плюс ', '=': ' дорівнює ', '%': ' відсотків ', '№': ' номер ', '/': ' дріб ', '\\': ' ', '*': ' ', '~': ' ', '|': ' '}
    for src, dst in symbol_map.items():
        text = text.replace(src, dst)

    text = re.sub(r'[""«»`]+', ' ', text).replace("'", '')
    text = re.sub(r'([!?.,:;])\1+', r'\1', text)
    text = re.sub(r'([а-яa-zіїєё])\1{3,}', r'\1\1', text, flags=re.IGNORECASE)
    text = re.sub(r'\s+', ' ', text).strip(' .,!?:;-')
    return text


def get_tiktok_event_id(event):
    common = getattr(event, 'common', None)
    for attr_name in ('message_id', 'msg_id', 'id'):
        value = getattr(common, attr_name, None) if common is not None else None
        if value:
            return str(value)
    for attr_name in ('comment_id', 'id'):
        value = getattr(event, attr_name, None)
        if value:
            return str(value)
    return None


def get_message_priority(platform, is_alert=False, priority=None):
    if priority is not None:
        return priority
    if is_alert:
        return PRIORITY_MAP["alert"]
    return PRIORITY_MAP["chat"]


def is_repeated_message_spam(display_name, text, current_time):
    global repeated_message_tracker
    normalized_name = (display_name or "").strip().lower()
    normalized_text = re.sub(r'\s+', ' ', (text or '').strip().lower())

    if not normalized_name or not normalized_text:
        return False

    with buffer_lock:
        repeated_message_tracker = {
            key: [ts for ts in timestamps if current_time - ts < IDENTICAL_MESSAGE_WINDOW]
            for key, timestamps in repeated_message_tracker.items()
            if any(current_time - ts < IDENTICAL_MESSAGE_WINDOW for ts in timestamps)
        }

        key = (normalized_name, normalized_text)
        timestamps = repeated_message_tracker.get(key, [])

        if len(timestamps) >= IDENTICAL_MESSAGE_LIMIT:
            repeated_message_tracker[key] = timestamps
            return True

        timestamps.append(current_time)
        repeated_message_tracker[key] = timestamps
    return False


def tiktok_event_timestamp_seconds(event):
    raw_value = getattr(event, 'create_time', None)
    if raw_value is None:
        common = getattr(event, 'common', None)
        raw_value = getattr(common, 'create_time', None) if common is not None else None
    try:
        value = float(raw_value)
        if value > 1000000000000:
            value = value / 1000.0
        return value
    except Exception:
        return None


def tiktok_plain_data(value, depth=3):
    if depth <= 0:
        return None
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, dict):
        return {str(k): tiktok_plain_data(v, depth - 1) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [tiktok_plain_data(v, depth - 1) for v in value[:40]]
    for method_name in ('as_dict', 'to_dict', 'dict'):
        method = getattr(value, method_name, None)
        if callable(method):
            try:
                converted = method()
                if converted is not value:
                    return tiktok_plain_data(converted, depth - 1)
            except Exception:
                pass
    raw_dict = getattr(value, '__dict__', None)
    if isinstance(raw_dict, dict):
        return {
            str(k): tiktok_plain_data(v, depth - 1)
            for k, v in raw_dict.items()
            if not str(k).startswith('_')
        }
    return None


def tiktok_find_first_int(data, names, minimum=0):
    names = {str(name).lower() for name in names}
    visited = set()

    def walk(value):
        marker = id(value)
        if marker in visited:
            return None
        visited.add(marker)
        if isinstance(value, dict):
            for key, item in value.items():
                if str(key).lower() in names:
                    try:
                        parsed = int(float(item or 0))
                        if parsed >= minimum:
                            return parsed
                    except Exception:
                        pass
            for item in value.values():
                found = walk(item)
                if found is not None:
                    return found
        elif isinstance(value, (list, tuple)):
            for item in value:
                found = walk(item)
                if found is not None:
                    return found
        return None

    return walk(data)


def tiktok_extract_viewer_count(event):
    # 'total' - поле поточної кількості глядачів на RoomUserSeqEvent у
    # TikTokLive 6.6.6 (перевірено по вихідниках бібліотеки). Навмисно НЕ
    # додаємо сюди 'total_user' - це інша метрика (унікальних глядачів за
    # весь стрім, а не поточних онлайн), її не можна плутати з лічильником
    # "зараз дивляться".
    current_fields = ('total', 'viewer_count', 'user_count', 'online_user_count', 'room_viewer_count', 'current_viewer_count', 'live_user_count')
    for attr_name in current_fields:
        raw_value = getattr(event, attr_name, None)
        if raw_value is None:
            continue
        try:
            parsed_value = int(float(raw_value or 0))
            if parsed_value >= 0:
                return parsed_value
        except Exception:
            pass
    plain = tiktok_plain_data(event, depth=4)
    return tiktok_find_first_int(plain, current_fields, minimum=0)


def tiktok_extract_like_counts(event):
    increment_fields = ('count', 'like_count', 'likes', 'likes_count', 'repeat_count')
    explicit_user_total_fields = ('user_like_count', 'user_likes', 'user_total_likes', 'like_count_total', 'likes_total')
    ambiguous_total_fields = ('total', 'total_count')
    stream_total_fields = ('total_like_count', 'total_likes', 'room_like_count', 'stream_like_count', 'like_total')

    def first_attr_int(names):
        for attr_name in names:
            raw_value = getattr(event, attr_name, None)
            if raw_value is None:
                continue
            try:
                parsed_value = int(float(raw_value or 0))
                if parsed_value >= 0:
                    return parsed_value
            except Exception:
                pass
        return None

    plain = None
    increment = first_attr_int(increment_fields)
    user_total = first_attr_int(explicit_user_total_fields)
    ambiguous_total = first_attr_int(ambiguous_total_fields)
    stream_total = first_attr_int(stream_total_fields)
    if increment is None or user_total is None or ambiguous_total is None or stream_total is None:
        plain = tiktok_plain_data(event, depth=5)
    if increment is None:
        increment = tiktok_find_first_int(plain, increment_fields, minimum=0)
    if user_total is None:
        user_total = tiktok_find_first_int(plain, explicit_user_total_fields, minimum=0)
    if ambiguous_total is None:
        ambiguous_total = tiktok_find_first_int(plain, ambiguous_total_fields, minimum=0)
    if stream_total is None:
        stream_total = tiktok_find_first_int(plain, stream_total_fields, minimum=0)

    if user_total is None and stream_total is None and ambiguous_total is not None:
        # IMPORTANT: TikTok's WebcastLikeMessage only ever exposes a
        # ROOM-WIDE cumulative total (shared across every viewer) under this
        # ambiguous 'total' field - there is no per-user cumulative total in
        # the real event payload. Treating it as a per-user total causes
        # cross-user contamination (one user's tracker picks up a huge delta
        # driven by OTHER users' likes). It is classified as `stream_total`
        # here; per-user counting must rely on the per-event `count` (burst
        # size) instead - see on_like().
        stream_total = ambiguous_total

    return int(increment or 0), int(user_total or 0), int(stream_total or 0), plain


def tiktok_mark_live_activity(min_viewers=1):
    global tiktok_live_viewer_count, tiktok_live_is_active
    tiktok_live_is_active = True
    try:
        current_viewers = int(tiktok_live_viewer_count or 0)
    except Exception:
        current_viewers = 0
    if current_viewers < int(min_viewers or 1):
        tiktok_live_viewer_count = int(min_viewers or 1)


def tiktok_try_retrieve_room_info(username, min_refresh_interval=45):
    global tiktok_room_info_cache, tiktok_room_info_cache_username, tiktok_last_room_info_refresh_ts, tiktok_last_room_info_debug_ts
    username = (username or '').strip().lstrip('@')
    if not username or not TIKTOK_AVAILABLE:
        return None
    now = time.time()
    if (
        tiktok_room_info_cache
        and tiktok_room_info_cache_username == username
        and now - float(tiktok_last_room_info_refresh_ts or 0) < max(5, int(min_refresh_interval or 45))
    ):
        return tiktok_room_info_cache
    try:
        client = TikTokLiveClient(unique_id=username)
        method = getattr(client, 'retrieve_room_info', None)
        room_info = None
        if callable(method):
            result = method()
            if hasattr(result, '__await__'):
                import asyncio
                loop = asyncio.new_event_loop()
                try:
                    asyncio.set_event_loop(loop)
                    room_info = loop.run_until_complete(result)
                finally:
                    asyncio.set_event_loop(None)
                    loop.close()
            else:
                room_info = result
        if not isinstance(room_info, dict):
            cached = getattr(client, 'room_info', None)
            if isinstance(cached, dict):
                room_info = cached
            else:
                converted = tiktok_plain_data(room_info, depth=4)
                if isinstance(converted, dict):
                    room_info = converted
                else:
                    converted = tiktok_plain_data(cached, depth=4)
                    if isinstance(converted, dict):
                        room_info = converted
        if isinstance(room_info, dict) and room_info:
            tiktok_room_info_cache = room_info
            tiktok_room_info_cache_username = username
            tiktok_last_room_info_refresh_ts = now
            try:
                status = int(room_info.get('status', 0) or 0)
            except Exception:
                status = 0
            try:
                user_count = int(room_info.get('user_count', 0) or 0)
            except Exception:
                user_count = 0
            try:
                total_user = int(((room_info.get('stats') or {}).get('total_user', 0)) or 0)
            except Exception:
                total_user = 0
            try:
                like_count = int(((room_info.get('stats') or {}).get('like_count', 0)) or 0)
            except Exception:
                like_count = 0
            if now - float(tiktok_last_room_info_debug_ts or 0) >= 15:
                tiktok_last_room_info_debug_ts = now
                print('[TikTok Analytics] retrieve_room_info ok | username=@{} | status={} | user_count={} | total_user={} | like_count={}'.format(username, status, user_count, total_user, like_count))
            return room_info
    except Exception as e:
        print('[TikTok Analytics] retrieve_room_info failed for @{}: {}'.format(username, e))
        return None
    return None


def remember_tiktok_comment_fingerprint(user_id, text, comment_ts=None, settle_mode=False):
    global tiktok_recent_comment_fingerprints, tiktok_recent_comment_simple_fingerprints
    now = time.time()
    normalized_user = (user_id or '').strip().lower()
    normalized_text = re.sub(r'\s+', ' ', (text or '').strip().lower())
    if not normalized_user or not normalized_text:
        return False

    exact_key = None
    if comment_ts is not None:
        try:
            exact_key = f"{normalized_user}::{normalized_text}::{int(float(comment_ts))}"
        except Exception:
            exact_key = None
    simple_key = f"{normalized_user}::{normalized_text}"

    with buffer_lock:
        tiktok_recent_comment_fingerprints = {
            key: ts for key, ts in tiktok_recent_comment_fingerprints.items()
            if now - ts < TIKTOK_DUPLICATE_TTL
        }
        tiktok_recent_comment_simple_fingerprints = {
            key: ts for key, ts in tiktok_recent_comment_simple_fingerprints.items()
            if now - ts < TIKTOK_SIMPLE_DUPLICATE_TTL
        }

        if exact_key and exact_key in tiktok_recent_comment_fingerprints:
            return True
        if settle_mode and simple_key in tiktok_recent_comment_simple_fingerprints:
            return True

        if exact_key:
            tiktok_recent_comment_fingerprints[exact_key] = now
        tiktok_recent_comment_simple_fingerprints[simple_key] = now
    return False


def remember_tiktok_comment_timestamp(comment_ts):
    global tiktok_last_comment_ts
    if comment_ts is None:
        return
    try:
        ts_value = float(comment_ts)
    except Exception:
        return
    with buffer_lock:
        if ts_value > float(tiktok_last_comment_ts or 0.0):
            tiktok_last_comment_ts = ts_value


def get_tiktok_last_comment_timestamp():
    with buffer_lock:
        return float(tiktok_last_comment_ts or 0.0)



def get_alert_widget_asset_path(platform, event_type, asset_kind):
    mapping = {
        ('tiktok', 'follow', 'audio'): 'tt_follow_audio_path',
        ('tiktok', 'follow', 'media'): 'tt_follow_media_path',
        ('tiktok', 'gift', 'audio'): 'tt_gift_audio_path',
        ('tiktok', 'gift', 'media'): 'tt_gift_media_path',
        ('tiktok', 'like', 'audio'): 'tt_like_audio_path',
        ('tiktok', 'like', 'media'): 'tt_like_media_path',
        ('tiktok', 'share', 'audio'): 'tt_share_audio_path',
        ('tiktok', 'share', 'media'): 'tt_share_media_path',
        ('youtube', 'member', 'audio'): 'yt_member_audio_path',
        ('youtube', 'member', 'media'): 'yt_member_media_path',
        ('youtube', 'sub', 'audio'): 'yt_sub_audio_path',
        ('youtube', 'sub', 'media'): 'yt_sub_media_path',
        ('youtube', 'like', 'audio'): 'yt_like_audio_path',
        ('youtube', 'like', 'media'): 'yt_like_media_path',
        ('twitch', 'sub', 'audio'): 'tw_sub_audio_path',
        ('twitch', 'sub', 'media'): 'tw_sub_media_path',
        ('twitch', 'follow', 'audio'): 'tw_follow_audio_path',
        ('twitch', 'follow', 'media'): 'tw_follow_media_path',
        ('twitch', 'raid', 'audio'): 'tw_raid_audio_path',
        ('twitch', 'raid', 'media'): 'tw_raid_media_path',
        ('twitch', 'bits', 'audio'): 'tw_bits_audio_path',
        ('twitch', 'bits', 'media'): 'tw_bits_media_path',
        ('twitch', 'points', 'audio'): 'tw_points_audio_path',
        ('twitch', 'points', 'media'): 'tw_points_media_path',
        ('twitch', 'hype', 'audio'): 'tw_hype_audio_path',
        ('twitch', 'hype', 'media'): 'tw_hype_media_path',
        ('kick', 'follow', 'audio'): 'kk_follow_audio_path',
        ('kick', 'follow', 'media'): 'kk_follow_media_path',
        ('kick', 'sub', 'audio'): 'kk_sub_audio_path',
        ('kick', 'sub', 'media'): 'kk_sub_media_path',
    }
    config_key = mapping.get(((platform or '').strip().lower(), (event_type or '').strip().lower(), (asset_kind or '').strip().lower()))
    if not config_key:
        return ''
    return (config.get(config_key, '') or '').strip()


def get_alert_voice_id(platform, event_type):
    mapping = {
        ('tiktok', 'follow'): 'tt_follow_voice_id',
        ('tiktok', 'gift'): 'tt_gift_voice_id',
        ('tiktok', 'like'): 'tt_like_voice_id',
        ('tiktok', 'share'): 'tt_share_voice_id',
        ('tiktok', 'follower_join'): 'tt_follower_join_voice_id',
        ('youtube', 'member'): 'yt_member_voice_id',
        ('youtube', 'sub'): 'yt_sub_voice_id',
        ('youtube', 'like'): 'yt_like_voice_id',
        ('twitch', 'sub'): 'tw_sub_voice_id',
        ('twitch', 'follow'): 'tw_follow_voice_id',
        ('twitch', 'raid'): 'tw_raid_voice_id',
        ('twitch', 'bits'): 'tw_bits_voice_id',
        ('twitch', 'points'): 'tw_points_voice_id',
        ('twitch', 'hype'): 'tw_hype_voice_id',
        ('kick', 'follow'): 'kk_follow_voice_id',
        ('kick', 'sub'): 'kk_sub_voice_id',
    }
    key = mapping.get(((platform or '').strip().lower(), (event_type or '').strip().lower()))
    return (config.get(key, '') or '').strip() if key else ''


def get_alert_show_in_chat(platform, event_type):
    mapping = {
        ('tiktok', 'follow'): 'tt_show_follows_in_chat',
        ('tiktok', 'gift'): 'tt_show_gifts_in_chat',
        ('tiktok', 'like'): 'tt_show_likes_in_chat',
        ('tiktok', 'share'): 'tt_show_shares_in_chat',
        ('tiktok', 'follower_join'): 'tt_show_follower_join_in_chat',
        ('youtube', 'member'): 'yt_show_members_in_chat',
        ('youtube', 'sub'): 'yt_show_subs_in_chat',
        ('youtube', 'like'): 'yt_show_likes_in_chat',
        ('twitch', 'sub'): 'tw_show_subs_in_chat',
        ('twitch', 'follow'): 'tw_show_follows_in_chat',
        ('twitch', 'raid'): 'tw_show_raids_in_chat',
        ('twitch', 'bits'): 'tw_show_bits_in_chat',
        ('twitch', 'points'): 'tw_show_points_in_chat',
        ('twitch', 'hype'): 'tw_show_hype_in_chat',
        ('kick', 'follow'): 'kk_show_follows_in_chat',
        ('kick', 'sub'): 'kk_show_subs_in_chat',
    }
    key = mapping.get(((platform or '').strip().lower(), (event_type or '').strip().lower()))
    return bool(config.get(key, True)) if key else True


def get_alert_title(platform, event_type):
    titles = {
        ('tiktok', 'follow'): 'Нова підписка TikTok',
        ('tiktok', 'gift'): 'Подарунок TikTok',
        ('tiktok', 'like'): 'Лайки TikTok',
        ('tiktok', 'share'): 'Репост TikTok',
        ('tiktok', 'follower_join'): 'Підписник зайшов на ефір',
        ('youtube', 'member'): 'Новий учасник YouTube',
        ('youtube', 'sub'): 'Новий підписник YouTube',
        ('youtube', 'like'): 'Лайки YouTube',
        ('twitch', 'sub'): 'Підписка Twitch',
        ('twitch', 'follow'): 'Новий фоловер Twitch',
        ('twitch', 'raid'): 'Рейд Twitch',
        ('twitch', 'bits'): 'Біти Twitch',
        ('twitch', 'points'): 'Бали каналу Twitch',
        ('twitch', 'hype'): 'Hype Train Twitch',
        ('kick', 'follow'): 'Новий фоловер Kick',
        ('kick', 'sub'): 'Підписка Kick',
    }
    return titles.get(((platform or '').strip().lower(), (event_type or '').strip().lower()), 'Подія стриму')


def get_tiktok_widget_asset_path(kind):
    kind = (kind or '').strip().lower()
    if not kind or '_' not in kind:
        return ''
    event_type, asset_kind = kind.rsplit('_', 1)
    return get_alert_widget_asset_path('tiktok', event_type, asset_kind)


def build_alert_widget_asset_url(platform, event_type, asset_kind):
    file_path = get_alert_widget_asset_path(platform, event_type, asset_kind)
    if not file_path:
        return ''
    cache_marker = int(time.time())
    try:
        if os.path.exists(file_path):
            cache_marker = int(os.path.getmtime(file_path))
    except Exception:
        pass
    return 'http://127.0.0.1:{}/event_alert_asset?platform={}&event={}&asset={}&v={}'.format(
        PORT,
        urllib.parse.quote((platform or '').strip().lower()),
        urllib.parse.quote((event_type or '').strip().lower()),
        urllib.parse.quote((asset_kind or '').strip().lower()),
        cache_marker
    )


def build_tiktok_widget_asset_url(kind):
    kind = (kind or '').strip().lower()
    if not kind or '_' not in kind:
        return ''
    event_type, asset_kind = kind.rsplit('_', 1)
    return build_alert_widget_asset_url('tiktok', event_type, asset_kind)


VIDEO_ALERT_EXTENSIONS = ('.mp4', '.webm', '.mov', '.m4v', '.mkv', '.avi', '.ogv')
IMAGE_ALERT_EXTENSIONS = ('.png', '.jpg', '.jpeg', '.gif', '.webp', '.bmp', '.apng', '.avif')


def detect_tiktok_media_kind(file_path):
    ext = os.path.splitext((file_path or '').lower())[1]
    if ext in VIDEO_ALERT_EXTENSIONS:
        return 'video'
    if ext in IMAGE_ALERT_EXTENSIONS:
        return 'image'
    return ''


def get_widget_priority_value(priority_key):
    key = (priority_key or 'alert').strip().lower()
    return int(PRIORITY_MAP.get(key, PRIORITY_MAP.get('alert', 70)))


def get_configured_alert_priority(platform, event_type, priority_key='alert'):
    mapping = {
        ('twitch', 'sub'): 'tw_sub_priority',
        ('twitch', 'follow'): 'tw_follow_priority',
        ('twitch', 'raid'): 'tw_raid_priority',
        ('twitch', 'bits'): 'tw_bits_priority',
        ('twitch', 'points'): 'tw_points_priority',
        ('twitch', 'hype'): 'tw_hype_priority',
    }
    config_key = mapping.get(((platform or '').strip().lower(), (event_type or '').strip().lower()))
    if config_key:
        try:
            return int(config.get(config_key, get_widget_priority_value(priority_key)))
        except Exception:
            pass
    return get_widget_priority_value(priority_key)


def cleanup_platform_widget_events(now=None):
    global tiktok_widget_events, platform_widget_event_queues, platform_widget_event_stats
    now_ms = int((time.time() if now is None else now) * 1000)
    ttl_ms = int(WIDGET_EVENT_TTL_SECONDS * 1000)
    fresh_events = []
    valid_ids = set()
    for item in tiktok_widget_events:
        if now_ms - int(item.get('timestamp', 0) or 0) <= ttl_ms:
            fresh_events.append(item)
            valid_ids.add(int(item.get('id', 0) or 0))
    if len(fresh_events) > WIDGET_EVENT_MAX:
        fresh_events = fresh_events[-WIDGET_EVENT_MAX:]
        valid_ids = {int(item.get('id', 0) or 0) for item in fresh_events}
    tiktok_widget_events = fresh_events

    new_queues = {}
    new_stats = {}
    for queue_key, items in (platform_widget_event_queues or {}).items():
        filtered = [item for item in items if int(item.get('id', 0) or 0) in valid_ids]
        if filtered:
            filtered = filtered[-WIDGET_QUEUE_MAX_PER_TYPE:]
            new_queues[queue_key] = filtered
            new_stats[queue_key] = len(filtered)
    platform_widget_event_queues = new_queues
    platform_widget_event_stats = new_stats


def get_platform_widget_events(after_id=0, limit=100):
    try:
        after_id = int(after_id or 0)
    except Exception:
        after_id = 0
    try:
        limit = max(1, min(int(limit or 100), WIDGET_EVENT_MAX))
    except Exception:
        limit = 100
    with buffer_lock:
        cleanup_platform_widget_events()
        pending = [dict(item) for item in tiktok_widget_events if int(item.get('id', 0) or 0) > after_id]
    pending.sort(key=lambda item: (
        -int(item.get('priority', 0) or 0),
        int(item.get('timestamp', 0) or 0),
        int(item.get('id', 0) or 0)
    ))
    return pending[:limit]


def queue_platform_widget_event(platform, event_type, user='', text='', priority_key='alert', subtitle='', priority_value=None, avatar_url='', show_user=True):
    global tiktok_widget_events, tiktok_widget_event_counter, platform_widget_event_queues, platform_widget_event_stats
    platform = (platform or '').strip().lower()
    event_type = (event_type or '').strip().lower()
    if not platform or not event_type:
        return False
    media_path = get_alert_widget_asset_path(platform, event_type, 'media')
    audio_path = get_alert_widget_asset_path(platform, event_type, 'audio')
    has_media = bool(media_path)
    has_audio = bool(audio_path)
    queue_key = '{}:{}'.format(platform, event_type)
    event = {
        'id': 0,
        'platform': platform,
        'event_type': event_type,
        'queue_key': queue_key,
        'title': get_alert_title(platform, event_type),
        'subtitle': subtitle or get_alert_title(platform, event_type),
        'user': user or platform.title(),
        'show_user': bool(show_user),
        'avatar_url': (avatar_url or '').strip(),
        'text': text or '',
        'media_url': build_alert_widget_asset_url(platform, event_type, 'media') if has_media else '',
        'media_kind': detect_tiktok_media_kind(media_path) if has_media else '',
        'audio_url': build_alert_widget_asset_url(platform, event_type, 'audio') if has_audio else '',
        'timestamp': int(time.time() * 1000),
        'image_duration': int(config.get('overlay_msg_timeout', 10) or 8),
        'priority_key': (priority_key or 'alert').strip().lower(),
        'priority': int(priority_value if priority_value is not None else get_widget_priority_value(priority_key)),
        'queue_index': 0,
        'queue_size_at_insert': 0,
    }
    with buffer_lock:
        cleanup_platform_widget_events()
        tiktok_widget_event_counter += 1
        event['id'] = tiktok_widget_event_counter
        queue_items = list(platform_widget_event_queues.get(queue_key, []))
        queue_items.append(event)
        if len(queue_items) > WIDGET_QUEUE_MAX_PER_TYPE:
            queue_items = queue_items[-WIDGET_QUEUE_MAX_PER_TYPE:]
        platform_widget_event_queues[queue_key] = queue_items
        event['queue_index'] = len(queue_items)
        event['queue_size_at_insert'] = len(queue_items)
        platform_widget_event_stats[queue_key] = len(queue_items)
        tiktok_widget_events.append(event)
        if len(tiktok_widget_events) > WIDGET_EVENT_MAX:
            tiktok_widget_events = tiktok_widget_events[-WIDGET_EVENT_MAX:]
    print('[Alert Widget] queued {}:{} | pr={}({}) | queue={} | idx={} | media={} | audio={}'.format(
        platform,
        event_type,
        event.get('priority_key', 'alert'),
        event.get('priority', 0),
        queue_key,
        event.get('queue_index', 0),
        int(has_media),
        int(has_audio)
    ))
    return True


def queue_tiktok_widget_event(event_type, user='', text=''):
    return queue_platform_widget_event('tiktok', event_type, user, text, priority_key=event_type)


def emit_platform_alert(platform, event_type, user, text, subtitle, priority_key, username='', source_display_name='', voice_id='', force_chat=True, stream_variant='', avatar_url='', show_user=True):
    platform = (platform or '').strip().lower()
    event_type = (event_type or '').strip().lower()
    show_in_chat = True if force_chat else get_alert_show_in_chat(platform, event_type)
    voice_id = (voice_id or get_alert_voice_id(platform, event_type) or '').strip()
    alert_priority = get_configured_alert_priority(platform, event_type, priority_key)
    message_id = add_to_buffer(
        platform,
        user,
        text,
        text,
        is_alert=True,
        subtitle=subtitle,
        priority=alert_priority,
        show_in_chat=show_in_chat,
        username=username,
        source_display_name=source_display_name or user,
        tts_engine_override='',
        tts_voice_id_override=voice_id,
        skip_signature_dedupe=True,
        stream_variant=stream_variant
    )
    widget_ok = queue_platform_widget_event(platform, event_type, user, text, priority_key=priority_key, subtitle=subtitle, priority_value=alert_priority, avatar_url=avatar_url, show_user=show_user)
    print('[Dispatch] {}:{} | user={} | buffer_id={} | chat={} | widget={} | priority={}'.format(platform, event_type, username or user, message_id or 0, int(bool(message_id)), int(bool(widget_ok)), alert_priority))
    return bool(message_id), bool(widget_ok)


def emit_tiktok_alert(event_type, user, text, subtitle, priority_key, username='', source_display_name='', voice_id='', force_chat=True, avatar_url='', show_user=True):
    return emit_platform_alert('tiktok', event_type, user, text, subtitle, priority_key, username=username, source_display_name=source_display_name, voice_id=voice_id, force_chat=force_chat, avatar_url=avatar_url, show_user=show_user)


def serve_local_asset(handler, file_path):
    if not file_path or not os.path.exists(file_path) or not os.path.isfile(file_path):
        handler.send_response(404)
        handler.end_headers()
        return
    content_type = mimetypes.guess_type(file_path)[0] or ''
    if not content_type:
        ext = os.path.splitext((file_path or '').lower())[1]
        content_type = {
            '.mp4': 'video/mp4', '.m4v': 'video/mp4', '.webm': 'video/webm',
            '.mov': 'video/quicktime', '.mkv': 'video/x-matroska', '.ogv': 'video/ogg',
            '.avi': 'video/x-msvideo', '.apng': 'image/apng', '.avif': 'image/avif',
            '.webp': 'image/webp', '.gif': 'image/gif',
        }.get(ext, 'application/octet-stream')
    with open(file_path, 'rb') as fh:
        data = fh.read()
    handler.send_response(200)
    handler.send_header('Content-type', content_type)
    handler.send_header('Content-Length', str(len(data)))
    handler.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
    handler.end_headers()
    handler.wfile.write(data)


def generate_tiktok_alert_widget_html():
    return """<!DOCTYPE html>
<html lang='uk'>
<head>
<meta charset='UTF-8'>
<meta name='viewport' content='width=device-width, initial-scale=1.0'>
<style>
html,body{margin:0;padding:0;background:transparent;overflow:hidden;width:100%;height:100%;font-family:'Segoe UI',system-ui,sans-serif}
#stage{position:relative;width:100vw;height:100vh;display:flex;align-items:center;justify-content:center;background:transparent;overflow:hidden}
.card{position:relative;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:12px;max-width:88vw;max-height:88vh;padding:18px 22px;border-radius:18px;background:rgba(0,0,0,.28);backdrop-filter:blur(8px);box-shadow:0 10px 40px rgba(0,0,0,.35);animation:popIn .25s ease}
.pill{font-size:13px;font-weight:800;letter-spacing:.08em;text-transform:uppercase;color:#fff;background:rgba(255,255,255,.14);padding:6px 10px;border-radius:999px;text-align:center}
.media-box{max-width:80vw;max-height:60vh;display:flex;align-items:center;justify-content:center}
.media-box img,.media-box video{max-width:80vw;max-height:60vh;border-radius:16px;display:block;object-fit:contain;background:transparent}
.title{font-size:30px;font-weight:800;color:#fff;text-shadow:0 2px 10px rgba(0,0,0,.6);text-align:center}
.subtitle{font-size:22px;font-weight:700;color:#ffd166;text-align:center;text-shadow:0 2px 10px rgba(0,0,0,.6)}
.text{font-size:18px;color:#fff;text-align:center;max-width:72vw;word-break:break-word;text-shadow:0 2px 10px rgba(0,0,0,.6)}
.meta{font-size:13px;color:rgba(255,255,255,.72);text-align:center}
.avatar{width:120px;height:120px;border-radius:50%;object-fit:cover;background:rgba(255,255,255,.12);box-shadow:0 6px 22px rgba(0,0,0,.45);border:3px solid rgba(255,255,255,.55)}
@keyframes popIn{from{opacity:0;transform:scale(.92)}to{opacity:1;transform:scale(1)}}
</style>
</head>
<body>
<div id='stage'></div>
<script>
let maxId=0,queue=[],active=false,seenIds=new Set();
function isVideo(kind){return kind==='video'}
function priorityValue(ev){return Number(ev && ev.priority || 0)}
function clearStage(){document.getElementById('stage').innerHTML=''}
function queueSort(a,b){const pr=priorityValue(b)-priorityValue(a);if(pr)return pr;const ta=Number(a&&a.timestamp||0)-Number(b&&b.timestamp||0);if(ta)return ta;return Number(a&&a.id||0)-Number(b&&b.id||0)}
function enqueueEvent(ev){if(!ev||!ev.id||seenIds.has(ev.id))return;seenIds.add(ev.id);queue.push(ev);queue.sort(queueSort)}
function renderEvent(ev){const stage=document.getElementById('stage');clearStage();const card=document.createElement('div');card.className='card';const pill=document.createElement('div');pill.className='pill';pill.textContent=((ev.platform||'stream').toUpperCase())+' • '+String(ev.priority_key||'alert').toUpperCase();const mediaBox=document.createElement('div');mediaBox.className='media-box';if(ev.media_url){if(isVideo(ev.media_kind)){const video=document.createElement('video');video.src=ev.media_url;video.autoplay=true;video.playsInline=true;video.preload='auto';video.loop=false;video.controls=false;/* якщо для події не заданий окремий звуковий файл — беремо звук із самого відео */video.muted=!!ev.audio_url;video.volume=1.0;video.setAttribute('disablepictureinpicture','');mediaBox.appendChild(video)}else{const img=document.createElement('img');img.src=ev.media_url;mediaBox.appendChild(img)}}const title=document.createElement('div');title.className='title';title.textContent=ev.title||'Подія';const avatarEl=(ev.avatar_url?(function(){const a=document.createElement('img');a.className='avatar';a.src=ev.avatar_url;a.onerror=function(){this.remove();};return a;})():null);const subtitle=document.createElement('div');subtitle.className='subtitle';subtitle.textContent=ev.user||'';const text=document.createElement('div');text.className='text';text.textContent=ev.text||'';const meta=document.createElement('div');meta.className='meta';meta.textContent='Черга: '+String(ev.queue_key||'event')+' #'+String(ev.queue_index||1);card.appendChild(pill);if(avatarEl)card.appendChild(avatarEl);if(mediaBox.children.length)card.appendChild(mediaBox);card.appendChild(title);if(ev.user&&ev.show_user!==false)card.appendChild(subtitle);if(ev.text)card.appendChild(text);card.appendChild(meta);stage.appendChild(card);return{media:mediaBox.firstChild||null}}
function duckBegin(){fetch('/api/audio_ducking',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'begin'})}).catch(()=>{});}
function duckEnd(){fetch('/api/audio_ducking',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'end'})}).catch(()=>{});}
function playNext(){if(active||queue.length===0)return;active=true;duckBegin();const ev=queue.shift();const rendered=renderEvent(ev);let audio=null,done=false,timer=null;function finish(){if(done)return;done=true;duckEnd();if(timer)clearTimeout(timer);if(audio){try{audio.pause()}catch(e){}}clearStage();active=false;setTimeout(playNext,120)}if(ev.audio_url){audio=new Audio(ev.audio_url);audio.volume=1.0;audio.play().catch(()=>{})}if(rendered.media&&rendered.media.tagName==='VIDEO'){const vid=rendered.media;vid.onended=finish;vid.onerror=()=>{timer=setTimeout(finish,Math.max(3000,(ev.image_duration||8)*1000))};const p=vid.play();if(p&&p.catch)p.catch(()=>{vid.muted=true;vid.play().catch(()=>{})});vid.onloadedmetadata=()=>{const dur=Number(vid.duration);if(isFinite(dur)&&dur>0){if(timer)clearTimeout(timer);timer=setTimeout(finish,Math.min(120000,dur*1000+700))}};timer=setTimeout(finish,20000)}else{timer=setTimeout(finish,Math.max(3000,(ev.image_duration||8)*1000))}}
async function poll(){try{const r=await fetch('/event_alerts/events?after_id='+encodeURIComponent(String(maxId))+'&ts='+Date.now(),{cache:'no-store'});const list=await r.json();for(const ev of list){maxId=Math.max(maxId,Number(ev.id)||0);enqueueEvent(ev)}if(!active)playNext()}catch(e){}setTimeout(poll,500)}
poll();
</script>
</body>
</html>"""

def flush_tiktok_gift_aggregation(gift_key):
    global tiktok_gift_tracker, processed_gift_ids
    user = " "
    gift_name = " "
    count = 0
    username = ""
    source_display_name = ""
    voice_id = ""
    dedupe_id = ""
    diamond_count = 0
    avatar_url = ""
    with buffer_lock:
        tracker = tiktok_gift_tracker.pop(gift_key, None)
        if not tracker:
            return False
        timer = tracker.get("timer")
        if timer:
            try:
                timer.cancel()
            except Exception:
                pass
        count = int(tracker.get("count", 0) or 0)
        user = tracker.get("user", " ")
        gift_name = tracker.get("gift_name", " ")
        username = tracker.get("username", "")
        source_display_name = tracker.get("source_display_name", user)
        voice_id = (tracker.get("voice_id", "") or "").strip()
        dedupe_id = tracker.get("dedupe_id", gift_key) or gift_key
        diamond_count = int(tracker.get("diamond_count", 0) or 0)
        avatar_url = tracker.get("avatar_url", "") or ""
        if count <= 0:
            return False
        if not dedup_is_new('tiktok', dedupe_id, 'gift-flush'):
            return False
    text = format_tiktok_text(config.get("tt_gift_template", "{user} відправив подарунок {gift} x{count}"), user=user, gift=gift_name, count=count)
    print(f"[TikTok Gift] {user}: {gift_name} x{count}")
    record_tiktok_viewer(username, user, avatar_url, 'gift', gift_diamonds=diamond_count * count, gift_name=gift_name, gift_count=count)
    emit_tiktok_alert("gift", user, text, "Подарунок TikTok", "gift", username=username, source_display_name=source_display_name, voice_id=voice_id, force_chat=True)
    return True


def strip_names_from_text(text, *names):
    """Видаляє з тексту нік/логін користувача, щоб автомодерація перевіряла ЛИШЕ текст повідомлення."""
    cleaned = str(text or "")
    if not cleaned:
        return ""
    seen = set()
    for name in names:
        candidate = (name or "")
        try:
            candidate = str(candidate).strip().strip('@').strip()
        except Exception:
            continue
        if len(candidate) < 2 or candidate.lower() in seen:
            continue
        seen.add(candidate.lower())
        try:
            cleaned = re.sub(re.escape(candidate), " ", cleaned, flags=re.IGNORECASE)
        except Exception:
            cleaned = cleaned.replace(candidate, " ")
    return cleaned


def find_blacklisted_word(text):
    """Повертає перше слово з чорного списку, знайдене в тексті (або None)."""
    if not blacklist_words or not text:
        return None
    lowered = str(text).lower()
    for word in blacklist_words:
        if word and word in lowered:
            return word
    return None


def censor_blacklisted_words(text):
    """Замінює всі слова з чорного списку на [цензура]."""
    if not blacklist_words or not text:
        return text
    result = str(text)
    for word in sorted(blacklist_words, key=len, reverse=True):
        if not word:
            continue
        try:
            result = re.sub(re.escape(word), ' [цензура] ', result, flags=re.IGNORECASE)
        except Exception:
            result = result.replace(word, ' [цензура] ')
    return result


def find_banned_word_in_text(text):
    words_str = (config.get("auto_mute_words", "") or "").strip()
    if not words_str or not text:
        return None
    text_lower = str(text).lower()
    for word in words_str.split(','):
        word = word.strip().lower()
        if word and word in text_lower:
            return word
    return None


def announce_auto_mute(platform, clean_name):
    template = (config.get("auto_mute_announce_template", "") or "").strip()
    if not template:
        return
    platform_labels = {'twitch': 'Twitch', 'youtube': 'YouTube', 'tiktok': 'TikTok', 'kick': 'Kick'}
    platform_label = platform_labels.get((platform or '').strip().lower(), platform or '')
    tts_text = template.replace("{user}", clean_name or "").replace("{platform}", platform_label)
    try:
        add_to_buffer("bot", "Модерація", tts_text, tts_text, is_alert=True, subtitle="🔇 Автозаглушення", show_in_chat=True)
    except Exception as e:
        print("[Модерація] Помилка сповіщення про автозаглушення: {}".format(e))


def process_filters_and_tts(platform, username, display_name, text, is_mod, is_broadcaster, is_subscriber=False):
    global config, user_cooldowns, blocked_users, no_tts_users

    username = (username or "").strip()
    display_name = (display_name or username or "Глядач").strip()

    if username.lower() in blocked_users or display_name.lower() in blocked_users:
        return None, None

    clean_name = resolve_display_name(platform, username, display_name)

    if config.get("auto_mute_enabled", False):
        # ВАЖЛИВО: перевіряємо ЛИШЕ текст повідомлення. Нік, логін і псевдонім
        # вирізаються з тексту, щоб заборонене слово в імені не заглушувало користувача.
        moderation_text = strip_names_from_text(text, username, display_name, clean_name)
        banned_word = find_banned_word_in_text(moderation_text) if moderation_text.strip() else None
        if banned_word:
            mute_key = normalize_moderation_name(username) or normalize_moderation_name(display_name)
            if not mute_key:
                print("[Модерація] Автозаглушення скасовано: не вдалося визначити імʼя користувача")
            else:
                was_already_muted = mute_key in no_tts_users or normalize_moderation_name(display_name) in no_tts_users
                disable_tts_for_user(mute_key)
                print("[Модерація] Автозаглушення {} ({}) - заборонене слово '{}' у тексті повідомлення".format(clean_name, platform, banned_word))
                if not was_already_muted:
                    announce_auto_mute(platform, clean_name)
                return clean_name, " "

    # Чорний список слів. Це НЕ список користувачів: перевіряється лише текст
    # повідомлення (нік вирізається), а дія обирається в налаштуваннях.
    blacklist_action = (config.get("blacklist_action", "censor") or "censor").strip().lower()
    blacklist_hit = None
    if blacklist_words and blacklist_action != 'off':
        bl_text = strip_names_from_text(text, username, display_name, clean_name)
        blacklist_hit = find_blacklisted_word(bl_text) if str(bl_text).strip() else None
    if blacklist_hit and blacklist_action == 'mute':
        mute_key = normalize_moderation_name(username) or normalize_moderation_name(display_name)
        if mute_key:
            was_already_muted = mute_key in no_tts_users or normalize_moderation_name(display_name) in no_tts_users
            disable_tts_for_user(mute_key)
            print("[Модерація] Чорний список: заглушено {} ({}) за слово '{}'".format(clean_name, platform, blacklist_hit))
            if not was_already_muted:
                announce_auto_mute(platform, clean_name)
            return clean_name, " "

    try:
        record_user_activity(platform, username, clean_name)
    except Exception as e:
        print("[Активність] Помилка запису: {}".format(e))

    if username.lower() in no_tts_users or display_name.lower() in no_tts_users:
        return clean_name, " "

    if not config["tts_enabled"]:
        return clean_name, " "

    if config.get("tts_sub_only", False):
        if not (is_broadcaster or is_mod or is_subscriber):
            return clean_name, " "

    current_time = time.time()
    if config["tts_cooldown"] > 0 and not (is_broadcaster or is_mod):
        last_speech = user_cooldowns.get(username.lower(), 0)
        if current_time - last_speech < config["tts_cooldown"]:
            return clean_name, " "
        user_cooldowns[username.lower()] = current_time

    clean_text = " " if text is None else str(text)

    if blacklist_hit and blacklist_action == 'skip':
        print("[Модерація] Чорний список: повідомлення {} не озвучено (слово '{}')".format(clean_name, blacklist_hit))
        return clean_name, " "
    if blacklist_words and blacklist_action == 'censor':
        clean_text = censor_blacklisted_words(clean_text)

    if config["hide_links"]:
        clean_text = re.sub(r'https?://[^\s]+|www.[^\s]+', '[посилання]', clean_text)
    else:
        clean_text = re.sub(r'https?://[^\s]+|www.[^\s]+', 'посилання', clean_text)

    if config["anti_caps"] and len(clean_text) > 4:
        letters = [c for c in clean_text if c.isalpha()]
        if letters and (sum(1 for c in letters if c.isupper()) / len(letters)) > 0.65:
            clean_text = clean_text.lower()

    if config["flood_control"]:
        clean_text = re.sub(r'([^\W\d_])\1{2,}', r'\1\1', clean_text, flags=re.UNICODE)
        clean_text = re.sub(r'(ха|ах){3,}', 'ахах', clean_text, flags=re.IGNORECASE)
        clean_text = re.sub(r'!{2,}', '!', clean_text)
        clean_text = re.sub(r'\?{2,}', '?', clean_text)
        clean_text = re.sub(r'\.{3,}', '...', clean_text)

    if config["hide_emojis"]:
        emoji_pattern = re.compile("[\U0001F600-\U0001F64F\U0001F300-\U0001F5FF\U0001F680-\U0001F6FF\U0001F1E0-\U0001F1FF\U00002702-\U000027B0\U000024C2-\U0001F251]+", flags=re.UNICODE)
        clean_text = emoji_pattern.sub(r'', clean_text)
    elif config["replace_emoji"]:
        emoji_map = {
            "\u2764\ufe0f": "сердечко", "\u2764": "сердечко", "\U0001f602": "смайлик", "\U0001f923": "сміється",
            "\U0001f44d": "клас", "\U0001f525": "вогонь", "\U0001f4a9": "какашка", "\U0001f60d": "закоханий",
            "\U0001f62d": "плаче", "\U0001f60a": "усмішка", "\U0001f60e": "круто", "\U0001f44f": "оплески",
            "\U0001f389": "свято", "\U0001f4af": "сто", "\U0001f4a5": "вибух", "\U0001f4a2": "злість",
            "\U0001f4a4": "сон", "\U0001f4a7": "крапля", "\U0001f31f": "зірка", "\U00002b50": "зірка",
            "\U0001f440": "очі", "\U0001f64f": "молитва", "\U0001f4aa": "сила", "\U0001f3c6": "трофей",
            "\U0001f3b5": "музика", "\U0001f3b6": "ноти", "\U0001f48e": "діамант", "\U0001f4b0": "гроші",
            "\U0001f4b8": "гроші летять", "\U0001f3af": "ціль", "\U0001f680": "ракета", "\U0001f4a1": "ідея",
            "\U0001f4a3": "бомба", "\U000026a1": "блискавка", "\U0001f494": "зламане серце", "\U0001f49c": "фіолетове серце",
            "\U0001f49a": "зелене серце", "\U0001f499": "синє серце", "\U0001f9e1": "помаранчеве серце", "\U0001f90d": "біле серце",
            "\U0001f90e": "коричневе серце", "\U0001fa76": "блакитне серце", "\U0001fa75": "рожеве серце", "\U0001f609": "підморгування",
            "\U0001f618": "поцілунок", "\U0001f61c": "язик", "\U0001f92a": "божевільний", "\U0001f929": "зоряні очі",
            "\U0001f973": "вечірка", "\U0001f970": "закоханий", "\U0001f607": "ангел", "\U0001f608": "біс",
            "\U0001f921": "клоун", "\U0001f47b": "привид", "\U0001f47d": "прибулець", "\U0001f916": "робот",
            "\U0001f383": "гарбуз", "\U0001f384": "ялинка", "\U0001f385": "санта", "\U0001f381": "подарунок",
            "\U0001f382": "торт", "\U0001f370": "десерт", "\U0001f355": "піца", "\U0001f354": "бургер",
            "\U0001f35f": "картопля", "\U0001f32d": "хот-дог", "\U0001f32e": "тако", "\U0001f32f": "буріто",
            "\U0001f959": "печиво", "\U0001f37a": "пиво", "\U0001f37b": "кружки", "\U0001f377": "вино",
            "\U0001f378": "коктейль", "\U0001f379": "тропічний", "\U0001f37e": "шампанське", "\U0001f942": "тост",
            "\U0001f373": "яєчня", "\U0001f95e": "млинці", "\U0001f9c7": "сир", "\U0001f953": "бекон",
            "\U0001f95a": "яйце", "\U0001f956": "багет", "\U0001f950": "круасан", "\U0001f968": "крендель",
            "\U0001f96f": "млинці", "\U0001f9c0": "сир", "\U0001f356": "м'ясо", "\U0001f357": "курка",
            "\U0001f969": "ребра", "\U0001f33d": "кукурудза", "\U0001f955": "морква", "\U0001f954": "картопля",
            "\U0001f96c": "капуста", "\U0001f966": "броколі", "\U0001f9c4": "часник", "\U0001f9c5": "цибуля",
            "\U0001f95c": "арахіс", "\U0001f330": "каштан", "\U0001f35e": "хліб"
        }
        for emo, rep in emoji_map.items():
            if emo:
                clean_text = clean_text.replace(emo, " {} ".format(rep))

    if config["filter_badwords"]:
        bad_patterns = [r'(х[уу́хxх][ййяеиюоовв])', r'(п[ии́иееё][3зздд][аа́аеоиуя])', r'([еёе][бб][аа́аеионуу])', r'(б[ллдд][яя́аио])']
        for p in bad_patterns:
            clean_text = re.sub(p, ' [цензура]', clean_text, flags=re.IGNORECASE)

    clean_text = normalize_tts_text(clean_text)

    # Раніше тут різалось до 120 символів ("і так далі") - через це TTS
    # завжди озвучував лише половину довгих повідомлень. Тепер читаємо
    # повідомлення повністю (Google TTS сам розбивається на частини у
    # synthesize_google_tts_bytes), лишаємо лише запобіжник від
    # надзвичайно довгого спаму/копіпасти.
    if len(clean_text) > TTS_MAX_MESSAGE_LENGTH:
        clean_text = clean_text[:TTS_MAX_MESSAGE_LENGTH].rstrip() + " і так далі"

    _tr_target = get_tts_translate_target()
    if _tr_target and clean_text.strip():
        _tr_source_text = clean_text
        try:
            clean_text = translate_text_to(clean_text, _tr_target)
        except Exception as _tr_err:
            print("[Translator] ПОМИЛКА перекладу ({}), лишаємо оригінал: {}".format(_tr_target, _tr_err))
        else:
            if not _looks_like_target(clean_text, _tr_target):
                print("[Translator] Переклад не вдався (мова джерела не розпізнана), "
                      "повідомлення пропущено в TTS: {}...".format(_tr_source_text[:30]))
                return clean_name, " "

    return clean_name, clean_text.strip()


def add_to_buffer(platform, display_name, text, tts_text, is_mod=False, is_broadcaster=False, is_alert=False, subtitle="", priority=None, is_announce=False, show_in_chat=True, username="", source_display_name="", tts_engine_override="", tts_voice_id_override="", skip_signature_dedupe=False, platform_user_id="", platform_message_id="", stream_variant=""):
    global message_counter, messages_buffer, recent_signatures, blocked_users, config

    if platform in config["filter_platforms"] and not config["filter_platforms"][platform]:
        return False
    if display_name.lower() in blocked_users:
        return False

    current_time = time.time()
    if not is_alert and is_repeated_message_spam(display_name, text, current_time):
        return False

    with buffer_lock:
        if not skip_signature_dedupe:
            recent_signatures = [s for s in recent_signatures if current_time - s["time"] < 4.0]
            if any(s["platform"] == platform and s["name"] == display_name and s["text"] == text for s in recent_signatures):
                return False
            recent_signatures.append({"platform": platform, "name": display_name, "text": text, "time": current_time})

        message_counter += 1
        tts_display_name = clean_nickname_for_tts(display_name) if not is_alert else display_name
        msg_priority = get_message_priority(platform, is_alert, priority)
        effective_username = username or source_display_name or display_name
        effective_display_name = source_display_name or display_name
        if tts_engine_override or tts_voice_id_override:
            msg_tts_engine = normalize_tts_engine(
                (tts_engine_override or config.get("tts_engine") or "google").strip())
            if msg_tts_engine == "elevenlabs":
                # для ElevenLabs потрібен саме ID голосу, а не мовний код типу uk-UA
                msg_tts_voice_id = resolve_elevenlabs_voice_id(tts_voice_id_override)
            else:
                msg_tts_voice_id = (tts_voice_id_override or config.get("tts_voice") or "uk-UA").strip()
        else:
            msg_tts_engine, msg_tts_voice_id = resolve_user_tts_profile(platform, effective_username, effective_display_name)

        msg_obj = {
            "id": message_counter, "platform": platform, "displayName": display_name, "ttsDisplayName": tts_display_name,
            "sourceDisplayName": effective_display_name, "username": effective_username,
            "text": text, "ttsText": tts_text, "isMod": is_mod, "isBroadcaster": is_broadcaster,
            "isAlert": is_alert, "isAnnounce": bool(is_announce), "subtitle": subtitle, "timestamp": int(current_time * 1000),
            "priority": msg_priority, "showInChat": show_in_chat,
            "ttsEngine": msg_tts_engine, "ttsVoiceId": msg_tts_voice_id,
            "platformUserId": platform_user_id or "", "platformMessageId": platform_message_id or "",
            "streamVariant": stream_variant or ""
        }
        messages_buffer.append(msg_obj)
        if len(messages_buffer) > 100:
            messages_buffer.pop(0)
        publish_unified_event(
            platform,
            UnifiedEventType.CHAT_MESSAGE.value if not is_alert else "alert",
            username=effective_username,
            message=text,
            metadata={
                "displayName": display_name,
                "ttsText": tts_text,
                "isMod": bool(is_mod),
                "isBroadcaster": bool(is_broadcaster),
                "isAlert": bool(is_alert),
                "subtitle": subtitle,
                "priority": msg_priority,
                "showInChat": bool(show_in_chat),
                "bufferId": msg_obj["id"],
            },
        )
        return msg_obj["id"]


INVALID_MODERATION_NAMES = {"", "-", "--", "—", "–", "?", "??", "null", "none", "undefined", "глядач", "user", "anonymous"}


def normalize_moderation_name(username):
    """Приводить імʼя до нижнього регістру і відсіює порожні / службові значення."""
    name = (username or "")
    try:
        name = str(name)
    except Exception:
        return ""
    name = name.strip().strip('@').strip()
    if not name:
        return ""
    lowered = name.lower()
    if lowered in INVALID_MODERATION_NAMES:
        return ""
    return lowered


def block_user(username):
    global blocked_users
    username_lower = normalize_moderation_name(username)
    if not username_lower:
        print("[Модерація] Пропущено блокування: порожнє імʼя користувача")
        return False
    if username_lower not in blocked_users:
        blocked_users.add(username_lower)
        save_moderation_data()
        print(f"[Модерація] Користувач {username_lower} заблокований")
    return True


def unblock_user(username):
    global blocked_users
    username_lower = normalize_moderation_name(username)
    if username_lower and username_lower in blocked_users:
        blocked_users.discard(username_lower)
        save_moderation_data()
        print(f"[Модерація] Користувач {username_lower} розблокований")
        return True
    return False


def disable_tts_for_user(username):
    global no_tts_users
    username_lower = normalize_moderation_name(username)
    if not username_lower:
        print("[Модерація] Пропущено вимкнення TTS: порожнє імʼя користувача")
        return False
    if username_lower not in no_tts_users:
        no_tts_users.add(username_lower)
        save_moderation_data()
        print(f"[Модерація] TTS вимкнено для {username_lower}")
    return True


def enable_tts_for_user(username):
    global no_tts_users
    username_lower = normalize_moderation_name(username)
    if username_lower and username_lower in no_tts_users:
        no_tts_users.discard(username_lower)
        save_moderation_data()
        print(f"[Модерація] TTS увімкнено для {username_lower}")
        return True
    return False


def unblock_all_users():
    """Знімає блокування чату з усіх користувачів одразу. Повертає кількість знятих блокувань."""
    global blocked_users
    removed = len(blocked_users)
    if removed:
        blocked_users = set()
        save_moderation_data()
    print(f"[Модерація] Розблоковано всіх користувачів: {removed}")
    return removed


def enable_tts_all_users():
    """Повертає TTS усім заглушеним користувачам одразу. Повертає кількість знятих заглушень."""
    global no_tts_users
    removed = len(no_tts_users)
    if removed:
        no_tts_users = set()
        save_moderation_data()
    print(f"[Модерація] TTS увімкнено для всіх користувачів: {removed}")
    return removed


def sanitize_moderation_sets():
    """Прибирає порожні / службові записи, які могли потрапити у списки раніше."""
    global blocked_users, no_tts_users
    clean_blocked = set(n for n in (normalize_moderation_name(x) for x in list(blocked_users)) if n)
    clean_no_tts = set(n for n in (normalize_moderation_name(x) for x in list(no_tts_users)) if n)
    changed = (clean_blocked != blocked_users) or (clean_no_tts != no_tts_users)
    if changed:
        dropped = (len(blocked_users) - len(clean_blocked)) + (len(no_tts_users) - len(clean_no_tts))
        blocked_users = clean_blocked
        no_tts_users = clean_no_tts
        save_moderation_data()
        print(f"[Модерація] Очищено некоректних записів у списках: {dropped}")
    return changed


def clear_all_messages():
    global messages_buffer, repeated_message_tracker, tiktok_like_tracker, tiktok_gift_tracker, tiktok_widget_events, tiktok_widget_event_counter, platform_widget_event_queues, platform_widget_event_stats
    with buffer_lock:
        messages_buffer.clear()
        repeated_message_tracker.clear()
        tiktok_like_tracker.clear()
        for tracker in tiktok_gift_tracker.values():
            timer = tracker.get("timer")
            if timer:
                try:
                    timer.cancel()
                except:
                    pass
        tiktok_gift_tracker.clear()
        tiktok_widget_events.clear()
        tiktok_widget_event_counter = 0
        platform_widget_event_queues.clear()
        platform_widget_event_stats.clear()


def log_status(platform, message):
    try:
        print(f"[MultiChat] [{platform}] {message}")
    except:
        pass


# ============================================================================
# ПОТОКИ (Twitch, YouTube, Kick, TikTok, Bot)
# ============================================================================
TWITCH_CHANNEL_URL_HOSTS = ('twitch.tv', 'www.twitch.tv', 'm.twitch.tv', 'go.twitch.tv')


def twitch_normalize_channel_login(value):
    """
    Приводить будь-який варіант введення каналу до чистого IRC/Helix login.

    ЧОМУ ЦЕ ПОТРІБНО: у логах було видно `#https://www.twitch.tv/covert227`
    - користувач вставив посилання на канал, а код очікував чистий login.
    IRC отримував `JOIN #https://www.twitch.tv/covert227` (канал не існує),
    а Helix `users?login=https%3A%2F%2F...` повертав порожній масив ->
    broadcaster_user_id був порожній -> EventSub відповідав
    `HTTP 400 Bad Identifiers`.

    Приймає: covert227, #covert227, @covert227, Covert227,
    twitch.tv/covert227, https://www.twitch.tv/covert227?tt_content=x,
    https://www.twitch.tv/covert227/videos, ' covert227 '.
    Повертає '' якщо login не вдалось витягти.
    """
    raw = (value or '')
    if not isinstance(raw, str):
        raw = str(raw)
    raw = raw.strip().strip('\​').strip()
    if not raw:
        return ''
    # прибираємо провідні '#' та '@' (у будь-якій кількості та порядку)
    raw = raw.lstrip('#@ \t')
    if not raw:
        return ''
    low = raw.lower()
    if low.startswith(('http://', 'https://', '//')) or low.startswith(TWITCH_CHANNEL_URL_HOSTS):
        candidate = raw if '//' in raw else '//' + raw
        try:
            parsed = urllib.parse.urlparse(candidate if candidate.startswith(('http://', 'https://')) else 'https:' + candidate)
            host = (parsed.hostname or '').lower()
            path = parsed.path or ''
        except Exception:
            host, path = '', ''
        if host in TWITCH_CHANNEL_URL_HOSTS or host.endswith('.twitch.tv') or host == 'twitch.tv':
            raw = path
        elif not host:
            raw = path
    # лишаємо лише перший сегмент шляху, без query/fragment
    raw = raw.split('?', 1)[0].split('#', 1)[0]
    raw = raw.strip('/')
    if '/' in raw:
        raw = raw.split('/', 1)[0]
    raw = raw.strip().lstrip('@').strip()
    login = ''.join(ch for ch in raw if ch.isalnum() or ch == '_')
    return login.lower()


def twitch_effective_channel_login():
    """Єдина точка правди про канал Twitch для IRC, Helix та EventSub."""
    login = twitch_normalize_channel_login(config.get('twitch_channel', ''))
    if not login:
        login = twitch_normalize_channel_login(config.get('twitch_irc_login', ''))
    return login


def twitch_unescape_tag_value(value):
    value = value or ''
    return value.replace('\\s', ' ').replace('\\:', ';').replace('\\r', '\\r').replace('\\n', '\\n').replace('\\\\', '\\')


def parse_twitch_irc_tags(raw_tags):
    tags = {}
    for chunk in (raw_tags or '').split(';'):
        if '=' in chunk:
            k, v = chunk.split('=', 1)
            tags[k] = twitch_unescape_tag_value(v)
    return tags


def parse_twitch_irc_line(raw_line):
    line = raw_line or ''
    tags = {}
    prefix = ''
    trailing = ''
    if line.startswith('@') and ' ' in line:
        raw_tags, line = line[1:].split(' ', 1)
        tags = parse_twitch_irc_tags(raw_tags)
    if line.startswith(':') and ' ' in line:
        prefix, line = line[1:].split(' ', 1)
    if ' :' in line:
        middle, trailing = line.split(' :', 1)
    else:
        middle = line
    parts = middle.split()
    command = parts[0] if parts else ''
    params = parts[1:] if len(parts) > 1 else []
    return tags, prefix, command, params, trailing


def build_twitch_subscription_text(msg_id, user, recipient='', months='', count=''):
    user = user or 'Twitch'
    recipient = recipient or ''
    months = str(months or '').strip()
    count = str(count or '').strip()
    if msg_id == 'sub':
        return '{} оформив підписку на Twitch'.format(user)
    if msg_id == 'resub':
        return '{} продовжив підписку на Twitch{}'.format(user, ' на {} міс.'.format(months) if months else '')
    if msg_id == 'subgift':
        return '{} подарував підписку Twitch {}'.format(user, recipient or 'глядачу').strip()
    if msg_id == 'submysterygift':
        return '{} подарував {} підписок Twitch спільноті'.format(user, count or 'кілька')
    return '{} оформив підписку на Twitch'.format(user)


def build_twitch_follow_text(user):
    return '{} почав відстежувати Twitch-канал'.format(user or 'Twitch')


def build_twitch_raid_text(user, viewers=''):
    user = user or 'Twitch'
    viewers = str(viewers or '').strip()
    suffix = ' з {} глядачами'.format(viewers) if viewers else ''
    return '{} зарейдив канал{}'.format(user, suffix)


def build_twitch_bits_text(user, bits='', message='', bits_type=''):
    user = user or 'Anonymous'
    bits = str(bits or '').strip()
    bits_type = (bits_type or '').strip().lower()
    base = '{} підтримав канал на {} біт'.format(user, bits or '?')
    if bits and bits != '1':
        base += 'ів'
    if bits_type and bits_type not in ('cheer', 'bits'):
        base += ' ({})'.format(bits_type)
    if message:
        base += ': {}'.format(message)
    return base


def build_twitch_points_text(user, reward_title='', reward_cost='', user_input=''):
    user = user or 'Twitch Viewer'
    reward_title = reward_title or 'Нагорода Twitch'
    reward_cost = str(reward_cost or '').strip()
    text = "{} активував нагороду '{}'".format(user, reward_title)
    if reward_cost:
        text += ' за {} балів'.format(reward_cost)
    if user_input:
        text += ' | {}'.format(user_input)
    return text


def build_twitch_hype_text(stage, level='', total='', progress='', goal=''):
    stage = (stage or '').strip().lower()
    level = str(level or '').strip()
    total = str(total or '').strip()
    progress = str(progress or '').strip()
    goal = str(goal or '').strip()
    if stage == 'begin':
        text = 'На каналі стартував Hype Train'
    elif stage == 'end':
        text = 'Hype Train завершився'
    else:
        text = 'Hype Train просувається'
    if level:
        text += ' | рівень {}'.format(level)
    if total:
        text += ' | очки {}'.format(total)
    if progress and goal:
        text += ' | прогрес {}/{}'.format(progress, goal)
    return text


def twitch_required_eventsub_scopes():
    scopes = []
    if config.get('tw_enable_follows', True):
        scopes.append('moderator:read:followers')
    if config.get('tw_enable_bits', True):
        scopes.append('bits:read')
    if config.get('tw_enable_points', True):
        scopes.append('channel:read:redemptions')
    if config.get('tw_enable_hype', True):
        scopes.append('channel:read:hype_train')
    # Модерація з адмін-панелі (таймаут/бан/видалення повідомлень) -
    # завжди запитуємо, це базова функціональність, а не опційний алерт.
    scopes.append('moderator:manage:banned_users')
    scopes.append('moderator:manage:chat_messages')
    # Відповідь у чат (reply_parent_message_id через Send Chat Message API) -
    # базова функціональність поряд з таймаутом/баном/видаленням.
    scopes.append('user:write:chat')
    return list(dict.fromkeys(scopes or TWITCH_EVENTSUB_SCOPES))


def twitch_build_authorize_url(client_id, redirect_uri=TWITCH_DEFAULT_REDIRECT_URI, scopes=None):
    global twitch_oauth_state_cache
    client_id = (client_id or '').strip()
    redirect_uri = (redirect_uri or TWITCH_DEFAULT_REDIRECT_URI).strip()
    scopes = scopes or twitch_required_eventsub_scopes()
    if not client_id:
        return ''
    state = base64.urlsafe_b64encode(os.urandom(18)).decode('utf-8').rstrip('=')
    twitch_oauth_state_cache = {'state': state, 'ts': time.time()}
    params = {
        'response_type': 'code',
        'client_id': client_id,
        'redirect_uri': redirect_uri,
        'scope': ' '.join(scopes),
        'state': state,
        'force_verify': 'true',
    }
    return 'https://id.twitch.tv/oauth2/authorize?' + urllib.parse.urlencode(params)


def twitch_exchange_authorization_code(client_id, client_secret, code, redirect_uri=TWITCH_DEFAULT_REDIRECT_URI, timeout=15):
    global twitch_user_oauth_cache
    client_id = (client_id or '').strip()
    client_secret = (client_secret or '').strip()
    code = (code or '').strip()
    redirect_uri = (redirect_uri or TWITCH_DEFAULT_REDIRECT_URI).strip()
    if not client_id or not client_secret or not code:
        return None
    data = urllib.parse.urlencode({
        'client_id': client_id,
        'client_secret': client_secret,
        'code': code,
        'grant_type': 'authorization_code',
        'redirect_uri': redirect_uri,
    }).encode('utf-8')
    headers = {
        'User-Agent': 'Mozilla/5.0',
        'Content-Type': 'application/x-www-form-urlencoded',
        'Accept': 'application/json',
    }
    try:
        req = urllib.request.Request('https://id.twitch.tv/oauth2/token', data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            payload = json.loads(response.read().decode('utf-8'))
        access_token = (payload.get('access_token') or '').strip()
        refresh_token = (payload.get('refresh_token') or '').strip()
        expires_in = int(payload.get('expires_in', 0) or 0)
        scope = payload.get('scope') or []
        if access_token:
            twitch_user_oauth_cache = {
                'access_token': access_token,
                'refresh_token': refresh_token,
                'expires_at': time.time() + max(60, expires_in or 0),
                'scope': scope,
            }
            oauth_manager.set_token("twitch", payload, client_id=client_id)
            return payload
    except Exception as e:
        print('[Twitch Auth] code exchange failed: {}'.format(e))
    return None


def twitch_refresh_user_token(timeout=15):
    """Оновлює user-токен Twitch через refresh_token.

    Twitch видає access_token приблизно на 4 години, а refresh_token живе
    доти, доки користувач не відкличе доступ. Без цієї функції токен
    «здихав» між сесіями OBS і скрипт вимагав повторної авторизації.
    """
    global twitch_user_oauth_cache
    refresh_token = (twitch_user_oauth_cache.get('refresh_token') or '').strip()
    client_id = (config.get('twitch_client_id', '') or '').strip()
    client_secret = (config.get('twitch_client_secret', '') or '').strip()
    if not refresh_token:
        return None
    if not client_id or not client_secret:
        print('[Twitch OAuth] Немає Client ID / Client Secret — оновити токен неможливо, потрібна повторна авторизація.')
        return None
    data = urllib.parse.urlencode({
        'grant_type': 'refresh_token',
        'refresh_token': refresh_token,
        'client_id': client_id,
        'client_secret': client_secret,
    }).encode('utf-8')
    headers = {
        'User-Agent': 'Mozilla/5.0',
        'Content-Type': 'application/x-www-form-urlencoded',
        'Accept': 'application/json',
    }
    try:
        req = urllib.request.Request('https://id.twitch.tv/oauth2/token', data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            payload = json.loads(response.read().decode('utf-8'))
        access_token = (payload.get('access_token') or '').strip()
        new_refresh_token = (payload.get('refresh_token') or refresh_token).strip()
        expires_in = int(payload.get('expires_in', 0) or 0)
        if access_token:
            twitch_user_oauth_cache = {
                'access_token': access_token,
                'refresh_token': new_refresh_token,
                'expires_at': time.time() + max(60, expires_in or 14400),
                'scope': payload.get('scope') or twitch_user_oauth_cache.get('scope', []),
            }
            payload.setdefault('refresh_token', new_refresh_token)
            oauth_manager.set_token("twitch", payload, client_id=client_id)
            config['twitch_irc_oauth'] = 'oauth:' + access_token
            print('[Twitch OAuth] Токен успішно оновлено через refresh_token (дійсний ще ~{} хв).'.format(
                int(max(60, expires_in or 14400) / 60)))
            return access_token
    except urllib.error.HTTPError as e:
        try:
            error_body = e.read().decode('utf-8', errors='ignore')
        except Exception:
            error_body = ''
        print('[Twitch OAuth] Не вдалося оновити токен: HTTP {} {}. {}'.format(e.code, e.reason, error_body[:300]))
        if e.code in (400, 401):
            print('[Twitch OAuth] refresh_token більше не діє — потрібна повторна авторизація через /auth/twitch/start')
    except Exception as e:
        print('[Twitch OAuth] Не вдалося оновити токен: {}'.format(e))
    return None


def oauth_refresh_on_startup():
    """Фоново оновлює токени Twitch/Kick одразу після завантаження скрипта.

    Виконується в окремому потоці, щоб мережеві запити не підвішували
    інтерфейс OBS під час старту.
    """
    try:
        twitch_expires = float(twitch_user_oauth_cache.get('expires_at', 0) or 0)
        if (twitch_user_oauth_cache.get('refresh_token') or '').strip() and time.time() > twitch_expires - 600:
            print('[Twitch OAuth] Токен прострочений або майже прострочений — оновлюю автоматично...')
            twitch_refresh_user_token()
    except Exception as e:
        print('[Twitch OAuth] Автооновлення впало: {}'.format(e))
    try:
        kick_expires = float(kick_user_oauth_cache.get('expires_at', 0) or 0)
        if (kick_user_oauth_cache.get('refresh_token') or '').strip() and time.time() > kick_expires - 600:
            print('[Kick OAuth] Токен прострочений або майже прострочений — оновлюю автоматично...')
            kick_refresh_user_token()
    except Exception as e:
        print('[Kick OAuth] Автооновлення впало: {}'.format(e))


def twitch_user_access_token():
    token = (config.get('twitch_irc_oauth', '') or '').strip()
    if token.lower().startswith('oauth:'):
        token = token[6:]
    token = token.strip()
    if token:
        return token
    cached_token = (twitch_user_oauth_cache.get('access_token') or '').strip()
    if cached_token and time.time() < float(twitch_user_oauth_cache.get('expires_at', 0) or 0) - 60:
        return cached_token
    return cached_token


def twitch_validate_user_token(token):
    global twitch_token_validation_cache
    token = (token or '').strip()
    if not token:
        return None
    now = time.time()
    if twitch_token_validation_cache.get('token') == token and now - float(twitch_token_validation_cache.get('ts', 0) or 0) < 300:
        return twitch_token_validation_cache.get('payload')
    headers = {'User-Agent': 'Mozilla/5.0', 'Authorization': 'OAuth {}'.format(token)}
    try:
        req = urllib.request.Request('https://id.twitch.tv/oauth2/validate', headers=headers)
        with urllib.request.urlopen(req, timeout=15) as response:
            payload = json.loads(response.read().decode('utf-8'))
        twitch_token_validation_cache = {'token': token, 'payload': payload, 'ts': now}
        return payload
    except Exception as e:
        print('[Twitch Auth] validate failed: {}'.format(e))
        return None


def twitch_effective_client_id(token=''):
    configured_client_id = (config.get('twitch_client_id', '') or '').strip()
    validation = twitch_validate_user_token(token) if token else None
    validated_client_id = ((validation or {}).get('client_id') or '').strip()
    if validated_client_id and configured_client_id and validated_client_id != configured_client_id:
        print('[Twitch Auth] Client ID mismatch fixed automatically: config={} token={}'.format(configured_client_id, validated_client_id))
        return validated_client_id
    return validated_client_id or configured_client_id


def twitch_helix_request_json(url, method='GET', payload=None, token=''):
    client_id = twitch_effective_client_id(token)
    if not client_id:
        return None
    headers = {'User-Agent': 'Mozilla/5.0', 'Client-Id': client_id}
    if token:
        headers['Authorization'] = 'Bearer {}'.format(token)
    data = None
    if payload is not None:
        headers['Content-Type'] = 'application/json'
        data = json.dumps(payload).encode('utf-8')
    try:
        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        with urllib.request.urlopen(req, timeout=15) as response:
            body = response.read().decode('utf-8', errors='ignore').strip()
            return json.loads(body) if body else {}
    except urllib.error.HTTPError as e:
        try:
            error_body = e.read().decode('utf-8', errors='ignore')
        except Exception:
            error_body = ''
        print('[Twitch EventSub] HTTP {} {} -> {}'.format(e.code, method, error_body[:500]))
    except Exception as e:
        print('[Twitch EventSub] {} {} failed: {}'.format(method, url, e))
    return None


def twitch_get_user_by_login(login, token):
    login = twitch_normalize_channel_login(login)
    if not login:
        return None
    data = twitch_helix_request_json('https://api.twitch.tv/helix/users?login={}'.format(quote(login)), token=token)
    items = (data or {}).get('data') or []
    return items[0] if items else None


def twitch_get_current_user(token):
    data = twitch_helix_request_json('https://api.twitch.tv/helix/users', token=token)
    items = (data or {}).get('data') or []
    return items[0] if items else None


# ---------------------------------------------------------------------------
# СПІЛЬНИЙ КЕШ ІДЕНТИФІКАТОРІВ TWITCH
# ---------------------------------------------------------------------------
# Раніше broadcaster_user_id тягнувся окремо модерацією (з кешем на 600 с) і
# окремо EventSub-воркером (БЕЗ кешу, на кожному реконнекті). Тепер це один
# кеш, прив'язаний до нормалізованого login: зміна каналу в налаштуваннях
# автоматично інвалідує кеш, а повторні реконнекти EventSub не роблять
# жодного зайвого виклику Helix.
TWITCH_ID_CACHE_TTL = 600

_twitch_broadcaster_cache = {'login': '', 'broadcaster_id': '', 'moderator_id': '',
                             'broadcaster_user': None, 'auth_user': None, 'ts': 0.0}
_twitch_id_cache_lock = threading.Lock()


def twitch_id_cache_clear(reason=''):
    global _twitch_broadcaster_cache
    with _twitch_id_cache_lock:
        _twitch_broadcaster_cache = {'login': '', 'broadcaster_id': '', 'moderator_id': '',
                                     'broadcaster_user': None, 'auth_user': None, 'ts': 0.0}
    if reason:
        print('[Twitch] Кеш ID скинуто: {}'.format(reason))


def twitch_id_cache_snapshot():
    with _twitch_id_cache_lock:
        c = dict(_twitch_broadcaster_cache)
    c.pop('broadcaster_user', None)
    c.pop('auth_user', None)
    c['age'] = round(time.time() - (c.get('ts') or 0), 1) if c.get('ts') else None
    c['expected_login'] = twitch_effective_channel_login()
    return c


def twitch_resolve_identity(token, force=False):
    """Повертає (broadcaster_user, auth_user) для нормалізованого login.
    Один Helix-виклик на TTL, спільний для модерації та EventSub."""
    global _twitch_broadcaster_cache
    login = twitch_effective_channel_login()
    if not login:
        log_error('Twitch', 'Канал Twitch не заданий або записаний у форматі, з якого не вдалось '
                            'витягти login (очікується нік, напр. covert227, або посилання '
                            'https://twitch.tv/covert227). Поточне значення: {!r}'.format(
                                config.get('twitch_channel', '')))
        return None, None
    now = time.time()
    with _twitch_id_cache_lock:
        cached = dict(_twitch_broadcaster_cache)
    if (not force and cached.get('login') == login and cached.get('broadcaster_id')
            and now - (cached.get('ts') or 0) < TWITCH_ID_CACHE_TTL):
        return cached.get('broadcaster_user'), cached.get('auth_user')
    broadcaster_user = twitch_get_user_by_login(login, token)
    auth_user = twitch_get_current_user(token) or broadcaster_user
    broadcaster_id = str(pick_first_non_empty((broadcaster_user or {}).get('id'), '') or '').strip()
    if not broadcaster_id:
        log_error('Twitch', 'Helix не знайшов канал login="{}" (порожній users.data). '
                            'Саме через це EventSub раніше отримував HTTP 400 Bad Identifiers.'.format(login))
        return None, auth_user
    moderator_id = str(pick_first_non_empty((auth_user or {}).get('id'), broadcaster_id) or '').strip()
    with _twitch_id_cache_lock:
        _twitch_broadcaster_cache = {'login': login, 'broadcaster_id': broadcaster_id,
                                     'moderator_id': moderator_id,
                                     'broadcaster_user': broadcaster_user,
                                     'auth_user': auth_user, 'ts': time.time()}
    print('[Twitch] ID кеш: login={} broadcaster_user_id={} moderator_user_id={}'.format(
        login, broadcaster_id, moderator_id))
    return broadcaster_user, auth_user


def twitch_resolve_broadcaster_and_moderator(token):
    """(broadcaster_id, moderator_id) для викликів moderation API. moderator_id
    - це ID власника токена, він має бути реальним модератором/власником
    каналу, інакше Twitch поверне 403."""
    broadcaster_user, auth_user = twitch_resolve_identity(token)
    broadcaster_id = str(pick_first_non_empty((broadcaster_user or {}).get('id'), '') or '').strip()
    if not broadcaster_id:
        return '', ''
    moderator_id = str(pick_first_non_empty((auth_user or {}).get('id'), broadcaster_id) or '').strip()
    return broadcaster_id, moderator_id


def twitch_moderation_action(action, **kwargs):
    """Єдина точка входу для дій модерації Twitch: 'timeout' | 'ban' | 'unban' | 'delete'.
    Офіційний Helix API (IRC-команди /ban, /timeout деприкейтені з лютого 2023
    і більше не працюють - див. https://dev.twitch.tv/docs/chat/moderation/).
    Повертає {'ok': bool, 'error': str|None}."""
    token = twitch_user_access_token()
    if not token:
        return {'ok': False, 'error': "Немає дійсного Twitch OAuth токена - авторизуйтесь у налаштуваннях"}
    broadcaster_id, moderator_id = twitch_resolve_broadcaster_and_moderator(token)
    if not broadcaster_id or not moderator_id:
        return {'ok': False, 'error': 'Не вдалося визначити broadcaster/moderator ID Twitch'}

    if action in ('timeout', 'ban'):
        user_id = (kwargs.get('user_id') or '').strip()
        if not user_id:
            return {'ok': False, 'error': "Немає Twitch user_id для цього повідомлення (оновіть сторінку чату, якщо повідомлення прийшло до оновлення скрипта)"}
        body = {'data': {'user_id': user_id, 'reason': (kwargs.get('reason') or '')[:500]}}
        if action == 'timeout':
            duration = int(kwargs.get('duration_seconds') or 600)
            body['data']['duration'] = max(1, min(duration, 1209600))  # Twitch max = 14 днів
        url = 'https://api.twitch.tv/helix/moderation/bans?broadcaster_id={}&moderator_id={}'.format(broadcaster_id, moderator_id)
        result = twitch_helix_request_json(url, method='POST', payload=body, token=token)
        return {'ok': result is not None, 'error': None if result is not None else 'Twitch відхилив запит (деталі в консолі скрипта)'}

    if action == 'unban':
        user_id = (kwargs.get('user_id') or '').strip()
        if not user_id:
            return {'ok': False, 'error': 'Немає user_id'}
        url = 'https://api.twitch.tv/helix/moderation/bans?broadcaster_id={}&moderator_id={}&user_id={}'.format(broadcaster_id, moderator_id, user_id)
        result = twitch_helix_request_json(url, method='DELETE', token=token)
        return {'ok': result is not None, 'error': None if result is not None else 'Twitch відхилив запит (деталі в консолі скрипта)'}

    if action == 'delete':
        message_id = (kwargs.get('message_id') or '').strip()
        if not message_id:
            return {'ok': False, 'error': "Немає Twitch message_id для цього повідомлення (старе повідомлення, або минуло 6 годин - Twitch більше не дозволяє видалення)"}
        url = 'https://api.twitch.tv/helix/moderation/chat?broadcaster_id={}&moderator_id={}&message_id={}'.format(broadcaster_id, moderator_id, message_id)
        result = twitch_helix_request_json(url, method='DELETE', token=token)
        return {'ok': result is not None, 'error': None if result is not None else 'Twitch відхилив запит (деталі в консолі скрипта)'}

    if action == 'reply':
        text = (kwargs.get('text') or '').strip()
        message_id = (kwargs.get('message_id') or '').strip()
        if not text:
            return {'ok': False, 'error': 'Немає тексту відповіді'}
        if not message_id:
            return {'ok': False, 'error': "Немає Twitch message_id для відповіді (повідомлення прийшло до оновлення скрипта)"}
        body = {'broadcaster_id': broadcaster_id, 'sender_id': moderator_id, 'message': text[:500], 'reply_parent_message_id': message_id}
        url = 'https://api.twitch.tv/helix/chat/messages'
        result = twitch_helix_request_json(url, method='POST', payload=body, token=token)
        return {'ok': result is not None, 'error': None if result is not None else 'Twitch відхилив запит на відповідь (потрібен новий OAuth токен зі скоупом user:write:chat - переавторизуйтесь у налаштуваннях)'}

    return {'ok': False, 'error': 'Невідома дія модерації'}


def twitch_open_websocket(url):
    parsed = urlparse(url)
    host = parsed.hostname or 'eventsub.wss.twitch.tv'
    port = parsed.port or (443 if parsed.scheme == 'wss' else 80)
    path = parsed.path or '/ws'
    if parsed.query:
        path += '?' + parsed.query
    raw_sock = socket.create_connection((host, port), timeout=10)
    sock = raw_sock
    if parsed.scheme == 'wss':
        context = ssl.create_default_context()
        sock = context.wrap_socket(raw_sock, server_hostname=host)
    sock.settimeout(35.0)
    ws_key = base64.b64encode(os.urandom(16)).decode('utf-8')
    handshake = 'GET {} HTTP/1.1\r\nHost: {}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Key: {}\r\nUser-Agent: MultiChat-Ultimate\r\n\r\n'.format(path, host, ws_key)
    sock.sendall(handshake.encode('utf-8'))
    response = b''
    while b'\r\n\r\n' not in response:
        chunk = sock.recv(4096)
        if not chunk:
            raise ConnectionError('Немає відповіді від Twitch EventSub WebSocket')
        response += chunk
    header_bytes, recv_buffer = response.split(b'\r\n\r\n', 1)
    status_line = header_bytes.decode('utf-8', 'ignore').splitlines()[0] if header_bytes else ''
    if '101' not in status_line:
        raise ConnectionError('WebSocket handshake failed: {}'.format(status_line or 'unknown'))
    return sock, recv_buffer


def twitch_valid_user_id(value):
    """Twitch user_id - завжди рядок з цифр. Будь-що інше означає, що ми
    підставили сміття (наприклад, залишок URL) і отримаємо 400 Bad
    Identifiers."""
    v = str(value or '').strip()
    return v if (v and v.isdigit()) else ''


def twitch_build_eventsub_topics(broadcaster_user_id, moderator_user_id):
    broadcaster_user_id = twitch_valid_user_id(broadcaster_user_id)
    moderator_user_id = twitch_valid_user_id(moderator_user_id) or broadcaster_user_id
    if not broadcaster_user_id:
        log_error('Twitch EventSub', 'Порожній/некоректний broadcaster_user_id - підписки не створюються '
                                     '(це і був HTTP 400 Bad Identifiers).')
        return []
    topics = []
    if config.get('tw_enable_follows', True):
        topics.append({'type': 'channel.follow', 'version': '2', 'condition': {'broadcaster_user_id': broadcaster_user_id, 'moderator_user_id': moderator_user_id or broadcaster_user_id}})
    if config.get('tw_enable_raids', True):
        topics.append({'type': 'channel.raid', 'version': '1', 'condition': {'to_broadcaster_user_id': broadcaster_user_id}})
    if config.get('tw_enable_bits', True):
        topics.append({'type': 'channel.bits.use', 'version': '1', 'condition': {'broadcaster_user_id': broadcaster_user_id}})
    if config.get('tw_enable_points', True):
        topics.append({'type': 'channel.channel_points_custom_reward_redemption.add', 'version': '1', 'condition': {'broadcaster_user_id': broadcaster_user_id}})
        topics.append({'type': 'channel.channel_points_automatic_reward_redemption.add', 'version': '2', 'condition': {'broadcaster_user_id': broadcaster_user_id}})
    if config.get('tw_enable_hype', True):
        topics.append({'type': 'channel.hype_train.begin', 'version': '2', 'condition': {'broadcaster_user_id': broadcaster_user_id}})
        topics.append({'type': 'channel.hype_train.progress', 'version': '2', 'condition': {'broadcaster_user_id': broadcaster_user_id}})
        topics.append({'type': 'channel.hype_train.end', 'version': '2', 'condition': {'broadcaster_user_id': broadcaster_user_id}})
    return topics


def twitch_register_eventsub_topics(ws_session_id, token, broadcaster_user, auth_user):
    broadcaster_user_id = twitch_valid_user_id(pick_first_non_empty((broadcaster_user or {}).get('id'), ''))
    moderator_user_id = twitch_valid_user_id(pick_first_non_empty((auth_user or {}).get('id'), '')) or broadcaster_user_id
    if not broadcaster_user_id or not ws_session_id:
        log_error('Twitch EventSub', 'Підписки не створено: broadcaster_user_id="{}" ws_session_id="{}"'.format(
            broadcaster_user_id, 'OK' if ws_session_id else ''))
        return False
    ok = False
    failed = []
    for topic in twitch_build_eventsub_topics(broadcaster_user_id, moderator_user_id):
        payload = {
            'type': topic['type'],
            'version': topic['version'],
            'condition': topic['condition'],
            'transport': {'method': 'websocket', 'session_id': ws_session_id}
        }
        response = twitch_helix_request_json('https://api.twitch.tv/helix/eventsub/subscriptions', method='POST', payload=payload, token=token)
        if response is not None:
            ok = True
            print('[Twitch EventSub] subscribed: {}'.format(topic['type']))
        else:
            failed.append(topic['type'])
            print('[Twitch EventSub] FAILED {} condition={}'.format(topic['type'], json.dumps(topic['condition'])))
    if failed:
        log_error('Twitch EventSub', 'Не підписалось {} топіків: {}. Перевір scopes токена '
                                     '(broadcaster_user_id={} / moderator_user_id={}).'.format(
                                         len(failed), ', '.join(failed), broadcaster_user_id, moderator_user_id))
    return ok


def twitch_handle_eventsub_notification(subscription_type, event, metadata=None):
    global processed_twitch_event_ids
    metadata = metadata or {}
    message_id = (metadata.get('message_id') or '').strip()
    if message_id:
        if not dedup_is_new('twitch', message_id, 'eventsub'):
            return False

    subscription_type = (subscription_type or '').strip()
    event = event or {}

    if subscription_type == 'channel.follow' and config.get('tw_enable_follows', True):
        user = pick_first_non_empty(event.get('user_name'), event.get('user_login'), 'Twitch')
        username = pick_first_non_empty(event.get('user_login'), user)
        text = build_twitch_follow_text(user)
        print('[Twitch Follow] {}'.format(text))
        emit_platform_alert('twitch', 'follow', user, text, 'Новий фоловер Twitch', 'follow', username=username, source_display_name=user, force_chat=False)
        return True

    if subscription_type == 'channel.raid' and config.get('tw_enable_raids', True):
        user = pick_first_non_empty(event.get('from_broadcaster_user_name'), event.get('from_broadcaster_user_login'), 'Twitch')
        username = pick_first_non_empty(event.get('from_broadcaster_user_login'), user)
        viewers = pick_first_non_empty(event.get('viewers'), '')
        text = build_twitch_raid_text(user, viewers)
        print('[Twitch Raid] {}'.format(text))
        emit_platform_alert('twitch', 'raid', user, text, 'Рейд Twitch', 'raid', username=username, source_display_name=user, force_chat=False)
        return True

    if subscription_type in ('channel.cheer', 'channel.bits.use') and config.get('tw_enable_bits', True):
        is_anonymous = bool(event.get('is_anonymous'))
        user = 'Anonymous' if is_anonymous else pick_first_non_empty(event.get('user_name'), event.get('user_login'), 'Twitch')
        username = '' if is_anonymous else pick_first_non_empty(event.get('user_login'), user)
        bits = pick_first_non_empty(event.get('bits'), event.get('total_bits_used'), '')
        message = (event.get('message') or '').strip()
        bits_type = pick_first_non_empty(event.get('type'), 'cheer' if subscription_type == 'channel.cheer' else 'bits')
        text = build_twitch_bits_text(user, bits, message, bits_type)
        print('[Twitch Bits] {}'.format(text))
        emit_platform_alert('twitch', 'bits', user, text, 'Біти Twitch', 'bits', username=username, source_display_name=user, force_chat=False)
        return True

    if subscription_type in ('channel.channel_points_custom_reward_redemption.add', 'channel.channel_points_automatic_reward_redemption.add') and config.get('tw_enable_points', True):
        reward = event.get('reward') or {}
        user = pick_first_non_empty(event.get('user_name'), event.get('user_login'), 'Twitch Viewer')
        username = pick_first_non_empty(event.get('user_login'), user)
        reward_title = pick_first_non_empty(reward.get('title'), event.get('reward_title'), event.get('title'), event.get('type'), 'Нагорода Twitch')
        reward_cost = pick_first_non_empty(reward.get('cost'), event.get('reward_cost'), event.get('cost'), '')
        user_input = pick_first_non_empty(event.get('user_input'), event.get('message'), '')
        text = build_twitch_points_text(user, reward_title, reward_cost, user_input)
        print('[Twitch Points] {}'.format(text))
        emit_platform_alert('twitch', 'points', user, text, 'Бали каналу Twitch', 'points', username=username, source_display_name=user, force_chat=False)
        return True

    if subscription_type in ('channel.hype_train.begin', 'channel.hype_train.progress', 'channel.hype_train.end') and config.get('tw_enable_hype', True):
        stage = subscription_type.rsplit('.', 1)[-1]
        broadcaster_name = pick_first_non_empty(event.get('broadcaster_user_name'), twitch_effective_channel_login(), 'Twitch')
        broadcaster_login = pick_first_non_empty(event.get('broadcaster_user_login'), twitch_effective_channel_login())
        text = build_twitch_hype_text(stage, event.get('level'), event.get('total'), event.get('progress'), event.get('goal'))
        print('[Twitch Hype] {}'.format(text))
        emit_platform_alert('twitch', 'hype', broadcaster_name, text, 'Hype Train Twitch', 'hype', username=broadcaster_login, source_display_name=broadcaster_name, force_chat=False)
        return True

    return False


def twitch_eventsub_worker(session_id):
    if not twitch_effective_channel_login():
        return
    if not any(config.get(key, True) for key in ('tw_enable_follows', 'tw_enable_raids', 'tw_enable_bits', 'tw_enable_points', 'tw_enable_hype')):
        return

    token = twitch_user_access_token()
    client_id = (config.get('twitch_client_id', '') or '').strip()
    client_secret = (config.get('twitch_client_secret', '') or '').strip()
    if not client_id:
        log_status('Twitch EventSub', 'Пропуск: потрібен Twitch Client ID')
        return
    if not token:
        auth_url = twitch_build_authorize_url(client_id) if client_secret else ''
        if auth_url:
            log_status('Twitch EventSub', 'Потрібна авторизація Twitch. Відкрий у браузері: {}'.format(auth_url))
        else:
            log_status('Twitch EventSub', 'Пропуск: потрібні Twitch Client ID, Client Secret та User OAuth token')
        return

    validation = twitch_validate_user_token(token)
    if not validation:
        auth_url = twitch_build_authorize_url(client_id) if client_secret else ''
        if auth_url:
            log_status('Twitch EventSub', 'OAuth token Twitch не пройшов validate. Повторна авторизація: {}'.format(auth_url))
        else:
            log_status('Twitch EventSub', 'OAuth token Twitch не пройшов validate')
        return
    validated_client_id = ((validation or {}).get('client_id') or '').strip()
    auth_login = ((validation or {}).get('login') or '').strip()
    scopes = (validation or {}).get('scopes') or []
    if validated_client_id and client_id and validated_client_id != client_id:
        auth_url = twitch_build_authorize_url(client_id) if client_secret else ''
        log_status('Twitch EventSub', 'OAuth token належить іншому Twitch Client ID. Натисни кнопку авторизації Twitch або відкрий: {}'.format(auth_url or 'http://localhost:8080/auth/twitch/start'))
        return
    log_status('Twitch EventSub', 'Token OK | login={} | client_id={} | scopes={}'.format(auth_login or 'unknown', validated_client_id or client_id or 'unknown', ','.join(scopes) if scopes else '-'))

    broadcaster_user, auth_user = twitch_resolve_identity(token)
    if not twitch_valid_user_id((broadcaster_user or {}).get('id')):
        log_status('Twitch EventSub', 'Не вдалося отримати broadcaster_user_id для каналу "{}" '
                                      '(перевір нік каналу в налаштуваннях)'.format(twitch_effective_channel_login()))
        return

    base_url = 'wss://eventsub.wss.twitch.tv/ws?keepalive_timeout_seconds=30'
    next_url = base_url
    reconnect_now = False
    reconnect_delay = 5

    while session_is_current(session_id):
        sock = None
        recv_buffer = b''
        current_url = next_url or base_url
        should_register = (current_url == base_url)
        next_url = base_url
        reconnect_now = False
        try:
            sock, recv_buffer = twitch_open_websocket(current_url)
            log_status('Twitch EventSub', 'WebSocket підключено')
            platform_mark_connected('twitch_eventsub')
            while session_is_current(session_id):
                try:
                    opcode, payload, recv_buffer = read_ws_frame(sock, recv_buffer)
                except socket.timeout:
                    continue

                if opcode == 0x9:
                    sock.sendall(build_ws_frame(payload, opcode=0xA))
                    continue
                if opcode == 0x8:
                    raise ConnectionError('Twitch EventSub WebSocket closed by server')
                if opcode != 0x1:
                    continue

                msg = json.loads(payload.decode('utf-8', 'ignore'))
                metadata = msg.get('metadata') or {}
                payload_data = msg.get('payload') or {}
                message_type = (metadata.get('message_type') or '').strip()

                if message_type == 'session_welcome':
                    ws_session_id = (((payload_data.get('session') or {}).get('id')) or '').strip()
                    if ws_session_id and should_register:
                        twitch_register_eventsub_topics(ws_session_id, token, broadcaster_user, auth_user)
                    continue

                if message_type == 'session_keepalive':
                    continue

                if message_type == 'notification':
                    subscription = payload_data.get('subscription') or {}
                    event = payload_data.get('event') or {}
                    twitch_handle_eventsub_notification((subscription.get('type') or '').strip(), event, metadata)
                    continue

                if message_type == 'revocation':
                    subscription = payload_data.get('subscription') or {}
                    print('[Twitch EventSub] revoked: {}'.format(subscription.get('type') or 'unknown'))
                    continue

                if message_type == 'session_reconnect':
                    reconnect_url = (((payload_data.get('session') or {}).get('reconnect_url')) or '').strip()
                    if reconnect_url:
                        next_url = reconnect_url
                        reconnect_now = True
                        log_status('Twitch EventSub', 'Отримано reconnect_url, перепідключення...')
                    break

            reconnect_delay = 0
        except Exception as e:
            print('[Twitch EventSub] error: {}'.format(e))
            reconnect_delay = platform_backoff_delay('twitch_eventsub', 'eventsub_ws: {}'.format(e))
        finally:
            if sock:
                try:
                    sock.close()
                except Exception:
                    pass

        if not session_is_current(session_id):
            break
        if reconnect_now:
            continue
        # Пауза рахується platform_backoff_delay() -> перепідключається ЛИШЕ
        # EventSub, решта платформ навіть не знає про цю помилку.
        time.sleep(reconnect_delay if reconnect_delay else 5)


TWITCH_ANON_NICK_PREFIX = 'justinfan'


def twitch_worker(session_id):
    """
    Read-only Twitch chat (IRC) reader.

    ARCHITECTURE NOTE (important - do not "fix" this back):
    This connection is ALWAYS anonymous and depends ONLY on `twitch_channel`
    (the channel name the user types in). It intentionally never reads
    `twitch_client_id`, `twitch_client_secret` or the Twitch OAuth token -
    those three fields are reserved exclusively for:
      - TwitchAdapter (Live Analytics / viewer count), and
      - twitch_eventsub_worker (alert widget: follows, raids, bits,
        channel points, hype trains).

    Previously this worker also tried to log in to IRC with the same OAuth
    token used for EventSub. If that token was invalid, expired, or was an
    app-only token (not a user token with chat scopes), Twitch would reject
    the IRC login. The socket then kept returning empty reads forever with
    no reconnect, silently killing chat for the rest of the session even
    though the channel name was correctly configured. Anonymous mode has no
    such failure mode: there is nothing to authenticate, so filling in
    Client ID / Client Secret / OAuth token can no longer break chat.

    Subscriptions/resubs/gift-subs are still detected here via IRC
    USERNOTICE, which Twitch sends to anonymous ("justinfan") clients too,
    as long as the `twitch.tv/commands` capability is requested alongside
    `twitch.tv/tags` (this was previously only requested in the now-removed
    authenticated branch, which is why sub alerts used to depend on
    filling in credentials - that is no longer the case).
    """
    global config
    if not twitch_effective_channel_login():
        return

    reconnect_delay = 2
    while session_is_current(session_id):
        sock = None
        try:
            # ЄДИНА нормалізація: приймає і нік, і повне посилання на канал.
            channel = twitch_effective_channel_login()
            if not channel:
                log_error('Twitch', 'IRC: не вдалось витягти login каналу з {!r}'.format(
                    config.get('twitch_channel', '')))
                return

            sock = socket.socket()
            sock.settimeout(2.0)
            sock.connect(("irc.chat.twitch.tv", 6667))
            anon_nick = "{}{}".format(TWITCH_ANON_NICK_PREFIX, secrets.randbelow(80000) + 10000)
            sock.send(b"CAP REQ :twitch.tv/tags twitch.tv/commands\r\n")
            sock.send("NICK {}\r\n".format(anon_nick).encode('utf-8'))
            sock.send("JOIN #{}\r\n".format(channel).encode('utf-8'))
            log_status('Twitch', 'IRC чат підключено анонімно (нік {}) до каналу #{}'.format(anon_nick, channel))
            platform_mark_connected('twitch')

            read_buffer = ""
            consecutive_empty_reads = 0
            while session_is_current(session_id):
                try:
                    raw = sock.recv(4096)
                except socket.timeout:
                    continue
                if not raw:
                    # A closed/dead socket keeps returning b'' forever instead of
                    # raising - without this check chat would silently stop.
                    consecutive_empty_reads += 1
                    if consecutive_empty_reads >= 3:
                        raise ConnectionError('Twitch IRC socket closed by server')
                    continue
                consecutive_empty_reads = 0
                data = raw.decode('utf-8', errors='ignore')
                read_buffer += data
                while "\r\n" in read_buffer:
                    line, read_buffer = read_buffer.split("\r\n", 1)
                    tags, prefix, command, params, trailing = parse_twitch_irc_line(line)
                    if command == 'PING':
                        payload = trailing or (params[0] if params else 'tmi.twitch.tv')
                        sock.send("PONG :{}\r\n".format(payload).encode('utf-8'))
                        continue
                    if command == 'PRIVMSG':
                        user = prefix.split('!', 1)[0] if prefix else ''
                        msg = trailing
                        badges = tags.get('badges', '')
                        is_broadcaster = 'broadcaster' in badges
                        is_mod = 'moderator' in badges
                        is_subscriber = 'subscriber' in badges or 'founder' in badges
                        display_name = tags.get('display-name', user)
                        twitch_user_id = (tags.get('user-id') or '').strip()
                        twitch_msg_id = (tags.get('id') or '').strip()
                        # Дедуп до будь-якої обробки: після реконнекту IRC
                        # сервер може повторно віддати ті самі PRIVMSG.
                        if not dedup_is_new('twitch', twitch_msg_id):
                            continue
                        c_name, tts_text = process_filters_and_tts('twitch', user, display_name, msg, is_mod, is_broadcaster, is_subscriber)
                        if c_name:
                            add_to_buffer('twitch', c_name, msg, tts_text, is_mod, is_broadcaster, username=user, source_display_name=display_name, platform_user_id=twitch_user_id, platform_message_id=twitch_msg_id)
                        continue
                    if command == 'USERNOTICE' and config.get('tw_enable_subs', True):
                        msg_id = (tags.get('msg-id') or '').strip()
                        if msg_id not in ('sub', 'resub', 'subgift', 'submysterygift'):
                            continue
                        user = tags.get('display-name') or tags.get('login') or 'Twitch'
                        username = tags.get('login') or user
                        recipient = tags.get('msg-param-recipient-display-name') or tags.get('msg-param-recipient-user-name') or ''
                        months = tags.get('msg-param-cumulative-months') or tags.get('msg-param-months') or ''
                        count = tags.get('msg-param-mass-gift-count') or tags.get('msg-param-sender-count') or ''
                        text = build_twitch_subscription_text(msg_id, user, recipient, months, count)
                        print('[Twitch Sub] {} | {}'.format(msg_id, text))
                        emit_platform_alert('twitch', 'sub', user, text, 'Підписка Twitch', 'subscription', username=username, source_display_name=user, force_chat=False)
            reconnect_delay = 0
        except Exception as e:
            if session_is_current(session_id):
                log_error('Twitch', 'IRC чат: помилка з\'єднання, перепідключення... ({})'.format(e))
                reconnect_delay = platform_backoff_delay('twitch', 'irc: {}'.format(e))
        finally:
            if sock:
                try:
                    sock.close()
                except Exception:
                    pass

        if not session_is_current(session_id):
            break
        # Перепідключається ЛИШЕ Twitch IRC: без kill_services/run_services,
        # тому дедуп, TTS і решта платформ не зачіпаються.
        time.sleep(reconnect_delay if reconnect_delay else 2)

YOUTUBE_YTCFG_REGEX = r'ytcfg\.set\(\s*({.+?})\s*\);'
YOUTUBE_INITIAL_DATA_REGEX = r'(?:window\s*[\s*["\']ytInitialData["\']\s*]|ytInitialData)\s*=\s*({.+?})\s*;\s*(?:var\s+meta|</script|\n)'
YOUTUBE_CONSENT_COOKIE = 'CONSENT=YES+cb.20210328-17-p0.en+FX+999'

YOUTUBE_QUOTA_RETRY_MIN_SECONDS = 300    # не повторювати частіше, ніж раз на 5 хв
YOUTUBE_QUOTA_RETRY_MAX_SECONDS = 3600   # але перевіряти хоча б раз на годину (раптом квоту підняли вручну)


def youtube_seconds_until_quota_reset():
    """
    Скільки секунд лишилось до опівночі Pacific Time — це реальний момент,
    коли Google скидає денну квоту YouTube Data API v3 (підтверджено
    офіційною документацією: "Daily quotas reset at midnight Pacific
    Time"). Попередня версія коду чекала рівно 3600 секунд після 429,
    що майже завжди НЕ співпадає зі скиданням квоти — тому скрипт зазвичай
    отримував другий 429 одразу після завершення "кулдауну".

    Якщо zoneinfo (Python 3.9+) недоступний, використовується наближення
    UTC-8 без урахування літнього часу (похибка щонайбільше ~1 год, що
    прийнятно — цей результат все одно затиснутий у діапазон
    [YOUTUBE_QUOTA_RETRY_MIN_SECONDS, YOUTUBE_QUOTA_RETRY_MAX_SECONDS]).
    """
    try:
        if ZoneInfo is not None:
            now_pt = datetime.now(ZoneInfo("America/Los_Angeles"))
        else:
            now_pt = datetime.utcnow() - timedelta(hours=8)
        next_midnight_pt = (now_pt + timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
        seconds_left = (next_midnight_pt - now_pt).total_seconds()
    except Exception:
        seconds_left = YOUTUBE_QUOTA_RETRY_MAX_SECONDS
    return max(YOUTUBE_QUOTA_RETRY_MIN_SECONDS, min(seconds_left, YOUTUBE_QUOTA_RETRY_MAX_SECONDS))


# ---------------------------------------------------------------------------
# СТАН КВОТИ / ЛІМІТІВ YOUTUBE API
# ---------------------------------------------------------------------------
# Раніше HTTP 429 трактувався так само, як 403 quotaExceeded: піднімався
# youtube_quota_exceeded і БЛОКУВАЛИСЬ УСІ виклики API до наступної півночі
# за тихоокеанським часом. 429 - це не денна квота, а тимчасовий рейт-ліміт,
# і найдорожчий винуватець - search.list (100 юнітів за виклик). Тепер:
#   * 429 -> блокуємо ЛИШЕ search.list на YOUTUBE_SEARCH_RATE_LIMIT_COOLDOWN
#   * вже відомий video_id беремо з пам'яті -> web-читач працює далі
#   * жодна інша підсистема не перезапускається
YOUTUBE_SEARCH_RATE_LIMIT_COOLDOWN = 300   # скільки не торкатись search.list після 429
YOUTUBE_API_RATE_LIMIT_PAUSE = 60          # коротка пауза для інших ендпоінтів
YOUTUBE_TARGET_MEMORY_TTL = 6 * 3600       # скільки пам'ятаємо знайдений video_id

youtube_search_blocked_until = 0.0
youtube_api_pause_until = 0.0
_youtube_api_key_fingerprint = None

youtube_target_memory_lock = threading.Lock()
youtube_target_memory = {}   # ключ джерела -> {"video_ids": [...], "ts": float}


def youtube_search_is_blocked():
    return time.time() < youtube_search_blocked_until


def youtube_note_rate_limited(kind='api'):
    """Викликається на HTTP 429. Нічого не перезапускає."""
    global youtube_search_blocked_until, youtube_api_pause_until
    now = time.time()
    youtube_search_blocked_until = now + YOUTUBE_SEARCH_RATE_LIMIT_COOLDOWN
    if kind != 'search':
        youtube_api_pause_until = now + YOUTUBE_API_RATE_LIMIT_PAUSE
    log_status('YouTube', '⚠️ HTTP 429 (рейт-ліміт). Зупиняю ТІЛЬКИ пошук трансляцій '
                          '(search.list) на {} с, використовую вже відомий video_id і '
                          'web-читач чату. Інші сервіси НЕ перезапускаються.'.format(
                              int(YOUTUBE_SEARCH_RATE_LIMIT_COOLDOWN)))


def youtube_quota_clear(reason='manual'):
    global youtube_quota_exceeded, youtube_quota_reset_time
    global youtube_search_blocked_until, youtube_api_pause_until
    was = youtube_quota_exceeded or youtube_search_is_blocked()
    youtube_quota_exceeded = False
    youtube_quota_reset_time = 0
    youtube_search_blocked_until = 0.0
    youtube_api_pause_until = 0.0
    if was:
        log_status('YouTube', 'Стан квоти скинуто (причина: {})'.format(reason))
    return was


def youtube_quota_clear_if_key_changed():
    """Скидає стан квоти ЛИШЕ якщо змінився API-ключ.

    Раніше і script_update(), і перезапуск після зміни налаштувань робили
    youtube_quota_exceeded = False беззастережно: OBS сам викликає
    script_update() (оновлення властивостей, збереження колекції сцен), і
    скрипт одразу знову бомбардував search.list, отримував 429/403 і палив
    залишок квоти.
    """
    global _youtube_api_key_fingerprint
    key = (config.get('yt_api_key', '') or '').strip()
    fingerprint = hashlib.sha1(key.encode('utf-8')).hexdigest() if key else ''
    if fingerprint == _youtube_api_key_fingerprint:
        return False
    _youtube_api_key_fingerprint = fingerprint
    return youtube_quota_clear('api_key_changed')


def youtube_quota_state():
    now = time.time()
    return {
        "quota_exceeded": bool(youtube_quota_exceeded),
        "quota_reset_in": max(0, int((youtube_quota_reset_time or 0) - now)),
        "search_blocked": youtube_search_is_blocked(),
        "search_blocked_in": max(0, int(youtube_search_blocked_until - now)),
        "api_paused_in": max(0, int(youtube_api_pause_until - now)),
        "remembered_targets": youtube_target_memory_snapshot(),
    }


def youtube_remember_live_targets(source, video_ids):
    key = str(source or '').strip().lower()
    if not key or not video_ids:
        return
    with youtube_target_memory_lock:
        youtube_target_memory[key] = {"video_ids": list(video_ids), "ts": time.time()}


def youtube_recall_live_targets(source):
    key = str(source or '').strip().lower()
    if not key:
        return []
    with youtube_target_memory_lock:
        entry = youtube_target_memory.get(key)
        if not entry:
            return []
        if time.time() - entry.get("ts", 0) > YOUTUBE_TARGET_MEMORY_TTL:
            return []
        return list(entry.get("video_ids") or [])


def youtube_target_memory_snapshot():
    with youtube_target_memory_lock:
        return {k: list(v.get("video_ids") or []) for k, v in youtube_target_memory.items()}


def youtube_api_get_json(url, timeout=10, kind='api'):
    global youtube_quota_exceeded, youtube_quota_reset_time
    if youtube_quota_exceeded:
        if time.time() < youtube_quota_reset_time:
            return None
        youtube_quota_clear('quota_window_elapsed')
    # 429 блокує лише пошук трансляцій, а не весь API.
    if kind == 'search' and youtube_search_is_blocked():
        return None
    if kind != 'search' and time.time() < youtube_api_pause_until:
        return None
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req, timeout=timeout) as response:
            return json.loads(response.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        error_body = e.read().decode('utf-8', errors='ignore')
        log_status("YouTube", f"HTTP {e.code}: {error_body[:200]}")
        if e.code == 403 and "quota" in error_body.lower():
            log_status("YouTube", "⚠️ Вичерпано денну квоту YouTube API! Перемикаюсь на web-режим YouTube чату.")
            youtube_quota_exceeded = True
            youtube_quota_reset_time = time.time() + youtube_seconds_until_quota_reset()
        elif e.code == 429:
            # НЕ вважаємо це вичерпаною денною квотою і НЕ блокуємо весь API.
            youtube_note_rate_limited(kind)
        elif e.code == 403:
            if "no longer live" in error_body:
                log_status("YouTube", "⚠️ Трансляція завершена або чат недоступний")
            elif "authenticated user cannot" in error_body:
                log_status("YouTube", "⚠️ Помилка 403: Перевірте API ключ")
            else:
                log_status("YouTube", "⚠️ Помилка 403: Можливо, ключ неактивний")
        return None
    except Exception as e:
        log_status("YouTube", f"Помилка API: {e}")
        return None

def youtube_web_get_text(url, timeout=15, extra_headers=None):
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
        'Accept-Language': 'uk-UA,uk;q=0.9,en-US;q=0.8,en;q=0.7',
        'Cookie': YOUTUBE_CONSENT_COOKIE,
        'Origin': 'https://www.youtube.com',
        'Referer': 'https://www.youtube.com/'
    }
    if extra_headers:
        headers.update(extra_headers)
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return response.read().decode('utf-8', errors='ignore')

def youtube_web_post_json(url, payload, timeout=15, extra_headers=None):
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
        'Accept-Language': 'uk-UA,uk;q=0.9,en-US;q=0.8,en;q=0.7',
        'Cookie': YOUTUBE_CONSENT_COOKIE,
        'Origin': 'https://www.youtube.com',
        'Referer': 'https://www.youtube.com/',
        'Content-Type': 'application/json; charset=UTF-8'
    }
    if extra_headers:
        headers.update(extra_headers)
    data = json.dumps(payload).encode('utf-8')
    req = urllib.request.Request(url, data=data, headers=headers, method='POST')
    with urllib.request.urlopen(req, timeout=timeout) as response:
        return json.loads(response.read().decode('utf-8', errors='ignore'))

def youtube_extract_json_blob(html_text, pattern):
    if not html_text: return None
    match = re.search(pattern, html_text, re.DOTALL)
    if not match: return None
    try:
        return json.loads(match.group(1))
    except Exception:
        return None

def youtube_extract_json_blob_any(html_text, patterns):
    for pattern in patterns:
        data = youtube_extract_json_blob(html_text, pattern)
        if data is not None:
            return data
    return None

def youtube_iter_dicts(data):
    if isinstance(data, dict):
        yield data
        for value in data.values():
            for item in youtube_iter_dicts(value):
                yield item
    elif isinstance(data, list):
        for value in data:
            for item in youtube_iter_dicts(value):
                yield item

def youtube_find_reload_continuation(data):
    for node in youtube_iter_dicts(data):
        if not isinstance(node, dict):
            continue
        for key in (
            'reloadContinuationData',
            'timedContinuationData',
            'invalidationContinuationData',
            'liveChatReplayContinuationData'
        ):
            cont_data = node.get(key) or {}
            cont = cont_data.get('continuation')
            if cont:
                return cont
    return None


def youtube_extract_continuation_from_html(html_text):
    text = html_text or ''
    patterns = [
        r'"reloadContinuationData"\s*:\s*\{\s*"continuation"\s*:\s*"([^"]+)"',
        r'"timedContinuationData"\s*:\s*\{\s*"continuation"\s*:\s*"([^"]+)"',
        r'"invalidationContinuationData"\s*:\s*\{\s*"continuation"\s*:\s*"([^"]+)"',
        r'"liveChatReplayContinuationData"\s*:\s*\{\s*"continuation"\s*:\s*"([^"]+)"',
        r'\"reloadContinuationData\"\s*:\s*\{\s*\"continuation\"\s*:\s*\"([^\"]+)\"',
        r'\"timedContinuationData\"\s*:\s*\{\s*\"continuation\"\s*:\s*\"([^\"]+)\"'
    ]
    for pattern in patterns:
        match = re.search(pattern, text)
        if match:
            return match.group(1)
    return None

def youtube_find_next_continuation(data):
    for node in youtube_iter_dicts(data):
        timed = (node.get('timedContinuationData') or {}) if isinstance(node, dict) else {}
        invalidation = (node.get('invalidationContinuationData') or {}) if isinstance(node, dict) else {}
        live_replay = (node.get('liveChatReplayContinuationData') or {}) if isinstance(node, dict) else {}
        for item in (timed, invalidation, live_replay):
            cont = item.get('continuation')
            timeout_ms = item.get('timeoutMs') or 0
            if cont:
                return cont, int(timeout_ms or 0)
    return None, 0

def youtube_extract_video_id_from_html(html_text):
    patterns = [
        r'"videoDetails":{"videoId":"([A-Za-z0-9_-]{11})"',
        r'"canonicalBaseUrl":"/watch\?v=([A-Za-z0-9_-]{11})"',
        r'"urlCanonical":"https://www.youtube.com/watch\?v=([A-Za-z0-9_-]{11})"',
        r'<link rel="canonical" href="https://www.youtube.com/watch\?v=([A-Za-z0-9_-]{11})',
        r'"shortlinkUrl":"https://youtu.be/([A-Za-z0-9_-]{11})"',
        r'https://www.youtube.com/watch\?v=([A-Za-z0-9_-]{11})',
        r'https://www.youtube.com/live/([A-Za-z0-9_-]{11})',
        r'"videoId":"([A-Za-z0-9_-]{11})"'
    ]
    for pattern in patterns:
        match = re.search(pattern, html_text or '')
        if match:
            return match.group(1)
    return None

def youtube_extract_ytcfg(html_text):
    patterns = [
        r'ytcfg\.set\(\s*({.+?})\s*\);',
        r'ytcfg\.set\(\s*({.+?})\s*\)',
        YOUTUBE_YTCFG_REGEX,
        r'ytcfg.set(({.+?}));',
        r'ytcfg.set\s*(\s*({.+?})\s*)'
    ]
    return youtube_extract_json_blob_any(html_text, patterns) or {}

def youtube_extract_initial_data(html_text):
    patterns = [
        YOUTUBE_INITIAL_DATA_REGEX,
        r'var\s+ytInitialData\s*=\s*({.+?})\s*;\s*(?:</script|var\s+meta|\n)',
        r'window["ytInitialData"]\s*=\s*({.+?})\s*;'
    ]
    return youtube_extract_json_blob_any(html_text, patterns) or {}

def youtube_get_page_headers_for_url(url):
    try:
        parsed = urlparse(url)
        host = (parsed.netloc or '').lower()
        path = (parsed.path or '').lower()
    except Exception:
        return None
    if host.startswith('m.youtube.com') or '/shorts/' in path:
        return {
            'User-Agent': 'Mozilla/5.0 (Linux; Android 14; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Mobile Safari/537.36',
            'Origin': 'https://m.youtube.com',
            'Referer': 'https://m.youtube.com/'
        }
    return None


def youtube_candidate_urls_for_video(video_id):
    if not video_id:
        return []
    quoted = urllib.parse.quote(video_id)
    return [
        f'https://m.youtube.com/watch?v={quoted}',
        f'https://m.youtube.com/live/{quoted}',
        f'https://m.youtube.com/shorts/{quoted}',
        f'https://www.youtube.com/watch?v={quoted}',
        f'https://www.youtube.com/live/{quoted}',
        f'https://www.youtube.com/shorts/{quoted}',
        f'https://www.youtube.com/live_chat?is_popout=1&v={quoted}'
    ]


def youtube_expand_seed_urls(url):
    result = []
    if url:
        result.append(url)
    try:
        parsed = urlparse(url or '')
        host = (parsed.netloc or '').lower()
        if host == 'www.youtube.com':
            result.append(url.replace('https://www.youtube.com/', 'https://m.youtube.com/', 1))
        elif host == 'youtube.com':
            result.append(url.replace('https://youtube.com/', 'https://m.youtube.com/', 1))
        elif host == 'm.youtube.com':
            result.append(url.replace('https://m.youtube.com/', 'https://www.youtube.com/', 1))
    except Exception:
        pass
    seen = set()
    ordered = []
    for item in result:
        if item and item not in seen:
            seen.add(item)
            ordered.append(item)
    return ordered


def youtube_get_page_payload(url, timeout=15):
    html_text = youtube_web_get_text(url, timeout=timeout, extra_headers=youtube_get_page_headers_for_url(url))
    return {
        'url': url,
        'html': html_text,
        'ytcfg': youtube_extract_ytcfg(html_text),
        'initial_data': youtube_extract_initial_data(html_text),
        'video_id': youtube_extract_video_id_from_html(html_text)
    }

def youtube_runs_to_text(runs):
    parts = []
    for run in runs or []:
        text = (run.get('text') or '') if isinstance(run, dict) else ''
        if text:
            parts.append(text)
            continue
        emoji = (run.get('emoji') or {}) if isinstance(run, dict) else {}
        shortcut = (emoji.get('shortcuts') or [None])[0] or emoji.get('emojiId')
        if shortcut:
            parts.append(shortcut)
    return ''.join(parts).strip()

def youtube_extract_author_badges(renderer):
    is_mod = False
    is_owner = False
    is_subscriber = False
    badges = renderer.get('authorBadges') or []
    for badge in badges:
        badge_renderer = badge.get('liveChatAuthorBadgeRenderer') or {}
        tooltip = (badge_renderer.get('tooltip') or '').lower()
        icon = ((badge_renderer.get('icon') or {}).get('iconType') or '').lower()
        if 'moderator' in tooltip or icon == 'moderator':
            is_mod = True
        if 'owner' in tooltip or 'broadcaster' in tooltip or icon == 'owner':
            is_owner = True
        if 'member' in tooltip or 'sponsor' in tooltip or icon in ('member', 'sponsor'):
            is_subscriber = True
    return is_mod, is_owner, is_subscriber

def youtube_extract_message_from_action(action):
    renderer = None
    for candidate in (
        (((action.get('addChatItemAction') or {}).get('item')) or {}),
        (((action.get('addLiveChatTickerItemAction') or {}).get('item')) or {}),
        (((action.get('replaceChatItemAction') or {}).get('replacementItem')) or {})
    ):
        if candidate:
            renderer = candidate
            break
    if not renderer:
        return None
    renderer_name = None
    renderer_data = None
    for key, value in renderer.items():
        if key.endswith('Renderer') and isinstance(value, dict):
            renderer_name = key
            renderer_data = value
            break
    if not renderer_data:
        return None
    display_name = ((renderer_data.get('authorName') or {}).get('simpleText') or '').strip() or 'YouTube'
    author_id = (renderer_data.get('authorExternalChannelId') or display_name).strip()
    is_mod, is_owner, is_subscriber = youtube_extract_author_badges(renderer_data)
    message_text = ''
    event_type = ''
    if renderer_name == 'liveChatTextMessageRenderer':
        message_text = youtube_runs_to_text((renderer_data.get('message') or {}).get('runs'))
    elif renderer_name == 'liveChatPaidMessageRenderer':
        amount = ((renderer_data.get('purchaseAmountText') or {}).get('simpleText') or '').strip()
        comment = youtube_runs_to_text((renderer_data.get('message') or {}).get('runs'))
        message_text = (f'Суперчат {amount}. {comment}' if comment else f'Суперчат {amount}').strip('. ')
    elif renderer_name == 'liveChatPaidStickerRenderer':
        amount = ((renderer_data.get('purchaseAmountText') or {}).get('simpleText') or '').strip()
        alt = (((renderer_data.get('sticker') or {}).get('accessibility') or {}).get('accessibilityData') or {}).get('label', '')
        base = f'Суперстікер {amount}'.strip()
        message_text = f'{base}. {alt}'.strip('. ')
    elif renderer_name == 'liveChatMembershipItemRenderer':
        primary = youtube_runs_to_text((renderer_data.get('headerPrimaryText') or {}).get('runs'))
        sub = youtube_runs_to_text((renderer_data.get('headerSubtext') or {}).get('runs'))
        msg = youtube_runs_to_text((renderer_data.get('message') or {}).get('runs'))
        message_text = '. '.join([part for part in (primary, sub, msg) if part]).strip()
        event_type = 'member'
    else:
        message_text = youtube_runs_to_text((renderer_data.get('message') or {}).get('runs'))
    message_text = (message_text or '').strip()
    if not message_text:
        return None
    return {
        'display_name': display_name,
        'author_id': author_id,
        'message_text': message_text,
        'is_mod': is_mod,
        'is_owner': is_owner,
        'is_subscriber': is_subscriber,
        'event_type': event_type,
        # Той самий ідентифікатор, що і item['id'] у Data API - завдяки цьому
        # дедуп працює наскрізь між web-читачем і API-читачем.
        'message_id': (renderer_data.get('id') or '').strip()
    }

def youtube_build_watch_url(input_value):
    raw_value = (input_value or '').strip()
    input_type, normalized = normalize_youtube_input(raw_value)
    if input_type == 'video_id':
        return f'https://www.youtube.com/watch?v={normalized}', normalized
    if input_type == 'channel_id':
        return f'https://www.youtube.com/channel/{normalized}/live', None
    if input_type == 'handle':
        return f'https://www.youtube.com/@{normalized.lstrip("@")}' + '/live', None
    try:
        prepared = raw_value if '://' in raw_value else 'https://' + raw_value
        parsed = urlparse(prepared)
        host = (parsed.netloc or '').lower()
        path_parts = [p for p in (parsed.path or '').split('/') if p]
        if 'youtube.com' in host:
            if 'live_chat' in path_parts:
                qs = parse_qs(parsed.query)
                candidate = (qs.get('v') or [None])[0]
                if candidate and len(candidate) == 11:
                    return f'https://www.youtube.com/watch?v={candidate}', candidate
            if extract_youtube_video_id(raw_value):
                video_id = extract_youtube_video_id(raw_value)
                return f'https://www.youtube.com/watch?v={video_id}', video_id
            if path_parts and path_parts[0].startswith('@'):
                return f'https://www.youtube.com/{path_parts[0]}/live', None
            if len(path_parts) >= 2 and path_parts[0] in ('channel', 'c', 'user'):
                return f'https://www.youtube.com/{path_parts[0]}/{path_parts[1]}/live', None
    except Exception:
        pass
    handle = raw_value.lstrip('@')
    return f'https://www.youtube.com/@{handle}/live', None

def youtube_extract_innertube_fallback(html_text):
    text = html_text or ''
    result = {}

    m = re.search(r'"INNERTUBE_API_KEY":"([^"]+)"', text)
    if not m:
        m = re.search(r'"innertubeApiKey":"([^"]+)"', text)
    if m:
        result['INNERTUBE_API_KEY'] = m.group(1)

    m = re.search(r'"INNERTUBE_CLIENT_VERSION":"([^"]+)"', text)
    if not m:
        m = re.search(r'"clientVersion":"([^"]+)"', text)
    if m:
        result['INNERTUBE_CLIENT_VERSION'] = m.group(1)

    m = re.search(r'"INNERTUBE_CONTEXT_CLIENT_NAME":\s*([0-9]+)', text)
    if m:
        result['INNERTUBE_CONTEXT_CLIENT_NAME'] = m.group(1)
    else:
        m = re.search(r'"INNERTUBE_CLIENT_NAME":"([^"]+)"', text)
        if m:
            name_map = {'WEB': '1', 'MWEB': '2'}
            result['INNERTUBE_CONTEXT_CLIENT_NAME'] = name_map.get(m.group(1), '1')
        else:
            result['INNERTUBE_CONTEXT_CLIENT_NAME'] = '1'

    m = re.search(r'"INNERTUBE_CONTEXT":(\{.+?\})\s*,\s*"INNERTUBE_CONTEXT_CLIENT_NAME"', text, re.DOTALL)
    if not m:
        m = re.search(r'"INNERTUBE_CONTEXT":(\{.+?\})\s*,\s*"INNERTUBE_API_KEY"', text, re.DOTALL)
    if m:
        try:
            result['INNERTUBE_CONTEXT'] = json.loads(m.group(1))
        except Exception:
            pass

    return result


def youtube_make_context_result(source_url, video_id, continuation, ytcfg, html_text=''):
    ytcfg = dict(ytcfg or {})
    if not ytcfg.get('INNERTUBE_API_KEY') or not ytcfg.get('INNERTUBE_CONTEXT'):
        fallback = youtube_extract_innertube_fallback(html_text)
        for k, v in fallback.items():
            if v and not ytcfg.get(k):
                ytcfg[k] = v

    innertube_context = ytcfg.get('INNERTUBE_CONTEXT') or {}
    innertube_api_key = ytcfg.get('INNERTUBE_API_KEY') or ''
    client_name = str(ytcfg.get('INNERTUBE_CONTEXT_CLIENT_NAME') or '1')
    client_version = str(ytcfg.get('INNERTUBE_CLIENT_VERSION') or '')
    if not continuation or not innertube_context or not innertube_api_key:
        return None
    return {
        'watch_url': source_url,
        'video_id': video_id,
        'continuation': continuation,
        'api_key': innertube_api_key,
        'context': innertube_context,
        'client_name': client_name,
        'client_version': client_version
    }

def youtube_get_web_context(input_value):
    watch_url, explicit_video_id = youtube_build_watch_url(input_value)
    visited = set()
    queue = []
    for seed in youtube_expand_seed_urls(watch_url):
        if seed not in queue:
            queue.append(seed)
    if explicit_video_id:
        for candidate in youtube_candidate_urls_for_video(explicit_video_id):
            if candidate not in queue:
                queue.append(candidate)

    merged_ytcfg = {}
    resolved_video_id = explicit_video_id

    while queue:
        url = queue.pop(0)
        if not url or url in visited:
            continue
        visited.add(url)
        try:
            page = youtube_get_page_payload(url, timeout=15)
        except Exception:
            continue

        page_ytcfg = page.get('ytcfg') or {}
        if page_ytcfg and not merged_ytcfg:
            merged_ytcfg = page_ytcfg

        page_video_id = resolved_video_id or page.get('video_id')
        if not page_video_id:
            page_video_id = page.get('video_id')
        if page_video_id and not resolved_video_id:
            resolved_video_id = page_video_id

        continuation = youtube_find_reload_continuation(page.get('initial_data') or {})
        if not continuation:
            continuation = youtube_extract_continuation_from_html(page.get('html') or '')

        context_result = youtube_make_context_result(url, page_video_id, continuation, page_ytcfg or merged_ytcfg, page.get('html') or '')
        if context_result:
            return context_result

        if page_video_id:
            for candidate in youtube_candidate_urls_for_video(page_video_id):
                if candidate not in visited and candidate not in queue:
                    queue.append(candidate)

    if resolved_video_id:
        for chat_url in youtube_candidate_urls_for_video(resolved_video_id):
            if chat_url in visited:
                continue
            try:
                page = youtube_get_page_payload(chat_url, timeout=15)
                continuation = youtube_find_reload_continuation(page.get('initial_data') or {})
                if not continuation:
                    continuation = youtube_extract_continuation_from_html(page.get('html') or '')
                context_result = youtube_make_context_result(chat_url, resolved_video_id, continuation, page.get('ytcfg') or merged_ytcfg, page.get('html') or '')
                if context_result:
                    return context_result
            except Exception:
                pass
    return None

def youtube_fetch_live_chat_web(continuation, youtube_context):
    api_key = youtube_context.get('api_key') or ''
    innertube_context = youtube_context.get('context') or {}
    if not api_key or not innertube_context or not continuation:
        return [], None, 0
    endpoint = f'https://www.youtube.com/youtubei/v1/live_chat/get_live_chat?key={urllib.parse.quote(api_key)}'
    extra_headers = {}
    client_name = youtube_context.get('client_name')
    client_version = youtube_context.get('client_version')
    watch_url = youtube_context.get('watch_url') or 'https://www.youtube.com/'
    if client_name:
        extra_headers['X-YouTube-Client-Name'] = str(client_name)
    if client_version:
        extra_headers['X-YouTube-Client-Version'] = str(client_version)
    if 'm.youtube.com' in watch_url:
        extra_headers['Origin'] = 'https://m.youtube.com'
        extra_headers['Referer'] = watch_url
        extra_headers['User-Agent'] = 'Mozilla/5.0 (Linux; Android 14; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Mobile Safari/537.36'
    else:
        extra_headers['Origin'] = 'https://www.youtube.com'
        extra_headers['Referer'] = watch_url
    payload = {'context': innertube_context, 'continuation': continuation}
    data = youtube_web_post_json(endpoint, payload, timeout=15, extra_headers=extra_headers)
    actions = (((data.get('continuationContents') or {}).get('liveChatContinuation')) or {}).get('actions', [])
    next_continuation, timeout_ms = youtube_find_next_continuation(data)
    messages = []
    for action in actions:
        parsed = youtube_extract_message_from_action(action)
        if parsed:
            messages.append(parsed)
    return messages, next_continuation, timeout_ms

def extract_youtube_video_id(value):
    value = (value or '').strip()
    if not value:
        return None
    if len(value) == 11 and re.match(r'^[a-zA-Z0-9_-]{11}$', value):
        return value
    try:
        normalized = value if '://' in value else 'https://' + value
        parsed = urlparse(normalized)
        host = (parsed.netloc or '').lower()
        path = parsed.path or ''
        if 'youtu.be' in host:
            candidate = path.strip('/').split('/')[0]
            if len(candidate) == 11 and re.match(r'^[a-zA-Z0-9_-]{11}$', candidate):
                return candidate
        if 'youtube.com' in host:
            qs = parse_qs(parsed.query)
            if 'v' in qs:
                candidate = qs['v'][0]
                if len(candidate) == 11 and re.match(r'^[a-zA-Z0-9_-]{11}$', candidate):
                    return candidate
            parts = [p for p in path.split('/') if p]
            for marker in ('live', 'embed', 'shorts', 'watch'):
                if marker in parts:
                    idx = parts.index(marker)
                    if idx + 1 < len(parts):
                        candidate = parts[idx + 1]
                        if len(candidate) == 11 and re.match(r'^[a-zA-Z0-9_-]{11}$', candidate):
                            return candidate
    except Exception:
        pass
    return None

def normalize_youtube_input(value):
    value = (value or '').strip()
    if not value:
        return ('empty', '')
    if re.match(r'^(Ei|Cg)[A-Za-z0-9_-]+$', value):
        return ('chat_id', value)
    video_id = extract_youtube_video_id(value)
    if video_id:
        return ('video_id', video_id)
    channel_match = re.search(r'(UC[a-zA-Z0-9_-]{22})', value)
    if channel_match:
        return ('channel_id', channel_match.group(1))
    handle_match = re.search(r'/@([A-Za-z0-9._-]+)', value)
    if handle_match:
        return ('handle', handle_match.group(1))
    if value.startswith('@'):
        return ('handle', value[1:])
    if re.match(r'^UC[a-zA-Z0-9_-]{22}$', value):
        return ('channel_id', value)
    try:
        normalized = value if '://' in value else 'https://' + value
        parsed = urlparse(normalized)
        host = (parsed.netloc or '').lower()
        path_parts = [p for p in (parsed.path or '').split('/') if p]
        if 'youtube.com' in host and len(path_parts) >= 2:
            if path_parts[0] == 'channel':
                return ('channel_id', path_parts[1])
            if path_parts[0] in ('c', 'user'):
                return ('handle', path_parts[1])
        if 'youtu.be' in host and path_parts:
            maybe_video = extract_youtube_video_id(value)
            if maybe_video:
                return ('video_id', maybe_video)
    except Exception:
        pass
    return ('handle', value)

def extract_youtube_message_text(item):
    snippet = item.get('snippet', {}) or {}
    msg_type = (snippet.get('type') or '').strip()
    display_message = (snippet.get('displayMessage') or '').strip()
    if msg_type == 'textMessageEvent':
        return (snippet.get('textMessageDetails', {}) or {}).get('messageText', '').strip() or display_message
    if msg_type == 'superChatEvent':
        details = snippet.get('superChatDetails', {}) or {}
        amount = (details.get('amountDisplayString') or '').strip()
        comment = (details.get('userComment') or '').strip()
        base = f'Суперчат {amount}'.strip()
        return f'{base}. {comment}'.strip('. ') if comment else base
    if msg_type == 'memberMilestoneChatEvent':
        details = snippet.get('memberMilestoneChatDetails', {}) or {}
        comment = (details.get('userComment') or '').strip()
        months = details.get('memberMonth') or details.get('memberLevelName') or ''
        base = f'Ювілей підписки {months}'.strip()
        return f'{base}. {comment}'.strip('. ') if comment else base
    if msg_type == 'newSponsorEvent':
        return 'Оформив спонсорство каналу'
    if msg_type == 'pollEvent':
        return ''
    return display_message

class YouTubeLiveSearchCache:
    """
    Thread-safe кеш/дросель навколо search.list (100 квота-юнітів за
    виклик — найдорожчий метод YouTube Data API v3) для пошуку активного
    live-відео каналу за channel_id.

    ЧОМУ ЦЕ ПОТРІБНО (корінна причина вичерпання квоти):
    І читач чату (youtube_worker → youtube_expand_live_targets, кожні
    20 с), і аналітика (YouTubeAdapter.get_viewer_count →
    find_active_streams → youtube_expand_live_targets, кожні
    config['analytics_update_interval'] секунд, за замовчуванням 25 с)
    НЕЗАЛЕЖНО одне від одного викликають
    get_youtube_live_video_ids_by_channel_id() для того самого каналу.
    Без кешування це до ~540 квота-юнітів/хв (100 юнітів × (3 рази/хв з
    читача чату + 2.4 рази/хв з аналітики)) СУМАРНО, навіть якщо канал
    ще не в ефірі — денна квота (стандартні 10 000 юнітів, а тим паче
    менший ліміт метрики 'Search Queries per day') вичерпується за
    лічені хвилини.

    Кешування в ОДНІЙ точці, через яку проходять ОБИДВА споживачі,
    означає, що реальний мережевий запит до search.list відбувається
    щонайбільше раз на live_hit_ttl секунд (коли трансляцію вже
    знайдено — вона не зникає за секунди, тож немає сенсу перепитувати
    так само часто) або раз на live_miss_ttl секунд (поки чекаємо, доки
    канал стане live).
    """

    def __init__(self, live_hit_ttl=300, live_miss_ttl=90):
        self._lock = threading.Lock()
        self._entries = {}  # channel_id -> {"video_ids": [...], "expires_at": float}
        self.live_hit_ttl = live_hit_ttl
        self.live_miss_ttl = live_miss_ttl

    def get(self, channel_id):
        with self._lock:
            entry = self._entries.get(channel_id)
            if not entry:
                return None
            if time.time() >= entry["expires_at"]:
                return None
            return list(entry["video_ids"])

    def get_stale(self, channel_id):
        """Віддає навіть прострочений результат. Потрібно, коли search.list
        заблокований після 429: краще працювати з відомим video_id, ніж
        втратити чат."""
        with self._lock:
            entry = self._entries.get(channel_id)
            if not entry:
                return None
            return list(entry["video_ids"])

    def set(self, channel_id, video_ids):
        ttl = self.live_hit_ttl if video_ids else self.live_miss_ttl
        expires_at = time.time() + ttl
        with self._lock:
            self._entries[channel_id] = {"video_ids": list(video_ids), "expires_at": expires_at}

    def invalidate(self, channel_id):
        with self._lock:
            self._entries.pop(channel_id, None)


_youtube_live_search_cache = YouTubeLiveSearchCache()


def get_youtube_channel_id_from_handle(handle_or_query, api_key):
    if not api_key:
        return None
    handle = (handle_or_query or '').strip().lstrip('@')
    if not handle:
        return None
    try:
        url = f'https://www.googleapis.com/youtube/v3/channels?part=id&forHandle={urllib.parse.quote(handle)}&key={api_key}'
        data = youtube_api_get_json(url)
        items = (data or {}).get('items', [])
        if items:
            return items[0].get('id')
    except Exception:
        pass
    try:
        url = f'https://www.googleapis.com/youtube/v3/channels?part=id&forUsername={urllib.parse.quote(handle)}&key={api_key}'
        data = youtube_api_get_json(url)
        items = (data or {}).get('items', [])
        if items:
            return items[0].get('id')
    except Exception:
        pass
    if youtube_search_is_blocked():
        return None
    search_url = f'https://www.googleapis.com/youtube/v3/search?part=snippet&type=channel&maxResults=5&q={urllib.parse.quote(handle)}&key={api_key}'
    data = youtube_api_get_json(search_url, kind='search')
    items = (data or {}).get('items', [])
    for item in items:
        item_id = item.get('id', {})
        channel_id = item_id.get('channelId') or item.get('snippet', {}).get('channelId')
        if channel_id:
            return channel_id
    return None

_youtube_video_title_cache = {}


def youtube_get_cached_title(video_id):
    return _youtube_video_title_cache.get((video_id or '').strip(), '')


_youtube_orientation_cache = {}


def youtube_detect_video_orientation(video_id, timeout=6):
    """Визначає вертикальне (Shorts) чи горизонтальне (звичайна трансляція)
    джерело для video_id. YouTube Data API НЕ надає прямого поля "це
    Shorts" - надійний безкоштовний спосіб: сторінка /shorts/<id> віддає
    HTTP 200 і залишається на /shorts/, якщо відео справді Shorts, і робить
    редірект (301/302) на /watch?v=<id>, якщо це звичайне відео/трансляція
    (перевірено на живих трансляціях). Результат кешується назавжди для
    video_id (орієнтація одного відео не змінюється), щоб не робити цей
    запит на кожному опитуванні статистики.
    Повертає 'vertical' | 'horizontal' | '' (не вдалось визначити)."""
    video_id = (video_id or '').strip()
    if not video_id:
        return ''
    if video_id in _youtube_orientation_cache:
        return _youtube_orientation_cache[video_id]
    result = ''
    try:
        conn = http.client.HTTPSConnection('www.youtube.com', timeout=timeout)
        try:
            conn.request('HEAD', '/shorts/{}'.format(urllib.parse.quote(video_id)),
                         headers={'User-Agent': 'Mozilla/5.0'})
            resp = conn.getresponse()
            resp.read()
            location = resp.getheader('Location') or ''
            if resp.status in (301, 302, 303, 307, 308):
                result = 'horizontal' if '/watch' in location else 'vertical'
            elif resp.status == 200:
                result = 'vertical'
            else:
                result = ''
        finally:
            conn.close()
    except Exception:
        result = ''
    if result:
        _youtube_orientation_cache[video_id] = result
    return result


def get_youtube_live_video_ids_by_channel_id(channel_id, api_key, max_results=10, force_refresh=False):
    if not api_key or not channel_id:
        return []
    requested = int(max(1, max_results or 10))
    if not force_refresh:
        cached = _youtube_live_search_cache.get(channel_id)
        if cached is not None:
            return cached[:requested]
    if youtube_search_is_blocked() or youtube_quota_exceeded:
        # Дорогий search.list зараз заборонений - працюємо з тим, що вже знаємо.
        stale = _youtube_live_search_cache.get_stale(channel_id)
        if stale:
            return stale[:requested]
        return []
    fetch_count = max(requested, 10)
    live_url = f'https://www.googleapis.com/youtube/v3/search?part=snippet&channelId={urllib.parse.quote(channel_id)}&eventType=live&type=video&maxResults={fetch_count}&key={api_key}'
    data = youtube_api_get_json(live_url, kind='search')
    items = (data or {}).get('items', [])
    result = []
    for item in items:
        video_id = ((item.get('id') or {}).get('videoId') or '').strip()
        if video_id and video_id not in result:
            result.append(video_id)
            # Заголовок трансляції вже присутній у цій самій відповіді
            # search.list (part=snippet) - беремо його безкоштовно, без
            # додаткового запиту, і використовуємо як надійну мітку джерела
            # повідомлення (на відміну від спроби вгадати орієнтацію відео
            # за пропорціями мініатюр - YouTube офіційно не гарантує, що
            # width/height мініатюри відображають реальну пропорцію
            # контенту, може бути з чорними полями).
            title = ((item.get('snippet') or {}).get('title') or '').strip()
            if title:
                _youtube_video_title_cache[video_id] = title
    _youtube_live_search_cache.set(channel_id, result)
    return result[:requested]


def get_youtube_live_video_id_by_channel_id(channel_id, api_key):
    video_ids = get_youtube_live_video_ids_by_channel_id(channel_id, api_key, max_results=1)
    return video_ids[0] if video_ids else None

def get_youtube_chat_id_from_video(video_id, api_key):
    if not api_key or not video_id:
        return None
    chat_url = f'https://www.googleapis.com/youtube/v3/videos?part=liveStreamingDetails&id={urllib.parse.quote(video_id)}&key={api_key}'
    data = youtube_api_get_json(chat_url)
    items = (data or {}).get('items', [])
    if not items:
        return None
    return items[0].get('liveStreamingDetails', {}).get('activeLiveChatId')

def resolve_youtube_chat_id(input_value, api_key):
    input_type, normalized = normalize_youtube_input(input_value)
    if input_type == 'chat_id':
        return normalized
    if input_type == 'video_id':
        return get_youtube_chat_id_from_video(normalized, api_key)
    channel_id = None
    if input_type == 'channel_id':
        channel_id = normalized
    elif input_type == 'handle':
        channel_id = get_youtube_channel_id_from_handle(normalized, api_key)
    if not channel_id:
        return None
    video_id = get_youtube_live_video_id_by_channel_id(channel_id, api_key)
    if not video_id:
        return None
    return get_youtube_chat_id_from_video(video_id, api_key)

def youtube_expand_live_targets(input_value, api_key=''):
    raw_value = str(input_value or '').strip()
    if not raw_value:
        return []
    input_type, normalized = normalize_youtube_input(raw_value)
    if input_type in ('chat_id', 'video_id'):
        return [normalized]
    if api_key and input_type in ('channel_id', 'handle'):
        channel_id = normalized if input_type == 'channel_id' else get_youtube_channel_id_from_handle(normalized, api_key)
        video_ids = get_youtube_live_video_ids_by_channel_id(channel_id, api_key, max_results=10) if channel_id else []
        if video_ids:
            youtube_remember_live_targets(raw_value, video_ids)
            return video_ids
        # Пошук нічого не дав (або заблокований після 429) - беремо останній
        # відомий video_id, щоб web-читач продовжив працювати.
        remembered = youtube_recall_live_targets(raw_value)
        if remembered:
            if youtube_search_is_blocked() or youtube_quota_exceeded:
                log_status('YouTube', 'Пошук трансляцій недоступний (ліміт API) - '
                                      'використовую вже відомий video_id: {}'.format(
                                          ', '.join(remembered)))
            return remembered
    watch_url, explicit_video_id = youtube_build_watch_url(raw_value)
    if explicit_video_id:
        youtube_remember_live_targets(raw_value, [explicit_video_id])
        return [explicit_video_id]
    return [raw_value]


def youtube_format_target_label(value):
    raw_value = str(value or '').strip()
    if not raw_value:
        return 'YouTube'
    input_type, normalized = normalize_youtube_input(raw_value)
    if input_type == 'video_id':
        return f'video {normalized}'
    if input_type == 'handle':
        return '@' + normalized.lstrip('@')
    if input_type == 'channel_id':
        return normalized
    return raw_value


def youtube_worker_api(session_id, yt_input, api_key):
    global youtube_quota_exceeded
    chat_id = None
    waiting_logged = False
    while session_is_current(session_id) and not chat_id:
        if youtube_quota_exceeded:
            if not waiting_logged:
                log_status('YouTube', '⏳ Квоту YouTube API вичерпано. Очікування відновлення...')
                waiting_logged = True
            time.sleep(60)
            continue
        chat_id = resolve_youtube_chat_id(yt_input, api_key)
        if not chat_id:
            if not waiting_logged:
                log_status('YouTube', f'Очікування activeLiveChatId для: {yt_input}. Запустіть трансляцію або перевірте API ключ.')
                waiting_logged = True
            time.sleep(30)
            if not session_is_current(session_id) or not chat_id:
                return
    log_status('YouTube', f'Підключення до liveChatId через API: {chat_id}')
    platform_mark_connected('youtube')
    next_page_token = ''
    base_url = f'https://www.googleapis.com/youtube/v3/liveChat/messages?liveChatId={urllib.parse.quote(chat_id)}&part=snippet,authorDetails&maxResults=200&key={api_key}'
    error_count = 0
    max_errors = 5
    while session_is_current(session_id):
        try:
            req_url = base_url + (f'&pageToken={urllib.parse.quote(next_page_token)}' if next_page_token else '')
            data = youtube_api_get_json(req_url, timeout=10)
            if not data:
                error_count += 1
                if error_count >= max_errors:
                    log_status('YouTube', f'Перевищено кількість помилок ({max_errors}), перезапуск...')
                    time.sleep(30)
                    error_count = 0
                    chat_id = resolve_youtube_chat_id(yt_input, api_key)
                    if not chat_id:
                        log_status('YouTube', 'Не вдалось отримати chat_id, вихід...')
                        break
                    base_url = f'https://www.googleapis.com/youtube/v3/liveChat/messages?liveChatId={urllib.parse.quote(chat_id)}&part=snippet,authorDetails&maxResults=200&key={api_key}'
                else:
                    time.sleep(6.0)
                continue
            error_count = 0
            next_page_token = data.get('nextPageToken', next_page_token)
            for item in data.get('items', []):
                msg_id = item.get('id')
                # Спільний namespace 'youtube' з web-читачем: ID у API та у
                # web-рендерері однакові, тож перемикання API <-> web (напр.
                # після HTTP 429) не спричиняє повторного озвучення.
                if not dedup_is_new('youtube', msg_id):
                    continue
                snippet = item.get('snippet', {})
                author = item.get('authorDetails', {})
                msg_text = extract_youtube_message_text(item)
                if not msg_text:
                    continue
                display_name = author.get('displayName') or author.get('channelId') or snippet.get('authorChannelId') or 'YouTube'
                author_id = author.get('channelId') or snippet.get('authorChannelId') or display_name
                is_mod = author.get('isChatModerator', False)
                is_owner = author.get('isChatOwner', False)
                is_subscriber = author.get('isChatSponsor', False)
                c_name, tts_text = process_filters_and_tts('youtube', author_id, display_name, msg_text, is_mod, is_owner, is_subscriber)
                if c_name:
                    msg_type = (snippet.get('type') or '').strip()
                    if msg_type in ('newSponsorEvent', 'memberMilestoneChatEvent'):
                        emit_platform_alert('youtube', 'member', c_name, msg_text, 'Новий учасник YouTube', 'subscription', username=author_id, source_display_name=display_name, voice_id=(config.get('yt_member_voice_id') or '').strip(), force_chat=False)
                    else:
                        add_to_buffer('youtube', c_name, msg_text, tts_text, is_mod, is_owner, username=author_id, source_display_name=display_name)
            polling_ms = data.get('pollingIntervalMillis', 4000)
            polling_seconds = max(4.0, float(polling_ms) / 1000.0)
            time.sleep(polling_seconds)
        except Exception as e:
            log_status('YouTube', f'Помилка читання чату через API: {e}')
            error_count += 1
            if error_count >= max_errors:
                log_status('YouTube', 'Перевищено кількість помилок, перезапуск через 30 сек...')
                time.sleep(30)
                error_count = 0
            else:
                time.sleep(6.0)

def youtube_target_worker(session_id, yt_input, stream_variant=''):
    global config
    yt_input = str(yt_input or '').strip()
    if not yt_input:
        return
    wait_logged = False
    while session_is_current(session_id) and youtube_target_is_active(yt_input):
        web_context = None
        try:
            web_context = youtube_get_web_context(yt_input)
        except Exception as e:
            log_status('YouTube', f'Web-режим недоступний: {e}')
        if web_context:
            log_status('YouTube', f'Web-режим активний для YouTube: {web_context.get("watch_url") or yt_input}')
            platform_mark_connected('youtube')
            wait_logged = False
            continuation = web_context.get('continuation')
            error_count = 0
            max_errors = 5
            while session_is_current(session_id) and youtube_target_is_active(yt_input) and continuation:
                try:
                    messages, next_continuation, timeout_ms = youtube_fetch_live_chat_web(continuation, web_context)
                    error_count = 0
                    for item in messages:
                        # Якщо YouTube дав справжній ID - дедупимо по ньому у
                        # спільному з API namespace. Якщо ні (старий рендерер)
                        # - відкат на signature, але теж у довговічному реєстрі,
                        # а не в локальному set, що гинув при кожному реконнекті.
                        web_msg_id = (item.get('message_id') or '').strip()
                        if web_msg_id:
                            if not dedup_is_new('youtube', web_msg_id):
                                continue
                        else:
                            signature = 'sig::{}::{}'.format(
                                item.get('author_id', ''), item.get('message_text', ''))
                            if not dedup_is_new('youtube', signature):
                                continue
                        c_name, tts_text = process_filters_and_tts(
                            'youtube',
                            item.get('author_id') or item.get('display_name') or 'YouTube',
                            item.get('display_name') or 'YouTube',
                            item.get('message_text') or '',
                            item.get('is_mod', False),
                            item.get('is_owner', False),
                            item.get('is_subscriber', False)
                        )
                        if c_name:
                            if item.get('event_type') == 'member':
                                emit_platform_alert('youtube', 'member', c_name, item.get('message_text') or '', 'Новий учасник YouTube', 'subscription', username=item.get('author_id', ''), source_display_name=item.get('display_name', item.get('author_name', '')), voice_id=(config.get('yt_member_voice_id') or '').strip(), force_chat=False, stream_variant=stream_variant)
                            else:
                                add_to_buffer('youtube', c_name, item.get('message_text') or '', tts_text, item.get('is_mod', False), item.get('is_owner', False), username=item.get('author_id', ''), source_display_name=item.get('display_name', item.get('author_name', '')), stream_variant=stream_variant)
                    if not next_continuation:
                        log_status('YouTube', '⚠️ Web-режим тимчасово втратив continuation. Оновлюю контекст...')
                        time.sleep(5)
                        refreshed = youtube_get_web_context(web_context.get('video_id') or yt_input)
                        if not refreshed:
                            break
                        web_context = refreshed
                        continuation = refreshed.get('continuation')
                        continue
                    continuation = next_continuation
                    time.sleep(max(1.5, float(timeout_ms or 0) / 1000.0))
                except urllib.error.HTTPError as he:
                    if he.code in (400, 404):
                        # HTTP 400 від get_live_chat = continuation застарів
                        # (трансляція перезапустилась / чат перевідкрито).
                        # Повторювати той самий continuation безглуздо -
                        # одразу оновлюємо контекст. Раніше тут витрачалось
                        # 5 марних спроб і 20 с пауза, і чат «замовкав».
                        log_status('YouTube', 'Web-режим: continuation застарів '
                                              '(HTTP {}). Оновлюю контекст...'.format(he.code))
                        refreshed = None
                        try:
                            refreshed = youtube_get_web_context(web_context.get('video_id') or yt_input)
                        except Exception as re_err:
                            log_status('YouTube', 'Не вдалося оновити web-контекст: {}'.format(re_err))
                        if refreshed:
                            web_context = refreshed
                            continuation = refreshed.get('continuation')
                            error_count = 0
                            platform_mark_connected('youtube')
                            time.sleep(2.0)
                            continue
                        time.sleep(platform_backoff_delay('youtube', 'web_continuation_expired'))
                        break
                    error_count += 1
                    log_status('YouTube', f'Помилка web-читання чату: HTTP {he.code}')
                    if error_count >= max_errors:
                        time.sleep(platform_backoff_delay('youtube', 'web_http_{}'.format(he.code)))
                        break
                    time.sleep(6.0)
                except Exception as e:
                    error_count += 1
                    log_status('YouTube', f'Помилка web-читання чату: {e}')
                    if error_count >= max_errors:
                        log_status('YouTube', 'Web-режим YouTube недоступний, пробую перепідключення...')
                        time.sleep(platform_backoff_delay('youtube', 'web_read_failed'))
                        break
                    time.sleep(6.0)
            if not session_is_current(session_id) or not youtube_target_is_active(yt_input):
                return
            time.sleep(5)
            continue
        if config.get('yt_api_key', '').strip():
            log_status('YouTube', f'Web-режим ще недоступний для {yt_input}. API ключ використовується для пошуку активних YouTube Live/Shorts та analytics. Повторна спроба через 20 сек...')
        else:
            log_status('YouTube', f'Web-режим ще недоступний для {yt_input}. Повторна спроба через 20 сек...')
        time.sleep(20)


def youtube_worker(session_id):
    global config
    raw_inputs = get_youtube_input_sources(config['yt_live_id'])
    if not raw_inputs:
        log_status('YouTube', 'Пропуск: не вказано канал / handle / ID / посилання')
        set_youtube_active_targets([])
        return
    worker_threads = {}
    while session_is_current(session_id):
        expanded_targets = []
        api_key = (config.get('yt_api_key', '') or '').strip()
        for source in raw_inputs:
            for target in youtube_expand_live_targets(source, api_key):
                target_value = str(target or '').strip()
                if target_value and target_value not in expanded_targets:
                    expanded_targets.append(target_value)
        if not expanded_targets:
            expanded_targets = list(raw_inputs)
        set_youtube_active_targets(expanded_targets)
        # Якщо одночасно активні декілька трансляцій з одного каналу
        # (напр. горизонтальна + вертикальна) - позначаємо кожне джерело
        # заголовком ЙОГО трансляції (безкоштовно, вже отримано разом з
        # пошуком live-відео), щоб у чаті було видно, звідки повідомлення.
        # Якщо трансляція одна - міток не показуємо, все як і раніше.
        show_source_label = len(expanded_targets) > 1
        for target in expanded_targets:
            thread_obj = worker_threads.get(target)
            if thread_obj and thread_obj.is_alive():
                continue
            variant = youtube_get_cached_title(target) if show_source_label else ''
            variant_note = f' [{variant}]' if variant else ''
            log_status('YouTube', f'Запуск читача YouTube для: {youtube_format_target_label(target)}{variant_note}')
            worker_threads[target] = threading.Thread(target=youtube_target_worker, args=(session_id, target, variant), daemon=True)
            worker_threads[target].start()
        for target in list(worker_threads.keys()):
            if target not in expanded_targets and not worker_threads[target].is_alive():
                worker_threads.pop(target, None)
        time.sleep(20)
    set_youtube_active_targets([])

YOUTUBE_VIDEO_ID_RE = re.compile(r'^[A-Za-z0-9_-]{11}$')


def youtube_collect_stats_snapshot(api_key, video_ids):
    """Повертає (likes_by_video, subs_by_channel) одним-двома запитами до API.

    videos.list -> statistics.likeCount + snippet.channelId (1 одиниця квоти)
    channels.list -> statistics.subscriberCount (1 одиниця квоти)
    """
    likes = {}
    channels = {}
    if not api_key or not video_ids:
        return likes, {}
    ids_param = ','.join(video_ids[:50])
    url = ('https://www.googleapis.com/youtube/v3/videos'
           '?part=statistics,snippet&id={}&key={}'.format(urllib.parse.quote(ids_param), urllib.parse.quote(api_key)))
    data = youtube_api_get_json(url)
    if not data:
        return likes, {}
    for item in data.get('items', []) or []:
        vid = str(item.get('id') or '').strip()
        stats = item.get('statistics', {}) or {}
        snippet = item.get('snippet', {}) or {}
        if not vid:
            continue
        try:
            likes[vid] = int(stats.get('likeCount', 0) or 0)
        except Exception:
            likes[vid] = 0
        ch = str(snippet.get('channelId') or '').strip()
        if ch:
            channels[ch] = True
    subs = {}
    if channels:
        ch_param = ','.join(list(channels.keys())[:50])
        ch_url = ('https://www.googleapis.com/youtube/v3/channels'
                  '?part=statistics&id={}&key={}'.format(urllib.parse.quote(ch_param), urllib.parse.quote(api_key)))
        ch_data = youtube_api_get_json(ch_url)
        for item in (ch_data or {}).get('items', []) or []:
            cid = str(item.get('id') or '').strip()
            stats = item.get('statistics', {}) or {}
            if not cid:
                continue
            if stats.get('hiddenSubscriberCount'):
                if cid not in youtube_stats_state.get('hidden_subs_warned', set()):
                    youtube_stats_state.setdefault('hidden_subs_warned', set()).add(cid)
                    log_status('YouTubeStats', '!!! На каналі (ID {}) кількість підписників ПРИХОВАНА в публічній статистиці YouTube. Алерти нових підписників технічно НЕМОЖЛИВІ, поки власник каналу не увімкне показ лічильника у налаштуваннях YouTube Studio -> Налаштування -> Канал -> Розширені налаштування -> "Показувати кількість підписників".'.format(cid))
                continue
            try:
                subs[cid] = int(stats.get('subscriberCount', 0) or 0)
            except Exception:
                continue
    return likes, subs


def youtube_stats_worker(session_id):
    """Опитує лічильники YouTube (підписники каналу + лайки трансляції).

    YouTube НЕ надсилає подій про безкоштовні підписки та лайки в live-чат,
    тому єдиний робочий спосіб - періодичний опит статистики. Через це
    неможливо дізнатись НІК підписника: доступна лише зміна лічильника.
    """
    while session_is_current(session_id):
        try:
            enable_subs = bool(config.get('yt_enable_sub_alerts', True))
            enable_likes = bool(config.get('yt_enable_like_alerts', True))
            api_key = (config.get('yt_api_key', '') or '').strip()
            if api_key and (enable_subs or enable_likes):
                with youtube_active_targets_lock:
                    targets = list(youtube_active_targets)
                video_ids = [t for t in targets if YOUTUBE_VIDEO_ID_RE.match(t or '')]
                if video_ids:
                    likes, subs = youtube_collect_stats_snapshot(api_key, video_ids)
                    if enable_likes:
                        threshold = max(1, int(config.get('yt_like_threshold', 50) or 50))
                        for vid, total_likes in likes.items():
                            step = int(total_likes) // threshold
                            prev = youtube_stats_state['like_step'].get(vid)
                            youtube_stats_state['like_step'][vid] = step
                            if prev is None or step <= prev or step <= 0:
                                continue
                            reached = step * threshold
                            orientation = youtube_detect_video_orientation(vid)
                            orientation_label = {'vertical': 'Shorts (вертикально)', 'horizontal': 'звичайна трансляція (горизонтально)'}.get(orientation, '')
                            template = config.get('yt_like_template', '') or 'На трансляції YouTube вже {likes} лайків!'
                            try:
                                text = template.format(likes=reached, total=total_likes, source=orientation_label)
                            except Exception:
                                text = 'На трансляції YouTube вже {} лайків!'.format(reached)
                            if orientation_label and '{source}' not in template:
                                text += ' [{}]'.format(orientation_label)
                            emit_platform_alert('youtube', 'like', 'YouTube', text,
                                                '{} лайків'.format(reached), 'like',
                                                username='', source_display_name='YouTube',
                                                force_chat=False, show_user=False,
                                                stream_variant=orientation_label)
                    if enable_subs:
                        for cid, total_subs in subs.items():
                            prev = youtube_stats_state['subs'].get(cid)
                            youtube_stats_state['subs'][cid] = total_subs
                            if prev is None or total_subs <= prev:
                                continue
                            delta = total_subs - prev
                            template = config.get('yt_sub_template', '') or 'Новий підписник на YouTube! Всього: {total}'
                            try:
                                text = template.format(total=total_subs, count=delta)
                            except Exception:
                                text = 'Новий підписник на YouTube! Всього: {}'.format(total_subs)
                            emit_platform_alert('youtube', 'sub', 'YouTube', text,
                                                '+{} | всього {}'.format(delta, total_subs), 'subscription',
                                                username='', source_display_name='YouTube',
                                                force_chat=False, show_user=False)
        except Exception as e:
            log_error('YouTubeStats', e)
        try:
            delay = max(30, int(config.get('yt_stats_poll_seconds', 60) or 60))
        except Exception:
            delay = 60
        for _ in range(delay):
            if not session_is_current(session_id):
                return
            time.sleep(1)


def kick_fetch_json(url, referer=None, timeout=10, headers_extra=None):
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
        'Accept': 'application/json',
        'Origin': 'https://kick.com'
    }
    if referer:
        headers['Referer'] = referer
    if headers_extra:
        headers.update(headers_extra)
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        if e.code == 403:
            log_status("Kick", "HTTP 403 від Kick для {}. Публічний v2 endpoint часто блокується; для analytics краще використовувати офіційний API з Client ID/Secret, а для подій — webhooks.".format(url))
        else:
            log_status("Kick", "HTTP помилка {} для {}".format(e.code, url))
        return None
    except Exception as e:
        log_status("Kick", "urllib помилка: {}".format(e))
        return None


_kick_token_cache = {'access_token': '', 'expires_at': 0.0, 'client_id': '', 'client_secret': '', 'last_error_log': 0.0}


def kick_get_app_access_token(client_id, client_secret, timeout=10):
    global _kick_token_cache
    client_id = (client_id or '').strip()
    client_secret = (client_secret or '').strip()
    if not client_id or not client_secret:
        return None
    now = time.time()
    if (
        _kick_token_cache.get('access_token')
        and _kick_token_cache.get('client_id') == client_id
        and _kick_token_cache.get('client_secret') == client_secret
        and now < float(_kick_token_cache.get('expires_at', 0) or 0) - 60
    ):
        return _kick_token_cache.get('access_token')

    data = urllib.parse.urlencode({
        'grant_type': 'client_credentials',
        'client_id': client_id,
        'client_secret': client_secret,
    }).encode('utf-8')
    headers = {
        'User-Agent': 'Mozilla/5.0',
        'Content-Type': 'application/x-www-form-urlencoded',
        'Accept': 'application/json',
    }
    try:
        req = urllib.request.Request('https://id.kick.com/oauth/token', data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            payload = json.loads(response.read().decode('utf-8'))
        access_token = (payload.get('access_token') or '').strip()
        expires_in = int(payload.get('expires_in', 3600) or 3600)
        if not access_token:
            return None
        _kick_token_cache = {
            'access_token': access_token,
            'expires_at': now + max(60, expires_in),
            'client_id': client_id,
            'client_secret': client_secret,
            'last_error_log': 0.0,
        }
        return access_token
    except urllib.error.HTTPError as e:
        if now - float(_kick_token_cache.get('last_error_log', 0) or 0) >= 60:
            # e.read() дає тіло відповіді Kick - зазвичай там конкретний
            # OAuth-код помилки (invalid_client / invalid_scope /
            # invalid_request тощо), якого не видно в самому str(e).
            try:
                error_body = e.read().decode('utf-8', errors='replace')[:500]
            except Exception:
                error_body = '<не вдалося прочитати тіло відповіді>'
            log_status("Kick", "Не вдалося отримати OAuth token: HTTP {} {}. Тіло відповіді Kick: {}".format(e.code, e.reason, error_body))
            _kick_token_cache['last_error_log'] = now
        return None
    except Exception as e:
        if now - float(_kick_token_cache.get('last_error_log', 0) or 0) >= 60:
            log_status("Kick", "Не вдалося отримати OAuth token: {}".format(e))
            _kick_token_cache['last_error_log'] = now
        return None


def kick_exchange_authorization_code(client_id, client_secret, code, redirect_uri=KICK_DEFAULT_REDIRECT_URI, timeout=10, code_verifier=''):
    global kick_user_oauth_cache
    client_id = (client_id or '').strip()
    client_secret = (client_secret or '').strip()
    code = (code or '').strip()
    redirect_uri = (redirect_uri or KICK_DEFAULT_REDIRECT_URI).strip()
    if not client_id or not client_secret or not code:
        return None
    form_data = {
        'grant_type': 'authorization_code',
        'client_id': client_id,
        'client_secret': client_secret,
        'redirect_uri': redirect_uri,
        'code': code,
    }
    if (code_verifier or '').strip():
        form_data['code_verifier'] = (code_verifier or '').strip()
    data = urllib.parse.urlencode(form_data).encode('utf-8')
    headers = {
        'User-Agent': 'Mozilla/5.0',
        'Content-Type': 'application/x-www-form-urlencoded',
        'Accept': 'application/json',
    }
    try:
        req = urllib.request.Request('https://id.kick.com/oauth/token', data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            payload = json.loads(response.read().decode('utf-8'))
        access_token = (payload.get('access_token') or '').strip()
        refresh_token = (payload.get('refresh_token') or '').strip()
        expires_in = int(payload.get('expires_in', 3600) or 3600)
        scope = payload.get('scope') or ''
        if access_token:
            kick_user_oauth_cache = {
                'access_token': access_token,
                'refresh_token': refresh_token,
                'expires_at': time.time() + max(60, expires_in),
                'scope': scope,
            }
            oauth_manager.set_token("kick", payload, client_id=client_id)
            print('[Kick OAuth] access token отримано, scope={}'.format(scope or '-'))
            return payload
    except Exception as e:
        print('[Kick OAuth] code exchange failed: {}'.format(e))
        return None
    return None


def kick_fetch_public_channel(slug, client_id='', client_secret='', timeout=10, log_errors=True):
    slug = (slug or '').strip().lower()
    token = kick_get_app_access_token(client_id, client_secret, timeout=timeout)
    if not token or not slug:
        return None
    url = 'https://api.kick.com/public/v1/channels?slug={}'.format(urllib.parse.quote(slug))
    headers = {
        'Authorization': 'Bearer {}'.format(token),
        'Accept': 'application/json',
        'User-Agent': 'Mozilla/5.0'
    }
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            payload = json.loads(response.read().decode('utf-8'))
        if isinstance(payload, dict):
            data = payload.get('data')
            if isinstance(data, list):
                return data[0] if data else None
            if isinstance(data, dict):
                return data
            if payload.get('slug'):
                return payload
        if isinstance(payload, list):
            return payload[0] if payload else None
        return None
    except Exception as e:
        if log_errors:
            log_status("Kick", "Офіційний API channels помилка: {}".format(e))
        return None


def kick_refresh_user_token(timeout=10):
    global kick_user_oauth_cache
    refresh_token = (kick_user_oauth_cache.get('refresh_token') or '').strip()
    client_id = (config.get('kick_client_id', '') or '').strip()
    client_secret = (config.get('kick_client_secret', '') or '').strip()
    if not refresh_token or not client_id or not client_secret:
        return None
    form_data = {
        'grant_type': 'refresh_token',
        'client_id': client_id,
        'client_secret': client_secret,
        'refresh_token': refresh_token,
    }
    data = urllib.parse.urlencode(form_data).encode('utf-8')
    headers = {
        'User-Agent': 'Mozilla/5.0',
        'Content-Type': 'application/x-www-form-urlencoded',
        'Accept': 'application/json',
    }
    try:
        req = urllib.request.Request('https://id.kick.com/oauth/token', data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            payload = json.loads(response.read().decode('utf-8'))
        access_token = (payload.get('access_token') or '').strip()
        new_refresh_token = (payload.get('refresh_token') or refresh_token).strip()
        expires_in = int(payload.get('expires_in', 3600) or 3600)
        if access_token:
            kick_user_oauth_cache = {
                'access_token': access_token,
                'refresh_token': new_refresh_token,
                'expires_at': time.time() + max(60, expires_in),
                'scope': payload.get('scope') or kick_user_oauth_cache.get('scope', ''),
            }
            oauth_manager.set_token("kick", payload, client_id=client_id)
            return access_token
    except urllib.error.HTTPError as e:
        try:
            error_body = e.read().decode('utf-8', errors='ignore')
        except Exception:
            error_body = ''
        print('[Kick OAuth] Не вдалося оновити токен: HTTP {} {}. {}'.format(e.code, e.reason, error_body[:300]))
    except Exception as e:
        print('[Kick OAuth] Не вдалося оновити токен: {}'.format(e))
    return None


def kick_user_access_token():
    # Kick user-токени живуть ~1 годину (документовано офіційно), а стрім
    # зазвичай довший - тому оновлюємо завчасно (за 60 сек до закінчення),
    # інакше дії модерації почнуть мовчки падати посеред ефіру.
    cached_token = (kick_user_oauth_cache.get('access_token') or '').strip()
    if cached_token and time.time() < float(kick_user_oauth_cache.get('expires_at', 0) or 0) - 60:
        return cached_token
    refreshed = kick_refresh_user_token()
    return refreshed or (cached_token or None)


_kick_broadcaster_cache = {'broadcaster_id': '', 'ts': 0.0}


def kick_resolve_broadcaster_id():
    global _kick_broadcaster_cache
    now = time.time()
    if _kick_broadcaster_cache['broadcaster_id'] and now - _kick_broadcaster_cache['ts'] < 600:
        return _kick_broadcaster_cache['broadcaster_id']
    slug = extract_kick_slug(config.get('kick_chat_url', ''))
    if not slug:
        return ''
    channel = kick_fetch_public_channel(slug, config.get('kick_client_id', ''), config.get('kick_client_secret', ''), log_errors=False)
    broadcaster_id = str((channel or {}).get('broadcaster_user_id') or '').strip()
    if broadcaster_id:
        _kick_broadcaster_cache = {'broadcaster_id': broadcaster_id, 'ts': now}
    return broadcaster_id


def kick_api_request(url, method='GET', payload=None, timeout=10):
    token = kick_user_access_token()
    if not token:
        return None, "Немає дійсного Kick OAuth токена - авторизуйтесь у налаштуваннях"
    headers = {
        'Authorization': 'Bearer {}'.format(token),
        'Accept': 'application/json',
        'User-Agent': 'Mozilla/5.0',
    }
    data = None
    if payload is not None:
        headers['Content-Type'] = 'application/json'
        data = json.dumps(payload).encode('utf-8')
    try:
        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        with urllib.request.urlopen(req, timeout=timeout) as response:
            body = response.read().decode('utf-8', errors='ignore').strip()
            return (json.loads(body) if body else {}), None
    except urllib.error.HTTPError as e:
        try:
            error_body = e.read().decode('utf-8', errors='ignore')
        except Exception:
            error_body = ''
        msg = 'HTTP {} {}: {}'.format(e.code, e.reason, error_body[:300])
        print('[Kick Moderation] {}'.format(msg))
        return None, msg
    except Exception as e:
        print('[Kick Moderation] {}'.format(e))
        return None, str(e)


def kick_subscribe_to_events():
    """Реєструє Kick webhook-підписки на канал (channel.followed / channel.subscription.*),
    інакше Kick ніколи не надішле ці events на наш /callback/kick_webhook - і алерти мовчать,
    навіть якщо OAuth пройшов і kk_enable_follows/kk_enable_subs увімкнені.
    Викликається один раз одразу після успішного обміну authorization code (і при потребі
    повторно), ідемпотентно - спершу читає вже наявні підписки і не дублює їх."""
    wanted = []
    if (config.get('kk_enable_follows', True)):
        wanted.append(('channel.followed', 1))
    if (config.get('kk_enable_subs', True)):
        wanted.append(('channel.subscription.new', 1))
        wanted.append(('channel.subscription.renewal', 1))
        wanted.append(('channel.subscription.gifts', 1))
    if not wanted:
        return False, "Підписки на фоловерів/підписки вимкнені в налаштуваннях - нічого реєструвати"
    existing, err = kick_api_request('https://api.kick.com/public/v1/events/subscriptions', method='GET')
    existing_names = set()
    if existing and isinstance(existing.get('data'), list):
        for row in existing['data']:
            existing_names.add((row.get('event') or '').strip())
    to_create = [{'name': name, 'version': version} for name, version in wanted if name not in existing_names]
    if not to_create:
        print('[Kick Events] Усі потрібні webhook-підписки вже зареєстровані ({})'.format(', '.join(sorted(existing_names)) or '-'))
        return True, None
    body = {'method': 'webhook', 'events': to_create}
    result, err = kick_api_request('https://api.kick.com/public/v1/events/subscriptions', method='POST', payload=body)
    if err:
        print('[Kick Events] Не вдалося зареєструвати webhook-підписки {}: {}'.format([e['name'] for e in to_create], err))
        return False, err
    failed = []
    if result and isinstance(result.get('data'), list):
        for row in result['data']:
            if row.get('error'):
                failed.append('{}: {}'.format(row.get('name'), row.get('error')))
    if failed:
        print('[Kick Events] Частина підписок не зареєструвалась: {}'.format('; '.join(failed)))
        return False, '; '.join(failed)
    print('[Kick Events] Зареєстровано webhook-підписки: {}'.format([e['name'] for e in to_create]))
    return True, None


def kick_moderation_action(action, **kwargs):
    """Єдина точка входу для дій модерації Kick: 'timeout' | 'ban' | 'unban' | 'delete'.
    Офіційний Kick Public API (docs.kick.com): POST/DELETE
    /public/v1/moderation/bans (потребує scope moderation:ban) і DELETE
    /public/v1/chat/:message_id (потребує scope moderation:chat_message:manage,
    додано в офіційний API 02/12/2025). Повертає {'ok': bool, 'error': str|None}."""
    broadcaster_id = kick_resolve_broadcaster_id()
    if not broadcaster_id:
        return {'ok': False, 'error': "Не вдалося визначити broadcaster_id Kick (перевірте посилання на канал у налаштуваннях)"}

    if action in ('timeout', 'ban'):
        user_id = (kwargs.get('user_id') or '').strip()
        if not user_id:
            return {'ok': False, 'error': "Немає Kick user_id для цього повідомлення (оновіть сторінку чату, якщо повідомлення прийшло до оновлення скрипта)"}
        try:
            body = {'broadcaster_user_id': int(broadcaster_id), 'user_id': int(user_id), 'reason': (kwargs.get('reason') or 'Порушення правил чату')[:100]}
        except (TypeError, ValueError):
            return {'ok': False, 'error': 'Некоректний user_id'}
        if action == 'timeout':
            duration = int(kwargs.get('duration_minutes') or 10)
            body['duration'] = max(1, min(duration, 10080))  # Kick max = 7 днів
        result, error = kick_api_request('https://api.kick.com/public/v1/moderation/bans', method='POST', payload=body)
        if result is None:
            error = '{} [payload={}, token scope="{}"]'.format(error, json.dumps(body, ensure_ascii=False), kick_user_oauth_cache.get('scope', ''))
        return {'ok': result is not None, 'error': error}

    if action == 'unban':
        user_id = (kwargs.get('user_id') or '').strip()
        if not user_id:
            return {'ok': False, 'error': 'Немає user_id'}
        try:
            body = {'broadcaster_user_id': int(broadcaster_id), 'user_id': int(user_id)}
        except (TypeError, ValueError):
            return {'ok': False, 'error': 'Некоректний user_id'}
        result, error = kick_api_request('https://api.kick.com/public/v1/moderation/bans', method='DELETE', payload=body)
        if result is None:
            error = '{} [payload={}, token scope="{}"]'.format(error, json.dumps(body, ensure_ascii=False), kick_user_oauth_cache.get('scope', ''))
        return {'ok': result is not None, 'error': error}

    if action == 'delete':
        message_id = (kwargs.get('message_id') or '').strip()
        if not message_id:
            return {'ok': False, 'error': "Немає Kick message_id для цього повідомлення"}
        url = 'https://api.kick.com/public/v1/chat/{}'.format(urllib.parse.quote(message_id))
        result, error = kick_api_request(url, method='DELETE')
        if result is None:
            error = '{} [message_id={}, broadcaster_user_id={}, token scope="{}"]'.format(error, message_id, broadcaster_id, kick_user_oauth_cache.get('scope', ''))
        return {'ok': result is not None, 'error': error}

    if action == 'reply':
        text = (kwargs.get('text') or '').strip()
        message_id = (kwargs.get('message_id') or '').strip()
        if not text:
            return {'ok': False, 'error': 'Немає тексту відповіді'}
        if not message_id:
            return {'ok': False, 'error': "Немає Kick message_id для відповіді (повідомлення прийшло до оновлення скрипта)"}
        try:
            body = {'broadcaster_user_id': int(broadcaster_id), 'content': text[:500], 'type': 'user', 'reply_to_message_id': message_id}
        except (TypeError, ValueError):
            return {'ok': False, 'error': 'Некоректний broadcaster_id'}
        result, error = kick_api_request('https://api.kick.com/public/v1/chat', method='POST', payload=body)
        if result is None:
            error = '{} [broadcaster_user_id={}, token scope="{}"] - можливо потрібна переавторизація зі скоупом chat:write'.format(error, broadcaster_id, kick_user_oauth_cache.get('scope', ''))
        return {'ok': result is not None, 'error': error}

    return {'ok': False, 'error': 'Невідома дія модерації'}


def extract_kick_slug(value):
    value = (value or '').strip()
    if not value:
        return None
    normalized = value
    if not normalized.startswith(('http://', 'https://')):
        if '/' not in normalized and 'kick.com' not in normalized:
            return normalized.strip().strip('/').lower()
        normalized = 'https://' + normalized
    try:
        parsed = urlparse(normalized)
        host = (parsed.netloc or '').lower()
        path = (parsed.path or '').strip('/')
        if 'kick.com' not in host and host:
            return None
        parts = [p for p in path.split('/') if p]
        if not parts:
            return None
        if parts[0] == 'popout' and len(parts) >= 2:
            return parts[1].lower()
        return parts[0].lower()
    except:
        return None


def build_ws_frame(payload, opcode=0x1):
    if isinstance(payload, str):
        payload = payload.encode('utf-8')
    frame = bytearray()
    frame.append(0x80 | (opcode & 0x0F))
    length = len(payload)
    if length < 126:
        frame.append(0x80 | length)
    elif length < 65536:
        frame.append(0x80 | 126)
        frame.extend(length.to_bytes(2, 'big'))
    else:
        frame.append(0x80 | 127)
        frame.extend(length.to_bytes(8, 'big'))
    mask = os.urandom(4)
    frame.extend(mask)
    for i, b in enumerate(payload):
        frame.append(b ^ mask[i % 4])
    return bytes(frame)


def read_ws_frame(sock, recv_buffer):
    while True:
        while len(recv_buffer) < 2:
            chunk = sock.recv(4096)
            if not chunk:
                raise ConnectionError("WebSocket closed")
            recv_buffer += chunk

        first = recv_buffer[0]
        second = recv_buffer[1]
        opcode = first & 0x0F
        masked = (second & 0x80) != 0
        length = second & 0x7F
        offset = 2

        if length == 126:
            while len(recv_buffer) < 4:
                chunk = sock.recv(4096)
                if not chunk:
                    raise ConnectionError("WebSocket closed")
                recv_buffer += chunk
            length = int.from_bytes(recv_buffer[2:4], 'big')
            offset = 4
        elif length == 127:
            while len(recv_buffer) < 10:
                chunk = sock.recv(4096)
                if not chunk:
                    raise ConnectionError("WebSocket closed")
                recv_buffer += chunk
            length = int.from_bytes(recv_buffer[2:10], 'big')
            offset = 10

        if masked:
            while len(recv_buffer) < offset + 4:
                chunk = sock.recv(4096)
                if not chunk:
                    raise ConnectionError("WebSocket closed")
                recv_buffer += chunk
            mask_key = recv_buffer[offset:offset+4]
            offset += 4
        else:
            mask_key = None

        while len(recv_buffer) < offset + length:
            chunk = sock.recv(4096)
            if not chunk:
                raise ConnectionError("WebSocket closed")
            recv_buffer += chunk

        payload = recv_buffer[offset:offset+length]
        recv_buffer = recv_buffer[offset+length:]

        if mask_key is not None:
            payload = bytes([payload[i] ^ mask_key[i % 4] for i in range(len(payload))])
        return opcode, payload, recv_buffer


def kick_worker(session_id):
    global config
    kick_input = config["kick_chat_url"].strip()
    if not kick_input:
        log_status("Kick", "Пропуск: не вказано посилання на канал")
        return

    slug = extract_kick_slug(kick_input)
    if not slug:
        log_status("Kick", "Не вдалось визначити slug каналу з: {}".format(kick_input))
        return

    channel_url = "https://kick.com/{}".format(slug)
    channel_data = kick_fetch_json("https://kick.com/api/v2/channels/{}".format(urllib.parse.quote(slug)), referer=channel_url, timeout=10)
    if not channel_data:
        log_status("Kick", "Не вдалося отримати дані channel/chatroom.")
        return

    chatroom = channel_data.get("chatroom") or channel_data.get("livestream", {}).get("chatroom") or {}
    chatroom_id = chatroom.get("id")
    if not chatroom_id:
        log_status("Kick", "У каналу не знайдено chatroom.id")
        return

    pusher_key = "32cbd69e4b950bf97679"
    ws_host = "ws-us2.pusher.com"
    ws_path = "/app/{}?protocol=7&client=js&version=8.4.0-rc2&flash=false".format(pusher_key)

    recv_buffer = b""
    sock = None
    reconnect_delay = 5
    max_reconnect_delay = 60

    while session_is_current(session_id):
        try:
            raw_sock = socket.create_connection((ws_host, 443), timeout=10)
            context = ssl.create_default_context()
            sock = context.wrap_socket(raw_sock, server_hostname=ws_host)
            sock.settimeout(10.0)

            ws_key = base64.b64encode(os.urandom(16)).decode('utf-8')
            handshake = "GET {} HTTP/1.1\r\nHost: {}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nOrigin: https://kick.com\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Key: {}\r\n\r\n".format(ws_path, ws_host, ws_key)
            sock.sendall(handshake.encode('utf-8'))

            response = b""
            while b"\r\n\r\n" not in response:
                chunk = sock.recv(4096)
                if not chunk:
                    raise ConnectionError("Немає відповіді на WebSocket handshake")
                response += chunk

            header_bytes, recv_buffer = response.split(b"\r\n\r\n", 1)
            header_text = header_bytes.decode('utf-8', 'ignore')
            if "101" not in header_text:
                raise ConnectionError("Handshake failed: {}".format(header_text.splitlines()[0] if header_text else 'unknown'))

            log_status("Kick", "WebSocket підключено, chatroom={}".format(chatroom_id))

            socket_id = None
            start_wait = time.time()
            while session_is_current(session_id) and time.time() - start_wait < 15:
                opcode, payload, recv_buffer = read_ws_frame(sock, recv_buffer)
                if opcode == 0x9:
                    sock.sendall(build_ws_frame(payload, opcode=0xA))
                    continue
                if opcode == 0x8:
                    raise ConnectionError("Сервер закрив WebSocket до subscribe")
                if opcode != 0x1:
                    continue
                msg = json.loads(payload.decode('utf-8', 'ignore'))
                if msg.get("event") == "pusher:connection_established":
                    data_raw = msg.get("data", "{}")
                    data = json.loads(data_raw) if isinstance(data_raw, str) else data_raw
                    socket_id = data.get("socket_id")
                    break

            if not socket_id:
                raise ConnectionError("Не отримано socket_id від Pusher")

            subscribe_msg = {"event": "pusher:subscribe", "data": {"auth": "", "channel": "chatrooms.{}.v2".format(chatroom_id)}}
            sock.sendall(build_ws_frame(json.dumps(subscribe_msg)))
            log_status("Kick", "Підписка на chatrooms.{}.v2 відправлена".format(chatroom_id))

            sock.settimeout(5.0)
            last_keepalive = time.time()
            while session_is_current(session_id):
                try:
                    opcode, payload, recv_buffer = read_ws_frame(sock, recv_buffer)
                    if opcode == 0x9:
                        sock.sendall(build_ws_frame(payload, opcode=0xA))
                        continue
                    if opcode == 0x8:
                        raise ConnectionError("Сервер закрив WebSocket")
                    if opcode != 0x1:
                        continue

                    msg = json.loads(payload.decode('utf-8', 'ignore'))
                    event = msg.get("event")
                    if event == "pusher:ping":
                        sock.sendall(build_ws_frame(json.dumps({"event": "pusher:pong", "data": {}})))
                        last_keepalive = time.time()
                        continue
                    if event in ("pusher:error", "pusher:subscription_error"):
                        raise ConnectionError("Pusher error: {}".format(msg.get('data')))

                    if event == "App\\Events\\ChatMessageEvent":
                        raw_data = msg.get("data", "{}")
                        if isinstance(raw_data, (bytes, bytearray)):
                            raw_data = raw_data.decode('utf-8', 'ignore')
                        data = json.loads(raw_data) if isinstance(raw_data, str) else raw_data
                        sender = data.get("sender", {}) or {}
                        content = (data.get("content") or '').strip()
                        name = sender.get("username") or sender.get("slug") or sender.get("name") or "Unknown"
                        is_mod = bool(sender.get("is_staff") or sender.get("is_moderator"))
                        kick_user_id = str(sender.get("id") or '').strip()
                        kick_msg_id = str(data.get("id") or '').strip()
                        if name and content and dedup_is_new('kick', kick_msg_id):
                            c_name, tts_text = process_filters_and_tts("kick", name, name, content, is_mod, False, False)
                            if c_name:
                                add_to_buffer("kick", c_name, content, tts_text, is_mod, False, username=name, source_display_name=name, platform_user_id=kick_user_id, platform_message_id=kick_msg_id)

                except socket.timeout:
                    if time.time() - last_keepalive >= 25:
                        sock.sendall(build_ws_frame(json.dumps({"event": "pusher:ping", "data": {}})))
                        last_keepalive = time.time()
                    continue
                except Exception as e:
                    log_status("Kick", "Помилка підключення/читання: {}".format(e))
                    break

        except Exception as e:
            log_status("Kick", "Помилка: {}".format(e))
            log_status("Kick", "Перепідключення через {} сек...".format(reconnect_delay))
            if sock:
                try:
                    sock.close()
                except:
                    pass
            time.sleep(reconnect_delay)
            reconnect_delay = min(reconnect_delay * 2, max_reconnect_delay)
            continue
        finally:
            if sock:
                try:
                    sock.close()
                except:
                    pass
            if not session_is_current(session_id):
                log_status("Kick", "З'єднання закрите через перезапуск сервісів")
                break
            reconnect_delay = 5
            log_status("Kick", "З'єднання закрите, перепідключення через 5 сек...")
            time.sleep(5)


def tiktok_worker(session_id):
    global config, tiktok_like_tracker, tiktok_gift_tracker, processed_comment_ids, processed_gift_ids, processed_like_ids, processed_share_ids, tiktok_recent_comment_fingerprints, tiktok_recent_comment_simple_fingerprints, tiktok_live_viewer_count, tiktok_live_is_active, announced_follower_joins
    if not TIKTOK_AVAILABLE:
        tiktok_live_viewer_count = 0
        tiktok_live_is_active = False
        log_status("TikTok", "TikTokLive не завантажена, пропускаємо")
        return

    username = config["tt_username"].strip().lstrip('@')
    if not username:
        tiktok_live_viewer_count = 0
        tiktok_live_is_active = False
        log_status("TikTok", "Не вказано username, пропускаємо")
        return

    log_status("TikTok", "Запуск потоку для @{}".format(username))
    reconnect_attempts = 0

    while session_is_current(session_id):
        try:
            print('[TikTok] Підключення до @{}...'.format(username))
            print('[TikTok Debug] likes_enabled={} | like_threshold={} | show_likes_in_chat={} | username=@{}'.format(bool(config.get('tt_enable_likes', False)), int(config.get('tt_like_threshold', 100) or 100), bool(config.get('tt_show_likes_in_chat', True)), username))
            connection_started_at = time.time()
            backlog_cutoff_ts = get_tiktok_last_comment_timestamp()
            backlog_guard_until = connection_started_at + TIKTOK_BACKLOG_SETTLE_SECONDS
            strict_reconnect_guard_until = connection_started_at + TIKTOK_RECONNECT_DROP_SECONDS
            strict_reconnect_guard = backlog_cutoff_ts > 0 or reconnect_attempts > 0

            sign_api_key = (config.get("tt_sign_api_key", "") or "").strip()
            if TIKTOK_WEBDEFAULTS_AVAILABLE and sign_api_key:
                TikTokWebDefaults.tiktok_sign_api_key = sign_api_key
                if reconnect_attempts == 0:
                    print("[TikTok] 🔑 Euler Stream API-ключ застосовано — ліміт підключень підвищено")
            elif reconnect_attempts == 0:
                print("[TikTok] ⚠️ Euler Stream API-ключ не задано — підключення підуть по анонімному (низькому) ліміту, часті SIGN_NOT_200/RATE_LIMIT очікувані. Безкоштовний ключ: eulerstream.com")

            client = TikTokLiveClient(unique_id=username)

            if RoomUserSeqEvent is not None:
                @client.on(RoomUserSeqEvent)
                async def on_viewer_update(event):
                    global tiktok_live_viewer_count, tiktok_live_is_active, tiktok_last_viewer_update_ts, tiktok_last_viewer_debug_ts
                    try:
                        total_viewers = tiktok_extract_viewer_count(event)
                        raw_debug = tiktok_plain_data(event, depth=2)

                        room_info_debug = None
                        if total_viewers is None:
                            room_info = tiktok_try_retrieve_room_info(username, min_refresh_interval=15)
                            if isinstance(room_info, dict) and room_info:
                                try:
                                    fallback_user_count = int(room_info.get('user_count', 0) or 0)
                                except Exception:
                                    fallback_user_count = 0
                                try:
                                    fallback_total_user = int(((room_info.get('stats') or {}).get('total_user', 0)) or 0)
                                except Exception:
                                    fallback_total_user = 0
                                try:
                                    fallback_status = int(room_info.get('status', 0) or 0)
                                except Exception:
                                    fallback_status = 0
                                room_info_debug = {'status': fallback_status, 'user_count': fallback_user_count, 'total_user': fallback_total_user}
                                if fallback_user_count >= 0:
                                    total_viewers = fallback_user_count

                        if total_viewers is not None:
                            changed = int(tiktok_live_viewer_count or 0) != int(total_viewers or 0)
                            tiktok_live_viewer_count = total_viewers
                            tiktok_live_is_active = True
                            tiktok_last_viewer_update_ts = time.time()
                            if changed or (time.time() - float(tiktok_last_viewer_debug_ts or 0)) >= 15:
                                tiktok_last_viewer_debug_ts = time.time()
                                print('[TikTok Analytics] viewer_event raw={} | room_info={} -> current={}'.format(raw_debug, room_info_debug, total_viewers))
                        else:
                            if (time.time() - float(tiktok_last_viewer_debug_ts or 0)) >= 15:
                                tiktok_last_viewer_debug_ts = time.time()
                                print('[TikTok Analytics] viewer_event without current field | raw={} | room_info={}'.format(raw_debug, room_info_debug))
                    except Exception as e:
                        print("[TikTok Analytics] Помилка viewer_update: {}".format(e))

            @client.on(CommentEvent)
            async def on_chat(event):
                global tiktok_live_is_active
                if not config["tt_enable_chat"]:
                    return
                try:
                    tiktok_mark_live_activity()
                    comment_id = get_tiktok_event_id(event)
                    comment_time = tiktok_event_timestamp_seconds(event)
                    current_time = time.time()
                    settle_mode = current_time < backlog_guard_until
                    reconnect_guard_mode = strict_reconnect_guard and current_time < strict_reconnect_guard_until

                    if reconnect_guard_mode:
                        remember_tiktok_comment_timestamp(comment_time or current_time)
                        return

                    if comment_time and current_time - comment_time > 120:
                        return
                    if comment_time and comment_time < (connection_started_at - TIKTOK_HISTORY_GUARD_SECONDS):
                        return
                    if settle_mode and backlog_cutoff_ts and comment_time and comment_time <= (backlog_cutoff_ts + TIKTOK_BACKLOG_TS_SLACK_SECONDS):
                        return

                    if comment_id:
                        if not dedup_is_new('tiktok', comment_id, 'comment'):
                            return

                    user = event.user.nickname if event.user.nickname else event.user.unique_id
                    user_id = event.user.unique_id if hasattr(event.user, 'unique_id') else user
                    message_text = event.comment
                    record_tiktok_viewer(user_id, user, tiktok_extract_avatar_url(event.user), 'message', message_text=message_text)

                    if remember_tiktok_comment_fingerprint(user_id, message_text, comment_time, settle_mode=settle_mode):
                        return

                    # Реальний статус автора замість жорсткого False/False — впливає на
                    # "TTS тільки для підписників/модераторів" і на звільнення від TTS-кулдауну.
                    try:
                        is_mod = bool(getattr(event.user, 'is_moderator', False))
                    except Exception:
                        is_mod = False
                    try:
                        is_broadcaster = bool(user_id) and str(user_id).strip().lower().lstrip('@') == username.strip().lower().lstrip('@')
                    except Exception:
                        is_broadcaster = False
                    try:
                        user_identity = getattr(event, 'user_identity', None)
                        is_subscriber = bool(getattr(user_identity, 'is_subscriber_of_anchor', False)) if user_identity is not None else False
                    except Exception:
                        is_subscriber = False

                    c_name, tts_text = process_filters_and_tts("tiktok", user, user, message_text, is_mod, is_broadcaster, is_subscriber)
                    if c_name:
                        print("[TikTok Chat] {}: {}".format(user, message_text))
                        add_to_buffer("tiktok", c_name, message_text, tts_text, is_mod, is_broadcaster, priority=PRIORITY_MAP["chat"], username=user, source_display_name=user)
                        remember_tiktok_comment_timestamp(comment_time or current_time)
                except Exception as e:
                    print("[TikTok Chat] Помилка: {}".format(e))

            @client.on(FollowEvent)
            async def on_follow(event):
                global tiktok_live_is_active
                if not config["tt_enable_follows"]:
                    return
                try:
                    tiktok_mark_live_activity()
                    user = event.user.nickname if event.user.nickname else event.user.unique_id
                    unique_id = event.user.unique_id if hasattr(event.user, 'unique_id') else user
                    follow_avatar = tiktok_extract_avatar_url(event.user) or ""
                    record_tiktok_viewer(unique_id, user, follow_avatar, 'follow')
                    text = format_tiktok_text(config.get("tt_follow_template", "{user} підписався на TikTok"), user=user, gift=" ", count=1)
                    show_avatar = bool(config.get("tt_follow_show_avatar", True))
                    show_nick = bool(config.get("tt_follow_show_nick", True))
                    print("[TikTok Follow] {} | avatar={} | nick={}".format(user, int(bool(follow_avatar and show_avatar)), int(show_nick)))
                    emit_tiktok_alert(
                        "follow",
                        user,
                        text,
                        "Новий підписник TikTok",
                        "follow",
                        username=unique_id,
                        source_display_name=user,
                        voice_id=(config.get('tt_follow_voice_id') or '').strip(),
                        force_chat=True,
                        avatar_url=follow_avatar if show_avatar else "",
                        show_user=show_nick
                    )
                except Exception as e:
                    print("[TikTok Follow] Помилка: {}".format(e))

            @client.on(GiftEvent)
            async def on_gift(event):
                global tiktok_live_is_active
                if not config["tt_enable_gifts"]:
                    return
                try:
                    tiktok_mark_live_activity()
                    gift = getattr(event, 'gift', None)
                    if gift is None:
                        print("[TikTok Gift] Пропуск: gift=None")
                        return

                    user = event.user.nickname if event.user.nickname else event.user.unique_id
                    unique_id = event.user.unique_id if hasattr(event.user, 'unique_id') else user
                    gift_name = getattr(gift, 'name', None) or 'подарунок'
                    gift_type = int(getattr(gift, 'type', 0) or 0)
                    repeat_count = int(getattr(event, 'repeat_count', 0) or getattr(event, 'combo_count', 0) or 1)
                    repeat_count = max(1, repeat_count)
                    streaking = bool(getattr(event, 'streaking', False))
                    repeat_end = int(getattr(event, 'repeat_end', 0) or 0)
                    order_id = str(getattr(event, 'order_id', None) or '')
                    group_id = str(getattr(event, 'group_id', None) or '')
                    dedupe_id = order_id or group_id or "{}::{}::{}".format(get_tiktok_event_id(event) or unique_id, gift_name, gift_type)
                    voice_id = (config.get('tt_gift_voice_id') or '').strip()
                    gift_key = "{}::{}::{}".format(unique_id, gift_name, dedupe_id)

                    if gift_type == 1:
                        with buffer_lock:
                            tracker = tiktok_gift_tracker.setdefault(gift_key, {
                                "count": 0,
                                "user": user,
                                "gift_name": gift_name,
                                "timer": None,
                                "username": unique_id,
                                "source_display_name": user,
                                "voice_id": voice_id,
                                "dedupe_id": dedupe_id,
                                "diamond_count": int(getattr(gift, 'diamond_count', 0) or 0),
                                "avatar_url": tiktok_extract_avatar_url(event.user),
                            })
                            tracker["count"] = max(int(tracker.get("count", 0) or 0), repeat_count)
                            tracker["user"] = user
                            tracker["gift_name"] = gift_name
                            tracker["username"] = unique_id
                            tracker["source_display_name"] = user
                            tracker["voice_id"] = voice_id
                            tracker["dedupe_id"] = dedupe_id
                            tracker["diamond_count"] = int(getattr(gift, 'diamond_count', 0) or 0)
                            timer = tracker.get("timer")
                            if timer:
                                try:
                                    timer.cancel()
                                except Exception:
                                    pass
                                tracker["timer"] = None
                            if streaking and not repeat_end:
                                timer = threading.Timer(TIKTOK_GIFT_AGGREGATION_WINDOW, lambda: flush_tiktok_gift_aggregation(gift_key))
                                timer.daemon = True
                                tracker["timer"] = timer
                                timer.start()
                                print("[TikTok Gift] buffering streak {}: {} x{}".format(user, gift_name, repeat_count))
                                return
                        flush_tiktok_gift_aggregation(gift_key)
                        return

                    if not dedup_is_new('tiktok', dedupe_id, 'gift'):
                        return

                    text = format_tiktok_text(config.get("tt_gift_template", "{user} відправив подарунок {gift} x{count}"), user=user, gift=gift_name, count=repeat_count)
                    print("[TikTok Gift] {}: {} x{}".format(user, gift_name, repeat_count))
                    record_tiktok_viewer(unique_id, user, tiktok_extract_avatar_url(event.user), 'gift', gift_diamonds=int(getattr(gift, 'diamond_count', 0) or 0) * repeat_count, gift_name=gift_name, gift_count=repeat_count)
                    emit_tiktok_alert(
                        "gift",
                        user,
                        text,
                        "Подарунок TikTok",
                        "gift",
                        username=unique_id,
                        source_display_name=user,
                        voice_id=voice_id,
                        force_chat=True
                    )
                except Exception as e:
                    print("[TikTok Gift] Помилка: {}".format(e))

            @client.on(LikeEvent)
            async def on_like(event):
                global tiktok_live_is_active
                if not config["tt_enable_likes"]:
                    print('[TikTok Like Debug] skipped because tt_enable_likes=False')
                    return
                try:
                    tiktok_mark_live_activity()
                    current_time = time.time()

                    user = event.user.nickname if event.user.nickname else event.user.unique_id
                    unique_id = event.user.unique_id if hasattr(event.user, 'unique_id') else user
                    like_avatar = tiktok_extract_avatar_url(event.user) or ""
                    threshold = max(1, int(config.get("tt_like_threshold", 100) or 100))
                    like_increment, like_user_total, like_stream_total, like_debug = tiktok_extract_like_counts(event)

                    like_event_id = get_tiktok_event_id(event)
                    if like_event_id:
                        dedupe_key = "{}::{}::{}::{}::{}".format(like_event_id, unique_id, like_increment, like_user_total, like_stream_total)
                        if not dedup_is_new('tiktok', dedupe_key, 'like'):
                            return

                    announcements = []
                    with buffer_lock:
                        stale_before = current_time - 180
                        for stale_key in list(tiktok_like_tracker.keys()):
                            if float(tiktok_like_tracker.get(stale_key, {}).get("last_seen", 0) or 0) < stale_before:
                                tiktok_like_tracker.pop(stale_key, None)

                        tracker = tiktok_like_tracker.setdefault(unique_id, {
                            "count": 0,
                            "announced_step": 0,
                            "user": user,
                            "last_seen": 0,
                            "last_total": 0,
                            "last_stream_total": 0,
                            "last_event_count": 0,
                            "last_event_ts": 0,
                        })
                        if tracker.get("last_seen") and current_time - float(tracker.get("last_seen", 0) or 0) > 120:
                            tracker["count"] = 0
                            tracker["announced_step"] = 0
                            tracker["last_total"] = 0
                            tracker["last_stream_total"] = 0
                            tracker["last_event_count"] = 0
                            tracker["last_event_ts"] = 0
                        tracker["user"] = user
                        tracker["last_seen"] = current_time

                        effective_increment = 0
                        source_mode = "none"
                        last_total = int(tracker.get("last_total", 0) or 0)
                        if like_user_total > 0:
                            # Authoritative source: TikTok's cumulative like total for
                            # this session/user only ever increases, so diffing against
                            # the last seen value is immune to duplicate/overlapping
                            # "count" bursts (see note below on why raw `count` alone
                            # is unreliable for this).
                            if like_user_total < last_total:
                                # Total was reset (TikTok occasionally does this) - use
                                # this event's own burst size as a safe minimum instead
                                # of computing a bogus negative delta.
                                effective_increment = like_increment if like_increment > 0 else 0
                                source_mode = "user_total_reset"
                            elif like_user_total > last_total:
                                effective_increment = like_user_total - last_total
                                source_mode = "user_total_delta"
                            else:
                                source_mode = "user_total_unchanged"
                            tracker["last_total"] = max(last_total, like_user_total)
                        elif like_increment > 0:
                            # No cumulative total on this event - trust the burst size
                            # directly. IMPORTANT: `count` is the size of THIS batch of
                            # likes, not a running total, so it must NOT be diffed
                            # against the previous event's `count` (that comparison
                            # previously discarded almost every real like whenever two
                            # consecutive bursts happened to be the same size, e.g.
                            # count=15 followed by another count=15).
                            effective_increment = like_increment
                            source_mode = "increment_raw"
                        elif like_stream_total > 0:
                            tracker["last_stream_total"] = max(int(tracker.get("last_stream_total", 0) or 0), like_stream_total)

                        if effective_increment <= 0:
                            print('[TikTok Like Debug] ignored | user={} | raw_count={} | raw_user_total={} | raw_stream_total={} | threshold={} | tracker_count={} | last_total={} | last_stream_total={} | source={} | raw={}'.format(unique_id, like_increment, like_user_total, like_stream_total, threshold, tracker.get("count", 0), tracker.get("last_total", 0), tracker.get("last_stream_total", 0), source_mode, like_debug))
                            return

                        tracker["count"] = int(tracker.get("count", 0) or 0) + effective_increment
                        like_recorded = effective_increment
                        print('[TikTok Like Debug] user={} | raw_count={} | raw_user_total={} | raw_stream_total={} | effective_increment={} | aggregated={} | threshold={} | announced_step={} | source={}'.format(unique_id, like_increment, like_user_total, like_stream_total, effective_increment, tracker["count"], threshold, tracker.get("announced_step", 0), source_mode))
                        target_step = tracker["count"] // threshold

                        while tracker.get("announced_step", 0) < target_step:
                            tracker["announced_step"] += 1
                            announced_likes = tracker["announced_step"] * threshold
                            announce_user = tracker.get("user", user)
                            text = format_tiktok_text(config.get("tt_like_template", "{user} відправив {count} лайків"), user=announce_user, count=announced_likes, gift=" ")
                            announcements.append((announce_user, text, announced_likes))

                    try:
                        if like_recorded > 0:
                            record_tiktok_viewer(unique_id, user, tiktok_extract_avatar_url(event.user), 'like', like_count=like_recorded)
                    except Exception as rec_err:
                        print("[TikTok Like] Не вдалося записати в історію: {}".format(rec_err))

                    like_show_avatar = bool(config.get("tt_like_show_avatar", True))
                    for announce_user, text, announced_likes in announcements:
                        print("[TikTok Like] {}: {} (поріг {})".format(announce_user, announced_likes, threshold))
                        emit_tiktok_alert(
                            "like",
                            announce_user,
                            text,
                            "Лайки TikTok",
                            "like",
                            username=unique_id,
                            source_display_name=announce_user,
                            voice_id=(config.get('tt_like_voice_id') or '').strip(),
                            force_chat=config.get("tt_show_likes_in_chat", True),
                            avatar_url=like_avatar if like_show_avatar else "",
                            show_user=True
                        )
                except Exception as e:
                    print("[TikTok Like] Помилка: {}".format(e))

            if ShareEvent is not None:
                @client.on(ShareEvent)
                async def on_share(event):
                    global tiktok_live_is_active
                    if not config.get("tt_enable_shares", True):
                        return
                    try:
                        tiktok_mark_live_activity()
                        user = event.user.nickname if event.user.nickname else event.user.unique_id
                        unique_id = event.user.unique_id if hasattr(event.user, 'unique_id') else user

                        share_event_id = get_tiktok_event_id(event)
                        if share_event_id:
                            dedupe_key = "{}::{}".format(share_event_id, unique_id)
                            if not dedup_is_new('tiktok', dedupe_key, 'share'):
                                return

                        try:
                            users_joined = event.users_joined
                        except Exception:
                            users_joined = None

                        text = format_tiktok_text(
                            config.get("tt_share_template", "{user} зробив(-ла) репост трансляції!"),
                            user=user,
                            gift=" ",
                            count=1,
                            joined=(users_joined if users_joined is not None else "")
                        )
                        record_tiktok_viewer(unique_id, user, tiktok_extract_avatar_url(event.user), 'share')
                        print("[TikTok Share] {} (users_joined={})".format(user, users_joined))
                        emit_tiktok_alert(
                            "share",
                            user,
                            text,
                            "Репост TikTok",
                            "share",
                            username=unique_id,
                            source_display_name=user,
                            voice_id=(config.get('tt_share_voice_id') or '').strip(),
                            force_chat=config.get("tt_show_shares_in_chat", True)
                        )
                    except Exception as e:
                        print("[TikTok Share] Помилка: {}".format(e))

            if JoinEvent is not None:
                @client.on(JoinEvent)
                async def on_join(event):
                    global tiktok_live_is_active
                    try:
                        user_obj = getattr(event, 'user', None)
                        if user_obj is None:
                            return
                        join_user = user_obj.nickname if getattr(user_obj, 'nickname', None) else getattr(user_obj, 'unique_id', 'Глядач')
                        join_unique_id = getattr(user_obj, 'unique_id', join_user) or join_user
                        record_tiktok_viewer(join_unique_id, join_user, tiktok_extract_avatar_url(user_obj), 'join')

                        if not config.get("tt_enable_follower_join", False):
                            return
                        # follow_status: 0 = не підписаний, 1 = підписаний
                        # (одностороннє), 2 = взаємна підписка ("друзі").
                        # Нас цікавить будь-яка підписка (>=1), а не лише
                        # взаємна - тому напряму дивимось на follow_status,
                        # а не на готову властивість is_friend (яка вимагає >=2).
                        follow_info = getattr(user_obj, 'follow_info', None)
                        follow_status = getattr(follow_info, 'follow_status', 0) if follow_info is not None else 0
                        if not follow_status or follow_status < 1:
                            return
                        unique_id_for_dedupe = getattr(user_obj, 'unique_id', None) or getattr(user_obj, 'nickname', '') or ''
                        dedupe_key = unique_id_for_dedupe.lower().strip()
                        if dedupe_key and dedupe_key in announced_follower_joins:
                            return  # той самий підписник вже заходив на цьому стрімі - не дублюємо озвучку
                        if dedupe_key:
                            announced_follower_joins.add(dedupe_key)
                            if len(announced_follower_joins) > MAX_CACHE_SIZE:
                                announced_follower_joins.clear()
                        tiktok_mark_live_activity()
                        user = user_obj.nickname if getattr(user_obj, 'nickname', None) else getattr(user_obj, 'unique_id', 'Глядач')
                        unique_id = getattr(user_obj, 'unique_id', user) or user
                        text = format_tiktok_text(
                            config.get("tt_follower_join_template", "{user} (підписник) приєднався до ефіру!"),
                            user=user, gift=" ", count=1
                        )
                        print("[TikTok Join] Підписник зайшов на ефір: {}".format(user))
                        emit_tiktok_alert(
                            "follower_join",
                            user,
                            text,
                            "Підписник на ефірі",
                            "follow",
                            username=unique_id,
                            source_display_name=user,
                            voice_id=(config.get('tt_follower_join_voice_id') or '').strip(),
                            force_chat=config.get("tt_show_follower_join_in_chat", False)
                        )
                    except Exception as e:
                        print("[TikTok Join] Помилка: {}".format(e))

            import asyncio
            if sys.platform.startswith('win') and hasattr(asyncio, 'WindowsSelectorEventLoopPolicy'):
                asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)

            try:
                # Навмисно без wait_for()/timeout: client.connect() чекає
                # всередині await task аж до природного завершення стріму -
                # це штатна поведінка TikTokLive, а не "зависання". Будь-який
                # кінцевий timeout тут рано чи пізно спрацьовує навіть на
                # повністю здоровому з'єднанні й скасовує його - а обробка
                # скасування всередині TikTokLiveClient.connect() (v6.6.6)
                # синхронно викликає self._asyncio_loop.run_until_complete(
                # self.disconnect()) на вже запущеному loop, що падає з
                # "RuntimeError: This event loop is already running" і рве
                # з'єднання щоразу раніше часу.
                loop.run_until_complete(client.connect())
            finally:
                try:
                    if hasattr(client, "disconnect"):
                        result = client.disconnect()
                        if hasattr(result, "__await__"):
                            loop.run_until_complete(result)
                except:
                    pass
                pending = [task for task in asyncio.all_tasks(loop) if not task.done()]
                for task in pending:
                    task.cancel()
                if pending:
                    loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))
                loop.run_until_complete(loop.shutdown_asyncgens())
                asyncio.set_event_loop(None)
                loop.close()

            reconnect_attempts = 0
            print("[TikTok] З'єднання завершено, перевіряю перепідключення...")
            time.sleep(1)

        except Exception as e:
            print("[TikTok] Помилка: {}".format(e))
            is_user_offline = "UserOfflineError" in type(e).__name__ or "UserOfflineError" in str(e)
            if is_user_offline:
                tiktok_live_is_active = False
                tiktok_live_viewer_count = 0
            delay = 120 if is_user_offline else TIKTOK_RECONNECT_DELAYS[min(reconnect_attempts, len(TIKTOK_RECONNECT_DELAYS) - 1)]
            reconnect_attempts += 1
            if session_is_current(session_id):
                if is_user_offline:
                    print("[TikTok] Канал @{} офлайн, наступна перевірка через {} сек.".format(username, delay))
                else:
                    print("[TikTok] Перепідключення через {} сек.".format(delay))
                time.sleep(delay)


def bot_timer_worker(session_id):
    global config
    last_sent = time.time()
    while session_is_current(session_id):
        time.sleep(2.0)
        if config["bot_enabled"] and config["ad_text"]:
            if time.time() - last_sent > (config["ad_interval"] * 60):
                add_to_buffer("bot", "ОГОЛОШЕННЯ", config["ad_text"], config["ad_text"],
                              priority=PRIORITY_MAP["announce"], is_announce=True)
                last_sent = time.time()


# ============================================================================
# HTML СТОРІНКИ
# ============================================================================
def generate_tts_audio_html():
    return """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8">
<style>
html,body{margin:0;padding:0;background:transparent;width:100%;height:100%;overflow:hidden}
</style>
</head>
<body>
<script>
let maxId=0,ttsQueue=[],ttsActive=false;
let cCache={ttsTemplate:"{nickname} {comment}",ttsReadNicknames:true,ttsVolume:0.8,ttsEngine:"google",ttsVoice:"uk-UA",ttsSpeed:1.0,ringtoneUrl:null};
function detectLanguage(text){
if(/[іїєґІЄҐ]/.test(text))return "uk";
if(/[а-яёА-ЯЁ]/.test(text))return "ru";
return "en";
}
async function refreshConfig(){try{let r=await fetch('/get_config');let c=await r.json();cCache={...cCache,...c};updateTtsToggleBtn();}catch(e){}}
function duckBegin(){fetch('/api/audio_ducking',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'begin'})}).catch(()=>{});}
function duckEnd(){fetch('/api/audio_ducking',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'end'})}).catch(()=>{});}
function ttsHoldAnnounce(){const h=ttsQueue[0];if(!h||!h.isAnnounce)return false;if(ttsQueue.some(x=>!x.isAnnounce))return false;if((Date.now()-(h.queuedAt||0))<1500){setTimeout(playTTS,500);return true;}return false;}
function playTTS(){if(ttsQueue.length===0||ttsActive)return;ttsQueue.sort((a,b)=>(b.priority||0)-(a.priority||0)||((a.timestamp||0)-(b.timestamp||0)));if(ttsHoldAnnounce())return;ttsActive=true;duckBegin();let m=ttsQueue.shift();let nickname=cCache.ttsReadNicknames===false?'':(m.ttsDisplayName||m.name||'');let speakText=m.isAlert?m.text:cCache.ttsTemplate.replace('{nickname}',nickname).replace('{comment}',m.text).replace(/\\s+/g,' ').trim();let targetLang=detectLanguage(speakText);let speed=cCache.ttsSpeed||1.0;let engine=(m.ttsEngine||cCache.ttsEngine||'google');let voice=(m.ttsVoiceId||m.ttsVoice||cCache.ttsVoice||'uk-UA');if(engine==='browser')engine='google';function finish(){duckEnd();ttsActive=false;setTimeout(playTTS,50);}if(!speakText){finish();return;}function doTTS(){let url=`/tts?lang=${targetLang}&q=${encodeURIComponent(speakText)}&engine=${engine}&voice=${encodeURIComponent(voice)}&speed=${speed}&_=${Date.now()}`;let audio=new Audio(url);audio.volume=cCache.ttsVolume;audio.playbackRate=speed;audio.onended=finish;audio.onerror=finish;audio.play().catch(finish)}if(cCache.ringtoneUrl&&!(cCache.ringtoneChatOnly&&(m.isAlert||m.isAnnounce))){let ring=new Audio(cCache.ringtoneUrl+(cCache.ringtoneUrl.includes('?')?'&':'?')+'_='+Date.now());ring.volume=cCache.ttsVolume;ring.onended=doTTS;ring.onerror=doTTS;ring.play().catch(doTTS)}else{doTTS()}}
async function loop(){try{let res=await fetch('/get_messages');let list=await res.json();for(let msg of list){if(msg.id>maxId){maxId=msg.id;if(msg.ttsText){ttsQueue.push({name:msg.displayName,ttsDisplayName:msg.ttsDisplayName,text:msg.ttsText,isAlert:msg.isAlert,isAnnounce:!!msg.isAnnounce,queuedAt:Date.now(),priority:msg.priority,timestamp:msg.timestamp,ttsEngine:msg.ttsEngine,ttsVoiceId:msg.ttsVoiceId});playTTS();}}}}catch(e){}setTimeout(loop,400)}
refreshConfig();setInterval(refreshConfig,5000);loop();
</script>
</body>
</html>"""


def tts_audio_source_url():
    return "http://127.0.0.1:{}/tts_audio".format(PORT)


def ensure_tts_browser_source():
    source = obs.obs_get_source_by_name(TTS_BROWSER_SOURCE_NAME)
    if source:
        settings = obs.obs_data_create()
        try:
            obs.obs_data_set_string(settings, "url", tts_audio_source_url())
            obs.obs_data_set_int(settings, "width", TTS_BROWSER_SOURCE_SIZE)
            obs.obs_data_set_int(settings, "height", TTS_BROWSER_SOURCE_SIZE)
            obs.obs_data_set_int(settings, "fps", 30)
            obs.obs_data_set_bool(settings, "shutdown", False)
            obs.obs_data_set_bool(settings, "reroute_audio", True)
            obs.obs_data_set_bool(settings, "refreshnocache", True)
            obs.obs_data_set_string(settings, "css", "body { background: rgba(0,0,0,0); }")
            obs.obs_source_update(source, settings)
        finally:
            obs.obs_data_release(settings)
            obs.obs_source_release(source)


def on_obs_frontend_event(event):
    try:
        if event == obs.OBS_FRONTEND_EVENT_STREAMING_STARTED:
            if config.get("sn_enabled"):
                sn_on_stream_start()
        elif event == obs.OBS_FRONTEND_EVENT_STREAMING_STOPPED:
            if config.get("sn_enabled"):
                sn_on_stream_stop()
    except Exception as e:
        print("[StreamNotify] Помилка обробки події OBS: {}".format(e))


SETTINGS_SCHEMA = [{'id': 'general', 'title': 'Загальне та мережа', 'color': '#4facfe', 'fields': [{'key': '_update_open', 'label': '⬇ Оновлення (GitHub)', 'type': 'link', 'href': 'https://github.com/CriticalHit-one/Mult/blob/main/MUltchat.py'}, {'key': 'dock_port', 'label': 'Порт локального сервера (панель/оверлеї)', 'type': 'int'}, {'key': 'allow_network_access', 'label': 'Дозволити доступ по мережі (LAN), не тільки з цього ПК', 'type': 'bool'}, {'key': 'filter_platforms', 'label': 'Активні платформи', 'type': 'platforms', 'platforms': ['twitch', 'youtube', 'tiktok', 'kick', 'bot', 'alerts']}, {'key': 'bot_enabled', 'label': 'Бот увімкнено', 'type': 'bool'}, ], 'icon': 'gear'}, {'id': 'youtube', 'title': 'YouTube', 'color': '#ff0000', 'fields': [{'key': 'yt_live_id', 'label': 'Канал YouTube (@handle, ID каналу або посилання)', 'type': 'text'}, {'key': 'yt_api_key', 'label': 'YouTube Data API ключ', 'type': 'secret'}, {'key': 'yt_show_members_in_chat', 'label': 'Показувати нових учасників у чаті', 'type': 'bool'}, {'key': 'yt_member_audio_path', 'label': 'Звук алерту нового учасника', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'yt_member_media_path', 'label': 'Картинка / GIF / MP4 алерту нового учасника', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'yt_enable_sub_alerts', 'label': 'Алерт нових підписників (за лічильником каналу)', 'type': 'bool'}, {'key': 'yt_sub_template', 'label': 'Шаблон підписника ({total} - всього, {count} - приріст)', 'type': 'text'}, {'key': 'yt_show_subs_in_chat', 'label': 'Показувати підписників у чаті', 'type': 'bool'}, {'key': 'yt_sub_audio_path', 'label': 'Звук алерту підписника', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'yt_sub_media_path', 'label': 'Картинка / GIF / MP4 алерту підписника', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'yt_enable_like_alerts', 'label': 'Алерт лайків трансляції (за порогом)', 'type': 'bool'}, {'key': 'yt_like_threshold', 'label': 'Поріг лайків YouTube для алерту', 'type': 'int'}, {'key': 'yt_like_template', 'label': 'Шаблон лайків ({likes} - досягнутий поріг, {total} - точна кількість, {source} - Shorts/звичайна трансляція)', 'type': 'text'}, {'key': 'yt_show_likes_in_chat', 'label': 'Показувати лайки у чаті', 'type': 'bool'}, {'key': 'yt_like_audio_path', 'label': 'Звук алерту лайків', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'yt_like_media_path', 'label': 'Картинка / GIF / MP4 алерту лайків', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'yt_stats_poll_seconds', 'label': 'Період опитування статистики YouTube (сек, мін. 30)', 'type': 'int'}], 'icon': 'youtube'}, {'id': 'tiktok', 'title': 'TikTok', 'color': '#ff0050', 'fields': [{'key': 'tt_username', 'label': "Ім'я користувача TikTok (без @)", 'type': 'text'}, {'key': 'tt_sign_api_key', 'label': 'Euler Stream Sign API ключ', 'type': 'secret'}, {'key': 'tt_enable_chat', 'label': 'Озвучувати чат TikTok', 'type': 'bool'}, {'key': 'tt_enable_follows', 'label': 'Озвучувати підписки', 'type': 'bool'}, {'key': 'tt_enable_likes', 'label': 'Озвучувати лайки (агрегація)', 'type': 'bool'}, {'key': 'tt_enable_gifts', 'label': 'Озвучувати подарунки', 'type': 'bool'}, {'key': 'tt_enable_shares', 'label': 'Озвучувати репости трансляції', 'type': 'bool'}, {'key': 'tt_like_threshold', 'label': 'Поріг лайків для озвучки', 'type': 'int'}, {'key': 'tt_follow_template', 'label': 'Шаблон підписки', 'type': 'text'}, {'key': 'tt_follow_show_avatar', 'label': 'Підписки — показувати аватар у віджеті алертів', 'type': 'bool'}, {'key': 'tt_follow_show_nick', 'label': 'Підписки — показувати нік у віджеті алертів', 'type': 'bool'}, {'key': 'tt_like_show_avatar', 'label': 'Лайки — показувати аватар у віджеті алертів', 'type': 'bool'}, {'key': 'tt_gift_template', 'label': 'Шаблон подарунка', 'type': 'text'}, {'key': 'tt_like_template', 'label': 'Шаблон лайків', 'type': 'text'}, {'key': 'tt_share_template', 'label': 'Шаблон репосту', 'type': 'text'}, {'key': 'tt_show_follows_in_chat', 'label': 'Підписки — показувати в чаті', 'type': 'bool'}, {'key': 'tt_show_gifts_in_chat', 'label': 'Подарунки — показувати в чаті', 'type': 'bool'}, {'key': 'tt_show_likes_in_chat', 'label': 'Лайки — показувати в чаті', 'type': 'bool'}, {'key': 'tt_show_shares_in_chat', 'label': 'Репости — показувати в чаті', 'type': 'bool'}, {'key': 'tt_follow_audio_path', 'label': 'Звук алерту підписки', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tt_follow_media_path', 'label': 'Картинка / GIF / MP4 алерту підписки', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tt_like_audio_path', 'label': 'Звук алерту лайків', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tt_like_media_path', 'label': 'Картинка / GIF / MP4 алерту лайків', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tt_gift_audio_path', 'label': 'Звук алерту подарунка', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tt_gift_media_path', 'label': 'Картинка / GIF / MP4 алерту подарунка', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tt_share_audio_path', 'label': 'Звук алерту репосту', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tt_share_media_path', 'label': 'Картинка / GIF / MP4 алерту репосту', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tt_enable_follower_join', 'label': 'Озвучувати вхід підписників на ефір', 'type': 'bool'}, {'key': 'tt_follower_join_template', 'label': 'Шаблон входу підписника (можна {user})', 'type': 'text'}, {'key': 'tt_show_follower_join_in_chat', 'label': 'Вхід підписника — показувати в чаті', 'type': 'bool'}], 'icon': 'tiktok'}, {'id': 'twitch', 'title': 'Twitch', 'color': '#9146FF', 'fields': [{'key': '_oauth_twitch', 'label': 'Відкрити OAuth-авторизацію Twitch у браузері', 'type': 'link', 'href': '/auth/twitch/start'}, {'key': 'twitch_channel', 'label': 'Канал Twitch', 'type': 'text'}, {'key': 'twitch_irc_login', 'label': 'IRC логін бота', 'type': 'text'}, {'key': 'twitch_irc_oauth', 'label': 'IRC OAuth токен бота', 'type': 'secret'}, {'key': 'twitch_client_id', 'label': 'Twitch Client ID', 'type': 'text'}, {'key': 'twitch_client_secret', 'label': 'Twitch Client Secret', 'type': 'secret'}, {'key': 'tw_enable_subs', 'label': 'Озвучувати підписки (Subs)', 'type': 'bool'}, {'key': 'tw_enable_follows', 'label': 'Озвучувати фоловерів', 'type': 'bool'}, {'key': 'tw_enable_raids', 'label': 'Озвучувати рейди', 'type': 'bool'}, {'key': 'tw_enable_bits', 'label': 'Озвучувати Bits', 'type': 'bool'}, {'key': 'tw_enable_points', 'label': 'Озвучувати Channel Points', 'type': 'bool'}, {'key': 'tw_enable_hype', 'label': 'Озвучувати Hype Train', 'type': 'bool'}, {'key': 'tw_show_subs_in_chat', 'label': 'Підписки (Subs) — показувати в чаті', 'type': 'bool'}, {'key': 'tw_show_follows_in_chat', 'label': 'Фоловери — показувати в чаті', 'type': 'bool'}, {'key': 'tw_show_raids_in_chat', 'label': 'Рейди — показувати в чаті', 'type': 'bool'}, {'key': 'tw_show_bits_in_chat', 'label': 'Bits — показувати в чаті', 'type': 'bool'}, {'key': 'tw_show_points_in_chat', 'label': 'Channel Points — показувати в чаті', 'type': 'bool'}, {'key': 'tw_show_hype_in_chat', 'label': 'Hype Train — показувати в чаті', 'type': 'bool'}, {'key': 'tw_sub_audio_path', 'label': 'Звук — підписки', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tw_sub_media_path', 'label': 'Медіа (картинка / GIF / MP4) — підписки', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tw_follow_audio_path', 'label': 'Звук — фоловери', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tw_follow_media_path', 'label': 'Медіа (картинка / GIF / MP4) — фоловери', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tw_raid_audio_path', 'label': 'Звук — рейди', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tw_raid_media_path', 'label': 'Медіа (картинка / GIF / MP4) — рейди', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tw_bits_audio_path', 'label': 'Звук — Bits', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tw_bits_media_path', 'label': 'Медіа (картинка / GIF / MP4) — Bits', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tw_points_audio_path', 'label': 'Звук — Channel Points', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tw_points_media_path', 'label': 'Медіа (картинка / GIF / MP4) — Channel Points', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tw_hype_audio_path', 'label': 'Звук — Hype Train', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'tw_hype_media_path', 'label': 'Медіа (картинка / GIF / MP4) — Hype Train', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'tw_sub_priority', 'label': 'Пріоритет — підписки', 'type': 'int'}, {'key': 'tw_follow_priority', 'label': 'Пріоритет — фоловери', 'type': 'int'}, {'key': 'tw_raid_priority', 'label': 'Пріоритет — рейди', 'type': 'int'}, {'key': 'tw_bits_priority', 'label': 'Пріоритет — Bits', 'type': 'int'}, {'key': 'tw_points_priority', 'label': 'Пріоритет — Channel Points', 'type': 'int'}, {'key': 'tw_hype_priority', 'label': 'Пріоритет — Hype Train', 'type': 'int'}], 'icon': 'twitch'}, {'id': 'kick', 'title': 'Kick', 'color': '#53fc18', 'fields': [{'key': '_oauth_kick', 'label': 'Відкрити OAuth-авторизацію Kick у браузері', 'type': 'link', 'href': '/auth/kick/start'}, {'key': 'kick_chat_url', 'label': 'Посилання на канал Kick', 'type': 'text'}, {'key': 'kick_webhook_secret', 'label': 'Kick Webhook Secret', 'type': 'secret'}, {'key': 'kick_client_id', 'label': 'Kick Client ID', 'type': 'text'}, {'key': 'kick_client_secret', 'label': 'Kick Client Secret', 'type': 'secret'}, {'key': 'kk_enable_follows', 'label': 'Озвучувати фоловерів', 'type': 'bool'}, {'key': 'kk_enable_subs', 'label': 'Озвучувати підписки', 'type': 'bool'}, {'key': 'kk_show_follows_in_chat', 'label': 'Фоловери — показувати в чаті', 'type': 'bool'}, {'key': 'kk_show_subs_in_chat', 'label': 'Підписки — показувати в чаті', 'type': 'bool'}, {'key': 'kk_follow_audio_path', 'label': 'Звук — фоловери', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'kk_follow_media_path', 'label': 'Медіа (картинка / GIF / MP4) — фоловери', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}, {'key': 'kk_sub_audio_path', 'label': 'Звук — підписки', 'type': 'file', 'accept': '.mp3,.wav,.ogg,.m4a,.aac,.flac,.opus,.wma', 'kind': 'audio'}, {'key': 'kk_sub_media_path', 'label': 'Медіа (картинка / GIF / MP4) — підписки', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif,.apng,.mp4,.webm,.mov,.m4v,.mkv,.avi,image/*,video/*', 'kind': 'media'}], 'icon': 'kick'}, {'id': 'tts', 'title': 'TTS та голоси', 'color': '#00f2fe', 'fields': [{'key': 'tts_enabled', 'label': 'TTS увімкнено', 'type': 'bool'}, {'key': 'tts_engine', 'label': 'Рушій TTS', 'type': 'select', 'options': [{'label': 'Google Translate TTS', 'value': 'google'}, {'label': 'Браузерний рушій', 'value': 'browser'}, {'label': 'ElevenLabs (потрібен API-ключ)', 'value': 'elevenlabs'}]}, {'key': 'elevenlabs_api_key', 'label': 'ElevenLabs API-ключ (xi-api-key)', 'type': 'secret'}, {'key': 'elevenlabs_model', 'label': 'Модель ElevenLabs', 'type': 'select', 'options': [{'label': 'eleven_multilingual_v2 (найкраща якість, укр.)', 'value': 'eleven_multilingual_v2'}, {'label': 'eleven_turbo_v2_5 (швидкий, дешевший)', 'value': 'eleven_turbo_v2_5'}, {'label': 'eleven_flash_v2_5 (найшвидший)', 'value': 'eleven_flash_v2_5'}]}, {'key': 'elevenlabs_voice_id', 'label': 'Голос ElevenLabs за замовчуванням', 'type': 'voice_select'}, {'key': 'elevenlabs_stability', 'label': 'ElevenLabs: стабільність (%)', 'type': 'int'}, {'key': 'elevenlabs_similarity', 'label': 'ElevenLabs: схожість на голос (%)', 'type': 'int'}, {'key': 'elevenlabs_debug', 'label': 'ElevenLabs: докладний лог у консоль скрипта', 'type': 'bool'}, {'key': 'elevenlabs_test_link', 'label': '🔍 Перевірити ElevenLabs (відкриє звіт)', 'type': 'link', 'href': '/api/tts/elevenlabs_test'}, {'key': 'tts_volume', 'label': 'Гучність TTS (%)', 'type': 'int'}, {'key': 'tts_speed', 'label': 'Швидкість TTS (%)', 'type': 'int'}, {'key': 'tts_cooldown', 'label': 'Кулдаун між озвучками (сек)', 'type': 'int'}, {'key': 'tts_read_symbols', 'label': 'Озвучувати символи', 'type': 'bool'}, {'key': 'tts_read_nicknames', 'label': 'Озвучувати нікнейми', 'type': 'bool'}, {'key': 'tts_sub_only', 'label': 'Тільки для підписників', 'type': 'bool'}, {'key': 'tts_template', 'label': 'Шаблон озвучки повідомлення', 'type': 'textarea'}, {'key': 'tts_translate_uk', 'label': '🇺🇦 Автопереклад озвучки українською', 'type': 'bool'}, {'key': 'tts_translate_en', 'label': '🇬🇧 Автопереклад озвучки англійською', 'type': 'bool'}, {'key': 'tts_output_to_stream', 'label': 'Виводити TTS у трансляцію', 'type': 'bool'}, {'key': 'tts_ringtone_path', 'label': 'Звук-сповіщення перед TTS', 'type': 'browse', 'mode': 'file', 'ext': '.mp3,.wav,.ogg,.m4a,.flac,.aac'}, {'key': 'tts_ringtone_chat_only', 'label': 'Дзвіночок лише для повідомлень із чату (не для алертів і оголошень)', 'type': 'bool'}], 'icon': 'speaker'}, {'id': 'moderation', 'title': 'Модерація чату', 'color': '#ff416c', 'fields': [{'key': 'anti_caps', 'label': 'Анти-капс (великі літери)', 'type': 'bool'}, {'key': 'flood_control', 'label': 'Захист від флуду', 'type': 'bool'}, {'key': 'filter_badwords', 'label': 'Фільтр лайливих слів', 'type': 'bool'}, {'key': 'replace_emoji', 'label': 'Замінювати емодзі', 'type': 'bool'}, {'key': 'hide_links', 'label': 'Приховувати посилання', 'type': 'bool'}, {'key': 'hide_emojis', 'label': 'Приховувати емодзі', 'type': 'bool'}, {'key': 'blacklist', 'label': 'Чорний список слів (через кому) — фільтр тексту, НЕ блокування користувачів', 'type': 'textarea'}, {'key': 'blacklist_action', 'label': 'Що робити зі словом із чорного списку', 'type': 'select', 'options': [{'label': 'Замінювати на [цензура] (озвучувати без слова)', 'value': 'censor'}, {'label': 'Не озвучувати все повідомлення', 'value': 'skip'}, {'label': 'Заглушити користувачу TTS', 'value': 'mute'}, {'label': 'Вимкнено (не використовувати список)', 'value': 'off'}]}, {'key': 'auto_mute_enabled', 'label': 'Автозаглушення TTS за забороненими словами в повідомленні', 'type': 'bool'}, {'key': 'auto_mute_words', 'label': 'Заборонені слова для автозаглушення (через кому)', 'type': 'textarea'}, {'key': 'auto_mute_announce_template', 'label': 'Текст оголошення про автозаглушення (можна {user}, {platform})', 'type': 'textarea'}, {'key': 'ad_interval', 'label': 'Інтервал реклами (хв)', 'type': 'int'}, {'key': 'ad_text', 'label': 'Текст реклами', 'type': 'textarea'}], 'icon': 'shield'}, {'id': 'chatpanel', 'title': 'Панель чату (сторінка адміна у браузері)', 'color': '#9b8cff', 'fields': [{'key': 'msg_timeout', 'label': 'Тайм-аут повідомлення на панелі (сек)', 'type': 'int'}, {'key': 'chat_bg_image', 'label': 'Фонове зображення панелі чату', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif', 'kind': 'image'}, {'key': 'chat_msg_color', 'label': 'Колір фону повідомлення на панелі', 'type': 'select', 'options': [{'label': 'Напівпрозорий чорний', 'value': 'rgba(0, 0, 0, 0.5)'}, {'label': 'Біле розмиття', 'value': 'rgba(255, 255, 255, 0.1)'}, {'label': 'Прозорий', 'value': 'rgba(0, 0, 0, 0.0)'}, {'label': 'Синій напівпрозорий', 'value': 'rgba(0, 0, 100, 0.5)'}, {'label': 'Червоний напівпрозорий', 'value': 'rgba(100, 0, 0, 0.5)'}, {'label': 'Зелений напівпрозорий', 'value': 'rgba(0, 100, 0, 0.5)'}, {'label': 'Фіолетовий напівпрозорий', 'value': 'rgba(80, 0, 120, 0.5)'}, {'label': 'Помаранчевий напівпрозорий', 'value': 'rgba(180, 80, 0, 0.5)'}, {'label': 'Рожевий напівпрозорий', 'value': 'rgba(200, 50, 120, 0.5)'}, {'label': 'Золотий напівпрозорий', 'value': 'rgba(180, 140, 20, 0.5)'}]}, {'key': 'chat_font_size', 'label': 'Розмір шрифту панелі чату (px)', 'type': 'int'}], 'icon': 'chat'}, {'id': 'overlay', 'title': 'Оверлей чату (джерело Browser у OBS)', 'color': '#e2e2e9', 'fields': [{'key': 'overlay_max_messages', 'label': 'Макс. повідомлень в оверлеї', 'type': 'int'}, {'key': 'overlay_msg_timeout', 'label': 'Тайм-аут повідомлення оверлею (сек)', 'type': 'int'}, {'key': 'overlay_font_size', 'label': 'Розмір шрифту оверлею (px)', 'type': 'int'}, {'key': 'overlay_plain', 'label': 'Оверлей чату без плашки (лише текст, без фону й рамки)', 'type': 'bool'}, {'key': 'overlay_plain_marker', 'label': 'Позначка платформи в режимі без плашки', 'type': 'select', 'options': [{'label': 'Іконка платформи (▶ 🎮 🎵 🟩)', 'value': 'icon'}, {'label': 'Назва платформи одним словом', 'value': 'name'}, {'label': 'Без позначки (лише ім\'я і текст)', 'value': 'none'}]}, {'key': 'overlay_bg_color', 'label': 'Колір фону оверлею (CSS)', 'type': 'select', 'options': [{'label': 'Чорний напівпрозорий', 'value': 'rgba(0,0,0,0.7)'}, {'label': 'Білий напівпрозорий', 'value': 'rgba(255,255,255,0.2)'}, {'label': 'Синій (темний)', 'value': 'rgba(0,0,100,0.7)'}, {'label': 'Червоний (темний)', 'value': 'rgba(100,0,0,0.7)'}, {'label': 'Зелений (темний)', 'value': 'rgba(0,100,0,0.7)'}, {'label': 'Фіолетовий', 'value': 'rgba(80,0,120,0.7)'}, {'label': 'Помаранчевий', 'value': 'rgba(180,80,0,0.7)'}, {'label': 'Рожевий', 'value': 'rgba(200,50,120,0.7)'}, {'label': 'Сірий', 'value': 'rgba(50,50,50,0.8)'}, {'label': 'Золотий', 'value': 'rgba(180,140,20,0.7)'}]}, {'key': 'overlay_text_color', 'label': 'Колір тексту оверлею (CSS)', 'type': 'select', 'options': [{'label': 'Білий', 'value': '#ffffff'}, {'label': 'Чорний', 'value': '#000000'}, {'label': 'Жовтий', 'value': '#ffd700'}, {'label': 'Салатовий', 'value': '#aaffaa'}, {'label': 'Блакитний', 'value': '#00ffff'}, {'label': 'Червоний', 'value': '#ff4444'}, {'label': 'Зелений', 'value': '#44ff44'}, {'label': 'Синій', 'value': '#4444ff'}, {'label': 'Помаранчевий', 'value': '#ffaa44'}, {'label': 'Сріблястий', 'value': '#cccccc'}]}], 'icon': 'chat'}, {'id': 'analytics', 'title': 'Аналітика / LIVE-віджет', 'color': '#ffb703', 'fields': [{'key': 'analytics_enabled', 'label': 'Аналітика увімкнена', 'type': 'bool'}, {'key': 'analytics_update_interval', 'label': 'Інтервал оновлення аналітики (сек)', 'type': 'int'}, {'key': 'analytics_platforms', 'label': 'Платформи для аналітики глядачів', 'type': 'platforms', 'platforms': ['youtube', 'tiktok', 'twitch', 'kick']}, {'key': 'analytics_widget_enabled', 'label': 'LIVE-віджет увімкнено', 'type': 'bool'}, {'key': 'analytics_widget_mode', 'label': 'Режим віджета (compact / full)', 'type': 'select', 'options': [{'label': 'Компактний (іконка+цифра)', 'value': 'compact'}, {'label': 'Повний', 'value': 'full'}]}, {'key': 'analytics_widget_font_size', 'label': 'Розмір шрифту віджета (px)', 'type': 'int'}, {'key': 'analytics_widget_text_color', 'label': 'Колір тексту віджета (CSS)', 'type': 'select', 'options': [{'label': 'Білий', 'value': '#ffffff'}, {'label': 'Чорний', 'value': '#000000'}, {'label': 'Жовтий', 'value': '#ffd700'}, {'label': 'Салатовий', 'value': '#aaffaa'}, {'label': 'Блакитний', 'value': '#00ffff'}, {'label': 'Червоний', 'value': '#ff4444'}, {'label': 'Зелений', 'value': '#44ff44'}, {'label': 'Синій', 'value': '#4444ff'}, {'label': 'Помаранчевий', 'value': '#ffaa44'}, {'label': 'Сріблястий', 'value': '#cccccc'}]}, {'key': 'analytics_widget_bg_color', 'label': 'Колір фону віджета (CSS)', 'type': 'select', 'options': [{'label': 'Чорний напівпрозорий', 'value': 'rgba(0,0,0,0.7)'}, {'label': 'Білий напівпрозорий', 'value': 'rgba(255,255,255,0.2)'}, {'label': 'Синій (темний)', 'value': 'rgba(0,0,100,0.7)'}, {'label': 'Червоний (темний)', 'value': 'rgba(100,0,0,0.7)'}, {'label': 'Зелений (темний)', 'value': 'rgba(0,100,0,0.7)'}, {'label': 'Фіолетовий', 'value': 'rgba(80,0,120,0.7)'}, {'label': 'Помаранчевий', 'value': 'rgba(180,80,0,0.7)'}, {'label': 'Рожевий', 'value': 'rgba(200,50,120,0.7)'}, {'label': 'Сірий', 'value': 'rgba(50,50,50,0.8)'}, {'label': 'Золотий', 'value': 'rgba(180,140,20,0.7)'}]}, {'key': 'analytics_widget_platforms', 'label': 'Платформи у LIVE-віджеті', 'type': 'platforms', 'platforms': ['youtube', 'tiktok', 'twitch', 'kick']}, {'key': 'top_likes_widget_title', 'label': 'Заголовок віджета «Топ за лайками» (TikTok)', 'type': 'text'}, {'key': 'top_likes_widget_limit', 'label': 'Кількість глядачів у віджеті «Топ за лайками»', 'type': 'int'}, {'key': 'top_likes_widget_show_title', 'label': 'Показувати заголовок у віджеті «Топ за лайками»', 'type': 'bool'}, {'key': 'top_likes_widget_bg_enabled', 'label': 'Фон картки віджета «Топ за лайками»', 'type': 'bool'}, {'key': 'top_likes_widget_bg_color', 'label': 'Колір фону віджета «Топ за лайками» (CSS)', 'type': 'select', 'options': [{'label': 'Темний градієнт (за замовчуванням)', 'value': 'rgba(20,20,28,0.85)'}, {'label': 'Чорний напівпрозорий', 'value': 'rgba(0,0,0,0.7)'}, {'label': 'Білий напівпрозорий', 'value': 'rgba(255,255,255,0.2)'}, {'label': 'Синій (темний)', 'value': 'rgba(0,0,100,0.7)'}, {'label': 'Червоний (темний)', 'value': 'rgba(100,0,0,0.7)'}, {'label': 'Зелений (темний)', 'value': 'rgba(0,100,0,0.7)'}, {'label': 'Фіолетовий', 'value': 'rgba(80,0,120,0.7)'}, {'label': 'Помаранчевий', 'value': 'rgba(180,80,0,0.7)'}, {'label': 'Рожевий', 'value': 'rgba(200,50,120,0.7)'}, {'label': 'Сірий', 'value': 'rgba(50,50,50,0.8)'}, {'label': 'Золотий', 'value': 'rgba(180,140,20,0.7)'}]}, {'key': 'top_likes_widget_text_color', 'label': 'Колір тексту віджета «Топ за лайками» (CSS)', 'type': 'select', 'options': [{'label': 'Білий', 'value': '#ffffff'}, {'label': 'Чорний', 'value': '#000000'}, {'label': 'Жовтий', 'value': '#ffd700'}, {'label': 'Салатовий', 'value': '#aaffaa'}, {'label': 'Блакитний', 'value': '#00ffff'}, {'label': 'Червоний', 'value': '#ff4444'}, {'label': 'Зелений', 'value': '#44ff44'}, {'label': 'Синій', 'value': '#4444ff'}, {'label': 'Помаранчевий', 'value': '#ffaa44'}, {'label': 'Сріблястий', 'value': '#cccccc'}]}, {'key': 'top_likes_widget_row_plate', 'label': 'Плашка під кожним глядачем у списку', 'type': 'bool'}], 'icon': 'chart'}, {'id': 'netmon', 'title': 'Моніторинг інтернету', 'color': '#00e5ff', 'fields': [{'key': 'netmon_enabled', 'label': 'Моніторинг інтернету увімкнено', 'type': 'bool'}, {'key': 'netmon_ping_host', 'label': 'Хост для ping', 'type': 'text'}, {'key': 'netmon_ping_interval', 'label': 'Інтервал ping (сек)', 'type': 'int'}, {'key': 'netmon_loss_threshold', 'label': "Поріг втрати пакетів для \"нестабільно\" (%)", 'type': 'int'}, {'key': 'netmon_ping_threshold', 'label': "Поріг затримки для \"нестабільно\" (мс, 0 = не враховувати)", 'type': 'int'}, {'key': 'netmon_debounce_count', 'label': "Скільки поганих/хороших вимірів підряд для зміни статусу", 'type': 'int'}, {'key': 'netmon_show_in_chat', 'label': 'Показувати сповіщення про мережу в чаті (а не лише озвучувати)', 'type': 'bool'}, {'key': 'netmon_unstable_text', 'label': 'Текст TTS при нестабільному інтернеті (можна {ping}, {loss})', 'type': 'textarea'}, {'key': 'netmon_stable_text', 'label': "Текст TTS при стабілізації з'єднання (можна {ping}, {loss})", 'type': 'textarea'}, {'key': 'netmon_speedtest_enabled', 'label': 'Вимірювати швидкість download/upload (додаткове навантаження на мережу)', 'type': 'bool'}, {'key': 'netmon_speedtest_interval', 'label': 'Інтервал speedtest (сек)', 'type': 'int'}, {'key': 'netmon_ping_hosts', 'label': 'Хости для ping (через кому, декілька для точності)', 'type': 'text'}, {'key': 'netmon_window_size', 'label': 'Розмір ковзного вікна вимірів (шт.)', 'type': 'int'}, {'key': 'netmon_jitter_threshold', 'label': "Поріг джитеру для \"нестабільно\" (мс, 0 = не враховувати)", 'type': 'int'}, {'key': 'netmon_show_obs_frames', 'label': 'Показувати пропущені кадри OBS у панелі', 'type': 'bool'}], 'icon': 'wifi'}, {'id': 'music', 'title': 'Музичний плеєр', 'color': '#ff6ec7', 'fields': [{'key': 'music_enabled', 'label': 'Музичний плеєр увімкнено', 'type': 'bool'}, {'key': 'music_duck_on_alert', 'label': 'Приглушувати музику під час TTS/алертів', 'type': 'bool'}, {'key': 'music_duck_resume_delay', 'label': 'Пауза перед відновленням музики після алерту (сек)', 'type': 'int'}, {'key': 'music_duck_source_names', 'label': "ЕКСПЕРИМЕНТАЛЬНО: джерела OBS, які призупиняють музику під час звучання (список тягнеться напряму з OBS, познач потрібні)", 'type': 'obs_sources'}], 'icon': 'gear'}, {'id': 'giveaway', 'title': 'Giveaway (Telegram)', 'color': '#ffd700', 'fields': [{'key': 'gw_enabled', 'label': 'Модуль розіграшів увімкнено', 'type': 'bool'}, {'key': 'gw_tg_token', 'label': 'Telegram Bot Token', 'type': 'secret'}, {'key': 'gw_tg_chat_id', 'label': 'Telegram Chat ID', 'type': 'text'}, {'key': 'gw_prize_title', 'label': 'Назва призу', 'type': 'text'}, {'key': 'gw_announce_text', 'label': 'Текст анонсу', 'type': 'text'}, {'key': 'gw_img_path', 'label': 'Картинка розіграшу', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif', 'kind': 'image'}, {'key': 'gw_duration_min', 'label': 'Тривалість (хвилин)', 'type': 'int'}, {'key': '_gw_start', 'label': '▶ Запустити розіграш', 'type': 'action', 'endpoint': '/api/giveaway/start', 'style': 'start'}, {'key': '_gw_stop', 'label': '⏹ Зупинити розіграш', 'type': 'action', 'endpoint': '/api/giveaway/stop', 'style': 'stop'}], 'icon': 'gift'}, {'id': 'streamnotify', 'title': 'Stream Notify', 'color': '#4facfe', 'fields': [{'key': 'sn_enabled', 'label': 'Модуль Stream Notify увімкнено', 'type': 'bool'}, {'key': 'sn_stream_title', 'label': 'Назва стріму', 'type': 'text'}, {'key': 'sn_stream_game', 'label': 'Гра', 'type': 'text'}, {'key': 'sn_custom_text', 'label': "Текст посту (свій, необов'язково)", 'type': 'textarea'}, {'key': 'sn_preview_path', 'label': "Прев'ю-картинка", 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif', 'kind': 'image'}, {'key': 'sn_post_image_path', 'label': 'Картинка для ручної публікації', 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif', 'kind': 'image'}, {'key': 'sn_streamer_name', 'label': "Ім'я стрімера (для Discord)", 'type': 'text'}, {'key': 'sn_send_delay', 'label': 'Затримка перед відправкою (сек)', 'type': 'int'}, {'key': 'sn_tg_token', 'label': 'Telegram Bot Token', 'type': 'secret'}, {'key': 'sn_tg_chat_id', 'label': 'Telegram Chat ID', 'type': 'text'}, {'key': 'sn_tg_delete_on_stop', 'label': 'Видаляти пост Telegram при зупинці стриму', 'type': 'bool'}, {'key': 'sn_dc_webhook', 'label': 'Discord Webhook URL', 'type': 'secret'}, {'key': 'sn_dc_mention', 'label': 'Discord — згадка', 'type': 'select', 'options': [{'label': 'Без згадки', 'value': 'none'}, {'label': '@here', 'value': 'here'}, {'label': '@everyone', 'value': 'everyone'}]}, {'key': 'sn_url_tiktok', 'label': 'TikTok — посилання', 'type': 'text'}, {'key': 'sn_btn_style_tiktok', 'label': 'TikTok — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_twitch', 'label': 'Twitch — посилання', 'type': 'text'}, {'key': 'sn_btn_style_twitch', 'label': 'Twitch — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_youtube', 'label': 'YouTube — посилання', 'type': 'text'}, {'key': 'sn_btn_style_youtube', 'label': 'YouTube — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_kick', 'label': 'Kick — посилання', 'type': 'text'}, {'key': 'sn_btn_style_kick', 'label': 'Kick — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_discord', 'label': 'Discord — посилання', 'type': 'text'}, {'key': 'sn_btn_style_discord', 'label': 'Discord — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_telegram', 'label': 'Telegram — посилання', 'type': 'text'}, {'key': 'sn_btn_style_telegram', 'label': 'Telegram — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_steamtv', 'label': 'Steam.TV — посилання', 'type': 'text'}, {'key': 'sn_btn_style_steamtv', 'label': 'Steam.TV — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_fb_gaming', 'label': 'FB Gaming — посилання', 'type': 'text'}, {'key': 'sn_btn_style_fb_gaming', 'label': 'FB Gaming — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_facebook', 'label': 'Facebook — посилання', 'type': 'text'}, {'key': 'sn_btn_style_facebook', 'label': 'Facebook — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_instagram', 'label': 'Instagram — посилання', 'type': 'text'}, {'key': 'sn_btn_style_instagram', 'label': 'Instagram — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_url_donat', 'label': 'Донат — посилання', 'type': 'text'}, {'key': 'sn_btn_style_donat', 'label': 'Донат — колір кнопки Telegram', 'type': 'select', 'options': [{'label': 'За замовчуванням (сірий)', 'value': ''}, {'label': 'Синій (primary)', 'value': 'primary'}, {'label': 'Зелений (success)', 'value': 'success'}, {'label': 'Червоний (danger)', 'value': 'danger'}]}, {'key': 'sn_tg_edit_on_stop', 'label': 'Редагувати пост Telegram після зупинки стриму', 'type': 'bool'}, {'key': 'sn_after_image_path', 'label': "Картинка для посту 'після стриму'", 'type': 'file', 'accept': '.png,.jpg,.jpeg,.webp,.avif,.bmp,.gif', 'kind': 'image'}, {'key': 'sn_after_text', 'label': "Текст посту 'після стриму'", 'type': 'textarea'}, {'key': 'sn_after_url_tiktok', 'label': 'Після стриму: показувати TikTok', 'type': 'bool'}, {'key': 'sn_after_url_twitch', 'label': 'Після стриму: показувати Twitch', 'type': 'bool'}, {'key': 'sn_after_url_youtube', 'label': 'Після стриму: показувати YouTube', 'type': 'bool'}, {'key': 'sn_after_url_kick', 'label': 'Після стриму: показувати Kick', 'type': 'bool'}, {'key': 'sn_after_url_discord', 'label': 'Після стриму: показувати Discord', 'type': 'bool'}, {'key': 'sn_after_url_telegram', 'label': 'Після стриму: показувати Telegram', 'type': 'bool'}, {'key': 'sn_after_url_steamtv', 'label': 'Після стриму: показувати Steam.TV', 'type': 'bool'}, {'key': 'sn_after_url_fb_gaming', 'label': 'Після стриму: показувати FB Gaming', 'type': 'bool'}, {'key': 'sn_after_url_facebook', 'label': 'Після стриму: показувати Facebook', 'type': 'bool'}, {'key': 'sn_after_url_instagram', 'label': 'Після стриму: показувати Instagram', 'type': 'bool'}, {'key': 'sn_after_url_donat', 'label': 'Після стриму: показувати Донат', 'type': 'bool'}, {'key': 'sn_schedule_date', 'label': 'Запланована дата (РРРР-ММ-ДД)', 'type': 'text'}, {'key': 'sn_schedule_time', 'label': 'Запланований час (ГГ:ХХ)', 'type': 'text'}, {'key': '_sn_test_send', 'label': '🧪 Тест: відправити зараз', 'type': 'action', 'endpoint': '/api/streamnotify/test_send', 'style': 'start'}, {'key': '_sn_test_after', 'label': '🧪 Тест: застосувати зміни після стриму', 'type': 'action', 'endpoint': '/api/streamnotify/test_after', 'style': 'stop'}, {'key': '_sn_publish', 'label': '📤 Опублікувати пост зараз', 'type': 'action', 'endpoint': '/api/streamnotify/publish', 'style': 'start'}, {'key': '_sn_schedule', 'label': '🗓 Запланувати пост', 'type': 'action', 'endpoint': '/api/streamnotify/schedule', 'style': 'start'}, {'key': '_sn_delete_schedule', 'label': '🗑 Видалити запланований пост', 'type': 'action', 'endpoint': '/api/streamnotify/delete_schedule', 'style': 'stop'}], 'icon': 'megaphone'}]


SETTINGS_PAGE_HTML = """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8">
<meta http-equiv="Cache-Control" content="no-cache, no-store, must-revalidate">
<meta http-equiv="Pragma" content="no-cache">
<meta http-equiv="Expires" content="0">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>MultiChat — Налаштування</title>
<style>
*{box-sizing:border-box}
@keyframes fadeSlideIn{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}
@keyframes popIn{from{opacity:0;transform:scale(0.96)}to{opacity:1;transform:scale(1)}}
@keyframes glowPulse{0%,100%{box-shadow:0 0 0 rgba(79,172,254,0)}50%{box-shadow:0 0 14px rgba(79,172,254,0.35)}}
html{scrollbar-color:#3a3a48 #14141b;scrollbar-width:thin}
body{background:radial-gradient(1200px 700px at 15% -10%,rgba(79,172,254,0.10),transparent),radial-gradient(1000px 600px at 100% 0%,rgba(255,183,3,0.06),transparent),#0e0e13;color:#f1f1f7;font-family:'Segoe UI',system-ui,sans-serif;margin:0;padding:0;font-size:14px}
.topbar{position:sticky;top:0;z-index:50;background:rgba(14,14,19,0.92);backdrop-filter:blur(14px) saturate(140%);border-bottom:1px solid rgba(255,255,255,0.1);padding:12px 14px;display:flex;flex-direction:column;gap:8px;box-shadow:0 6px 22px rgba(0,0,0,0.35)}
.topbar-row{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.title{font-weight:bold;font-size:17px;flex:1;background:linear-gradient(120deg,#ffb703,#ffd76a,#ffb703);-webkit-background-clip:text;background-clip:text;color:transparent;letter-spacing:.2px}
.search-input{flex:1;min-width:120px;padding:9px 14px;border-radius:20px;border:1px solid rgba(255,255,255,0.2);background:rgba(0,0,0,0.4);color:#f1f1f7;font-size:13px;transition:border-color .2s ease,box-shadow .2s ease}
.search-input:focus{outline:none;border-color:#4facfe;box-shadow:0 0 0 3px rgba(79,172,254,0.18)}
.btn{background:linear-gradient(135deg,#00f2fe 0%,#4facfe 100%);padding:9px 18px;border-radius:20px;font-weight:bold;border:none;color:#08131c;cursor:pointer;font-size:13px;white-space:nowrap;transition:transform .15s ease,box-shadow .15s ease;box-shadow:0 3px 10px rgba(79,172,254,0.25)}
.btn:hover:not(:disabled){transform:translateY(-1px);box-shadow:0 6px 16px rgba(79,172,254,0.4)}
.btn:active:not(:disabled){transform:translateY(0px) scale(0.98)}
.btn:disabled{opacity:0.5;cursor:default;box-shadow:none}
.btn-secondary{background:rgba(255,255,255,0.1);border:1px solid rgba(255,255,255,0.2);padding:9px 16px;border-radius:20px;color:#e2e2e9;cursor:pointer;font-size:13px;transition:background .15s ease,transform .15s ease,border-color .15s ease}
.btn-secondary:hover{background:rgba(255,255,255,0.18);border-color:rgba(255,255,255,0.35);transform:translateY(-1px)}
.status{font-size:12px;color:#8a8a99;min-height:16px;transition:color .2s ease}
.status.ok{color:#4caf50}
.status.err{color:#ff416c}
.container{padding:12px;display:flex;flex-direction:column;gap:10px}
.section{background:linear-gradient(180deg,rgba(255,255,255,0.05),rgba(255,255,255,0.025));border:1px solid rgba(255,255,255,0.08);border-radius:16px;overflow:hidden;transition:border-color .2s ease,box-shadow .2s ease;animation:fadeSlideIn .35s ease both}
.section:hover{border-color:rgba(255,255,255,0.16)}
.section.open{box-shadow:0 8px 24px rgba(0,0,0,0.28)}
.section-header{padding:13px 14px;display:flex;align-items:center;gap:10px;cursor:pointer;user-select:none;border-left:4px solid var(--accent,#4facfe);transition:background .18s ease}
.section-header:hover{background:rgba(255,255,255,0.045)}
.section-title{font-weight:bold;flex:1;transition:color .18s ease}
.section-caret{transition:transform .25s cubic-bezier(.4,0,.2,1);opacity:0.65;display:inline-block}
.section.open .section-caret{transform:rotate(90deg);opacity:1}
.section-body{max-height:0;opacity:0;overflow:hidden;padding:0 14px 0 18px;border-top:0 solid rgba(255,255,255,0.06);transition:max-height .32s cubic-bezier(.4,0,.2,1),opacity .28s ease,padding .32s ease}
.section.open .section-body{display:flex;flex-direction:column;gap:12px;max-height:4000px;opacity:1;padding:10px 14px 16px 18px;border-top-width:1px}
.field{display:flex;flex-direction:column;gap:5px;animation:fadeSlideIn .3s ease both}
.field.hidden{display:none}
.field-label{font-size:12.5px;color:#c8c8d4}
input[type=text],input[type=number],input[type=password],textarea{width:100%;padding:9px 11px;border-radius:10px;border:1px solid rgba(255,255,255,0.15);background:rgba(0,0,0,0.35);color:#f1f1f7;font-size:13.5px;font-family:inherit;transition:border-color .18s ease,box-shadow .18s ease,background .18s ease}
textarea{min-height:60px;resize:vertical}
input:hover,textarea:hover{border-color:rgba(255,255,255,0.28)}
input:focus,textarea:focus{outline:none;border-color:#4facfe;box-shadow:0 0 0 3px rgba(79,172,254,0.16);background:rgba(0,0,0,0.5)}
.secret-wrap{position:relative;display:flex}
.file-row{display:flex;gap:6px}
.file-row input[type=text]{flex:1;opacity:0.85}
.btn-clear-path{flex:0 0 auto;width:32px;padding:0;cursor:pointer;border-radius:6px;border:1px solid #3a4152;background:#242a38;color:#e6e9f0;font-size:13px;line-height:30px;transition:background .15s ease,border-color .15s ease,color .15s ease}
.btn-clear-path:hover{background:#3a2530;border-color:#7a3040;color:#ff8a9c}
.secret-wrap input{padding-right:38px}
.eye-btn{position:absolute;right:4px;top:50%;transform:translateY(-50%);background:none;border:none;color:#8a8a99;cursor:pointer;font-size:15px;padding:4px 8px;transition:color .15s ease}
.eye-btn:hover{color:#4facfe}
.switch{position:relative;display:inline-block;width:42px;height:24px;flex-shrink:0}
.switch input{opacity:0;width:0;height:0}
.slider{position:absolute;cursor:pointer;top:0;left:0;right:0;bottom:0;background:rgba(255,255,255,0.15);border-radius:24px;transition:background .25s ease,box-shadow .25s ease}
.slider:before{position:absolute;content:"";height:18px;width:18px;left:3px;bottom:3px;background:#e2e2e9;border-radius:50%;transition:transform .25s cubic-bezier(.4,0,.2,1),background .25s ease;box-shadow:0 1px 3px rgba(0,0,0,0.3)}
input:checked + .slider{background:linear-gradient(135deg,#00f2fe 0%,#4facfe 100%);box-shadow:0 0 10px rgba(79,172,254,0.5)}
input:checked + .slider:before{transform:translateX(18px);background:#08131c}
.bool-row{display:flex;align-items:center;gap:10px}
.bool-row .field-label{margin:0}
.platform-grid{display:flex;flex-wrap:wrap;gap:10px}
.platform-chip{display:flex;align-items:center;gap:6px;background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.12);border-radius:16px;padding:6px 12px;font-size:12.5px;transition:background .18s ease,border-color .18s ease,transform .15s ease}
.platform-chip:hover{background:rgba(255,255,255,0.11);border-color:rgba(255,255,255,0.22);transform:translateY(-1px)}
.hint{font-size:11px;color:#6f6f7c;line-height:1.4}
.empty-state{padding:30px;text-align:center;color:#6f6f7c;font-size:13px}
.fatal-error{display:none;margin:12px;padding:14px;border-radius:12px;background:rgba(255,65,108,0.12);border:1px solid #ff416c;color:#ffb3c1;font-size:12.5px;white-space:pre-wrap;font-family:monospace;animation:fadeSlideIn .3s ease both}
.fs-modal-overlay{display:none;position:fixed;inset:0;background:rgba(0,0,0,0.65);backdrop-filter:blur(3px);z-index:100;align-items:center;justify-content:center}
.fs-modal-overlay.open{display:flex;animation:fadeSlideIn .18s ease both}
.fs-modal{background:#15151c;border:1px solid rgba(255,255,255,0.15);border-radius:16px;width:92%;max-width:520px;max-height:80vh;display:flex;flex-direction:column;overflow:hidden;box-shadow:0 20px 60px rgba(0,0,0,0.5);animation:popIn .2s cubic-bezier(.34,1.56,.64,1) both}
.fs-modal-header{padding:12px 14px;border-bottom:1px solid rgba(255,255,255,0.08);font-weight:bold}
.fs-modal-path{padding:8px 14px;font-size:11px;color:#8a8a99;word-break:break-all;border-bottom:1px solid rgba(255,255,255,0.06)}
.fs-modal-list{flex:1;overflow-y:auto;padding:6px;min-height:120px}
.fs-entry{display:flex;align-items:center;gap:8px;padding:8px 10px;border-radius:8px;cursor:pointer;font-size:13px;transition:background .15s ease,padding-left .15s ease}
.fs-entry:hover{background:rgba(255,255,255,0.09);padding-left:12px}
.fs-modal-footer{padding:10px 14px;border-top:1px solid rgba(255,255,255,0.08);display:flex;justify-content:flex-end;gap:8px}
.fs-modal-error{padding:10px 14px;color:#ff416c;font-size:12px}
</style>
</head>
<body>
<div class="topbar">
  <div class="topbar-row">
    <div class="title">⚙️ MultiChat — Налаштування</div>
  </div>
  <div class="topbar-row">
    <input class="search-input" id="searchInput" type="text" placeholder="Пошук по налаштуваннях...">
    <button class="btn-secondary" id="reloadBtn">Оновити</button>
    <button class="btn" id="saveBtn">Зберегти зміни</button>
  </div>
  <div class="status" id="statusLine"></div>
</div>
<div class="fatal-error" id="fatalError"></div>
<div class="fs-modal-overlay" id="fsModalOverlay">
  <div class="fs-modal">
    <div class="fs-modal-header" id="fsModalTitle">Оберіть файл</div>
    <div class="fs-modal-path" id="fsModalPath"></div>
    <div class="fs-modal-error" id="fsModalError" style="display:none"></div>
    <div class="fs-modal-list" id="fsModalList"></div>
    <div class="fs-modal-footer">
      <button type="button" class="btn-secondary" id="fsModalCancel">Скасувати</button>
      <button type="button" class="btn" id="fsModalSelectDir" style="display:none">Обрати цю папку</button>
    </div>
  </div>
</div>
<div class="container" id="sectionsContainer"></div>
<script>
const SCHEMA = """ + json.dumps(SETTINGS_SCHEMA, ensure_ascii=False) + """;
const VOICE_OPTIONS = """ + json.dumps(build_voice_options(), ensure_ascii=False) + """;
let currentSettings = {};
let dirty = false;

function escapeHtml(str) {
  return String(str == null ? "" : str).replace(/[&<>"']/g, function (ch) {
    return {"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[ch];
  });
}

function setStatus(text, kind) {
  const el = document.getElementById("statusLine");
  el.textContent = text || "";
  el.className = "status" + (kind ? " " + kind : "");
}

function markDirty() {
  dirty = true;
  const btn = document.getElementById("saveBtn");
  btn.textContent = "Зберегти зміни *";
  setStatus("Є незбережені зміни", "");
}

function openDynLink(sourceKey) {
  const el = document.querySelector('[data-key="' + sourceKey + '"]:not([data-subkey])');
  let url = el ? String(el.value || "").trim() : "";
  if (!url) { url = String((currentSettings && currentSettings[sourceKey]) || "").trim(); }
  if (!url) { alert("Спочатку вкажи посилання на нову версію у полі вище і натисни «Зберегти»"); return; }
  const lower = url.toLowerCase();
  if (lower.slice(0, 7) !== "http://" && lower.slice(0, 8) !== "https://") { url = "https://" + url; }
  window.open(url, "_blank");
}

function fieldInputHtml(field) {
  const key = field.key;
  if (field.type === "link") {
    return '<a class="btn-secondary" style="display:inline-block;text-decoration:none;text-align:center" target="_blank" href="' + field.href + '">' + escapeHtml(field.label) + '</a>';
  }
  if (field.type === "dynlink") {
    return '<button type="button" class="btn" onclick="openDynLink(&quot;' + field.source + '&quot;)">' + escapeHtml(field.label) + '</button>' +
      '<div class="hint">Відкриє у браузері адресу з поля вище</div>';
  }
  if (field.type === "action") {
    const btnClass = field.style === "stop" ? "btn-secondary" : "btn";
    return '<button type="button" class="' + btnClass + '" data-action-endpoint="' + field.endpoint + '" onclick="runAction(this)">' + escapeHtml(field.label) + '</button>' +
      '<div class="hint" data-action-hint="' + key + '"></div>';
  }
  if (field.type === "bool") {
    return '<div class="bool-row"><label class="switch"><input type="checkbox" data-key="' + key + '"><span class="slider"></span></label>' +
      '<span class="field-label">' + escapeHtml(field.label) + '</span></div>';
  }
  if (field.type === "secret") {
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<div class="secret-wrap"><input type="password" data-key="' + key + '" autocomplete="off">' +
      '<button type="button" class="eye-btn" onclick="toggleSecret(this)">👁</button></div>';
  }
  if (field.type === "int") {
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<input type="number" data-key="' + key + '">';
  }
  if (field.type === "textarea") {
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<textarea data-key="' + key + '"></textarea>';
  }
  if (field.type === "select") {
    let opts = "";
    (field.options || []).forEach(function (opt) {
      opts += '<option value="' + escapeHtml(opt.value) + '">' + escapeHtml(opt.label) + '</option>';
    });
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<select data-key="' + key + '">' + opts + '</select>';
  }
  if (field.type === "voice_select") {
    let opts = "";
    VOICE_OPTIONS.forEach(function (opt) {
      opts += '<option value="' + escapeHtml(opt.value) + '">' + escapeHtml(opt.label) + '</option>';
    });
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<select data-key="' + key + '">' + opts + '</select>';
  }
  if (field.type === "file") {
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<div class="file-row">' +
      '<input type="text" data-key="' + key + '" placeholder="Шлях до файлу на цьому ПК" readonly>' +
      '<button type="button" class="btn-clear-path" onclick="clearPathField(this)" title="Очистити поле">✕</button>' +
      '<button type="button" class="btn-secondary" data-accept="' + escapeHtml(field.accept || '') + '" data-kind="' + escapeHtml(field.kind || 'media') + '" onclick="pickFile(this)">Обрати файл...</button>' +
      '<input type="file" data-file-for="' + key + '" style="display:none" accept="' + escapeHtml(field.accept || '') + '">' +
      '</div>' +
      '<div class="hint" data-upload-hint="' + key + '"></div>';
  }
  if (field.type === "browse") {
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<div class="file-row">' +
      '<input type="text" data-key="' + key + '" placeholder="Шлях на цьому ПК">' +
      '<button type="button" class="btn-clear-path" onclick="clearPathField(this)" title="Очистити поле">✕</button>' +
      '<button type="button" class="btn-secondary" data-browse-mode="' + escapeHtml(field.mode || 'file') + '" data-browse-ext="' + escapeHtml(field.ext || '') + '" onclick="openFsBrowser(this)">Огляд...</button>' +
      '</div>';
  }
  if (field.type === "platforms") {
    let chips = "";
    (field.platforms || []).forEach(function (p) {
      chips += '<label class="platform-chip"><input type="checkbox" data-key="' + key + '" data-subkey="' + p + '"> ' + escapeHtml(p) + '</label>';
    });
    return '<div class="field-label">' + escapeHtml(field.label) + '</div><div class="platform-grid">' + chips + '</div>';
  }
  if (field.type === "obs_sources") {
    return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
      '<div class="platform-grid" data-obs-sources-for="' + key + '">' +
      '<span class="hint">Завантаження списку джерел OBS...</span></div>';
  }
  return '<div class="field-label">' + escapeHtml(field.label) + '</div>' +
    '<input type="text" data-key="' + key + '">';
}

function toggleSecret(btn) {
  const input = btn.previousElementSibling;
  input.type = input.type === "password" ? "text" : "password";
}

function fileToBase64(file) {
  return new Promise(function (resolve, reject) {
    const reader = new FileReader();
    reader.onload = function () { resolve(String(reader.result).split(",")[1] || ""); };
    reader.onerror = function () { reject(new Error("Не вдалося прочитати файл")); };
    reader.readAsDataURL(file);
  });
}

function clearPathField(btn) {
  const row = btn.closest(".file-row");
  if (!row) return;
  const textInput = row.querySelector('input[type="text"]');
  if (!textInput) return;
  textInput.value = "";
  const hint = row.parentElement ? row.parentElement.querySelector('[data-upload-hint="' + textInput.dataset.key + '"]') : null;
  if (hint) hint.textContent = "Поле очищено (не забудьте зберегти зміни)";
  textInput.dispatchEvent(new Event("input", {bubbles: true}));
  textInput.dispatchEvent(new Event("change", {bubbles: true}));
  markDirty();
}

function pickFile(btn) {
  const kind = btn.dataset.kind || "media";
  const row = btn.closest(".file-row");
  const fileInput = row.querySelector('input[type="file"]');
  const textInput = row.querySelector('input[type="text"]');
  const hint = row.parentElement.querySelector('[data-upload-hint="' + textInput.dataset.key + '"]');
  fileInput.onchange = async function () {
    const file = fileInput.files && fileInput.files[0];
    if (!file) return;
    const originalLabel = btn.textContent;
    btn.disabled = true;
    btn.textContent = "Завантаження...";
    if (hint) hint.textContent = "";
    try {
      const sizeMb = (file.size / 1048576).toFixed(1);
      if (hint) hint.textContent = "Завантаження " + file.name + " (" + sizeMb + " МБ)…";
      let res = await fetch("/api/upload_asset_stream", {
        method: "POST",
        headers: {
          "X-Asset-Filename": encodeURIComponent(file.name),
          "X-Asset-Kind": kind,
          "Content-Type": "application/octet-stream"
        },
        body: file
      });
      if (res.status === 404 || res.status === 405 || res.status === 501) {
        const b64 = await fileToBase64(file);
        res = await fetch("/api/upload_asset", {
          method: "POST",
          headers: {"Content-Type": "application/json"},
          body: JSON.stringify({filename: file.name, data_base64: b64, kind: kind})
        });
      }
      const data = await res.json();
      if (!data.ok) throw new Error(data.error || "Помилка завантаження файлу");
      textInput.value = data.path;
      if (hint) hint.textContent = "✅ Завантажено: " + file.name + " (" + sizeMb + " МБ)";
      markDirty();
    } catch (err) {
      if (hint) hint.textContent = "❌ Помилка: " + err.message;
    } finally {
      btn.disabled = false;
      btn.textContent = originalLabel;
      fileInput.value = "";
    }
  };
  fileInput.click();
}

let fsBrowserState = {targetInput: null, mode: "file", ext: "", currentPath: ""};

function openFsBrowser(btn) {
  const mode = btn.dataset.browseMode || "file";
  const ext = btn.dataset.browseExt || "";
  const row = btn.closest(".file-row");
  const textInput = row.querySelector('input[type="text"]');
  fsBrowserState = {targetInput: textInput, mode: mode, ext: ext, currentPath: ""};
  document.getElementById("fsModalTitle").textContent = mode === "dir" ? "Оберіть папку" : "Оберіть файл";
  document.getElementById("fsModalSelectDir").style.display = mode === "dir" ? "" : "none";
  document.getElementById("fsModalOverlay").classList.add("open");
  loadFsPath((textInput.value || "").trim());
}

function closeFsBrowser() {
  document.getElementById("fsModalOverlay").classList.remove("open");
}

async function loadFsPath(path) {
  const listEl = document.getElementById("fsModalList");
  const pathEl = document.getElementById("fsModalPath");
  const errEl = document.getElementById("fsModalError");
  errEl.style.display = "none";
  listEl.textContent = "Завантаження...";
  try {
    const onlyDirs = fsBrowserState.mode === "dir" ? "1" : "0";
    const url = "/api/browse_fs?path=" + encodeURIComponent(path || "") + "&only_dirs=" + onlyDirs + "&ext=" + encodeURIComponent(fsBrowserState.ext || "");
    const res = await fetch(url);
    const data = await res.json();
    if (!data.ok) {
      errEl.style.display = "block";
      errEl.textContent = data.error || "Помилка";
      listEl.innerHTML = "";
      return;
    }
    fsBrowserState.currentPath = data.current_path || "";
    pathEl.textContent = data.current_path || "Диски";
    listEl.innerHTML = "";
    if (data.parent_path !== null && data.parent_path !== undefined) {
      const up = document.createElement("div");
      up.className = "fs-entry";
      up.textContent = "⬆ Вгору";
      up.addEventListener("click", function () { loadFsPath(data.parent_path); });
      listEl.appendChild(up);
    }
    (data.entries || []).forEach(function (entry) {
      const row = document.createElement("div");
      row.className = "fs-entry";
      row.textContent = (entry.is_dir ? "📁 " : "📄 ") + entry.name;
      row.addEventListener("click", function () {
        if (entry.is_dir) {
          loadFsPath(entry.path);
        } else if (fsBrowserState.mode === "file") {
          selectFsPath(entry.path);
        }
      });
      listEl.appendChild(row);
    });
    if (!data.entries || (data.entries.length === 0 && (data.parent_path === null || data.parent_path === undefined))) {
      listEl.innerHTML = '<div class="hint">Порожньо</div>';
    }
  } catch (err) {
    errEl.style.display = "block";
    errEl.textContent = "Не вдалося завантажити: " + err.message;
    listEl.innerHTML = "";
  }
}

function selectFsPath(path) {
  if (fsBrowserState.targetInput) {
    fsBrowserState.targetInput.value = path;
    markDirty();
  }
  closeFsBrowser();
}

document.getElementById("fsModalCancel").addEventListener("click", closeFsBrowser);
document.getElementById("fsModalSelectDir").addEventListener("click", function () {
  selectFsPath(fsBrowserState.currentPath);
});
document.getElementById("fsModalOverlay").addEventListener("click", function (e) {
  if (e.target.id === "fsModalOverlay") closeFsBrowser();
});

function sectionIconSvg(iconKey, color) {
  const c = escapeHtml(color || "#4facfe");
  const glyphs = {
    gear: '<path d="M12 8a4 4 0 100 8 4 4 0 000-8z" fill="none" stroke="#fff" stroke-width="1.6"/><path d="M12 4v2M12 18v2M4 12h2M18 12h2M6.3 6.3l1.4 1.4M16.3 16.3l1.4 1.4M6.3 17.7l1.4-1.4M16.3 7.7l1.4-1.4" stroke="#fff" stroke-width="1.6" stroke-linecap="round"/>',
    youtube: '<rect x="5" y="8" width="14" height="8" rx="2.5" fill="#fff"/><path d="M11 10.8v4.4l4-2.2z" fill="' + c + '"/>',
    tiktok: '<text x="12" y="16.5" font-size="10" font-weight="800" text-anchor="middle" fill="#fff" font-family="Segoe UI, sans-serif">TT</text>',
    twitch: '<rect x="6" y="5" width="12" height="11" rx="1.5" fill="#fff"/><rect x="8.3" y="7.3" width="1.6" height="4.5" fill="' + c + '"/><rect x="13.1" y="7.3" width="1.6" height="4.5" fill="' + c + '"/><path d="M9 16l-2.5 2.5V16" fill="#fff"/>',
    kick: '<text x="12" y="16.5" font-size="11" font-weight="800" text-anchor="middle" fill="#fff" font-family="Segoe UI, sans-serif">K</text>',
    donate: '<path d="M12 18s-6-3.8-6-8.2C6 7 7.8 5.3 10 5.3c1 0 1.6.4 2 .9.4-.5 1-.9 2-.9 2.2 0 4 1.7 4 4.5 0 4.4-6 8.2-6 8.2z" fill="#fff"/>',
    speaker: '<path d="M6 10v4h3l4 3V7l-4 3H6z" fill="#fff"/><path d="M15.5 9.5a3.5 3.5 0 010 5" fill="none" stroke="#fff" stroke-width="1.6" stroke-linecap="round"/>',
    shield: '<path d="M12 5l6 2.2v4.3c0 4-2.6 6.6-6 7.5-3.4-.9-6-3.5-6-7.5V7.2L12 5z" fill="none" stroke="#fff" stroke-width="1.6" stroke-linejoin="round"/><path d="M9.3 12l1.8 1.8 3.6-3.6" fill="none" stroke="#fff" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/>',
    chat: '<path d="M5 7h14v8H10l-3 3v-3H5z" fill="none" stroke="#fff" stroke-width="1.6" stroke-linejoin="round"/>',
    chart: '<rect x="6" y="13" width="2.6" height="5" fill="#fff"/><rect x="10.7" y="9" width="2.6" height="9" fill="#fff"/><rect x="15.4" y="6" width="2.6" height="12" fill="#fff"/>',
    gift: '<rect x="5" y="10" width="14" height="8" rx="1" fill="#fff"/><rect x="5" y="7.5" width="14" height="3" rx="1" fill="#fff"/><rect x="11" y="7.5" width="2" height="10.5" fill="' + c + '"/><path d="M9 7.5c-1.4 0-2.2-1-2.2-2S7.6 3.5 9 3.5c1.6 0 3 2 3 4-2-.4-3 0-3 0zM15 7.5c1.4 0 2.2-1 2.2-2S16.4 3.5 15 3.5c-1.6 0-3 2-3 4 2-.4 3 0 3 0z" fill="#fff"/>',
    megaphone: '<path d="M5 10v4h2.5L14 17V7L7.5 10H5z" fill="#fff"/><path d="M16 10.2a2.4 2.4 0 010 3.6" fill="none" stroke="#fff" stroke-width="1.6" stroke-linecap="round"/>',
    wifi: '<path d="M6 11a8.5 8.5 0 0112 0" fill="none" stroke="#fff" stroke-width="1.6" stroke-linecap="round"/><path d="M8.5 13.7a5 5 0 017 0" fill="none" stroke="#fff" stroke-width="1.6" stroke-linecap="round"/><circle cx="12" cy="16.3" r="1.3" fill="#fff"/>',
  };
  const glyph = glyphs[iconKey] || glyphs.gear;
  return '<svg width="22" height="22" viewBox="0 0 24 24" style="flex-shrink:0"><circle cx="12" cy="12" r="11" fill="' + c + '"/>' + glyph + '</svg>';
}

function renderSchema() {
  const container = document.getElementById("sectionsContainer");
  container.innerHTML = "";
  SCHEMA.forEach(function (section, idx) {
    const sectionEl = document.createElement("div");
    sectionEl.className = "section" + (idx === 0 ? " open" : "");
    sectionEl.dataset.sectionId = section.id;
    sectionEl.style.setProperty("--accent", section.color || "#4facfe");

    const header = document.createElement("div");
    header.className = "section-header";
    header.innerHTML = sectionIconSvg(section.icon, section.color) + '<span class="section-title">' + escapeHtml(section.title) + '</span><span class="section-caret">▶</span>';
    header.addEventListener("click", function () {
      sectionEl.classList.toggle("open");
    });

    const body = document.createElement("div");
    body.className = "section-body";
    section.fields.forEach(function (field) {
      const fieldEl = document.createElement("div");
      fieldEl.className = "field";
      fieldEl.dataset.label = (field.label || "").toLowerCase();
      fieldEl.dataset.fieldKey = field.key;
      fieldEl.innerHTML = fieldInputHtml(field);
      body.appendChild(fieldEl);
    });

    sectionEl.appendChild(header);
    sectionEl.appendChild(body);
    container.appendChild(sectionEl);
  });

  container.querySelectorAll("input, textarea").forEach(function (el) {
    el.addEventListener("input", markDirty);
    el.addEventListener("change", markDirty);
  });

  // Автопереклад озвучки: два перемикачі взаємовиключні
  const trUk = container.querySelector('input[data-key="tts_translate_uk"]');
  const trEn = container.querySelector('input[data-key="tts_translate_en"]');
  if (trUk && trEn) {
    trUk.addEventListener("change", function () { if (trUk.checked) { trEn.checked = false; } });
    trEn.addEventListener("change", function () { if (trEn.checked) { trUk.checked = false; } });
  }

  loadObsSourcesFields();
}

function loadObsSourcesFields() {
  const containers = document.querySelectorAll('[data-obs-sources-for]');
  if (!containers.length) return;
  fetch("/api/obs_sources").then(function (res) { return res.json(); }).then(function (data) {
    const names = (data && data.ok && Array.isArray(data.names)) ? data.names : [];
    containers.forEach(function (el) {
      const key = el.dataset.obsSourcesFor;
      if (!names.length) {
        el.innerHTML = '<span class="hint">Джерел не знайдено (перевірте, чи OBS запущено і скрипт активний)</span>';
        return;
      }
      let chips = "";
      names.forEach(function (name) {
        chips += '<label class="platform-chip"><input type="checkbox" data-key="' + key + '" data-subkey="' + escapeHtml(name) + '"> ' + escapeHtml(name) + '</label>';
      });
      el.innerHTML = chips;
      el.querySelectorAll("input").forEach(function (input) {
        input.addEventListener("input", markDirty);
        input.addEventListener("change", markDirty);
      });
    });
    // Позначки чекбоксів залежать від вже завантажених currentSettings -
    // застосовуємо їх повторно тепер, коли чекбокси щойно з'явились у DOM.
    applyValues(currentSettings);
  }).catch(function () {
    containers.forEach(function (el) {
      el.innerHTML = '<span class="hint">Не вдалося завантажити список джерел OBS</span>';
    });
  });
}

function applyValues(settings) {
  currentSettings = settings || {};
  SCHEMA.forEach(function (section) {
    section.fields.forEach(function (field) {
      if (field.type === "link" || field.type === "action" || field.type === "dynlink") return;
      const value = currentSettings[field.key];
      if (field.type === "platforms" || field.type === "obs_sources") {
        const group = value && typeof value === "object" ? value : {};
        document.querySelectorAll('input[data-key="' + field.key + '"][data-subkey]').forEach(function (el) {
          el.checked = !!group[el.dataset.subkey];
        });
        return;
      }
      const input = document.querySelector('[data-key="' + field.key + '"]:not([data-subkey])');
      if (!input) return;
      if (field.type === "bool") {
        input.checked = !!value;
      } else {
        input.value = value == null ? "" : value;
      }
    });
  });
}

function collectPayload() {
  const payload = {};
  SCHEMA.forEach(function (section) {
    section.fields.forEach(function (field) {
      if (field.type === "link" || field.type === "action" || field.type === "dynlink") return;
      if (field.type === "platforms" || field.type === "obs_sources") {
        const group = {};
        document.querySelectorAll('input[data-key="' + field.key + '"][data-subkey]').forEach(function (el) {
          group[el.dataset.subkey] = el.checked;
        });
        payload[field.key] = group;
        return;
      }
      const input = document.querySelector('[data-key="' + field.key + '"]:not([data-subkey])');
      if (!input) return;
      if (field.type === "bool") {
        payload[field.key] = input.checked;
      } else if (field.type === "int") {
        const parsed = parseInt(input.value, 10);
        payload[field.key] = isNaN(parsed) ? 0 : parsed;
      } else {
        payload[field.key] = input.value;
      }
    });
  });
  return payload;
}

async function load() {
  setStatus("Завантаження...", "");
  try {
    const res = await fetch("/api/settings");
    const data = await res.json();
    if (!data.ok) throw new Error(data.error || "Помилка завантаження");
    applyValues(data.settings);
    dirty = false;
    document.getElementById("saveBtn").textContent = "Зберегти зміни";
    setStatus("Завантажено", "ok");
  } catch (err) {
    setStatus("Не вдалося завантажити налаштування: " + err.message, "err");
  }
}

async function save() {
  const btn = document.getElementById("saveBtn");
  btn.disabled = true;
  setStatus("Зберігаю...", "");
  try {
    const payload = collectPayload();
    const res = await fetch("/api/settings", {
      method: "POST",
      headers: {"Content-Type": "application/json"},
      body: JSON.stringify(payload)
    });
    const data = await res.json();
    if (!data.ok) throw new Error(data.error || "Помилка збереження");
    dirty = false;
    btn.textContent = "Зберегти зміни";
    setStatus("Збережено. Застосовую зміни (сервіси перезапускаються)...", "ok");
    setTimeout(function () { setStatus("Збережено ✓", "ok"); }, 2500);
  } catch (err) {
    setStatus("Помилка збереження: " + err.message, "err");
  } finally {
    btn.disabled = false;
  }
}

async function runAction(btn) {
  const endpoint = btn.dataset.actionEndpoint;
  const key = btn.closest(".field").dataset.fieldKey;
  const hint = document.querySelector('[data-action-hint="' + key + '"]');
  btn.disabled = true;
  if (hint) { hint.textContent = "Зберігаю налаштування..."; }
  try {
    if (dirty) { await save(); }
    if (hint) { hint.textContent = "Виконую..."; }
    const res = await fetch(endpoint, {method: "POST", headers: {"Content-Type": "application/json"}, body: "{}"});
    const data = await res.json();
    if (hint) { hint.textContent = data.ok ? "Готово \u2713" : ("Помилка: " + (data.error || "невідома")); }
  } catch (err) {
    if (hint) { hint.textContent = "Помилка: " + err.message; }
  } finally {
    btn.disabled = false;
  }
}

function doSearch(query) {
  const q = (query || "").trim().toLowerCase();
  document.querySelectorAll(".section").forEach(function (sectionEl) {
    let anyVisible = false;
    sectionEl.querySelectorAll(".field").forEach(function (fieldEl) {
      const match = !q || fieldEl.dataset.label.indexOf(q) !== -1 || fieldEl.dataset.fieldKey.indexOf(q) !== -1;
      fieldEl.classList.toggle("hidden", !match);
      if (match) anyVisible = true;
    });
    sectionEl.style.display = anyVisible ? "" : "none";
    if (q && anyVisible) sectionEl.classList.add("open");
  });
}

function showFatalError(message) {
  const el = document.getElementById("fatalError");
  if (!el) return;
  el.style.display = "block";
  el.textContent = "Помилка панелі налаштувань: " + message + ". Спробуйте: правою кнопкою по доку -> видалити і додати дублі /settings, або натисніть \\"Оновити\\".";
}

window.addEventListener("error", function (e) {
  showFatalError((e && e.message) || "Невідома помилка JavaScript");
});
window.addEventListener("unhandledrejection", function (e) {
  showFatalError((e && e.reason && (e.reason.message || String(e.reason))) || "Невідома помилка Promise");
});

document.getElementById("saveBtn").addEventListener("click", save);
document.getElementById("reloadBtn").addEventListener("click", function () {
  if (dirty && !confirm("Є незбережені зміни. Оновити і втратити їх?")) return;
  load();
});
document.getElementById("searchInput").addEventListener("input", function (e) {
  doSearch(e.target.value);
});
window.addEventListener("beforeunload", function (e) {
  if (dirty) { e.preventDefault(); e.returnValue = ""; }
});

try {
  renderSchema();
  load();
} catch (err) {
  showFatalError((err && err.stack) || (err && err.message) || String(err));
}
</script>
</body>
</html>"""


HTML_CONTENT = """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8">
<style>
*{box-sizing:border-box}
body{background-color:transparent!important;background-image:var(--bg-image,none);background-position:center;background-size:cover;color:#f1f1f7;font-family:'Segoe UI',system-ui,sans-serif;margin:0;padding:0;overflow:hidden;height:100vh;font-size:var(--font-size,14px)}
#barrier{position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(14,14,19,0.85);backdrop-filter:blur(5px);display:flex;align-items:center;justify-content:center;z-index:9999}
.btn{background:linear-gradient(135deg,#00f2fe 0%,#4facfe 100%);padding:12px 24px;border-radius:30px;font-weight:bold;border:none;color:white;cursor:pointer}
.btn-danger{background:linear-gradient(135deg,#ff416c 0%,#ff4b2b 100%);padding:8px 16px;border-radius:20px;font-weight:bold;border:none;color:white;cursor:pointer;margin-left:10px}
.btn-filter{background:rgba(255,255,255,0.1);padding:6px 12px;border-radius:15px;font-weight:normal;border:1px solid rgba(255,255,255,0.2);color:#e2e2e9;cursor:pointer;margin:0 3px}
.btn-filter.active{background:linear-gradient(135deg,#00f2fe 0%,#4facfe 100%);border-color:transparent;color:white}
#filter-twitch.active{background:linear-gradient(135deg,#9146FF 0%,#772CE8 100%);color:#fff}
#filter-youtube.active{background:linear-gradient(135deg,#FF0000 0%,#CC0000 100%);color:#fff}
#filter-tiktok.active{background:linear-gradient(135deg,#00F2EA 0%,#FF0050 100%);color:#fff}
#filter-kick.active{background:linear-gradient(135deg,#53FC18 0%,#3ecf0f 100%);color:#04220a}
.header-section{position:fixed;top:0;left:0;right:0;z-index:100;background:rgba(14,14,19,0.9);backdrop-filter:blur(10px);padding:10px;border-bottom:1px solid rgba(255,255,255,0.1);overflow:visible}
.platform-filters{display:flex;gap:5px;flex-wrap:wrap;margin-bottom:8px}
.controls{display:flex;gap:10px;flex-wrap:wrap;position:relative;overflow:visible}.menu-wrapper{position:relative;overflow:visible}.menu-dropdown{display:none;position:fixed;top:56px;left:10px;right:auto;min-width:220px;max-width:min(320px,calc(100vw - 20px));max-height:min(60vh,320px);overflow-y:auto;background:rgba(20,20,28,0.99);border:1px solid rgba(255,255,255,0.18);border-radius:14px;padding:8px;box-shadow:0 12px 28px rgba(0,0,0,0.52);z-index:2147483000}.menu-dropdown.show{display:flex;flex-direction:column;gap:8px}.menu-dropdown .btn-danger{margin-left:0;width:100%;text-align:left;display:block;visibility:visible;opacity:1;position:relative;z-index:2147483001}
.search-section{position:fixed;top:110px;left:0;right:0;z-index:99;padding:10px;background:rgba(14,14,19,0.8);backdrop-filter:blur(5px);border-bottom:1px solid rgba(255,255,255,0.1)}
.search-input{width:100%;padding:10px 15px;border-radius:25px;border:1px solid rgba(255,255,255,0.2);background:rgba(0,0,0,0.6);color:#f1f1f7;font-size:14px;backdrop-filter:blur(5px)}
.chat-container{position:fixed;top:170px;left:0;right:0;bottom:0;overflow-y:auto;padding:10px}
#log{display:flex;flex-direction:column;gap:8px}
.msg{padding:10px 14px;border-radius:12px;background:var(--msg-color,rgba(255,255,255,0.1));border:1px solid rgba(255,255,255,0.08);backdrop-filter:blur(5px);animation:fadeIn 0.25s ease forwards}
.msg.fade-out{opacity:0;transform:translateY(-10px)}
.msg.hidden{display:none}
.twitch{border-left:4px solid #9146FF}
.kick{border-left:4px solid #53fc18}
.youtube{border-left:4px solid #ff0000}
.tiktok{border-left:4px solid #ff0050}
.bot{border-left:4px solid #00f2fe}
.alert-card{background:linear-gradient(90deg,rgba(255,215,0,0.15) 0%,rgba(255,165,0,0.02) 100%);border:2px solid #ffd700}
.meta{display:flex;align-items:center;gap:6px;font-size:0.85em;margin-bottom:4px}
.p-icon{font-weight:bold;font-size:9px;padding:1px 4px;border-radius:4px;color:#fff}
.p-tw{background:#9146FF}
.p-kk{background:#53fc18;color:#000}
.p-yt{background:#ff0000}
.p-tt{background:#ff0050}
.p-bt{background:#00f2fe;color:#000}
.name{font-weight:bold;color:#ffb703;cursor:pointer;user-select:none}
.name:hover{color:#ffd700;text-decoration:underline}
.text{color:#e2e2e9;word-break:break-word}
.alert-title{color:#ffd700;font-weight:bold;text-transform:uppercase;margin-bottom:2px}
@keyframes fadeIn{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}
.modal{display:none;position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,0.8);backdrop-filter:blur(8px);z-index:10000;justify-content:center;align-items:center}
.modal-content{background:rgba(30,30,40,0.95);border-radius:20px;padding:20px;min-width:300px;max-width:500px;width:90%;max-height:80vh;overflow-y:auto;box-shadow:0 0 20px rgba(0,0,0,0.5);border:1px solid rgba(255,255,255,0.2)} 
.modal-header{display:flex;justify-content:space-between;align-items:center;border-bottom:1px solid rgba(255,255,255,0.2);padding-bottom:10px;margin-bottom:15px}
.modal-header h3{margin:0;color:#ffb703}
.close-modal{background:none;border:none;color:#fff;font-size:28px;cursor:pointer}
.blocked-list{list-style:none;padding:0;margin:0}
.blocked-item{display:flex;justify-content:space-between;align-items:center;padding:10px;border-bottom:1px solid rgba(255,255,255,0.1)}
.blocked-name{font-weight:bold;color:#e2e2e9}
.mod-bulk-bar{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:8px 4px 12px 4px;border-bottom:1px solid rgba(255,255,255,.08);margin-bottom:8px;font-size:12px;opacity:.95}
.clear-all-btn{background:#e14a4a;border:none;border-radius:20px;padding:6px 14px;color:white;cursor:pointer;font-size:12px;font-weight:600}
.clear-all-btn:hover{background:#c93c3c}
.unblock-btn{background:#4caf50;border:none;border-radius:20px;padding:5px 12px;color:white;cursor:pointer;font-size:12px}
.unblock-btn:hover{background:#45a049}
.context-menu{display:none;position:fixed;background:rgba(30,30,40,0.95);border:1px solid rgba(255,255,255,0.2);border-radius:12px;padding:10px;z-index:10001;min-width:200px;box-shadow:0 4px 12px rgba(0,0,0,0.5)}
.context-menu.show{display:block}
.context-menu-header{font-weight:bold;color:#ffb703;padding:8px;border-bottom:1px solid rgba(255,255,255,0.1);margin-bottom:8px}
.context-menu-item{padding:8px 12px;cursor:pointer;border-radius:6px;color:#e2e2e9;display:flex;align-items:center;gap:8px}
.context-menu-item:hover{background:rgba(255,255,255,0.1)}
.context-menu-item.danger{color:#ff416c}
.context-menu-item.danger:hover{background:rgba(255,65,108,0.2)}
.netmon-bar{display:none;position:fixed;left:0;right:0;bottom:0;z-index:98;padding:6px 12px;background:rgba(14,14,19,0.92);backdrop-filter:blur(8px);border-top:1px solid rgba(255,255,255,0.12);font-size:0.82em;align-items:center;gap:14px;flex-wrap:wrap}
.netmon-bar.show{display:flex}
body.netmon-active .chat-container{bottom:32px}.chat-container{transition:bottom .15s ease}
.netmon-dot{width:8px;height:8px;border-radius:50%;flex-shrink:0}
.netmon-dot.ok{background:#3ddc84;box-shadow:0 0 6px #3ddc84}
.netmon-dot.warn{background:#ffb703;box-shadow:0 0 6px #ffb703}
.netmon-dot.bad{background:#ff416c;box-shadow:0 0 6px #ff416c}
.netmon-item{color:#c7c7d1;white-space:nowrap}
.netmon-item b{color:#f1f1f7;font-weight:600}
</style>
</head>
<body>
<div id="barrier"><button class="btn" onclick="unlock()">АКТИВУВАТИ ЧАТ</button></div>
<div class="header-section">
<div class="platform-filters">
<button class="btn-filter active" onclick="togglePlatform('twitch')" id="filter-twitch">Twitch</button>
<button class="btn-filter active" onclick="togglePlatform('youtube')" id="filter-youtube">YouTube</button>
<button class="btn-filter active" onclick="togglePlatform('tiktok')" id="filter-tiktok">TikTok</button>
<button class="btn-filter active" onclick="togglePlatform('kick')" id="filter-kick">Kick</button>
<button class="btn-filter active" onclick="togglePlatform('bot')" id="filter-bot">Бот</button>
</div>
<div class="controls">
<div class="menu-wrapper">
<button class="btn-danger" onclick="toggleAdminMenu(event)">☰ Меню</button>
<div id="adminMenuDropdown" class="menu-dropdown">
<button class="btn-danger" onclick="clearChat();hideAdminMenu()">🗑 Очистити чат</button>
<button class="btn-danger" onclick="showBlockedModal();hideAdminMenu()">🚫 Заблоковані</button>
<button class="btn-danger" onclick="showNoTtsModal();hideAdminMenu()">🔇 Вимкнені TTS</button>
<button class="btn-danger" onclick="showNicknamesModal();hideAdminMenu()">✏️ Псевдоніми</button>
<button class="btn-danger" id="ttsToggleBtn" onclick="toggleTtsFromMenu()">🔇 Вимкнути TTS</button>
</div>
</div>
</div>
</div>
<div class="search-section">
<input type="text" class="search-input" id="searchInput" placeholder="Пошук за ніком або текстом..." oninput="searchMessages()">
</div>
<div class="chat-container" id="chatScroller"><div id="log"></div></div>
<div class="netmon-bar" id="netmonBar">
<span class="netmon-dot" id="netmonDot"></span>
<span class="netmon-item" id="netmonPing">Ping: —</span>
<span class="netmon-item" id="netmonLoss">Втрати: —</span>
<span class="netmon-item" id="netmonJitter" style="display:none">Джитер: —</span>
<span class="netmon-item" id="netmonTargets" style="display:none" title="По цілях"></span>
<span class="netmon-item" id="netmonObs" style="display:none">Кадри OBS: —</span>
<span class="netmon-item" id="netmonSpeed" style="display:none">↓ — / ↑ —</span>
</div>
<div id="blockedModal" class="modal">
<div class="modal-content">
<div class="modal-header"><h3>🚫 Заблоковані користувачі</h3><span class="close-modal" onclick="closeBlockedModal()">&times;</span></div>
<div class="mod-bulk-bar"><span id="blockedCount">0 записів</span><button class="clear-all-btn" onclick="unblockAllUsers()">🔓 Розблокувати всіх</button></div>
<div id="blockedListContainer"><ul class="blocked-list" id="blockedList"></ul></div>
</div>
</div>
<div id="noTtsModal" class="modal">
<div class="modal-content">
<div class="modal-header"><h3>🔇 Користувачі з вимкненим TTS</h3><span class="close-modal" onclick="closeNoTtsModal()">&times;</span></div>
<div class="mod-bulk-bar"><span id="noTtsCount">0 записів</span><button class="clear-all-btn" onclick="enableTtsAllUsers()">🔊 Увімкнути TTS усім</button></div>
<div id="noTtsListContainer"><ul class="blocked-list" id="noTtsList"></ul></div>
</div>
</div>
<div id="nicknamesModal" class="modal">
<div class="modal-content">
<div class="modal-header"><h3>✏️ Кастомні псевдоніми</h3><span class="close-modal" onclick="closeNicknamesModal()">&times;</span></div>
<div id="nicknamesListContainer"><ul class="blocked-list" id="nicknamesList"></ul></div>
</div>
</div>
<div id="topActiveModal" class="modal">
<div class="modal-content">
<div class="modal-header"><h3>🏆 Топ активних</h3><span class="close-modal" onclick="closeTopActiveModal()">&times;</span></div>
<div style="padding:6px 4px 2px;font-weight:600;color:#e2e2e9">Топ-5 за останні 30 днів</div>
<div id="topActive30Container"><ul class="blocked-list" id="topActive30List"></ul></div>
<div style="padding:14px 4px 2px;font-weight:600;color:#e2e2e9">Топ-10 за весь час</div>
<div id="topActiveAllContainer"><ul class="blocked-list" id="topActiveAllList"></ul></div>
</div>
</div>
<div id="contextMenu" class="context-menu">
<div class="context-menu-header" id="contextMenuHeader">Користувач</div>
<div class="context-menu-item" onclick="setNicknameFromMenu()">Задати псевдонім</div>
<div class="context-menu-item" onclick="openVoiceModalFromMenu()">Голос озвучки</div>
<div class="context-menu-item" onclick="disableTtsFromMenu()">Вимкнути TTS</div>
<div class="context-menu-item danger" onclick="blockFromMenu()">Заблокувати користувача</div>
<div class="context-menu-item mod-only-item" style="display:none" onclick="replyFromMenu()">💬 Відповісти</div>
<div class="context-menu-item mod-only-item" style="display:none" onclick="timeoutFromMenu()">⏱ Тайм-аут</div>
<div class="context-menu-item danger mod-only-item" style="display:none" onclick="banFromMenu()">🔨 Бан назавжди</div>
<div class="context-menu-item danger mod-only-item" style="display:none" onclick="deleteMessageFromMenu()">🗑 Видалити повідомлення</div>
</div>
<div id="voiceModal" class="modal">
<div class="modal-content">
<div class="modal-header"><h3>🎤 Голос користувача</h3><span class="close-modal" onclick="closeVoiceModal()">&times;</span></div>
<div style="display:flex;flex-direction:column;gap:12px">
<div id="voiceModalUserLabel" class="blocked-name"></div>
<select id="voiceProfileSelect" class="search-input"></select>
<div style="display:flex;gap:10px;flex-wrap:wrap">
<button class="btn" onclick="saveVoiceAssignmentFromModal()">Зберегти</button>
<button class="btn-danger" onclick="clearVoiceAssignmentFromModal()">Скинути</button>
</div>
</div>
</div>
</div>
<script>
let maxId=0,unlocked=false,ttsQueue=[],ttsActive=false,loopStarted=false;
let cCache={ttsTemplate:"{nickname} {comment}",ttsReadNicknames:true,msgTimeout:20,ttsVolume:0.8,ttsEngine:"google",ttsVoice:"uk-UA",ttsSpeed:1.0,ringtoneUrl:null,ttsOutputToStream:true,ttsEnabled:true};
let activePlatforms={twitch:true,youtube:true,tiktok:true,kick:true,bot:true,alerts:true};
let searchTerm='';
let currentContextUser='';
let currentContextPlatform='';
let currentContextDisplayName='';
let currentContextAlias='';
let currentContextPlatformUserId='';
let currentContextMessageId='';
function toggleAdminMenu(event){if(event)event.stopPropagation();let menu=document.getElementById('adminMenuDropdown');if(!menu)return;let willShow=!menu.classList.contains('show');hideAdminMenu();if(!willShow)return;let btn=(event&&event.currentTarget)||document.querySelector('.menu-wrapper .btn-danger');if(btn){let rect=btn.getBoundingClientRect();let top=Math.max(8,Math.min(window.innerHeight-60,rect.bottom+8));let left=Math.max(8,Math.min(window.innerWidth-240,rect.left));menu.style.top=top+'px';menu.style.left=left+'px';menu.style.right='auto';}menu.classList.add('show')}
function hideAdminMenu(){let menu=document.getElementById('adminMenuDropdown');if(menu)menu.classList.remove('show')}
function unlock(){unlocked=true;let barrier=document.getElementById('barrier');if(barrier)barrier.style.display='none';fetch('/get_config').then(r=>r.json()).then(c=>{cCache={...cCache,...c};if(c.bgImage){document.documentElement.style.setProperty('--bg-image',`url('/local_bg?t=${Date.now()}')`)}else{document.documentElement.style.setProperty('--bg-image','none')}document.documentElement.style.setProperty('--msg-color',c.msgColor);document.documentElement.style.setProperty('--font-size',c.fontSize+'px');updateTtsToggleBtn();});if(!loopStarted){loopStarted=true;loop()}}
function updateTtsToggleBtn(){let btn=document.getElementById('ttsToggleBtn');if(!btn)return;btn.textContent=cCache.ttsEnabled?'🔇 Вимкнути TTS':'🔊 Увімкнути TTS';}
function toggleTtsFromMenu(){fetch('/api/tts/toggle',{method:'POST'}).then(r=>r.json()).then(d=>{cCache.ttsEnabled=!!d.enabled;updateTtsToggleBtn();hideAdminMenu();if(!cCache.ttsEnabled){ttsQueue=[];window.speechSynthesis&&window.speechSynthesis.cancel();}}).catch(()=>alert('Не вдалося перемкнути TTS'));}
function togglePlatform(platform){activePlatforms[platform]=!activePlatforms[platform];document.getElementById('filter-'+platform).classList.toggle('active');let msgs=document.querySelectorAll('.msg');msgs.forEach(msg=>{if(msg.classList.contains(platform)){if(activePlatforms[platform]){if(!searchTerm||matchesSearch(msg)){msg.classList.remove('hidden')}}else{msg.classList.add('hidden')}}});fetch('/set_platform_filter',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({platform:platform,enabled:activePlatforms[platform]})})}
function searchMessages(){searchTerm=document.getElementById('searchInput').value.toLowerCase();let msgs=document.querySelectorAll('.msg');msgs.forEach(msg=>{if(matchesSearch(msg)&&isActivePlatform(msg)){msg.classList.remove('hidden')}else{msg.classList.add('hidden')}})}
function matchesSearch(msg){if(!searchTerm)return true;let name=msg.querySelector('.name');let text=msg.querySelector('.text');if(!name||!text)return true;return name.textContent.toLowerCase().includes(searchTerm)||text.textContent.toLowerCase().includes(searchTerm)}
function isActivePlatform(msg){if(msg.classList.contains('twitch'))return activePlatforms['twitch'];if(msg.classList.contains('youtube'))return activePlatforms['youtube'];if(msg.classList.contains('tiktok'))return activePlatforms['tiktok'];if(msg.classList.contains('kick'))return activePlatforms['kick'];if(msg.classList.contains('bot'))return activePlatforms['bot'];return true}
function showContextMenu(event,meta){event.stopPropagation();currentContextUser=(meta.username||meta.sourceDisplayName||meta.displayName||'').trim();currentContextPlatform=(meta.platform||'').trim();currentContextDisplayName=(meta.sourceDisplayName||meta.displayName||currentContextUser||'').trim();currentContextAlias=(meta.displayName||currentContextDisplayName||currentContextUser||'').trim();currentContextPlatformUserId=(meta.platformUserId||'').trim();currentContextMessageId=(meta.messageId||'').trim();document.getElementById('contextMenuHeader').textContent=' '+currentContextAlias;let modOnly=(currentContextPlatform==='twitch'||currentContextPlatform==='kick');document.querySelectorAll('.mod-only-item').forEach(el=>{el.style.display=modOnly?'block':'none';});let menu=document.getElementById('contextMenu');menu.style.left='0px';menu.style.top='0px';menu.classList.add('show');let mw=menu.offsetWidth;let mh=menu.offsetHeight;let x=event.pageX;let y=event.pageY;if(x+mw>window.innerWidth)x=Math.max(0,window.innerWidth-mw-8);if(y+mh>window.innerHeight)y=Math.max(0,window.innerHeight-mh-8);menu.style.left=x+'px';menu.style.top=y+'px'}
function hideContextMenu(){document.getElementById('contextMenu').classList.remove('show')}
function setNicknameFromMenu(){if(!currentContextUser&&!currentContextDisplayName)return;let currentLabel=currentContextAlias||currentContextDisplayName||currentContextUser;let nickname=prompt('Новий псевдонім для '+currentLabel,(currentContextAlias&&currentContextAlias!==currentContextDisplayName)?currentContextAlias:'');if(nickname===null)return;fetch('/set_custom_nickname',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({platform:currentContextPlatform,username:currentContextUser,display_name:currentContextDisplayName,nickname:nickname})}).then(r=>{if(!r.ok)throw new Error('save failed');hideContextMenu();if(document.getElementById('nicknamesModal').style.display==='flex'){fetchCustomNicknames();}alert(nickname.trim()?'Псевдонім збережено':'Псевдонім видалено');}).catch(()=>alert('Не вдалося зберегти псевдонім'));}
function openVoiceModalFromMenu(){if(!currentContextUser&&!currentContextDisplayName)return;hideContextMenu();Promise.all([fetch('/voice_profiles').then(r=>r.json()),fetch(`/user_voice_assignment?platform=${encodeURIComponent(currentContextPlatform)}&username=${encodeURIComponent(currentContextUser)}&display_name=${encodeURIComponent(currentContextDisplayName)}`).then(r=>r.json())]).then(([profiles,current])=>{let select=document.getElementById('voiceProfileSelect');select.innerHTML='';let defaultOption=document.createElement('option');defaultOption.value='';defaultOption.textContent='За замовчуванням';select.appendChild(defaultOption);profiles.forEach(profile=>{let option=document.createElement('option');option.value=profile.id;option.textContent=profile.title||profile.id;select.appendChild(option);});select.value=(current&&current.voice_id)||'';document.getElementById('voiceModalUserLabel').textContent=currentContextAlias||currentContextDisplayName||currentContextUser||'Користувач';document.getElementById('voiceModal').style.display='flex';}).catch(()=>alert('Не вдалося завантажити голосові профілі'));}
function closeVoiceModal(){document.getElementById('voiceModal').style.display='none';}
function saveVoiceAssignmentFromModal(){let voiceId=(document.getElementById('voiceProfileSelect').value||'').trim();fetch('/set_user_voice_assignment',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({platform:currentContextPlatform,username:currentContextUser,display_name:currentContextDisplayName,voice_id:voiceId})}).then(r=>{if(!r.ok)throw new Error('save failed');closeVoiceModal();alert(voiceId?'Голосовий профіль збережено':'Встановлено голос за замовчуванням');}).catch(()=>alert('Не вдалося зберегти голосовий профіль'));}
function clearVoiceAssignmentFromModal(){fetch('/remove_user_voice_assignment',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({platform:currentContextPlatform,username:currentContextUser,display_name:currentContextDisplayName})}).then(r=>{if(!r.ok)throw new Error('remove failed');closeVoiceModal();alert('Голосовий профіль скинуто');}).catch(()=>alert('Не вдалося скинути голосовий профіль'));}
function disableTtsFromMenu(){if(currentContextUser){fetch('/disable_tts_user',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:currentContextUser})}).then(()=>{hideContextMenu();alert('TTS вимкнено для '+currentContextUser)})}}
function blockFromMenu(){if(confirm('Заблокувати '+currentContextUser+'?')){fetch('/block_user',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:currentContextUser})}).then(()=>{hideContextMenu();let msgs=document.querySelectorAll('.msg');msgs.forEach(msg=>{if(msg.querySelector('.name')&&msg.querySelector('.name').textContent.includes(currentContextUser)){msg.remove()}})})}}
function callModAction(body){return fetch('/api/mod/action',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)}).then(r=>r.json()).catch(()=>({ok:false,error:'Не вдалося виконати запит до сервера'}));}
function replyFromMenu(){hideContextMenu();if(!currentContextMessageId){alert('Немає ID цього повідомлення для відповіді (повідомлення прийшло до оновлення скрипта - дочекайтесь нового повідомлення від цього юзера)');return;}let text=prompt('Відповідь для '+currentContextAlias+':','');if(text===null)return;text=text.trim();if(!text){alert('Порожня відповідь не надсилається');return;}callModAction({platform:currentContextPlatform,action:'reply',message_id:currentContextMessageId,text:text}).then(res=>{if(res.ok){alert('Відповідь надіслано')}else{alert('Помилка: '+(res.error||'невідома'))}});}
function timeoutFromMenu(){hideContextMenu();if(!currentContextPlatformUserId){alert('Немає ID користувача для тайм-ауту (повідомлення прийшло до оновлення скрипта - дочекайтесь нового повідомлення від цього юзера)');return;}let mins=prompt('Тайм-аут для '+currentContextAlias+' (ID: '+currentContextPlatformUserId+') на скільки хвилин?','10');if(mins===null)return;let n=parseInt(mins,10);if(!n||n<=0){alert('Некоректна кількість хвилин');return;}callModAction({platform:currentContextPlatform,action:'timeout',user_id:currentContextPlatformUserId,duration_seconds:n*60,duration_minutes:n}).then(res=>{if(res.ok){alert('Тайм-аут '+n+' хв застосовано до '+currentContextAlias)}else{alert('Помилка: '+(res.error||'невідома'))}});}
function banFromMenu(){hideContextMenu();if(!currentContextPlatformUserId){alert('Немає ID користувача для бану (повідомлення прийшло до оновлення скрипта - дочекайтесь нового повідомлення від цього юзера)');return;}if(!confirm('Забанити назавжди '+currentContextAlias+' (ID: '+currentContextPlatformUserId+') на '+currentContextPlatform+'?'))return;callModAction({platform:currentContextPlatform,action:'ban',user_id:currentContextPlatformUserId}).then(res=>{if(res.ok){alert(currentContextAlias+' забанено')}else{alert('Помилка: '+(res.error||'невідома'))}});}
function deleteMessageFromMenu(){hideContextMenu();if(!currentContextMessageId){alert('Немає ID цього повідомлення для видалення (повідомлення прийшло до оновлення скрипта)');return;}if(!confirm('Видалити це повідомлення (ID: '+currentContextMessageId+')?'))return;callModAction({platform:currentContextPlatform,action:'delete',message_id:currentContextMessageId}).then(res=>{if(res.ok){alert('Повідомлення видалено')}else{alert('Помилка: '+(res.error||'невідома'))}});}
document.addEventListener('click',function(e){if(!e.target.closest('.context-menu')){hideContextMenu()}if(!e.target.closest('.menu-wrapper')){hideAdminMenu()}if(e.target&&e.target.id==='voiceModal'){closeVoiceModal()}})
function detectLanguage(text){if(/[іїєґІЇЄҐ]/.test(text))return "uk";if(/[а-яёА-ЯЁ]/.test(text))return "ru";return "en"}
function ttsHoldAnnounce(){const h=ttsQueue[0];if(!h||!h.isAnnounce)return false;if(ttsQueue.some(x=>!x.isAnnounce))return false;if((Date.now()-(h.queuedAt||0))<1500){setTimeout(playTTS,500);return true;}return false;}
function playTTS(){if(ttsQueue.length===0||ttsActive||!unlocked)return;ttsQueue.sort((a,b)=>(b.priority||0)-(a.priority||0)||((a.timestamp||0)-(b.timestamp||0)));if(ttsHoldAnnounce())return;ttsActive=true;let m=ttsQueue.shift();let nickname=cCache.ttsReadNicknames===false?'':(m.ttsDisplayName||m.name||'');let speakText=m.isAlert?m.text:cCache.ttsTemplate.replace('{nickname}',nickname).replace('{comment}',m.text).replace(/\\s+/g,' ').trim();let targetLang=detectLanguage(speakText);let speed=cCache.ttsSpeed||1.0;let engine=(m.ttsEngine||cCache.ttsEngine||'google');let voice=(m.ttsVoiceId||m.ttsVoice||cCache.ttsVoice||'uk-UA');function finish(){ttsActive=false;setTimeout(playTTS,50);}if(!speakText){finish();return;}function doTTS(){if(engine==="browser"){let utterance=new SpeechSynthesisUtterance(speakText);utterance.volume=cCache.ttsVolume;utterance.lang=(voice&&voice.includes('-'))?voice:(targetLang==='uk'?'uk-UA':targetLang==='ru'?'ru-RU':'en-US');utterance.rate=speed;utterance.onend=finish;utterance.onerror=finish;window.speechSynthesis.speak(utterance)}else{let url=`/tts?lang=${targetLang}&q=${encodeURIComponent(speakText)}&engine=${engine}&voice=${encodeURIComponent(voice)}&speed=${speed}`;let audio=new Audio(url);audio.volume=cCache.ttsVolume;audio.playbackRate=speed;audio.onended=finish;audio.onerror=finish;audio.play().catch(finish)}}if(cCache.ringtoneUrl&&!(cCache.ringtoneChatOnly&&(m.isAlert||m.isAnnounce))){let ring=new Audio(cCache.ringtoneUrl);ring.volume=cCache.ttsVolume;ring.onended=doTTS;ring.play().catch(doTTS)}else{doTTS()}}
function showBlockedModal(){document.getElementById('blockedModal').style.display='flex';fetchBlockedUsers();}
function closeBlockedModal(){document.getElementById('blockedModal').style.display='none';}
function unblockAllUsers(){fetch('/blocked_users').then(r=>r.json()).then(list=>{let n=(list||[]).length;if(n===0){alert('Список заблокованих порожній');return;}if(confirm('Розблокувати ВСІХ ('+n+') користувачів? Дію не можна скасувати.')){fetch('/unblock_all_users',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}).then(r=>r.json()).then(d=>{alert('Розблоковано: '+(d.removed||0));fetchBlockedUsers();}).catch(e=>{console.error(e);alert('Помилка: '+e);});}}).catch(e=>console.error(e));}
function enableTtsAllUsers(){fetch('/no_tts_users').then(r=>r.json()).then(list=>{let n=(list||[]).length;if(n===0){alert('Список без TTS порожній');return;}if(confirm('Увімкнути TTS ВСІМ ('+n+') користувачам? Дію не можна скасувати.')){fetch('/enable_tts_all_users',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}).then(r=>r.json()).then(d=>{alert('TTS увімкнено для: '+(d.removed||0));fetchNoTtsUsers();}).catch(e=>{console.error(e);alert('Помилка: '+e);});}}).catch(e=>console.error(e));}
function setModCount(id,n){let el=document.getElementById(id);if(el){el.textContent=n+' записів';}}
function fetchBlockedUsers(){fetch('/blocked_users').then(r=>r.json()).then(list=>{let container=document.getElementById('blockedList');container.innerHTML='';setModCount('blockedCount',(list||[]).length);if(list.length===0){let li=document.createElement('li');li.textContent='Немає заблокованих користувачів';li.style.padding='10px';li.style.textAlign='center';container.appendChild(li);return;}list.forEach(user=>{let li=document.createElement('li');li.className='blocked-item';let span=document.createElement('span');span.className='blocked-name';span.textContent=user;let btn=document.createElement('button');btn.className='unblock-btn';btn.textContent='🔓 Розблокувати';btn.onclick=()=>unblockUser(user);li.appendChild(span);li.appendChild(btn);container.appendChild(li);});}).catch(e=>console.error(e));}
function unblockUser(username){if(confirm('Розблокувати '+username+'?')){fetch('/unblock_user',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:username})}).then(()=>{fetchBlockedUsers();});}}
function showNoTtsModal(){document.getElementById('noTtsModal').style.display='flex';fetchNoTtsUsers();}
function closeNoTtsModal(){document.getElementById('noTtsModal').style.display='none';}
function fetchNoTtsUsers(){fetch('/no_tts_users').then(r=>r.json()).then(list=>{let container=document.getElementById('noTtsList');container.innerHTML='';setModCount('noTtsCount',(list||[]).length);if(list.length===0){let li=document.createElement('li');li.textContent='Немає користувачів з вимкненим TTS';li.style.padding='10px';li.style.textAlign='center';container.appendChild(li);return;}list.forEach(user=>{let li=document.createElement('li');li.className='blocked-item';let span=document.createElement('span');span.className='blocked-name';span.textContent=user;let btn=document.createElement('button');btn.className='unblock-btn';btn.textContent='🔊 Увімкнути TTS';btn.onclick=()=>enableTtsUser(user);li.appendChild(span);li.appendChild(btn);container.appendChild(li);});}).catch(e=>console.error(e));}
function closeTopActiveModal(){document.getElementById('topActiveModal').style.display='none';}
function renderTopActiveList(containerId,items){let container=document.getElementById(containerId);container.innerHTML='';if(!items||items.length===0){let li=document.createElement('li');li.textContent='Поки що немає даних';li.style.padding='10px';li.style.textAlign='center';container.appendChild(li);return;}let platformLabels={twitch:'Twitch',youtube:'YouTube',tiktok:'TikTok',kick:'Kick'};let medals=['🥇','🥈','🥉'];items.forEach((u,i)=>{let li=document.createElement('li');li.className='blocked-item';let span=document.createElement('span');span.className='blocked-name';let place=medals[i]||((i+1)+'.');let nickPart=u.nickname?(' — псевдонім: '+u.nickname):'';span.textContent=place+' '+(u.display_name||u.username)+' ('+(platformLabels[u.platform]||u.platform)+')'+nickPart+' — '+u.count+' повід.';li.appendChild(span);container.appendChild(li);});}
function showTopActiveModal(){document.getElementById('topActiveModal').style.display='flex';fetch('/api/top_active').then(r=>r.json()).then(d=>{renderTopActiveList('topActive30List',d.last_30_days);renderTopActiveList('topActiveAllList',d.all_time);}).catch(e=>console.error(e));}
function enableTtsUser(username){if(confirm('Увімкнути TTS для '+username+'?')){fetch('/enable_tts_user',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:username})}).then(()=>{fetchNoTtsUsers();});}}
function showNicknamesModal(){document.getElementById('nicknamesModal').style.display='flex';fetchCustomNicknames();}
function closeNicknamesModal(){document.getElementById('nicknamesModal').style.display='none';}
function fetchCustomNicknames(){fetch('/custom_nicknames').then(r=>r.json()).then(list=>{let container=document.getElementById('nicknamesList');container.innerHTML='';if(list.length===0){let li=document.createElement('li');li.textContent='Немає збережених псевдонімів';li.style.padding='10px';li.style.textAlign='center';container.appendChild(li);return;}list.forEach(item=>{let li=document.createElement('li');li.className='blocked-item';let span=document.createElement('span');span.className='blocked-name';let label=(item.platform?('['+item.platform+'] '):'')+item.username+' → '+item.nickname;span.textContent=label;let btn=document.createElement('button');btn.className='unblock-btn';btn.textContent='🗑 Видалити';btn.onclick=()=>removeNickname(item);li.appendChild(span);li.appendChild(btn);container.appendChild(li);});}).catch(e=>console.error(e));}
function removeNickname(item){if(confirm('Видалити псевдонім для '+item.username+'?')){fetch('/remove_custom_nickname',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({platform:item.platform,username:item.username,display_name:item.username})}).then(()=>{fetchCustomNicknames();});}}
function clearChat(){if(confirm('Очистити чат?')){fetch('/clear_chat',{method:'POST'});document.getElementById('log').innerHTML='';let scroller=document.getElementById('chatScroller');if(scroller){scroller.scrollTop=scroller.scrollHeight;}autoScrollChat=true;}}
function getChatScroller(){return document.getElementById('chatScroller');}
function isChatNearBottom(){let scroller=getChatScroller();if(!scroller)return true;return (scroller.scrollHeight-scroller.scrollTop-scroller.clientHeight)<=60;}
let autoScrollChat=true;
function bindChatScroller(){let scroller=getChatScroller();if(!scroller||scroller.dataset.bound==='1')return;scroller.dataset.bound='1';scroller.addEventListener('scroll',function(){autoScrollChat=isChatNearBottom();});}
function buildMessageElement(msg){let div=document.createElement('div');if(msg.isAlert){div.className='msg alert-card';let title=document.createElement('div');title.className='alert-title';title.textContent=msg.subtitle||'';let name=document.createElement('div');name.className='name';name.textContent=(msg.displayName||'')+':';let text=document.createElement('div');text.className='text';text.textContent=msg.text||'';div.appendChild(title);div.appendChild(name);div.appendChild(text);return div;}div.className=`msg ${msg.platform}`;let pClass=msg.platform==='twitch'?'p-tw':msg.platform==='kick'?'p-kk':msg.platform==='youtube'?'p-yt':msg.platform==='tiktok'?'p-tt':'p-bt';let pName=msg.platform==='bot'?'БОТ':msg.platform;let meta=document.createElement('div');meta.className='meta';let pIcon=document.createElement('span');pIcon.className=`p-icon ${pClass}`;pIcon.textContent=pName;meta.appendChild(pIcon);if(msg.platform==='youtube'&&msg.streamVariant){let variantBadge=document.createElement('span');variantBadge.className='p-icon';variantBadge.style.background='rgba(255,255,255,0.15)';variantBadge.title='Джерело: '+msg.streamVariant;let shortTitle=msg.streamVariant.length>18?msg.streamVariant.slice(0,18)+'…':msg.streamVariant;variantBadge.textContent='🎬 '+shortTitle;meta.appendChild(variantBadge);}let name=document.createElement('span');name.className='name';name.textContent=msg.displayName||'';name.addEventListener('click',function(event){showContextMenu(event,{platform:msg.platform,username:msg.username||msg.sourceDisplayName||msg.displayName||'',displayName:msg.displayName||'',sourceDisplayName:msg.sourceDisplayName||msg.displayName||'',platformUserId:msg.platformUserId||'',messageId:msg.platformMessageId||''});});name.addEventListener('dblclick',function(){currentContextUser=(msg.username||msg.sourceDisplayName||msg.displayName||'').trim();currentContextDisplayName=(msg.sourceDisplayName||msg.displayName||currentContextUser||'').trim();currentContextPlatform=(msg.platform||'').trim();currentContextAlias=(msg.displayName||currentContextDisplayName||currentContextUser||'').trim();blockFromMenu();});let text=document.createElement('div');text.className='text';text.textContent=msg.text||'';meta.appendChild(name);div.appendChild(meta);div.appendChild(text);return div;}
async function loop(){try{bindChatScroller();let res=await fetch('/get_messages');let list=await res.json();let logDiv=document.getElementById('log');let scroller=getChatScroller();let stickToBottom=autoScrollChat||isChatNearBottom();let appended=false;for(let msg of list){if(msg.id>maxId){maxId=msg.id;if(msg.ttsText&&cCache.ttsEnabled){ttsQueue.push({name:msg.displayName,ttsDisplayName:msg.ttsDisplayName,text:msg.ttsText,isAlert:msg.isAlert,isAnnounce:!!msg.isAnnounce,queuedAt:Date.now(),priority:msg.priority,timestamp:msg.timestamp});playTTS();}if(!msg.showInChat)continue;let div=buildMessageElement(msg);logDiv.appendChild(div);appended=true;if(cCache.msgTimeout>0){setTimeout(()=>{div.classList.add('fade-out');setTimeout(()=>div.remove(),400)},cCache.msgTimeout*1000)}}}if(appended&&scroller&&stickToBottom){scroller.scrollTop=scroller.scrollHeight;autoScrollChat=true;}}catch(e){}setTimeout(loop,400)}
async function updateNetMon(){try{let res=await fetch('/api/netmon');let d=await res.json();let bar=document.getElementById('netmonBar');if(!d||!d.enabled){if(bar)bar.classList.remove('show');document.body.classList.remove('netmon-active');return;}bar.classList.add('show');document.body.classList.add('netmon-active');let dot=document.getElementById('netmonDot');dot.className='netmon-dot '+(d.status==='unstable'?'bad':d.status==='stable'?'ok':'warn');let pingEl=document.getElementById('netmonPing');pingEl.innerHTML='Ping: <b>'+(d.ping!=null?d.ping+' мс':'—')+'</b>';let lossEl=document.getElementById('netmonLoss');lossEl.innerHTML='Втрати: <b>'+(d.loss!=null?d.loss+'%':'—')+'</b>';let jitterEl=document.getElementById('netmonJitter');if(d.jitter!=null){jitterEl.style.display='';jitterEl.innerHTML='Джитер: <b>'+d.jitter+' мс</b>';}else{jitterEl.style.display='none';}let targetsEl=document.getElementById('netmonTargets');if(Array.isArray(d.targets)&&d.targets.length){targetsEl.style.display='';targetsEl.title=d.targets.map(t=>t.host+': '+(t.ping!=null?t.ping+' мс':'—')+' / '+(t.loss!=null?t.loss+'%':'—')).join('\\n');targetsEl.innerHTML='Цілі: <b>'+d.targets.filter(t=>t.bad).length+'/'+d.targets.length+' погано</b>';}else{targetsEl.style.display='none';}let obsEl=document.getElementById('netmonObs');if(d.obs&&d.obs.streaming){obsEl.style.display='';obsEl.innerHTML='Кадри OBS: <b>'+(d.obs.percent!=null?d.obs.percent+'%':'—')+'</b>'+(d.obs.dropped!=null?' ('+d.obs.dropped+'/'+d.obs.total+')':'');}else{obsEl.style.display='none';}let speedEl=document.getElementById('netmonSpeed');if(d.download!=null||d.upload!=null){speedEl.style.display='';speedEl.innerHTML='↓ <b>'+(d.download!=null?d.download+' Мбіт/с':'—')+'</b> / ↑ <b>'+(d.upload!=null?d.upload+' Мбіт/с':'—')+'</b>'+(d.speedtest_running?' (вимірюю…)':'');}else{speedEl.style.display='none';}requestAnimationFrame(function(){syncNetmonBarHeight();});}catch(e){}}
function syncNetmonBarHeight(){let bar=document.getElementById('netmonBar');let scroller=document.getElementById('chatScroller');if(!bar||!scroller)return;if(bar.classList.contains('show')){let h=bar.offsetHeight||0;scroller.style.bottom=(h+4)+'px';}else{scroller.style.bottom='';}}
window.addEventListener('resize',function(){setTimeout(syncNetmonBarHeight,150);});
updateNetMon();setInterval(updateNetMon,3000);
</script>
</body>
</html>"""


def generate_overlay_html(plain=None):
    if plain is None:
        plain = bool(config.get("overlay_plain", False))
    plain_marker = str(config.get("overlay_plain_marker", "icon") or "icon").strip().lower()
    if plain_marker not in ("icon", "name", "none"):
        plain_marker = "icon"
    max_msgs = config.get("overlay_max_messages", 20)
    timeout = config.get("overlay_msg_timeout", 10)
    font_size = config.get("overlay_font_size", 18)
    bg_color = config.get("overlay_bg_color", "rgba(0,0,0,0.7)")
    text_color = config.get("overlay_text_color", "#ffffff")
    rotation = config.get("overlay_rotation", 0)
    offset_x = config.get("overlay_offset_x", 0)
    offset_y = config.get("overlay_offset_y", 0)
    transform_css = "transform: translate({}px, {}px) rotate({}deg); transform-origin: center center;".format(offset_x, offset_y, rotation)
    # Режим без плашки: лишається тільки текст із контурною тінню для читабельності
    plain_css = ""
    if plain:
        plain_css = (
            ".msg{background:none!important;background-color:transparent!important;"
            "border:none!important;border-left:none!important;box-shadow:none!important;"
            "backdrop-filter:none!important;padding:0!important;margin-bottom:6px;"
            "text-shadow:0 0 4px #000,0 2px 4px #000,1px 1px 2px #000,-1px -1px 2px #000}"
            ".msg .name,.msg .platform,.msg .text{text-shadow:0 0 4px #000,0 2px 4px #000,"
            "1px 1px 2px #000,-1px -1px 2px #000}"
            ".plain-line{word-break:break-word;line-height:1.35}"
            ".pmark{color:var(--platform-color,#9146FF);font-weight:700;margin-right:2px}"
        )

    overlay_html = """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8">
<style>
*{{box-sizing:border-box}}body{{background-color:transparent!important;margin:0;padding:10px;overflow:hidden;font-family:'Segoe UI',system-ui,sans-serif;height:100vh;pointer-events:auto}}.chat-container{{display:flex;flex-direction:column;height:100%;overflow:hidden;{transform_css}}}#log{{flex-grow:1;overflow-y:auto;display:flex;flex-direction:column;gap:10px;scrollbar-width:none}}#log::-webkit-scrollbar{{display:none}}.msg{{padding:12px 16px;border-radius:12px;background:{bg_color};border-left:5px solid var(--platform-color,#9146FF);backdrop-filter:blur(5px);animation:fadeIn 0.2s ease forwards;margin-bottom:5px;color:{text_color};font-size:{font_size}px}}.msg.fade-out{{opacity:0;transform:translateY(-10px);transition:opacity 0.3s,transform 0.3s}}.twitch{{--platform-color:#9146FF}}.youtube{{--platform-color:#ff0000}}.tiktok{{--platform-color:#ff0050}}.kick{{--platform-color:#53fc18}}.bot{{--platform-color:#00f2fe}}.alert-card{{--platform-color:#ffd700}}.meta{{display:flex;align-items:center;gap:8px;margin-bottom:4px;font-size:0.9em}}.name{{font-weight:bold;color:#ffb703}}.platform{{font-size:0.8em;opacity:0.85}}.text{{word-break:break-word}}@keyframes fadeIn{{from{{opacity:0;transform:translateY(10px)}}to{{opacity:1;transform:translateY(0)}}}}{plain_css}
</style>
</head>
<body>
<div class="chat-container"><div id="log"></div></div>
<script>let messagesQueue=[],maxId=0;const maxMessages={max_msgs};const msgTimeout={timeout};const PLAIN={plain_flag};const PLAIN_MARKER='{plain_marker}';const PLAT_ICONS={{twitch:'🎮',youtube:'▶',tiktok:'🎵',kick:'🟩',bot:'🤖'}};const PLAT_NAMES={{twitch:'Twitch',youtube:'YouTube',tiktok:'TikTok',kick:'Kick',bot:'БОТ'}};function renderMessage(msg){{let div=document.createElement('div');div.className=msg.isAlert?'msg alert-card':`msg ${{msg.platform}}`;if(PLAIN){{let line=document.createElement('div');line.className='text plain-line';if(PLAIN_MARKER!=='none'){{let mk=document.createElement('span');mk.className='pmark';mk.textContent=(PLAIN_MARKER==='name')?(msg.isAlert?'АЛЕРТ':(PLAT_NAMES[msg.platform]||msg.platform||'')):(msg.isAlert?'⭐':(PLAT_ICONS[msg.platform]||'💬'));line.appendChild(mk);line.appendChild(document.createTextNode(' '));}}if(msg.displayName){{let nm=document.createElement('span');nm.className='name';nm.textContent=msg.displayName;line.appendChild(nm);line.appendChild(document.createTextNode(': '));}}line.appendChild(document.createTextNode(msg.text||''));div.appendChild(line);return div;}}let meta=document.createElement('div');meta.className='meta';let name=document.createElement('span');name.className='name';name.textContent=msg.displayName||'';let platform=document.createElement('span');platform.className='platform';platform.textContent='['+(msg.platform==='bot'?'БОТ':msg.platform)+']';let text=document.createElement('div');text.className='text';text.textContent=msg.text||'';meta.appendChild(name);meta.appendChild(platform);div.appendChild(meta);div.appendChild(text);return div;}}function renderMessages(){{const logDiv=document.getElementById('log');logDiv.innerHTML='';for(let msg of messagesQueue){{let div=renderMessage(msg);logDiv.appendChild(div);if(msgTimeout>0){{setTimeout(()=>{{div.classList.add('fade-out');setTimeout(()=>{{const idx=messagesQueue.findIndex(m=>m.id===msg.id);if(idx!==-1)messagesQueue.splice(idx,1);renderMessages();}},300);}},msgTimeout*1000);}}}}if(logDiv.children.length)logDiv.lastChild.scrollIntoView({{behavior:'smooth',block:'end'}});}}async function loop(){{try{{let res=await fetch('/get_messages');let list=await res.json();for(let msg of list){{if(msg.id>maxId&&msg.showInChat!==false){{maxId=msg.id;messagesQueue.push(msg);if(messagesQueue.length>maxMessages)messagesQueue.shift();renderMessages();}}}}}}catch(e){{}}setTimeout(loop,400);}}loop();</script>
</body>
</html>""".format(transform_css=transform_css, bg_color=bg_color, text_color=text_color, font_size=font_size, max_msgs=max_msgs, timeout=timeout, plain_css=plain_css, plain_flag=('true' if plain else 'false'), plain_marker=plain_marker)
    return overlay_html


def generate_top_likes_widget_html():
    """Автономний OBS Browser Source віджет: топ-N глядачів TikTok за лайками.
    Дані оновлюються самостійно кожні кілька секунд через /api/top_likes -
    не потребує жодної додаткової взаємодії з адмінкою.

    Налаштовується: заголовок (показ/приховати), фон картки (увімк/вимк + колір),
    колір тексту, плашка під кожним рядком (увімк/вимк). JS оновлює список через
    ЦІЛЬОВЕ порівняння DOM (по ключу глядача), а не повний innerHTML-перезапис,
    щоб уникнути мерехтіння/перемальовування аватарок і рядків, які не змінилися."""
    limit = int(config.get("top_likes_widget_limit", 10) or 10)
    title = config.get("top_likes_widget_title", "🏆 Топ за лайками (TikTok)")
    show_title = bool(config.get("top_likes_widget_show_title", True))
    bg_enabled = bool(config.get("top_likes_widget_bg_enabled", True))
    bg_color = config.get("top_likes_widget_bg_color", "rgba(20,20,28,0.85)") or "rgba(20,20,28,0.85)"
    text_color = config.get("top_likes_widget_text_color", "#ffffff") or "#ffffff"
    row_plate = bool(config.get("top_likes_widget_row_plate", True))

    wrap_bg = "linear-gradient(160deg,{},{})".format(bg_color, bg_color) if bg_enabled else "transparent"
    wrap_shadow = "0 8px 24px rgba(0,0,0,0.35)" if bg_enabled else "none"

    html = """<!DOCTYPE html>
<html lang="uk">
<head><meta charset="UTF-8"><style>
*{margin:0;padding:0;box-sizing:border-box}
body{font-family:'Segoe UI',sans-serif;background:transparent;color:__TEXT_COLOR__;overflow:hidden}
.wrap{width:340px;padding:14px 16px;background:__WRAP_BG__;border-radius:16px;box-shadow:__WRAP_SHADOW__}
.title{font-size:16px;font-weight:700;margin-bottom:10px;text-align:center;letter-spacing:.3px;text-shadow:0 1px 3px rgba(0,0,0,0.5)}
.title.hidden{display:none}
.row{display:flex;align-items:center;gap:10px;padding:6px 8px;border-radius:10px;margin-bottom:4px;background:rgba(255,255,255,0.06);transition:background .25s ease}
.row.r1{background:linear-gradient(90deg,rgba(255,215,0,0.28),rgba(255,255,255,0.06))}
.row.r2{background:linear-gradient(90deg,rgba(192,192,192,0.24),rgba(255,255,255,0.06))}
.row.r3{background:linear-gradient(90deg,rgba(205,127,50,0.22),rgba(255,255,255,0.06))}
.row.no-plate,.row.no-plate.r1,.row.no-plate.r2,.row.no-plate.r3{background:none;padding:4px 2px}
.place{width:22px;text-align:center;font-weight:700;font-size:14px;flex:0 0 22px}
.avatar{width:28px;height:28px;border-radius:50%;object-fit:cover;flex:0 0 28px;background:rgba(255,255,255,0.15)}
.name{flex:1;font-size:13.5px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.likes{font-size:13.5px;font-weight:700;color:#ff2d78;display:flex;align-items:center;gap:4px;flex:0 0 auto}
.empty{text-align:center;opacity:.6;padding:12px;font-size:13px}
</style></head>
<body>
<div class="wrap">
<div class="title __TITLE_CLASS__">__TITLE__</div>
<div id="list"></div>
</div>
<script>
const LIMIT=__LIMIT__;
const ROW_PLATE=__ROW_PLATE__;
const rowEls=new Map();
function fmt(n){n=n||0;if(n>=1000000)return (n/1000000).toFixed(1)+'M';if(n>=1000)return (n/1000).toFixed(1)+'K';return String(n);}
function makeRow(){
  const el=document.createElement('div');
  el.innerHTML='<span class="place"></span><span class="avatar-wrap"></span><span class="name"></span><span class="likes"></span>';
  return el;
}
function render(items){
  const list=document.getElementById('list');
  if(!items.length){
    if(list.dataset.empty!=='1'){
      list.innerHTML='<div class="empty">Поки що немає даних про лайки</div>';
      list.dataset.empty='1';
      rowEls.clear();
    }
    return;
  }
  if(list.dataset.empty==='1'){list.innerHTML='';delete list.dataset.empty;}
  const sliced=items.slice(0,LIMIT);
  const seen=new Set();
  sliced.forEach((u,i)=>{
    const place=i+1;
    const key=String(u.username||u.nickname||u.display_name||i);
    seen.add(key);
    const medal=place===1?'🥇':place===2?'🥈':place===3?'🥉':(place+'.');
    const rowClass='row'+(ROW_PLATE?(place<=3?(' r'+place):''):' no-plate');
    const name=(u.nickname||u.display_name||u.username||'Глядач');
    const likesText='❤️ '+fmt(u.count);
    const avatarUrl=u.avatar_url||'';
    let el=rowEls.get(key);
    if(!el){el=makeRow();rowEls.set(key,el);}
    if(el.className!==rowClass)el.className=rowClass;
    const placeEl=el.querySelector('.place');
    if(placeEl.textContent!==medal)placeEl.textContent=medal;
    const nameEl=el.querySelector('.name');
    if(nameEl.textContent!==name)nameEl.textContent=name;
    const likesEl=el.querySelector('.likes');
    if(likesEl.textContent!==likesText)likesEl.textContent=likesText;
    const avatarWrap=el.querySelector('.avatar-wrap');
    if(avatarWrap.dataset.src!==avatarUrl){
      avatarWrap.dataset.src=avatarUrl;
      avatarWrap.innerHTML=avatarUrl?('<img class="avatar" src="'+avatarUrl+'">'):'<div class="avatar"></div>';
    }
    if(list.children[i]!==el)list.insertBefore(el,list.children[i]||null);
  });
  for(const [key,el] of Array.from(rowEls.entries())){
    if(!seen.has(key)){el.remove();rowEls.delete(key);}
  }
}
async function update(){
  try{
    const res=await fetch('/api/top_likes');
    const data=await res.json();
    render((data&&data.top_likes)||[]);
  }catch(e){console.error(e);}
}
update();setInterval(update,5000);
</script>
</body></html>"""
    html = html.replace('__TITLE__', str(title))
    html = html.replace('__TITLE_CLASS__', '' if show_title else 'hidden')
    html = html.replace('__LIMIT__', str(limit))
    html = html.replace('__ROW_PLATE__', 'true' if row_plate else 'false')
    html = html.replace('__TEXT_COLOR__', str(text_color))
    html = html.replace('__WRAP_BG__', wrap_bg)
    html = html.replace('__WRAP_SHADOW__', wrap_shadow)
    return html


def generate_tiktok_history_html():
    return """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8">
<title>TikTok - Історія глядачів</title>
<style>
*{box-sizing:border-box}
@keyframes fadeSlideIn{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}
@keyframes popIn{from{opacity:0;transform:scale(0.94)}to{opacity:1;transform:scale(1)}}
@keyframes shimmerGlow{0%,100%{text-shadow:0 0 6px rgba(255,0,80,0.35)}50%{text-shadow:0 0 14px rgba(255,0,80,0.65)}}
html{scrollbar-color:#3a3a48 #14141b;scrollbar-width:thin}
body{background:radial-gradient(1100px 650px at 10% -8%,rgba(255,0,80,0.09),transparent),radial-gradient(900px 600px at 100% 0%,rgba(0,242,254,0.07),transparent),#0e0e13;margin:0;padding:16px;font-family:'Segoe UI',system-ui,sans-serif;color:#e2e2e9;height:100vh;overflow-y:auto}
h1{font-size:1.15em;margin:0 0 4px;color:#ff0050;animation:shimmerGlow 3.5s ease-in-out infinite}
.sub{color:#9a9aa5;font-size:0.85em;margin-bottom:16px}
.top-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;margin-bottom:20px}
@media(max-width:900px){.top-grid{grid-template-columns:1fr}}
.top-card{background:linear-gradient(160deg,rgba(255,255,255,0.055),rgba(255,255,255,0.02));border-radius:14px;padding:12px;border:1px solid rgba(255,255,255,0.1);transition:border-color .2s ease,transform .2s ease,box-shadow .2s ease;animation:fadeSlideIn .35s ease both}
.top-card:hover{border-color:rgba(255,255,255,0.22);transform:translateY(-2px);box-shadow:0 10px 26px rgba(0,0,0,0.32)}
.top-card h3{margin:0 0 8px;font-size:0.9em;color:#00f2fe}
.top-row{display:flex;align-items:center;gap:8px;padding:6px 6px;border-radius:8px;border-bottom:1px solid rgba(255,255,255,0.06);font-size:0.85em;transition:background .18s ease,padding-left .18s ease}
.top-row:hover{background:rgba(255,255,255,0.05);padding-left:9px}
.top-row:last-child{border-bottom:none}
.top-row:nth-child(1){background:linear-gradient(90deg,rgba(255,215,0,0.16),transparent)}
.top-row:nth-child(2){background:linear-gradient(90deg,rgba(192,192,192,0.13),transparent)}
.top-row:nth-child(3){background:linear-gradient(90deg,rgba(205,127,50,0.12),transparent)}
.top-row img{width:24px;height:24px;border-radius:50%;object-fit:cover;background:#333;flex-shrink:0;transition:transform .18s ease}
.top-row:hover img{transform:scale(1.08)}
.top-row .rank{width:18px;text-align:center;flex-shrink:0;opacity:0.7}
.top-row .nick{flex-grow:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.top-row .nick a{color:#e2e2e9;text-decoration:none;transition:color .15s ease}
.top-row .nick a:hover{color:#ff0050;text-decoration:underline}
.top-row .val{color:#ffd700;font-weight:600;flex-shrink:0}
.plat{font-size:0.72em;padding:1px 6px;border-radius:6px;background:rgba(255,255,255,0.1);color:#9a9aa5;flex-shrink:0}
.empty{color:#666;font-size:0.85em;padding:8px 0}
.roster-title{font-size:1em;margin:0 0 10px;color:#e2e2e9}
.roster{display:flex;flex-direction:column;gap:6px}
.roster-item{display:flex;align-items:center;gap:10px;background:rgba(255,255,255,0.03);border-radius:12px;padding:8px 12px;border:1px solid rgba(255,255,255,0.05);transition:background .18s ease,border-color .18s ease,transform .18s ease;animation:fadeSlideIn .3s ease both}
.roster-item:hover{background:rgba(255,255,255,0.06);border-color:rgba(255,255,255,0.14);transform:translateX(2px)}
.roster-item img{width:36px;height:36px;border-radius:50%;object-fit:cover;background:#333;flex-shrink:0;transition:transform .18s ease}
.roster-item:hover img{transform:scale(1.06)}
.roster-item .name{font-weight:600;flex-shrink:0;min-width:140px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.roster-item .name a{color:#e2e2e9;text-decoration:none;transition:color .15s ease}
.roster-item .name a:hover{color:#ff0050;text-decoration:underline}
.roster-item .stats{display:flex;gap:14px;font-size:0.8em;color:#9a9aa5;flex-wrap:wrap;flex-grow:1}
.roster-item .stats b{color:#c7c7d1}
.icons{display:flex;gap:6px;flex-shrink:0}
.icon-btn{background:rgba(255,255,255,0.07);border:1px solid rgba(255,255,255,0.12);color:#e2e2e9;border-radius:8px;padding:5px 9px;font-size:0.9em;cursor:pointer;line-height:1;transition:background .15s ease,border-color .15s ease,transform .15s ease}
.icon-btn:hover:not(:disabled){background:rgba(255,0,80,0.25);border-color:#ff0050;transform:translateY(-1px)}
.icon-btn:disabled{opacity:0.3;cursor:default}
.day-selector{display:flex;align-items:center;gap:8px;margin-bottom:14px;flex-wrap:wrap}
.danger-btn{background:rgba(255,0,80,.18);border:1px solid rgba(255,0,80,.5);color:#ff8fae;border-radius:8px;padding:6px 12px;font-size:0.82em;cursor:pointer;transition:background .15s ease,color .15s ease,transform .15s ease}
.danger-btn:hover{background:rgba(255,0,80,.32);color:#fff;transform:translateY(-1px)}
.danger-btn.small{padding:3px 8px;font-size:0.72em;margin-left:8px;vertical-align:middle}
.top-card h3{display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:4px}
.day-selector label{font-size:0.85em;color:#9a9aa5}
.day-selector select{background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.15);color:#e2e2e9;border-radius:8px;padding:6px 10px;font-size:0.85em;transition:border-color .18s ease}
.day-selector select:focus{outline:none;border-color:#00f2fe}
.modal-bg{position:fixed;inset:0;background:rgba(0,0,0,0.72);backdrop-filter:blur(3px);display:none;align-items:center;justify-content:center;z-index:50;padding:20px}
.modal-bg.open{display:flex;animation:fadeSlideIn .18s ease both}
.modal{background:#16161d;border:1px solid rgba(255,255,255,0.15);border-radius:16px;width:100%;max-width:560px;max-height:80vh;display:flex;flex-direction:column;box-shadow:0 24px 64px rgba(0,0,0,0.55);animation:popIn .22s cubic-bezier(.34,1.56,.64,1) both}
.modal-head{display:flex;align-items:center;gap:10px;padding:14px 16px;border-bottom:1px solid rgba(255,255,255,0.1)}
.modal-head img{width:34px;height:34px;border-radius:50%;object-fit:cover;background:#333}
.modal-head .t{flex-grow:1;font-weight:600}
.modal-head .t small{display:block;font-weight:400;color:#9a9aa5;font-size:0.78em}
.modal-head .t small a{color:#00f2fe;text-decoration:none}
.modal-close{background:none;border:none;color:#9a9aa5;font-size:1.3em;cursor:pointer;transition:color .15s ease,transform .15s ease}
.modal-close:hover{color:#ff0050;transform:rotate(90deg)}
.modal-body{padding:12px 16px;overflow-y:auto}
.log-row{padding:7px 4px;border-radius:6px;border-bottom:1px solid rgba(255,255,255,0.06);font-size:0.87em;display:flex;gap:10px;transition:background .15s ease}
.log-row:hover{background:rgba(255,255,255,0.04)}
.log-row:last-child{border-bottom:none}
.log-row .ts{color:#6f6f7d;font-size:0.85em;flex-shrink:0;min-width:112px}
.log-row .txt{word-break:break-word}
.log-row .gift{color:#ffd700}
</style>
</head>
<body>
<h1>📱 TikTok — Історія глядачів</h1>
<div class="sub" id="totalKnown">Завантаження…</div>
<div class="day-selector">
<label for="daySelect">Показати за:</label>
<select id="daySelect">
<option value="all">Весь час</option>
</select>
<button class="danger-btn" onclick="clearDayHistory()">🧹 Очистити активних глядачів за день</button>
<button class="danger-btn" onclick="clearAllHistory()">🗑 Очистити всю історію відвідувань</button>
</div>
<div class="top-grid">
<div class="top-card"><h3 id="topAllTitle"><span>🌐 Топ глядачів усіх мереж</span><button class="danger-btn small" onclick="clearAllNetworksHistory()" title="Очистити тільки крос-мережевий рейтинг, історію TikTok не зачіпає">🧹 Очистити</button></h3><div id="topAll"></div></div>
<div class="top-card"><h3 id="topMessagesTitle">💬 Топ активних у TikTok</h3><div id="topMessages"></div></div>
<div class="top-card"><h3 id="topGiftsTitle">🎁 Топ дарувальників TikTok (💎)</h3><div id="topGifts"></div></div>
</div>
<div class="roster-title" id="rosterTitle">Усі глядачі (за останньою активністю)</div>
<div class="roster" id="roster"></div>

<div class="modal-bg" id="modalBg">
  <div class="modal">
    <div class="modal-head">
      <img id="mAvatar" src="">
      <div class="t"><span id="mTitle"></span><small id="mSub"></small></div>
      <button class="modal-close" id="mClose">✕</button>
    </div>
    <div class="modal-body" id="mBody"></div>
  </div>
</div>

<script>
let currentSelectedDate='all';
let daySelectPopulated=false;
const platLabels={tiktok:'TikTok',twitch:'Twitch',youtube:'YouTube',kick:'Kick',vkplay:'VK Play',rumble:'Rumble',dlive:'DLive'};
function esc(t){let d=document.createElement('div');d.textContent=t==null?'':t;return d.innerHTML;}
function tiktokUrl(uid){return 'https://www.tiktok.com/@'+String(uid||'').replace(/^@/,'');}
function fmtTs(ts){if(!ts)return '';let d=new Date(ts*1000);let p=n=>String(n).padStart(2,'0');return p(d.getDate())+'.'+p(d.getMonth()+1)+'.'+d.getFullYear()+' '+p(d.getHours())+':'+p(d.getMinutes());}
function fmtDayLabel(d){
  let today=new Date();let todayStr=today.toISOString().slice(0,10);
  let yest=new Date(today.getTime()-86400000);let yestStr=yest.toISOString().slice(0,10);
  if(d===todayStr)return 'Сьогодні ('+d+')';
  if(d===yestStr)return 'Вчора ('+d+')';
  return d;
}
function populateDaySelect(days){
  if(daySelectPopulated)return;
  let sel=document.getElementById('daySelect');
  days.forEach(d=>{
    let opt=document.createElement('option');
    opt.value=d;opt.textContent=fmtDayLabel(d);
    sel.appendChild(opt);
  });
  daySelectPopulated=true;
}
function renderTop(containerId,items,formatter,opts){
  opts=opts||{};
  let el=document.getElementById(containerId);el.innerHTML='';
  if(!items||items.length===0){el.innerHTML='<div class="empty">Поки що немає даних</div>';return;}
  let medals=['🥇','🥈','🥉'];
  items.forEach((it,i)=>{
    let row=document.createElement('div');row.className='top-row';
    let rank=document.createElement('span');rank.className='rank';rank.textContent=medals[i]||(i+1)+'.';
    let img=document.createElement('img');img.src=it.avatar_url||'';img.onerror=function(){this.style.visibility='hidden';};
    let nick=document.createElement('span');nick.className='nick';
    let uid=it.unique_id||'';
    let isTikTok=opts.tiktok||(it.platform==='tiktok');
    if(isTikTok&&uid){nick.innerHTML='<a href="'+tiktokUrl(uid)+'" target="_blank" rel="noopener">'+esc(it.nickname)+'</a>';}
    else{nick.textContent=it.nickname;}
    row.appendChild(rank);row.appendChild(img);row.appendChild(nick);
    if(opts.showPlatform&&it.platform){let pl=document.createElement('span');pl.className='plat';pl.textContent=platLabels[it.platform]||it.platform;row.appendChild(pl);}
    let val=document.createElement('span');val.className='val';val.textContent=formatter(it.value!==undefined?it.value:it.message_count);
    row.appendChild(val);
    el.appendChild(row);
  });
}
function renderRoster(items){
  let el=document.getElementById('roster');el.innerHTML='';
  if(!items||items.length===0){el.innerHTML='<div class="empty">Поки що немає даних - зачекайте, поки хтось зайде на ефір</div>';return;}
  items.forEach(u=>{
    let row=document.createElement('div');row.className='roster-item';
    let img=document.createElement('img');img.src=u.avatar_url||'';img.onerror=function(){this.style.visibility='hidden';};
    let name=document.createElement('span');name.className='name';
    let uid=u.unique_id||'';
    if(uid){name.innerHTML='<a href="'+tiktokUrl(uid)+'" target="_blank" rel="noopener" title="Відкрити профіль TikTok">'+esc(u.nickname)+'</a>';}
    else{name.textContent=u.nickname;}
    let stats=document.createElement('span');stats.className='stats';
    stats.innerHTML='💬 <b>'+u.message_count+'</b> · 🎁 <b>'+u.gift_diamonds+'</b> 💎';
    let icons=document.createElement('span');icons.className='icons';
    let bMsg=document.createElement('button');bMsg.className='icon-btn';bMsg.textContent='💬';bMsg.title='Показати повідомлення';
    bMsg.disabled=!uid;
    bMsg.onclick=()=>openDetail(uid,'messages');
    let bGift=document.createElement('button');bGift.className='icon-btn';bGift.textContent='🎁';bGift.title='Показати подарунки';
    bGift.disabled=!uid;
    bGift.onclick=()=>openDetail(uid,'gifts');
    icons.appendChild(bMsg);icons.appendChild(bGift);
    row.appendChild(img);row.appendChild(name);row.appendChild(stats);row.appendChild(icons);
    el.appendChild(row);
  });
}
function closeModal(){document.getElementById('modalBg').classList.remove('open');}
document.getElementById('mClose').onclick=closeModal;
document.getElementById('modalBg').addEventListener('click',e=>{if(e.target.id==='modalBg')closeModal();});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeModal();});
async function openDetail(uid,mode){
  if(!uid)return;
  let bg=document.getElementById('modalBg');
  document.getElementById('mTitle').textContent=uid;
  document.getElementById('mSub').innerHTML='';
  document.getElementById('mAvatar').src='';
  document.getElementById('mBody').innerHTML='<div class="empty">Завантаження…</div>';
  bg.classList.add('open');
  try{
    let res=await fetch('/api/tiktok_user_detail?unique_id='+encodeURIComponent(uid));
    let d=await res.json();
    document.getElementById('mAvatar').src=d.avatar_url||'';
    document.getElementById('mTitle').textContent=(d.nickname||uid)+(mode==='gifts'?' — 🎁 подарунки':' — 💬 повідомлення');
    document.getElementById('mSub').innerHTML='<a href="'+tiktokUrl(uid)+'" target="_blank" rel="noopener">@'+esc(String(uid).replace(/^@/,''))+'</a> · 💬 '+(d.message_count||0)+' · 🎁 '+(d.gift_diamonds||0)+' 💎';
    let body=document.getElementById('mBody');
    let list=(mode==='gifts'?d.gifts:d.messages)||[];
    if(list.length===0){
      body.innerHTML='<div class="empty">'+(mode==='gifts'?'Цей глядач ще не надсилав подарунків':'Від цього глядача ще немає збережених повідомлень')+'</div>';
      return;
    }
    body.innerHTML=list.map(it=>{
      let ts='<span class="ts">'+esc(fmtTs(it.ts))+'</span>';
      if(mode==='gifts'){
        return '<div class="log-row">'+ts+'<span class="txt gift">'+esc(it.name||'Подарунок')+' ×'+(it.count||1)+' · '+(it.diamonds||0)+' 💎</span></div>';
      }
      return '<div class="log-row">'+ts+'<span class="txt">'+esc(it.text||'')+'</span></div>';
    }).join('');
  }catch(e){
    document.getElementById('mBody').innerHTML='<div class="empty">Помилка завантаження даних</div>';
  }
}
async function clearAllHistory(){
  if(!confirm('Очистити ВСЮ історію відвідувань TikTok? Дію не можна скасувати.'))return;
  try{
    let r=await fetch('/api/tiktok_history/clear',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({scope:'all'})});
    let d=await r.json();
    alert('Історію очищено. Видалено глядачів: '+(d.removed||0));
    daySelectPopulated=false;
    let sel=document.getElementById('daySelect');
    sel.innerHTML='<option value="all">Весь час</option>';
    currentSelectedDate='all';
    refresh();
  }catch(e){alert('Помилка: '+e);}
}
async function clearAllNetworksHistory(){
  if(!confirm('Очистити рейтинг "Топ глядачів усіх мереж"? Історія відвідувань TikTok залишиться недоторканою. Дію не можна скасувати.'))return;
  try{
    let r=await fetch('/api/tiktok_history/clear',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({scope:'all_networks'})});
    let d=await r.json();
    alert('Крос-мережевий рейтинг очищено. Видалено записів: '+(d.removed||0));
    refresh();
  }catch(e){alert('Помилка: '+e);}
}
async function clearDayHistory(){
  let day=(currentSelectedDate&&currentSelectedDate!=='all')?currentSelectedDate:new Date().toISOString().slice(0,10);
  if(!confirm('Очистити список активних глядачів за '+day+'? Інші дні залишаться.'))return;
  try{
    let r=await fetch('/api/tiktok_history/clear',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({scope:'day',date:day})});
    let d=await r.json();
    alert('Очищено записів за '+(d.date||day)+': '+(d.removed||0));
    refresh();
  }catch(e){alert('Помилка: '+e);}
}
async function refresh(){
  try{
    let url='/api/tiktok_history'+(currentSelectedDate&&currentSelectedDate!=='all'?('?date='+encodeURIComponent(currentSelectedDate)):'');
    let res=await fetch(url);let d=await res.json();
    populateDaySelect(d.available_days||[]);
    let isDay=d.selected_date&&d.selected_date!=='all';
    document.getElementById('totalKnown').textContent=isDay?('Активних глядачів за цей день: '+(d.roster||[]).length):('Всього відомо глядачів: '+(d.total_viewers_known||0));
    document.getElementById('topMessagesTitle').textContent=isDay?'💬 Топ активних у TikTok (цей день)':'💬 Топ активних у TikTok';
    document.getElementById('topGiftsTitle').textContent=isDay?'🎁 Топ дарувальників TikTok (цей день)':'🎁 Топ дарувальників TikTok (💎)';
    document.getElementById('rosterTitle').textContent=isDay?'Глядачі за обраний день':'Усі глядачі (за останньою активністю)';
    let topMsgItems=isDay?(d.top_messages||[]).map(x=>({unique_id:x.unique_id,nickname:x.nickname,avatar_url:x.avatar_url,value:x.message_count})):d.top_messages;
    let topGiftItems=isDay?(d.top_gifts||[]).map(x=>({unique_id:x.unique_id,nickname:x.nickname,avatar_url:x.avatar_url,value:x.gift_diamonds})):d.top_gifts;
    renderTop('topAll',d.top_all_networks||[],v=>v+' повід.',{showPlatform:true});
    renderTop('topMessages',topMsgItems,v=>v+' повід.',{tiktok:true});
    renderTop('topGifts',topGiftItems,v=>v+' 💎',{tiktok:true});
    renderRoster(d.roster);
  }catch(e){}
}
document.getElementById('daySelect').addEventListener('change',(e)=>{
  currentSelectedDate=e.target.value;
  refresh();
});
refresh();setInterval(refresh,10000);
</script>
</body>
</html>"""


def generate_music_player_html():
    return """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8">
<title>MultiChat - Музичний плеєр</title>
<style>
*{box-sizing:border-box}
body{background:#0a0a0a;margin:0;padding:8px;font-family:'Consolas','Lucida Console','DejaVu Sans Mono',monospace;color:#00e05a;height:100vh;overflow:hidden;display:flex;flex-direction:column;gap:8px;-webkit-font-smoothing:none}
.amp{background:linear-gradient(180deg,#2b2b2b 0%,#1b1b1b 55%,#141414 100%);border:1px solid #000;border-top-color:#555;border-left-color:#4a4a4a;box-shadow:inset 0 0 0 1px #3a3a3a,0 2px 6px rgba(0,0,0,0.8);border-radius:3px;padding:5px}
.amp.pl{flex-grow:1;display:flex;flex-direction:column;min-height:0}
.amp-titlebar{background:linear-gradient(180deg,#4a4a4a,#2a2a2a);border:1px solid #000;border-top-color:#6a6a6a;color:#bdbdbd;font-size:10px;letter-spacing:2px;text-transform:uppercase;padding:3px 6px;text-align:center;text-shadow:0 1px 0 #000;margin-bottom:5px}
.amp-titlebar span{color:#00e05a}
.amp-display{background:#000;border:1px solid #000;box-shadow:inset 1px 1px 0 #1d1d1d,inset -1px -1px 0 #3d3d3d;padding:6px 8px;display:grid;grid-template-columns:auto 1fr;grid-template-rows:auto auto;gap:2px 10px;align-items:center}
.amp-time{grid-row:1;grid-column:1;font-size:30px;line-height:1;font-weight:700;color:#00e05a;text-shadow:0 0 8px rgba(0,224,90,0.55);letter-spacing:1px;font-variant-numeric:tabular-nums}
.amp-vis{grid-row:1;grid-column:2;display:flex;align-items:flex-end;gap:2px;height:30px;justify-self:start}
.amp-vis i{display:block;width:4px;height:3px;background:#00e05a;box-shadow:0 0 4px rgba(0,224,90,0.5);opacity:0.55}
body.playing .amp-vis i{animation:eq .7s ease-in-out infinite alternate;opacity:1}
body.playing .amp-vis i:nth-child(2n){animation-duration:.5s}
body.playing .amp-vis i:nth-child(3n){animation-duration:.9s}
body.playing .amp-vis i:nth-child(4n){animation-duration:.35s}
body.playing .amp-vis i:nth-child(5n){animation-duration:1.1s}
@keyframes eq{from{height:3px}to{height:28px}}
.amp-marquee{grid-row:2;grid-column:1/3;overflow:hidden;white-space:nowrap;font-size:12px;color:#00e05a;text-shadow:0 0 6px rgba(0,224,90,0.4);height:16px}
.amp-marquee span{display:inline-block;white-space:nowrap;padding-right:40px}
.amp-marquee span.scroll{animation:marq 14s linear infinite}
@keyframes marq{from{transform:translateX(0)}to{transform:translateX(-100%)}}
.amp-info{grid-row:3;grid-column:1/3;font-size:9.5px;color:#7fd8a6;letter-spacing:1px;text-transform:uppercase;height:12px;overflow:hidden;white-space:nowrap}
.amp-info .ducked-badge{color:#ffd700;margin-left:6px}
.amp-sliders{display:flex;align-items:center;gap:8px;margin-top:5px;font-size:9.5px;color:#9a9a9a;letter-spacing:1px}
.amp-sliders .sl-lab{color:#8a8a8a}
.amp-seek{display:flex;align-items:center;gap:6px;margin-top:5px}
input[type=range]{-webkit-appearance:none;appearance:none;background:#000;height:14px;border:1px solid #000;box-shadow:inset 1px 1px 0 #1d1d1d,inset -1px -1px 0 #3a3a3a;flex-grow:1;margin:0;cursor:pointer}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:11px;height:12px;background:linear-gradient(180deg,#8a8a8a,#3a3a3a);border:1px solid #000;box-shadow:inset 0 1px 0 #c8c8c8}
input[type=range]::-moz-range-thumb{width:11px;height:12px;background:linear-gradient(180deg,#8a8a8a,#3a3a3a);border:1px solid #000;border-radius:0}
input[type=range]#volumeSlider{max-width:120px;flex-grow:0}
.seek-time{font-size:10px;color:#00e05a;min-width:38px;text-align:center;font-variant-numeric:tabular-nums}
.mon{display:flex;align-items:center;gap:4px;color:#9a9a9a;cursor:pointer;margin-left:auto}
.mon input{accent-color:#00e05a}
.amp-transport{display:flex;align-items:center;gap:3px;margin-top:6px;flex-wrap:wrap}
.wbtn{background:linear-gradient(180deg,#4c4c4c,#262626);border:1px solid #000;border-top-color:#707070;border-left-color:#606060;color:#dcdcdc;font-family:inherit;font-size:11px;min-width:30px;height:24px;padding:0 6px;cursor:pointer;text-shadow:0 1px 0 #000}
.wbtn:hover{background:linear-gradient(180deg,#5c5c5c,#303030);color:#00e05a}
.wbtn:active{background:linear-gradient(180deg,#202020,#3a3a3a);border-top-color:#000;border-left-color:#000}
.wbtn.tog{font-size:9px;letter-spacing:1px;min-width:auto}
.wbtn.tog.on{color:#00e05a;background:linear-gradient(180deg,#1e3a28,#0d1f14);box-shadow:inset 0 0 6px rgba(0,224,90,0.35)}
.wbtn.sm{font-size:9px;letter-spacing:1px;height:20px;min-width:auto;padding:0 7px}
.playlist{flex-grow:1;overflow-y:auto;background:#000;border:1px solid #000;box-shadow:inset 1px 1px 0 #1d1d1d,inset -1px -1px 0 #3a3a3a;padding:3px;min-height:0}
.playlist::-webkit-scrollbar{width:10px}
.playlist::-webkit-scrollbar-track{background:#111}
.playlist::-webkit-scrollbar-thumb{background:linear-gradient(180deg,#5a5a5a,#2a2a2a);border:1px solid #000}
.track-item{display:flex;align-items:center;gap:6px;padding:1px 4px;font-size:11px;color:#00e05a;cursor:grab;line-height:16px}
.track-item.active{background:#00e05a;color:#000;font-weight:700}
.track-item.active .num{color:#000}
.track-item.drag-src{opacity:0.4}
.track-item.drag-hover{outline:1px dotted #00e05a}
.track-item .num{flex-shrink:0;width:24px;text-align:right;color:#00b04a}
.track-item .tname{flex-grow:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;cursor:pointer}
.track-item .ord{display:flex;gap:2px;flex-shrink:0;opacity:0;transition:opacity .1s}
.track-item:hover .ord{opacity:1}
.ord button{background:linear-gradient(180deg,#4c4c4c,#262626);border:1px solid #000;border-top-color:#6a6a6a;color:#dcdcdc;width:18px;height:15px;font-size:9px;cursor:pointer;line-height:1;padding:0;font-family:inherit}
.ord button:hover:not(:disabled){color:#00e05a}
.ord button:disabled{opacity:0.25;cursor:default}
.ord button.del:hover{color:#ff5050}
.pl-foot{display:flex;align-items:center;gap:4px;margin-top:5px}
.pl-clock{margin-left:auto;font-size:11px;color:#00e05a;font-variant-numeric:tabular-nums}
.opts{margin-top:5px;background:#000;border:1px solid #2a2a2a;padding:6px}
.empty{color:#4a8a63;font-size:11px;padding:10px;text-align:center}
.folder-row{display:flex;gap:4px}
.folder-row input[type=text]{flex-grow:1;background:#000;border:1px solid #000;box-shadow:inset 1px 1px 0 #1d1d1d,inset -1px -1px 0 #3a3a3a;color:#00e05a;padding:4px 6px;font-size:11px;font-family:inherit}
.pbtn{background:linear-gradient(180deg,#4c4c4c,#262626);border:1px solid #000;border-top-color:#6a6a6a;color:#dcdcdc;padding:4px 8px;font-size:10px;cursor:pointer;flex-shrink:0;font-family:inherit;letter-spacing:1px}
.pbtn:hover{color:#00e05a}
.folder-status{font-size:10px;color:#7fd8a6;margin-top:4px;min-height:12px}
.order-hint{font-size:9.5px;color:#5f7f6c;margin-top:4px}
body.drag-over-page{outline:2px dotted #00e05a;outline-offset:-4px}
.upload-list{font-size:10px;color:#7fd8a6;margin-top:4px;max-height:60px;overflow-y:auto}
.modal-bg{position:fixed;inset:0;background:rgba(0,0,0,0.85);display:none;align-items:center;justify-content:center;z-index:60;padding:18px}
.modal-bg.open{display:flex}
.modal{background:#1b1b1b;border:1px solid #000;box-shadow:inset 0 0 0 1px #3a3a3a;width:100%;max-width:520px;max-height:80vh;display:flex;flex-direction:column}
.modal-head{display:flex;align-items:center;gap:8px;padding:6px 8px;background:linear-gradient(180deg,#4a4a4a,#2a2a2a);color:#bdbdbd;font-size:10px;letter-spacing:1px;text-transform:uppercase}
.modal-head .t{flex-grow:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.modal-close{background:none;border:none;color:#bdbdbd;font-size:1.1em;cursor:pointer}
.modal-path{padding:6px 8px;font-size:10px;color:#7fd8a6;border-bottom:1px solid #2a2a2a;word-break:break-all}
.modal-body{padding:4px;overflow-y:auto;flex-grow:1;background:#000}
.fs-row{display:flex;align-items:center;gap:8px;padding:3px 6px;font-size:11px;cursor:pointer;color:#00e05a}
.fs-row:hover{background:#00e05a;color:#000}
.modal-foot{padding:6px 8px;border-top:1px solid #2a2a2a;display:flex;gap:6px;justify-content:flex-end}
</style>
</head>
<body>
<div class="amp">
<div class="amp-titlebar">MultiChat Плеєр <span>2.95</span></div>
<div class="amp-display">
  <div class="amp-time" id="bigTime">0:00</div>
  <div class="amp-vis" id="vis"><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i><i></i></div>
  <div class="amp-marquee"><span id="trackName">Завантаження…</span></div>
  <div class="amp-info"><span id="trackStatus"></span></div>
</div>
<div class="amp-sliders">
  <span class="sl-lab">ГУЧНІСТЬ</span>
  <input type="range" id="volumeSlider" min="0" max="100" value="70" title="Гучність">
  <label class="mon" title="Слухати самому (лише в цьому вікні)"><input type="checkbox" id="listenToggle" checked> ЧУТИ ТУТ</label>
</div>
<div class="amp-seek">
  <span class="seek-time" id="seekCur">0:00</span>
  <input type="range" id="seekSlider" min="0" max="1000" value="0" step="1" title="Перемотка треку">
  <span class="seek-time" id="seekDur">0:00</span>
</div>
<div class="amp-transport">
  <button class="wbtn" id="btnPrev" title="Попередній трек">⏮ НАЗАД</button>
  <button class="wbtn" id="btnPlay" title="Пауза / Відтворити">⏸ ПАУЗА</button>
  <button class="wbtn" id="btnStop" title="Стоп (на початок треку)">⏹ СТОП</button>
  <button class="wbtn" id="btnNext" title="Наступний трек">ВПЕРЕД ⏭</button>
  <button class="wbtn" id="btnEject" title="Додати файли з ПК">⏏ ДОДАТИ</button>
  <button class="wbtn tog" id="btnShuffle" title="Перемішування треків">ВИПАДКОВО</button>
  <button class="wbtn tog" id="btnRepeat" title="Повторювати поточний трек">&#8644; ПОВТОР</button>
</div>
</div>

<div class="amp pl">
<div class="amp-titlebar">Плейлист — <span id="trackCount">0</span> треків</div>
<div class="playlist" id="playlist"></div>
<div class="pl-foot">
  <button class="wbtn sm" id="pickFilesBtn" title="Додати файли з ПК">+ ФАЙЛИ</button>
  <button class="wbtn sm" id="pickFolderBtn" title="Додати папку з ПК">+ ПАПКА</button>
  <span id="restoreRow" style="display:none"><button class="wbtn sm" id="btnRestoreRemoved" title="Повернути прибрані треки">↺ ПОВЕРНУТИ <span id="removedCount">0</span></button></span>
  <button class="wbtn sm" id="btnOpts" title="Налаштування папки / підказки">НАЛАШТУВАННЯ</button>
  <span class="pl-clock" id="plClock">0:00 / 0:00</span>
</div>
<div class="opts" id="optsBox" style="display:none">
  <div class="folder-row">
    <input type="text" id="folderInput" placeholder="Шлях до папки з треками, напр. C:\\Music">
    <button class="pbtn" id="folderBrowseBtn" title="Обрати папку на цьому ПК">ОБРАТИ…</button>
    <button class="pbtn" id="folderSaveBtn">ЗБЕРЕГТИ</button>
  </div>
  <div class="folder-status" id="folderStatus"></div>
  <div class="upload-list" id="uploadList"></div>
  <div class="order-hint">ADD / DIR — додати з ПК • перетягніть файли у вікно • ▲▼ або перетягування рядка — порядок • клік — грати • ✖ — прибрати • REM — повернути прибрані</div>
</div>
</div>

<input type="file" id="fileInput" accept=".mp3,.wav,.ogg,.m4a,.flac,.aac,audio/*" multiple style="display:none">
<input type="file" id="dirInput" webkitdirectory directory multiple style="display:none">
<audio id="audioEl" preload="auto"></audio>

<div class="modal-bg" id="fsModal">
  <div class="modal">
    <div class="modal-head"><span class="t">Оберіть папку з музикою</span><button class="modal-close" id="fsClose">✕</button></div>
    <div class="modal-path" id="fsPath"></div>
    <div class="modal-body" id="fsBody"></div>
    <div class="modal-foot">
      <button class="pbtn" id="fsUp">⬆ ВГОРУ</button>
      <button class="pbtn" id="fsPick">✅ ОБРАТИ ЦЮ ПАПКУ</button>
    </div>
  </div>
</div>

<script>
let audio=document.getElementById('audioEl');
let currentIndex=-1;
let tracks=[];
let listenEnabled=true;
let lastAppliedPosition=-1;
let folderInputTouched=false;
let reorderBusy=false;
let dragFrom=-1;
let seeking=false;
let seekSuppressUntil=0;
let volumeSaveTimer=null;
let volumeInitialized=false;
let shuffleOn=false;
let repeatOne=false;
try{shuffleOn=localStorage.getItem('amp_shuffle')==='1';repeatOne=localStorage.getItem('amp_repeat')==='1';}catch(e){}

function fmtTime(sec){
  sec=Math.max(0,Math.floor(sec||0));
  let m=Math.floor(sec/60),s2=sec%60;
  return m+':'+(s2<10?'0':'')+s2;
}

function updateSeekUI(position){
  let dur=(audio&&isFinite(audio.duration)&&audio.duration>0)?audio.duration:0;
  let sl=document.getElementById('seekSlider');
  document.getElementById('seekDur').textContent=dur?fmtTime(dur):'--:--';
  document.getElementById('seekCur').textContent=fmtTime(position);
  if(seeking)return;
  sl.disabled=!dur;
  sl.value=dur?Math.round(Math.min(1000,(position/dur)*1000)):0;
}

async function sendSeek(positionSec){
  try{
    await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'seek',position:positionSec})});
  }catch(e){}
}

function esc(t){let d=document.createElement('div');d.textContent=t==null?'':t;return d.innerHTML;}

function fmtStatus(state){
  if(state.ducked)return 'Приглушено (грає TTS/алерт)';
  if(state.paused)return 'На паузі';
  return 'Відтворюється';
}

async function pollState(){
  if(reorderBusy)return;
  try{
    let res=await fetch('/api/music/state');
    let state=await res.json();
    tracks=state.tracks||[];
    if(!folderInputTouched){
      let fi=document.getElementById('folderInput');
      if(document.activeElement!==fi)fi.value=state.folder_path||'';
    }
    document.getElementById('trackCount').textContent=tracks.length;
    let removed=state.removed_count||0;
    document.getElementById('restoreRow').style.display=removed>0?'':'none';
    document.getElementById('removedCount').textContent=removed;
    renderPlaylist(state.track_index);

    if(!state.enabled||tracks.length===0){
      document.getElementById('trackName').textContent=tracks.length===0?'Плейлист порожній - вкажіть папку або додайте файли':'Плеєр вимкнено в налаштуваннях';
      document.getElementById('trackStatus').textContent='';
      audio.pause();
      return;
    }

    let trackName=tracks[state.track_index]||'';
    document.getElementById('trackName').textContent=trackName;
    document.getElementById('trackStatus').innerHTML=fmtStatus(state)+(state.ducked?'<span class="ducked-badge">🔇 ducking</span>':'');
    document.getElementById('btnPlay').textContent=state.paused?'▶ ГРАТИ':'⏸ ПАУЗА';

    if(currentIndex!==state.track_index||(trackName&&audio.src&&decodeURIComponent(audio.src.split('name=')[1]||'')!==trackName)){
      currentIndex=state.track_index;
      audio.src='/music_file?name='+encodeURIComponent(trackName);
      lastAppliedPosition=-1;
    }

    if(!seeking&&Date.now()>seekSuppressUntil&&Math.abs((lastAppliedPosition<0?state.position:audio.currentTime)-state.position)>2.5){
      audio.currentTime=state.position;
    }
    lastAppliedPosition=state.position;

    if(!volumeInitialized&&typeof state.volume==='number'){
      volumeInitialized=true;
      audio.volume=state.volume;
      document.getElementById('volumeSlider').value=Math.round(state.volume*100);
    }
    updateSeekUI(state.position);

    audio.muted=!listenEnabled;
    if(state.paused){
      if(!audio.paused)audio.pause();
    }else{
      if(audio.paused)audio.play().catch(()=>{});
    }
  }catch(e){}
}

function renderPlaylist(activeIndex){
  let el=document.getElementById('playlist');
  el.innerHTML='';
  if(tracks.length===0){
    el.innerHTML='<div class="empty">Немає треків - вкажіть папку, перетягніть файли або додайте їх з ПК</div>';
    return;
  }
  tracks.forEach((t,i)=>{
    let div=document.createElement('div');
    div.className='track-item'+(i===activeIndex?' active':'');
    div.draggable=true;
    div.dataset.index=i;

    let num=document.createElement('span');num.className='num';num.textContent=(i+1)+'.';
    let name=document.createElement('span');name.className='tname';
    name.textContent=(i===activeIndex?'▶ ':'')+t;
    name.title='Клік — грати цей трек';
    name.onclick=()=>playIndex(i);

    let ord=document.createElement('span');ord.className='ord';
    let up=document.createElement('button');up.textContent='▲';up.title='Вище в плейлисті';up.disabled=(i===0);
    up.onclick=(e)=>{e.stopPropagation();moveTrack(i,i-1);};
    let down=document.createElement('button');down.textContent='▼';down.title='Нижче в плейлисті';down.disabled=(i===tracks.length-1);
    down.onclick=(e)=>{e.stopPropagation();moveTrack(i,i+1);};
    let del=document.createElement('button');del.textContent='✖';del.className='del';
    del.title='Прибрати з плейлиста (файл на диску залишиться)';
    del.onclick=(e)=>{e.stopPropagation();removeTrack(t);};
    ord.appendChild(up);ord.appendChild(down);ord.appendChild(del);

    div.appendChild(num);div.appendChild(name);div.appendChild(ord);

    div.addEventListener('dragstart',(e)=>{dragFrom=i;div.classList.add('drag-src');e.dataTransfer.effectAllowed='move';try{e.dataTransfer.setData('text/plain',String(i));}catch(err){}});
    div.addEventListener('dragend',()=>{dragFrom=-1;div.classList.remove('drag-src');});
    div.addEventListener('dragover',(e)=>{if(dragFrom>=0){e.preventDefault();div.classList.add('drag-hover');}});
    div.addEventListener('dragleave',()=>div.classList.remove('drag-hover'));
    div.addEventListener('drop',(e)=>{
      div.classList.remove('drag-hover');
      if(dragFrom<0)return;
      e.preventDefault();e.stopPropagation();
      let to=i;let from=dragFrom;dragFrom=-1;
      if(from!==to)moveTrack(from,to);
    });

    el.appendChild(div);
  });
}

async function removeTrack(name){
  if(!name)return;
  reorderBusy=true;
  try{
    let res=await fetch('/api/music/remove_track',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({name:name})});
    let data=await res.json();
    if(!data.ok)alert('Не вдалося прибрати трек: '+(data.error||'невідома помилка'));
  }catch(e){}
  reorderBusy=false;
  pollState();
}

async function restoreRemoved(){
  reorderBusy=true;
  try{await fetch('/api/music/restore_removed',{method:'POST'});}catch(e){}
  reorderBusy=false;
  pollState();
}

async function playIndex(i){
  try{
    await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'goto',index:i})});
  }catch(e){}
  pollState();
}

async function moveTrack(from,to){
  if(from<0||to<0||from>=tracks.length||to>=tracks.length||from===to)return;
  let order=tracks.slice();
  let item=order.splice(from,1)[0];
  order.splice(to,0,item);
  tracks=order;
  renderPlaylist(currentIndex);
  reorderBusy=true;
  try{
    let res=await fetch('/api/music/reorder',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({order:order})});
    let data=await res.json();
    if(data.ok&&data.tracks){tracks=data.tracks;if(data.state)currentIndex=data.state.track_index;}
  }catch(e){}
  reorderBusy=false;
  pollState();
}

audio.addEventListener('ended',async()=>{
  try{
    if(repeatOne){
      await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'seek',position:0})});
      audio.currentTime=0;
      await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'play'})});
      pollState();
      return;
    }
    if(shuffleOn&&tracks.length>1){
      let idx=currentIndex;
      for(let i=0;i<12&&idx===currentIndex;i++)idx=Math.floor(Math.random()*tracks.length);
      await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'goto',index:idx})});
      pollState();
      return;
    }
    await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:'advance',from_index:currentIndex})});
  }catch(e){}
});

async function sendControl(action){
  try{
    await fetch('/api/music/control',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({action:action})});
  }catch(e){}
  pollState();
}

document.getElementById('btnPlay').addEventListener('click',()=>{
  sendControl(audio.paused?'play':'pause');
});
document.getElementById('btnNext').addEventListener('click',()=>sendControl('next'));
document.getElementById('btnRestoreRemoved').addEventListener('click',restoreRemoved);
document.getElementById('btnPrev').addEventListener('click',()=>sendControl('prev'));
document.getElementById('volumeSlider').addEventListener('input',(e)=>{
  let v=e.target.value/100;
  audio.volume=v;
  volumeInitialized=true;
  if(volumeSaveTimer)clearTimeout(volumeSaveTimer);
  volumeSaveTimer=setTimeout(()=>{
    fetch('/api/music/volume',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({volume:v})}).catch(()=>{});
  },300);
});

(function(){
  let sl=document.getElementById('seekSlider');
  const startSeek=()=>{seeking=true;};
  const applySeek=async()=>{
    if(!seeking)return;
    seeking=false;
    let dur=(audio&&isFinite(audio.duration)&&audio.duration>0)?audio.duration:0;
    if(!dur)return;
    let pos=(sl.value/1000)*dur;
    seekSuppressUntil=Date.now()+2500;
    audio.currentTime=pos;
    document.getElementById('seekCur').textContent=fmtTime(pos);
    await sendSeek(pos);
    pollState();
  };
  sl.addEventListener('mousedown',startSeek);
  sl.addEventListener('touchstart',startSeek);
  sl.addEventListener('keydown',startSeek);
  sl.addEventListener('input',()=>{
    let dur=(audio&&isFinite(audio.duration)&&audio.duration>0)?audio.duration:0;
    if(dur)document.getElementById('seekCur').textContent=fmtTime((sl.value/1000)*dur);
  });
  sl.addEventListener('change',applySeek);
  sl.addEventListener('mouseup',applySeek);
  sl.addEventListener('touchend',applySeek);
  audio.addEventListener('timeupdate',()=>{if(!seeking)updateSeekUI(audio.currentTime);});
  audio.addEventListener('loadedmetadata',()=>updateSeekUI(audio.currentTime));
})();
document.getElementById('listenToggle').addEventListener('change',(e)=>{
  listenEnabled=e.target.checked;
  audio.muted=!listenEnabled;
});

document.getElementById('folderInput').addEventListener('input',()=>{folderInputTouched=true;});
async function saveFolder(path){
  let statusEl=document.getElementById('folderStatus');
  statusEl.textContent='Зберігаю…';
  try{
    let res=await fetch('/api/settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({music_folder_path:path})});
    let data=await res.json();
    if(data.ok){
      statusEl.textContent='Збережено ✓ '+path;
      folderInputTouched=false;
      document.getElementById('folderInput').value=path;
      setTimeout(()=>{statusEl.textContent='';},2500);
      pollState();
    }else{
      statusEl.textContent='Помилка: '+(data.error||'невідома');
    }
  }catch(e){
    statusEl.textContent='Не вдалося зберегти';
  }
}
document.getElementById('folderSaveBtn').addEventListener('click',()=>{
  saveFolder(document.getElementById('folderInput').value.trim());
});

/* ---- серверний огляд диска: вибір папки з треками ---- */
let fsCurrent='';
function fsClose(){document.getElementById('fsModal').classList.remove('open');}
document.getElementById('fsClose').onclick=fsClose;
document.getElementById('fsModal').addEventListener('click',e=>{if(e.target.id==='fsModal')fsClose();});
document.addEventListener('keydown',e=>{if(e.key==='Escape')fsClose();});
async function fsLoad(path){
  let body=document.getElementById('fsBody');
  body.innerHTML='<div class="empty">Завантаження…</div>';
  try{
    let res=await fetch('/api/browse_fs?only_dirs=1&path='+encodeURIComponent(path||''));
    let d=await res.json();
    if(!d.ok){body.innerHTML='<div class="empty">'+esc(d.error||'Помилка')+'</div>';return;}
    fsCurrent=d.current_path||'';
    document.getElementById('fsPath').textContent=fsCurrent||'Диски / корінь';
    document.getElementById('fsUp').style.display=(d.parent_path===null?'none':'inline-block');
    document.getElementById('fsUp').onclick=()=>fsLoad(d.parent_path||'');
    document.getElementById('fsPick').style.display=fsCurrent?'inline-block':'none';
    body.innerHTML='';
    if(!(d.entries||[]).length){body.innerHTML='<div class="empty">Тут немає підпапок</div>';}
    (d.entries||[]).forEach(en=>{
      let row=document.createElement('div');row.className='fs-row';
      row.innerHTML='📁 '+esc(en.name);
      row.onclick=()=>fsLoad(en.path);
      body.appendChild(row);
    });
  }catch(e){body.innerHTML='<div class="empty">Помилка запиту</div>';}
}
document.getElementById('folderBrowseBtn').addEventListener('click',()=>{
  document.getElementById('fsModal').classList.add('open');
  fsLoad(document.getElementById('folderInput').value.trim());
});
document.getElementById('fsPick').addEventListener('click',()=>{
  if(fsCurrent){saveFolder(fsCurrent);fsClose();}
});

/* ---- додавання файлів з ПК (копіюються в папку плейлиста) ---- */
const AUDIO_EXT=['.mp3','.wav','.ogg','.m4a','.flac','.aac'];
function isAudio(name){let n=(name||'').toLowerCase();return AUDIO_EXT.some(x=>n.endsWith(x));}
async function uploadFiles(files){
  files=(files||[]).filter(f=>isAudio(f.name));
  if(files.length===0){
    let listEl=document.getElementById('uploadList');
    listEl.innerHTML='<div>⚠️ Аудіофайлів не знайдено (mp3, wav, ogg, m4a, flac, aac)</div>';
    setTimeout(()=>{listEl.innerHTML='';},4000);
    return;
  }
  let listEl=document.getElementById('uploadList');
  for(let file of files){
    let line=document.createElement('div');
    line.textContent='⏳ '+file.name;
    listEl.appendChild(line);
    listEl.scrollTop=listEl.scrollHeight;
    try{
      let res=await fetch('/api/music/upload',{method:'POST',headers:{'X-Music-Filename':encodeURIComponent(file.name)},body:file});
      let data=await res.json();
      line.textContent=data.ok?('✅ '+file.name):('❌ '+file.name+' - '+(data.error||'помилка'));
    }catch(err){
      line.textContent='❌ '+file.name+' - помилка мережі';
    }
  }
  setTimeout(()=>{listEl.innerHTML='';pollState();},4000);
  pollState();
}
document.getElementById('pickFilesBtn').addEventListener('click',()=>document.getElementById('fileInput').click());
document.getElementById('pickFolderBtn').addEventListener('click',()=>document.getElementById('dirInput').click());
document.getElementById('fileInput').addEventListener('change',(e)=>{uploadFiles(Array.from(e.target.files||[]));e.target.value='';});
document.getElementById('dirInput').addEventListener('change',(e)=>{uploadFiles(Array.from(e.target.files||[]));e.target.value='';});

// Drag&drop без видимої смуги: приймаємо файли по всій сторінці плеєра
let dropTarget=document.body;
['dragenter','dragover'].forEach(evt=>{
  dropTarget.addEventListener(evt,(e)=>{e.preventDefault();e.stopPropagation();dropTarget.classList.add('drag-over-page');});
});
['dragleave','dragend'].forEach(evt=>{
  dropTarget.addEventListener(evt,(e)=>{e.preventDefault();e.stopPropagation();if(!e.relatedTarget)dropTarget.classList.remove('drag-over-page');});
});
dropTarget.addEventListener('drop',async(e)=>{
  e.preventDefault();e.stopPropagation();
  dropTarget.classList.remove('drag-over-page');
  let files=Array.from((e.dataTransfer&&e.dataTransfer.files)||[]);
  if(files.length===0)return;
  uploadFiles(files);
});

/* ---- Winamp/Spotiamp skin: додаткові кнопки та LCD-індикація ---- */
function ampSyncToggles(){
  let sh=document.getElementById('btnShuffle'),rp=document.getElementById('btnRepeat');
  if(sh)sh.classList.toggle('on',shuffleOn);
  if(rp)rp.classList.toggle('on',repeatOne);
}
document.getElementById('btnShuffle').addEventListener('click',()=>{
  shuffleOn=!shuffleOn;
  try{localStorage.setItem('amp_shuffle',shuffleOn?'1':'0');}catch(e){}
  ampSyncToggles();
});
document.getElementById('btnRepeat').addEventListener('click',()=>{
  repeatOne=!repeatOne;
  try{localStorage.setItem('amp_repeat',repeatOne?'1':'0');}catch(e){}
  ampSyncToggles();
});
ampSyncToggles();
document.getElementById('btnStop').addEventListener('click',async()=>{
  seekSuppressUntil=Date.now()+2500;
  try{audio.pause();audio.currentTime=0;}catch(e){}
  await sendSeek(0);
  sendControl('pause');
});
document.getElementById('btnEject').addEventListener('click',()=>document.getElementById('fileInput').click());
document.getElementById('btnOpts').addEventListener('click',()=>{
  let box=document.getElementById('optsBox');
  let open=box.style.display==='none';
  box.style.display=open?'':'none';
  document.getElementById('btnOpts').classList.toggle('on',open);
});
function ampTick(){
  let cur=(audio&&isFinite(audio.currentTime))?audio.currentTime:0;
  let dur=(audio&&isFinite(audio.duration)&&audio.duration>0)?audio.duration:0;
  let bt=document.getElementById('bigTime');
  if(bt)bt.textContent=fmtTime(cur);
  let pc=document.getElementById('plClock');
  if(pc)pc.textContent=fmtTime(cur)+' / '+(dur?fmtTime(dur):'--:--');
  document.body.classList.toggle('playing',!!(audio&&!audio.paused&&!audio.ended));
  let sp=document.getElementById('trackName');
  if(sp)sp.classList.toggle('scroll',sp.scrollWidth>sp.parentNode.clientWidth+8);
}
setInterval(ampTick,250);
ampTick();

pollState();
setInterval(pollState,2000);
</script>
</body>
</html>"""


def synthesize_windows_sapi_bytes(text, speed):
    ps_path = None
    text_path = None
    output_path = None
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix='.ps1', mode='w', encoding='utf-8') as ps_file:
            ps_path = ps_file.name
            ps_file.write("""param([string]$TextPath,[string]$OutputPath,[int]$Rate)
Add-Type -AssemblyName System.Speech
$text = [System.IO.File]::ReadAllText($TextPath, [System.Text.Encoding]::UTF8)
$synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
$synth.Rate = [Math]::Max(-10, [Math]::Min(10, $Rate))
$synth.Volume = 100
$synth.SetOutputToWaveFile($OutputPath)
$synth.Speak($text)
$synth.Dispose()""")
        with tempfile.NamedTemporaryFile(delete=False, suffix='.txt', mode='w', encoding='utf-8') as text_file:
            text_path = text_file.name
            text_file.write(text)
        with tempfile.NamedTemporaryFile(delete=False, suffix='.wav') as output_file:
            output_path = output_file.name

        rate = int(max(-10, min(10, round((float(speed or 1.0) - 1.0) * 8))))
        powershell = os.path.join(os.environ.get("SystemRoot", r"C:\Windows"), "System32", "WindowsPowerShell", "v1.0", "powershell.exe")
        if not os.path.exists(powershell):
            powershell = "powershell"

        cmd = [powershell, "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", ps_path, text_path, output_path, str(rate)]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
        if proc.returncode != 0:
            err = proc.stderr.decode('utf-8', errors='replace')[:300]
            raise RuntimeError("Windows SAPI failed: {}".format(err))

        with open(output_path, 'rb') as output_file:
            return output_file.read(), 'audio/wav'
    finally:
        for path_to_remove in (ps_path, text_path, output_path):
            if path_to_remove and os.path.exists(path_to_remove):
                try:
                    os.unlink(path_to_remove)
                except:
                    pass


# ---------------------------------------------------------------------------
# СТІЙКІСТЬ TTS ДО ОБРИВІВ З'ЄДНАННЯ ([WinError 10053] та подібні)
# ---------------------------------------------------------------------------
# У логах: "Помилка TTS: [WinError 10053] Программа на вашем хост-компьютере
# разорвала установленное подключение". Що було раніше:
#   * обрив трактувався як звичайна помилка -> синтезоване аудіо вилітало,
#     а наступний запит синтезував ту саму фразу ЗНОВУ (реальні гроші на
#     ElevenLabs і, за іншим голосом, повторна озвучка);
#   * обрив ПІД ЧАС віддачі аудіо змушував код писати 500 у вже мертвий
#     сокет -> другий виняток усередині except;
#   * обрив у виклику ДО ElevenLabs одразу віддавав фразу Google TTS,
#     тобто глядач чув її іншим голосом.
# Тепер: транзитний обрив = повтор ТІЛЬКИ цього одного запиту, готові байти
# лежать у короткому кеші, а жодна інша підсистема (читачі чату, аналітика,
# HTTP-сервер) навіть не знає про цю подію.
TTS_TRANSIENT_ERRNOS = (10053, 10054, 10060, 32, 104, 110)
TTS_SYNTH_RETRIES = 2          # скільки повторів ОДНОГО запиту синтезу
TTS_SYNTH_RETRY_DELAY = 0.6
TTS_CACHE_TTL = 180            # скільки живуть готові байти (секунди)
TTS_CACHE_MAX = 40             # скільки фраз тримаємо максимум

tts_cache_lock = threading.Lock()
tts_audio_cache = collections.OrderedDict()
tts_stats = {'synthesized': 0, 'cache_hits': 0, 'retries': 0,
             'client_aborts': 0, 'served': 0, 'failed': 0}


def tts_note(event, count=1):
    with tts_cache_lock:
        tts_stats[event] = int(tts_stats.get(event, 0)) + count


def tts_error_is_transient(exc):
    """True для обривів сокета: WinError 10053/10054, ECONNRESET, EPIPE,
    таймаути. Саме їх має сенс повторювати."""
    if isinstance(exc, (ConnectionAbortedError, ConnectionResetError,
                        BrokenPipeError, socket.timeout, TimeoutError)):
        return True
    if isinstance(exc, urllib.error.HTTPError):
        return False          # відмова сервера - повторювати марно
    if isinstance(exc, urllib.error.URLError):
        return tts_error_is_transient(exc.reason) if isinstance(exc.reason, Exception) else True
    if isinstance(exc, OSError):
        code = getattr(exc, 'winerror', None) or getattr(exc, 'errno', None)
        return code in TTS_TRANSIENT_ERRNOS
    return False


def tts_call_with_retry(label, func):
    """Повторює ОДИН виклик синтезу при обриві з'єднання. Нічого не
    перезапускає і не змінює рушій TTS."""
    attempt = 0
    while True:
        try:
            return func()
        except Exception as e:
            if attempt >= TTS_SYNTH_RETRIES or not tts_error_is_transient(e):
                raise
            attempt += 1
            tts_note('retries')
            print("[TTS] {}: обрив з'єднання ({}: {}). Повтор {}/{} лише цього "
                  "запиту - інші сервіси не зачіпаються.".format(
                      label, type(e).__name__, e, attempt, TTS_SYNTH_RETRIES))
            time.sleep(TTS_SYNTH_RETRY_DELAY * attempt)


def tts_cache_key(text, lang, engine, voice, speed):
    raw = '|'.join([str(text or ''), str(lang or ''), str(engine or ''),
                    str(voice or ''), '{:.3f}'.format(float(speed or 1.0))])
    return hashlib.sha1(raw.encode('utf-8', 'ignore')).hexdigest()


def tts_cache_get(key):
    now = time.time()
    with tts_cache_lock:
        entry = tts_audio_cache.get(key)
        if not entry:
            return None
        if now - entry['ts'] > TTS_CACHE_TTL:
            tts_audio_cache.pop(key, None)
            return None
        tts_audio_cache.move_to_end(key)
        tts_stats['cache_hits'] = int(tts_stats.get('cache_hits', 0)) + 1
        return entry['audio'], entry['content_type']


def tts_cache_put(key, audio, content_type):
    if not audio:
        return
    with tts_cache_lock:
        tts_audio_cache[key] = {'audio': audio, 'content_type': content_type, 'ts': time.time()}
        tts_audio_cache.move_to_end(key)
        while len(tts_audio_cache) > TTS_CACHE_MAX:
            tts_audio_cache.popitem(last=False)   # FIFO, а не .clear()


def tts_state_snapshot():
    with tts_cache_lock:
        return {'cache_size': len(tts_audio_cache), 'cache_ttl': TTS_CACHE_TTL,
                'cache_max': TTS_CACHE_MAX, 'retries_allowed': TTS_SYNTH_RETRIES,
                'stats': dict(tts_stats)}


def split_text_for_google_tts(text, max_len=GOOGLE_TTS_CHUNK_LENGTH):
    """Ріже довгий текст на шматки для Google Translate TTS (у нього
    недокументований ліміт довжини одного запиту), намагаючись розбивати
    по кінцю речення/розділовому знаку чи хоча б по пробілу, а не всередині
    слова."""
    text = (text or "").strip()
    if not text:
        return []
    if len(text) <= max_len:
        return [text]
    chunks = []
    remaining = text
    while remaining:
        if len(remaining) <= max_len:
            chunks.append(remaining.strip())
            break
        window = remaining[:max_len]
        split_at = -1
        for sep in ('. ', '! ', '? ', '.\n', ', '):
            idx = window.rfind(sep)
            if idx > max_len * 0.4:
                split_at = idx + len(sep)
                break
        if split_at == -1:
            idx = window.rfind(' ')
            split_at = idx + 1 if idx > 0 else max_len
        chunk = remaining[:split_at].strip()
        if chunk:
            chunks.append(chunk)
        remaining = remaining[split_at:].strip()
    return [c for c in chunks if c]


def synthesize_google_tts_bytes(text, lang, speed=1.0):
    def _fetch_chunk(chunk_text):
        g_url = "https://translate.google.com/translate_tts?ie=UTF-8&client=tw-ob&tl={}&q={}".format(lang, urllib.parse.quote(chunk_text))

        def _fetch():
            req = urllib.request.Request(g_url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=20) as response:
                return response.read(), 'audio/mpeg'

        # Обрив сокета повторюється ТУТ: інакше фраза діставалась SAPI і
        # звучала іншим голосом попри те, що Google був цілком доступний.
        return tts_call_with_retry('Google TTS', _fetch)

    chunks = split_text_for_google_tts(text)
    if not chunks:
        chunks = [text or ""]

    try:
        if len(chunks) == 1:
            return _fetch_chunk(chunks[0])
        # Довге повідомлення: озвучуємо частинами і склеюємо MP3-байти в
        # один аудіопотік, щоб прозвучало ЦІЛЕ повідомлення, а не половина.
        audio_parts = []
        content_type = 'audio/mpeg'
        for chunk_text in chunks:
            data, ct = _fetch_chunk(chunk_text)
            audio_parts.append(data)
            content_type = ct or content_type
        return b"".join(audio_parts), content_type
    except Exception as e:
        print("[TTS] Google не вдався, перехід на Windows SAPI: {}".format(e))
        return synthesize_windows_sapi_bytes(text, speed)


def _copy_if_newer(src, dst):
    if not src or not os.path.exists(src):
        return False
    dst_dir = os.path.dirname(dst)
    if dst_dir and not os.path.isdir(dst_dir):
        os.makedirs(dst_dir, exist_ok=True)
    try:
        if os.path.exists(dst):
            same_size = os.path.getsize(src) == os.path.getsize(dst)
            src_mtime = int(os.path.getmtime(src))
            dst_mtime = int(os.path.getmtime(dst))
            if same_size and dst_mtime >= src_mtime:
                return False
        shutil.copy2(src, dst)
        return True
    except Exception:
        shutil.copyfile(src, dst)
        return True


def synthesize_elevenlabs_bytes(text, voice_id="", speed=1.0):
    """Синтез через ElevenLabs Text-to-Speech API.

    POST https://api.elevenlabs.io/v1/text-to-speech/{voice_id}
    Заголовок xi-api-key, у відповідь приходить готове аудіо (mp3).
    Ключ береться з налаштувань (поле типу secret) — у коді його немає.
    """
    api_key = (config.get("elevenlabs_api_key") or "").strip()
    if not api_key:
        raise RuntimeError("ElevenLabs: не вказано API-ключ у налаштуваннях")
    voice_id = resolve_elevenlabs_voice_id(voice_id)
    model_id = (config.get("elevenlabs_model") or "eleven_multilingual_v2").strip()
    output_format = (config.get("elevenlabs_output_format") or "mp3_44100_128").strip()
    try:
        stability = max(0.0, min(1.0, float(config.get("elevenlabs_stability", 50) or 50) / 100.0))
    except (TypeError, ValueError):
        stability = 0.5
    try:
        similarity = max(0.0, min(1.0, float(config.get("elevenlabs_similarity", 75) or 75) / 100.0))
    except (TypeError, ValueError):
        similarity = 0.75
    try:
        speed_value = max(0.7, min(1.2, float(speed or 1.0)))
    except (TypeError, ValueError):
        speed_value = 1.0

    voice_settings = {
        "stability": stability,
        "similarity_boost": similarity,
    }
    # 'speed' підтримують не всі моделі — надсилаємо лише коли реально треба
    if abs(speed_value - 1.0) > 0.01:
        voice_settings["speed"] = speed_value
    payload = {
        "text": text,
        "model_id": model_id,
        "voice_settings": voice_settings,
    }
    if config.get("elevenlabs_debug"):
        print("[TTS] ElevenLabs запит: voice={} model={} format={} stability={} similarity={} speed={} len(text)={}".format(
            voice_id, model_id, output_format, stability, similarity,
            voice_settings.get("speed", "—"), len(text or "")))
    url = "https://api.elevenlabs.io/v1/text-to-speech/{}?output_format={}".format(
        urllib.parse.quote(voice_id), urllib.parse.quote(output_format))
    req = urllib.request.Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "xi-api-key": api_key,
            "Content-Type": "application/json",
            "Accept": "audio/mpeg",
            "User-Agent": "MultiChat-OBS/1.0",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=30) as response:
        audio = response.read()
    content_type = "audio/wav" if output_format.startswith("pcm") else "audio/mpeg"
    return audio, content_type


def elevenlabs_diagnose():
    """Повна перевірка ElevenLabs: ключ, підписка, тестовий синтез.

    Повертає dict із текстовими рядками — його показує сторінка
    /api/tts/elevenlabs_test, щоб можна було просто скопіювати результат.
    """
    report = {"ok": False, "steps": []}

    def step(name, status, detail=""):
        report["steps"].append({"name": name, "status": status, "detail": detail})

    api_key = (config.get("elevenlabs_api_key") or "").strip()
    engine_raw = (config.get("tts_engine") or "").strip()
    report["engine_saved"] = engine_raw
    report["engine_effective"] = normalize_tts_engine(engine_raw)
    report["model"] = (config.get("elevenlabs_model") or "eleven_multilingual_v2").strip()
    report["output_format"] = (config.get("elevenlabs_output_format") or "mp3_44100_128").strip()
    report["voice_id_setting"] = (config.get("elevenlabs_voice_id") or "").strip()
    report["voice_id_effective"] = resolve_elevenlabs_voice_id(report["voice_id_setting"])
    report["stability"] = config.get("elevenlabs_stability")
    report["similarity"] = config.get("elevenlabs_similarity")

    if not api_key:
        step("API-ключ", "ПОМИЛКА", "Поле 'ElevenLabs API-ключ' порожнє — збережіть ключ у налаштуваннях.")
        return report
    step("API-ключ", "OK", "довжина {} символів, починається на '{}'".format(
        len(api_key), api_key[:4]))

    if engine_raw != "elevenlabs":
        step("Рушій TTS", "УВАГА", "У налаштуваннях обрано '{}', а не 'elevenlabs'.".format(engine_raw))
    else:
        step("Рушій TTS", "OK", "elevenlabs")

    # 1. підписка
    try:
        req = urllib.request.Request(
            "https://api.elevenlabs.io/v1/user/subscription",
            headers={"xi-api-key": api_key, "User-Agent": "MultiChat-OBS/1.0"})
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        step("Підписка", "OK", "тариф '{}', використано {} з {} символів".format(
            data.get("tier"), data.get("character_count"), data.get("character_limit")))
        report["characters_left"] = (data.get("character_limit") or 0) - (data.get("character_count") or 0)
    except urllib.error.HTTPError as e:
        try:
            body = e.read().decode("utf-8", errors="ignore")
        except Exception:
            body = ""
        step("Підписка", "ПОМИЛКА", "HTTP {} {} — {}".format(e.code, e.reason, body[:400]))
        return report
    except Exception as e:
        step("Підписка", "ПОМИЛКА", "{}: {}".format(type(e).__name__, e))
        return report

    # 2. список голосів акаунта
    try:
        req = urllib.request.Request(
            "https://api.elevenlabs.io/v1/voices",
            headers={"xi-api-key": api_key, "User-Agent": "MultiChat-OBS/1.0"})
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        available = [(v.get("voice_id"), v.get("name")) for v in (data.get("voices") or [])]
        report["account_voices"] = ["{} — {}".format(vid, name) for vid, name in available]
        ids = set(vid for vid, _ in available)
        missing = [v["id"] for v in ELEVENLABS_VOICES if v["id"] not in ids]
        if missing:
            step("Голоси акаунта", "УВАГА",
                 "у вашому акаунті НЕ знайдено ID: {}. Додайте ці голоси у свою бібліотеку на elevenlabs.io (Voice Library -> Add to my voices).".format(
                     ", ".join(missing)))
        else:
            step("Голоси акаунта", "OK", "всі {} голоси зі списку доступні".format(len(ELEVENLABS_VOICES)))
    except urllib.error.HTTPError as e:
        try:
            body = e.read().decode("utf-8", errors="ignore")
        except Exception:
            body = ""
        step("Голоси акаунта", "ПОМИЛКА", "HTTP {} {} — {}".format(e.code, e.reason, body[:400]))
    except Exception as e:
        step("Голоси акаунта", "ПОМИЛКА", "{}: {}".format(type(e).__name__, e))

    # 3. тестовий синтез
    try:
        audio, content_type = synthesize_elevenlabs_bytes("Тест озвучки", report["voice_id_effective"], 1.0)
        step("Тестовий синтез", "OK", "отримано {} байт, {} (голос {})".format(
            len(audio), content_type, report["voice_id_effective"]))
        report["ok"] = True
    except urllib.error.HTTPError as e:
        try:
            body = e.read().decode("utf-8", errors="ignore")
        except Exception:
            body = ""
        if e.code == 402 or "paid_plan_required" in body:
            step("Тестовий синтез", "ПОМИЛКА",
                 "HTTP 402 Payment Required. Ваш тариф ElevenLabs — Free. Безкоштовні акаунти не можуть "
                 "озвучувати голосами з Voice Library через API — це обмеження ElevenLabs, а не скрипта. "
                 "Рішення: платний план Starter ($5/міс), або власний клонований голос у вашому акаунті, "
                 "або лишити Google TTS. Повна відповідь: " + body[:400])
        else:
            step("Тестовий синтез", "ПОМИЛКА", "HTTP {} {} — {}".format(e.code, e.reason, body[:600]))
    except Exception as e:
        step("Тестовий синтез", "ПОМИЛКА", "{}: {}".format(type(e).__name__, e))
    return report


def elevenlabs_diagnose_html():
    def _esc(value):
        return (str(value).replace("&", "&amp;").replace("<", "&lt;")
                .replace(">", "&gt;").replace('"', "&quot;"))

    report = elevenlabs_diagnose()
    rows = ""
    for st in report["steps"]:
        color = {"OK": "#38d18b", "УВАГА": "#ffcc55", "ПОМИЛКА": "#ff6b81"}.get(st["status"], "#e6e9f0")
        rows += ('<tr><td>{}</td><td style="color:{};font-weight:600">{}</td>'
                 '<td>{}</td></tr>').format(
            _esc(st["name"]), color, _esc(st["status"]), _esc(st["detail"]))
    info = ""
    for label, key in (("Рушій у налаштуваннях", "engine_saved"), ("Рушій фактично", "engine_effective"),
                       ("Модель", "model"), ("Формат", "output_format"),
                       ("Голос (налаштування)", "voice_id_setting"), ("Голос (фактично)", "voice_id_effective"),
                       ("Стабільність %", "stability"), ("Схожість %", "similarity")):
        info += "<tr><td>{}</td><td colspan=2><code>{}</code></td></tr>".format(
            label, _esc(str(report.get(key, ""))))
    voices = report.get("account_voices") or []
    voices_html = ""
    if voices:
        voices_html = "<h3>Голоси у вашому акаунті ElevenLabs</h3><pre>{}</pre>".format(
            _esc("\n".join(voices)))
    verdict = ("✅ ElevenLabs працює — озвучка має йти через нього."
               if report["ok"] else
               "❌ ElevenLabs не працює. Скопіюйте цю сторінку і надішліть її.")
    return """<!DOCTYPE html><html lang="uk"><head><meta charset="utf-8">
<title>Перевірка ElevenLabs</title>
<style>body{font-family:Segoe UI,Arial,sans-serif;background:#15181f;color:#e6e9f0;padding:24px;line-height:1.5}
h2{margin-top:0}table{border-collapse:collapse;width:100%;margin-bottom:18px}
td{border:1px solid #2c313d;padding:8px 10px;vertical-align:top;font-size:14px}
pre{background:#1d212b;padding:12px;border-radius:8px;white-space:pre-wrap}
code{color:#8ad1ff}.verdict{font-size:17px;font-weight:700;margin:14px 0 20px}</style></head><body>
<h2>Перевірка ElevenLabs</h2>
<div class="verdict">""" + verdict + """</div>
<h3>Поточні налаштування</h3><table>""" + info + """</table>
<h3>Кроки перевірки</h3><table>""" + rows + """</table>""" + voices_html + """
</body></html>"""


def synthesize_tts_bytes(text, lang, engine, voice, speed):
    # Серверний синтез: ElevenLabs (якщо обрано і є ключ) або Google TTS
    # із автоматичним резервом на Windows SAPI усередині функції.
    engine = normalize_tts_engine(engine)
    cache_key = tts_cache_key(text, lang, engine, voice, speed)
    cached = tts_cache_get(cache_key)
    if cached is not None:
        # Той самий запит після обриву з'єднання: віддаємо ГОТОВІ байти.
        # Ні повторного синтезу, ні витрат ElevenLabs, ні зміни голосу.
        return cached
    audio_data, content_type = _synthesize_tts_bytes_uncached(text, lang, engine, voice, speed)
    tts_cache_put(cache_key, audio_data, content_type)
    tts_note('synthesized')
    return audio_data, content_type


def _synthesize_tts_bytes_uncached(text, lang, engine, voice, speed):
    if engine == "elevenlabs":
        try:
            return tts_call_with_retry(
                'ElevenLabs', lambda: synthesize_elevenlabs_bytes(text, voice, speed))
        except urllib.error.HTTPError as e:
            try:
                body = e.read().decode("utf-8", errors="ignore")
            except Exception:
                body = ""
            if e.code == 402 or "paid_plan_required" in body:
                print("[TTS] ❌ ElevenLabs: ваш тариф — Free, а безкоштовний акаунт НЕ МОЖЕ "
                      "використовувати голоси з Voice Library через API "
                      "(саме такі всі 9 голосів зі списку). Варіанти: 1) оформити платний план "
                      "Starter ($5/міс) — і всі голоси заробають одразу; 2) створити власний голос "
                      "(Instant Voice Clone) у своєму акаунті й вставити його ID; "
                      "3) залишити Google TTS. Зараз озвучую через Google.")
            else:
                print("[TTS] ElevenLabs відмовив: HTTP {} {} | voice='{}' model='{}' | тіло відповіді: {} — озвучую через Google.".format(
                    e.code, e.reason, resolve_elevenlabs_voice_id(voice),
                    (config.get("elevenlabs_model") or "eleven_multilingual_v2"), body[:300]))
        except Exception as e:
            print("[TTS] ElevenLabs не вдався ({}: {}) | voice='{}' — озвучую через Google.".format(
                type(e).__name__, e, voice))
    return synthesize_google_tts_bytes(text, lang, speed)



def pick_first_non_empty(*values):
    for value in values:
        if value is None:
            continue
        if isinstance(value, str):
            if value.strip():
                return value.strip()
        elif value:
            return value
    return ''


def extract_kick_event_name(headers, payload):
    return pick_first_non_empty(
        headers.get('Kick-Event-Type', ''),
        headers.get('X-Kick-Event-Type', ''),
        (payload.get('event') or '') if isinstance(payload, dict) else '',
        (payload.get('type') or '') if isinstance(payload, dict) else ''
    )


def extract_kick_event_payload(payload):
    if isinstance(payload, dict) and isinstance(payload.get('data'), dict):
        return payload.get('data') or {}
    return payload if isinstance(payload, dict) else {}


def handle_kick_webhook_event(event_name, payload):
    payload = extract_kick_event_payload(payload)
    event_name = (event_name or '').strip()
    user_obj = payload.get('user') or payload.get('follower') or payload.get('subscriber') or payload.get('gifter') or payload.get('sender') or {}
    recipient_obj = payload.get('recipient') or {}
    user = pick_first_non_empty(user_obj.get('username'), user_obj.get('slug'), user_obj.get('name'), payload.get('username'), payload.get('name'), 'Kick')
    username = pick_first_non_empty(user_obj.get('username'), user_obj.get('slug'), payload.get('username'), user)
    recipient = pick_first_non_empty(recipient_obj.get('username'), recipient_obj.get('slug'), recipient_obj.get('name'), payload.get('recipient_username'), '')
    gifted_count = pick_first_non_empty(payload.get('gifted_count'), payload.get('count'), payload.get('total'), '')

    if event_name in ('channel.followed', 'channel.follow', 'follow'):
        if not config.get('kk_enable_follows', True):
            return False
        text = '{} почав стежити за Kick-каналом'.format(user)
        print('[Kick Follow] {}'.format(user))
        emit_platform_alert('kick', 'follow', user, text, 'Новий фоловер Kick', 'follow', username=username, source_display_name=user, force_chat=False)
        publish_unified_event('kick', UnifiedEventType.FOLLOW.value, username=username, message=text, metadata={'payload': payload})
        return True
    if event_name in ('channel.subscription.new', 'channel.subscription.created', 'channel.subscription.renewal', 'channel.subscription', 'subscription', 'subscription.renewal'):
        if not config.get('kk_enable_subs', True):
            return False
        text = '{} оформив підписку на Kick'.format(user)
        print('[Kick Sub] {}'.format(user))
        emit_platform_alert('kick', 'sub', user, text, 'Підписка Kick', 'subscription', username=username, source_display_name=user, force_chat=False)
        publish_unified_event('kick', UnifiedEventType.SUBSCRIBE.value, username=username, message=text, metadata={'payload': payload})
        return True
    if event_name in ('channel.subscription.gifts', 'kicks.gifted', 'channel.subscription.gifted', 'subscription.gifted'):
        if not config.get('kk_enable_subs', True):
            return False
        text = '{} подарував підписку Kick {}'.format(user, recipient or (gifted_count if gifted_count else '')).strip()
        print('[Kick Gift] {}'.format(text))
        emit_platform_alert('kick', 'sub', user, text, 'Подарункова підписка Kick', 'gift', username=username, source_display_name=user, force_chat=False)
        publish_unified_event('kick', UnifiedEventType.GIFTED_SUBSCRIPTION.value, username=username, message=text, metadata={'recipient': recipient, 'gifted_count': gifted_count, 'payload': payload})
        return True
    return False


# ============================================================================
# ЗАГАЛЬНІ HTTP-ХЕЛПЕРИ (для Giveaway та Stream Notify)
# ============================================================================
# На відміну від оригінальних окремих скриптів (giveaway_obs.py на requests,
# stream_notify_v21.lua — через PowerShell/VBScript, бо в Lua немає HTTP),
# тут усе робиться через urllib.request, який уже й так використовується по
# всьому цьому файлу (YouTube API, TikTok web-режим, OAuth) — без нових
# обов'язкових залежностей.

def build_multipart_body(fields, file_field_name=None, file_name=None, file_bytes=None, mime_type="application/octet-stream"):
    boundary = "MultiChatBoundary" + secrets.token_hex(16)
    parts = []
    for key, value in (fields or {}).items():
        parts.append("--{}\r\n".format(boundary).encode("utf-8"))
        parts.append('Content-Disposition: form-data; name="{}"\r\n\r\n'.format(key).encode("utf-8"))
        parts.append("{}\r\n".format("" if value is None else value).encode("utf-8"))
    if file_field_name and file_bytes is not None:
        parts.append("--{}\r\n".format(boundary).encode("utf-8"))
        parts.append(
            'Content-Disposition: form-data; name="{}"; filename="{}"\r\nContent-Type: {}\r\n\r\n'.format(
                file_field_name, file_name or "file", mime_type
            ).encode("utf-8")
        )
        parts.append(file_bytes)
        parts.append(b"\r\n")
    parts.append("--{}--\r\n".format(boundary).encode("utf-8"))
    return "multipart/form-data; boundary={}".format(boundary), b"".join(parts)


def http_post_json(url, payload, timeout=15):
    try:
        data = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(url, data=data, headers={"Content-Type": "application/json"}, method="POST")
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            status = getattr(resp, "status", 200)
            raw = resp.read().decode("utf-8", errors="ignore")
            if not raw.strip():
                return {"ok": True, "status": status}
            try:
                parsed = json.loads(raw)
            except ValueError:
                return {"ok": True, "status": status, "raw": raw}
            if isinstance(parsed, dict):
                parsed.setdefault("ok", True)
                parsed["status"] = status
                return parsed
            return {"ok": True, "status": status, "data": parsed}
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="ignore")
        try:
            parsed = json.loads(body)
            if isinstance(parsed, dict):
                parsed["ok"] = False
                parsed["status"] = e.code
                parsed.setdefault("error", "HTTP {}: {}".format(e.code, body[:300]))
                return parsed
        except Exception:
            pass
        return {"ok": False, "status": e.code, "error": "HTTP {}: {}".format(e.code, body[:300])}
    except Exception as e:
        return {"ok": False, "error": str(e)}


def http_post_multipart(url, fields, file_field_name=None, file_path=None, file_name_override=None, timeout=25):
    try:
        file_bytes = None
        file_name = None
        mime_type = "application/octet-stream"
        if file_field_name and file_path:
            with open(file_path, "rb") as f:
                file_bytes = f.read()
            file_name = file_name_override or os.path.basename(file_path)
            mime_type = mimetypes.guess_type(file_path)[0] or "application/octet-stream"
        content_type, body = build_multipart_body(fields, file_field_name, file_name, file_bytes, mime_type)
        req = urllib.request.Request(url, data=body, headers={"Content-Type": content_type}, method="POST")
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            status = getattr(resp, "status", 200)
            raw = resp.read().decode("utf-8", errors="ignore")
            if not raw.strip():
                return {"ok": True, "status": status}
            try:
                parsed = json.loads(raw)
            except ValueError:
                return {"ok": True, "status": status, "raw": raw}
            if isinstance(parsed, dict):
                parsed.setdefault("ok", True)
                parsed["status"] = status
                return parsed
            return {"ok": True, "status": status, "data": parsed}
    except urllib.error.HTTPError as e:
        body_err = e.read().decode("utf-8", errors="ignore")
        try:
            parsed = json.loads(body_err)
            if isinstance(parsed, dict):
                parsed["ok"] = False
                parsed["status"] = e.code
                parsed.setdefault("error", "HTTP {}: {}".format(e.code, body_err[:300]))
                return parsed
        except Exception:
            pass
        return {"ok": False, "status": e.code, "error": "HTTP {}: {}".format(e.code, body_err[:300])}
    except Exception as e:
        return {"ok": False, "error": str(e)}


def http_get_text(url, timeout=15, headers=None):
    try:
        req = urllib.request.Request(url, headers=headers or {"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read().decode("utf-8", errors="ignore")
    except Exception:
        return None


def http_get_json(url, timeout=15, headers=None):
    text = http_get_text(url, timeout=timeout, headers=headers)
    if text is None:
        return None
    try:
        return json.loads(text)
    except ValueError:
        return None


# ============================================================================
# GIVEAWAY (Telegram) — перенесено з giveaway_obs.py, з тими самими правилами
# ============================================================================
# Що змінилось порівняно з окремим скриптом:
#   - overlay більше не пишеться у файл giveaway_data.json в довільну папку —
#     віддається тим самим локальним сервером (як усі інші оверлеї в цьому
#     файлі): /giveaway/overlay (HTML) і /giveaway/data (JSON).
#   - HTTP — через urllib замість requests (немає нової обов'язкової залежності).
#   - Старт/стоп — кнопки в веб-панелі налаштувань + ті самі хоткеї OBS.

giveaway_state = {
    "active": False,
    "end_time": 0,
    "participants": {},
    "winner": None,
    "msg_id": None,
}
giveaway_overlay_state = {"active": False, "prize": "", "seconds_left": 0, "participants": 0, "winner": None}
giveaway_poll_offset = 0
giveaway_timer_active = False

GIVEAWAY_OVERLAY_HTML = """<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<style>
  * { margin: 0; padding: 0; box-sizing: border-box; }

  body {
    background: transparent;
    overflow: hidden;
    font-family: 'Segoe UI', sans-serif;
  }

  #card {
    display: none;
    position: fixed;
    top: 40px;
    right: 40px;
    background: rgba(0, 0, 0, 0.88);
    border: 2px solid #a855f7;
    border-radius: 18px;
    padding: 20px 28px;
    min-width: 320px;
    max-width: 400px;
    flex-direction: column;
    gap: 12px;
    box-shadow: 0 0 30px rgba(168, 85, 247, 0.35);
    animation: fadeIn 0.5s ease;
  }

  #card.show { display: flex; }

  #card.hide {
    animation: fadeOut 0.5s ease forwards;
  }

  /* ---- шапка ---- */
  .header {
    display: flex;
    align-items: center;
    gap: 10px;
  }

  .icon {
    font-size: 28px;
    line-height: 1;
  }

  .label {
    font-size: 13px;
    font-weight: 700;
    letter-spacing: 2px;
    text-transform: uppercase;
    color: #a855f7;
  }

  /* ---- назва призу ---- */
  #prize {
    font-size: 20px;
    font-weight: 700;
    color: #ffffff;
    line-height: 1.2;
    border-left: 3px solid #a855f7;
    padding-left: 10px;
  }

  /* ---- таймер ---- */
  #timer {
    font-size: 46px;
    font-weight: 800;
    color: #ffffff;
    letter-spacing: 2px;
    text-align: center;
    font-variant-numeric: tabular-nums;
    text-shadow: 0 0 20px rgba(168, 85, 247, 0.6);
  }

  #timer.ending {
    color: #f87171;
    text-shadow: 0 0 20px rgba(248, 113, 113, 0.6);
    animation: pulse 1s infinite;
  }

  /* ---- учасники ---- */
  .participants-row {
    display: flex;
    align-items: center;
    justify-content: space-between;
    background: rgba(168, 85, 247, 0.1);
    border-radius: 10px;
    padding: 8px 14px;
  }

  .participants-label {
    font-size: 13px;
    color: #a1a1aa;
    font-weight: 500;
  }

  #participants {
    font-size: 22px;
    font-weight: 800;
    color: #a855f7;
  }

  /* ---- переможець ---- */
  #winner-block {
    display: none;
    flex-direction: column;
    align-items: center;
    gap: 8px;
    padding: 10px 0;
  }

  #winner-block.show { display: flex; }

  .winner-label {
    font-size: 13px;
    font-weight: 700;
    letter-spacing: 2px;
    text-transform: uppercase;
    color: #fbbf24;
  }

  #winner-name {
    font-size: 28px;
    font-weight: 800;
    color: #ffffff;
    text-align: center;
    animation: pop 0.4s cubic-bezier(0.175, 0.885, 0.32, 1.275);
  }

  /* ---- розділювач ---- */
  .divider {
    height: 1px;
    background: rgba(168, 85, 247, 0.25);
    border-radius: 1px;
  }

  /* ---- брендинг ---- */
  .brand {
    font-size: 11px;
    color: #52525b;
    text-align: right;
    font-weight: 600;
    letter-spacing: 1px;
    text-transform: uppercase;
  }

  /* ---- анімації ---- */
  @keyframes fadeIn {
    from { opacity: 0; transform: translateY(-20px) scale(0.95); }
    to   { opacity: 1; transform: translateY(0) scale(1); }
  }

  @keyframes fadeOut {
    from { opacity: 1; transform: translateY(0) scale(1); }
    to   { opacity: 0; transform: translateY(-20px) scale(0.95); }
  }

  @keyframes pulse {
    0%, 100% { opacity: 1; }
    50%       { opacity: 0.5; }
  }

  @keyframes pop {
    0%   { transform: scale(0.5); opacity: 0; }
    70%  { transform: scale(1.1); }
    100% { transform: scale(1);   opacity: 1; }
  }
</style>
</head>
<body>

<div id="card">

  <div class="header">
    <div class="label">Розіграш</div>
  </div>

  <div id="prize">...</div>

  <div class="divider"></div>

  <div id="timer">00:00</div>

  <div class="participants-row">
    <span class="participants-label">Учасників</span>
    <span id="participants">0</span>
  </div>

  <div id="winner-block">
    <div class="divider"></div>
    <div class="winner-label">Переможець</div>
    <div id="winner-name"></div>
  </div>

  <div class="brand">Critical Hit</div>

</div>

<script>
  const card         = document.getElementById('card');
  const timerEl      = document.getElementById('timer');
  const prizeEl      = document.getElementById('prize');
  const participantsEl = document.getElementById('participants');
  const winnerBlock  = document.getElementById('winner-block');
  const winnerName   = document.getElementById('winner-name');

  let visible = false;

  function show() {
    if (!visible) {
      card.classList.remove('hide');
      card.classList.add('show');
      visible = true;
    }
  }

  function hide() {
    if (visible) {
      card.classList.add('hide');
      setTimeout(() => {
        card.classList.remove('show', 'hide');
        visible = false;
      }, 500);
    }
  }

  async function tick() {
    try {
      const r = await fetch('/giveaway/data?t=' + Date.now());
      if (!r.ok) { hide(); return; }
      const d = await r.json();

      if (!d.active && !d.winner) { hide(); return; }

      show();

      prizeEl.textContent = d.prize || '';
      participantsEl.textContent = d.participants ?? 0;

      if (d.winner) {
        // Показуємо переможця
        timerEl.style.display = 'none';
        winnerBlock.classList.add('show');
        winnerName.textContent = '@' + d.winner;
        timerEl.classList.remove('ending');
      } else {
        timerEl.style.display = '';
        winnerBlock.classList.remove('show');
        winnerName.textContent = '';

        const left = Math.max(0, d.seconds_left ?? 0);
        const m = String(Math.floor(left / 60)).padStart(2, '0');
        const s = String(left % 60).padStart(2, '0');
        timerEl.textContent = m + ':' + s;

        if (left <= 60) {
          timerEl.classList.add('ending');
        } else {
          timerEl.classList.remove('ending');
        }
      }
    } catch(e) {
      // файл не знайдено — ховаємо
      hide();
    }
  }

  setInterval(tick, 1000);
  tick();
</script>

</body>
</html>
"""


def giveaway_write_state(active=False, prize="", seconds_left=0, participants=0, winner=None):
    giveaway_overlay_state["active"] = active
    giveaway_overlay_state["prize"] = prize
    giveaway_overlay_state["seconds_left"] = seconds_left
    giveaway_overlay_state["participants"] = participants
    giveaway_overlay_state["winner"] = winner


def giveaway_clear_overlay():
    giveaway_write_state(active=False)


def giveaway_tg_api(method, data=None, files_path=None, files_field=None):
    token = (config.get("gw_tg_token") or "").strip()
    if not token:
        return {}
    url = "https://api.telegram.org/bot{}/{}".format(token, method)
    if files_path:
        return http_post_multipart(url, data or {}, file_field_name=files_field, file_path=files_path)
    return http_post_json(url, data or {})


def giveaway_send_post():
    title = config.get("gw_prize_title", "")
    text = config.get("gw_announce_text") or "Підписники каналу можуть взяти участь у розіграші!"
    img = (config.get("gw_img_path") or "").strip()
    dur_min = config.get("gw_duration_min", 15)

    caption = "\U0001F381 РОЗІГРАШ!\n\n\U0001F3C6 Приз: {}\n\n{}\n\n\u23F1 Тривалість: {} хв\n\n\U0001F447 Натисни кнопку щоб взяти участь!".format(title, text, dur_min)
    keyboard = {"inline_keyboard": [[{"text": "\U0001F3AF Взяти участь", "callback_data": "join_giveaway"}]]}

    if img and os.path.isfile(img):
        result = giveaway_tg_api("sendPhoto", data={
            "chat_id": config.get("gw_tg_chat_id", ""),
            "caption": caption,
            "reply_markup": json.dumps(keyboard),
        }, files_path=img, files_field="photo")
    else:
        result = giveaway_tg_api("sendMessage", {
            "chat_id": config.get("gw_tg_chat_id", ""),
            "text": caption,
            "reply_markup": keyboard,
        })

    if result.get("ok"):
        msg_id = result["result"]["message_id"]
        log_status("Giveaway", "Пост розіграшу відправлено, message_id={}".format(msg_id))
        return msg_id
    log_status("Giveaway", "Помилка відправки посту: {}".format(result))
    return None


def giveaway_send_winner_post(winner_name):
    title = config.get("gw_prize_title", "")
    giveaway_tg_api("sendMessage", {
        "chat_id": config.get("gw_tg_chat_id", ""),
        "text": "\U0001F3C6 РОЗІГРАШ ЗАВЕРШЕНО!\n\n\U0001F381 Приз: {}\n\n\U0001F389 Переможець: @{}\n\nВітаємо! Напиши адміну для отримання призу.".format(title, winner_name),
    })
    log_status("Giveaway", "Пост переможця відправлено: @{}".format(winner_name))


def giveaway_close_button(msg_id, winner_name):
    title = config.get("gw_prize_title", "")
    giveaway_tg_api("editMessageCaption", {
        "chat_id": config.get("gw_tg_chat_id", ""),
        "message_id": msg_id,
        "caption": "\U0001F381 РОЗІГРАШ ЗАВЕРШЕНО!\n\n\U0001F3C6 Приз: {}\n\n\U0001F389 Переможець: @{}".format(title, winner_name),
    })


def giveaway_answer_callback(callback_id, text, alert=False):
    giveaway_tg_api("answerCallbackQuery", {
        "callback_query_id": callback_id,
        "text": text,
        "show_alert": alert,
    })


def giveaway_poll():
    global giveaway_poll_offset
    if not giveaway_state["active"]:
        return
    result = giveaway_tg_api("getUpdates", {
        "offset": giveaway_poll_offset,
        "timeout": 1,
        "allowed_updates": ["callback_query"],
    })
    if not result.get("ok"):
        return
    for update in result.get("result", []):
        giveaway_poll_offset = update["update_id"] + 1
        cb = update.get("callback_query")
        if not cb or cb.get("data") != "join_giveaway":
            continue
        if not giveaway_state["active"]:
            giveaway_answer_callback(cb["id"], "Розіграш не активний", alert=True)
            continue
        user = cb["from"]
        user_id = str(user["id"])
        uname = user.get("username") or user.get("first_name", "Unknown")
        if user_id in giveaway_state["participants"]:
            giveaway_answer_callback(cb["id"], "Ти вже берешь участь! \u2705")
        else:
            giveaway_state["participants"][user_id] = uname
            count = len(giveaway_state["participants"])
            giveaway_answer_callback(cb["id"], "\u2705 Ти в розіграші! Учасників: {}".format(count))
            log_status("Giveaway", "JOIN: @{} | Всього: {}".format(uname, count))


def giveaway_tick():
    try:
        _giveaway_tick_body()
    except Exception as e:
        try:
            log_error("Giveaway", "Помилка таймера розіграшу: {}".format(e))
        except Exception:
            pass


def _giveaway_tick_body():
    if not giveaway_state["active"]:
        return
    threading.Thread(target=giveaway_poll, daemon=True).start()
    left = int(giveaway_state["end_time"] - time.time())
    if left > 0:
        giveaway_write_state(active=True, prize=config.get("gw_prize_title", ""), seconds_left=left, participants=len(giveaway_state["participants"]))
    else:
        giveaway_state["active"] = False
        threading.Thread(target=giveaway_finish, daemon=True).start()


def giveaway_finish():
    global giveaway_timer_active
    giveaway_timer_active = False
    if not giveaway_state["participants"]:
        log_status("Giveaway", "Ніхто не взяв участь!")
        giveaway_write_state(active=False, prize=config.get("gw_prize_title", ""), seconds_left=0, participants=0)
        giveaway_tg_api("sendMessage", {
            "chat_id": config.get("gw_tg_chat_id", ""),
            "text": "\U0001F614 Розіграш '{}' завершено — ніхто не взяв участь.".format(config.get("gw_prize_title", "")),
        })
        time.sleep(8)
        giveaway_clear_overlay()
        return

    winner_id = random.choice(list(giveaway_state["participants"].keys()))
    winner_name = giveaway_state["participants"][winner_id]
    giveaway_state["winner"] = winner_name
    log_status("Giveaway", "WINNER: @{}".format(winner_name))

    giveaway_write_state(active=False, prize=config.get("gw_prize_title", ""), participants=len(giveaway_state["participants"]), winner=winner_name)

    if giveaway_state["msg_id"]:
        giveaway_close_button(giveaway_state["msg_id"], winner_name)
    giveaway_send_winner_post(winner_name)

    time.sleep(30)
    giveaway_clear_overlay()
    log_status("Giveaway", "Розіграш завершено")


def giveaway_start():
    global giveaway_timer_active
    if giveaway_state["active"]:
        return {"ok": False, "error": "Розіграш вже активний"}
    if not (config.get("gw_tg_token") or "").strip() or not (config.get("gw_tg_chat_id") or "").strip():
        return {"ok": False, "error": "Заповни Telegram Bot Token і Chat ID у розділі Giveaway"}
    if not (config.get("gw_prize_title") or "").strip():
        return {"ok": False, "error": "Заповни назву призу"}

    dur_sec = int(config.get("gw_duration_min", 15) or 15) * 60
    giveaway_state["active"] = True
    giveaway_state["end_time"] = time.time() + dur_sec
    giveaway_state["participants"] = {}
    giveaway_state["winner"] = None

    def send_and_start():
        msg_id = giveaway_send_post()
        giveaway_state["msg_id"] = msg_id
        log_status("Giveaway", "Розіграш запущено на {} хв".format(config.get("gw_duration_min", 15)))

    threading.Thread(target=send_and_start, daemon=True).start()
    # Таймер уже висить постійно (реєструється в script_load з головного
    # потоку OBS) — тут нічого чіпати не можна, інакше OBS падає.
    giveaway_timer_active = True
    return {"ok": True}


def giveaway_stop():
    global giveaway_timer_active
    if not giveaway_state["active"]:
        return {"ok": False, "error": "Розіграш не активний"}
    giveaway_state["active"] = False
    giveaway_state["end_time"] = time.time()
    giveaway_timer_active = False
    giveaway_clear_overlay()
    log_status("Giveaway", "Розіграш зупинено")
    return {"ok": True}


# ============================================================================
# STREAM NOTIFY — перенесено з stream_notify_v21.lua
# ============================================================================
# Головні відмінності від оригінального Lua-скрипта:
#   - Мережеві виклики йдуть через urllib (build_multipart_body/http_post_*),
#     замість генерації PowerShell + VBScript-обгортки — у Lua це був
#     обхідний шлях через відсутність HTTP у стандартній бібліотеці, у
#     Python цього обходу не потрібно.
#   - Запланований пост зберігається в тому самому config (settings.json),
#     а не в окремому текстовому файлі в AppData — один механізм
#     збереження на весь скрипт замість двох різних.
#   - Twitch VOD JSON розбирається через json.loads (справжній парсер)
#     замість регулярних виразів по сирому тексту відповіді.
#   - editMessageMedia тепер явно посилається на прикріплений файл
#     ("media": "attach://media") — в оригіналі це поле бракувало, через
#     що Telegram міг не підхопити нове фото при редагуванні поста.
#   - Порівняння "чи VOD достатньо свіжий" тепер коректно у UTC
#     (time.time() в Python завжди UTC, на відміну від os.time() у Lua з
#     таблицею дати, яка інтерпretувалась як локальний час) — тобто
#     точніше збігається з реальним часом публікації відео.

SN_PLATFORM_DEFS = [
    ("tiktok", "TikTok"),
    ("twitch", "Twitch"),
    ("youtube", "YouTube"),
    ("kick", "Kick"),
    ("discord", "Discord"),
    ("telegram", "Telegram"),
    ("steamtv", "Steam.TV"),
    ("fb_gaming", "FB Gaming"),
    ("facebook", "Facebook"),
    ("instagram", "Instagram"),
    ("donat", "Донат"),
]

# Telegram Bot API 9.4 (з 09.02.2026) дозволяє лише 3 готових кольори кнопок:
# danger (червоний), primary (синій), success (зелений) - довільний HEX
# недоступний. Наближено підбираємо під фірмові кольори платформ.
SN_PLATFORM_STYLES = {
    "youtube": "danger",
    "kick": "success",
    "donat": "primary",
}

sn_state = {
    "already_sent": False,
    "tg_message_id": None,
    "stream_start_time": None,
}


def sn_btn_style_for(slug):
    style = (config.get("sn_btn_style_" + slug) or "").strip()
    if style in ("primary", "success", "danger"):
        return style
    return SN_PLATFORM_STYLES.get(slug)


def sn_active_platforms():
    result = []
    for slug, label in SN_PLATFORM_DEFS:
        url = (config.get("sn_url_" + slug) or "").strip()
        if url:
            item = {"label": label, "url": url}
            style = sn_btn_style_for(slug)
            if style:
                item["style"] = style
            result.append(item)
    return result


def sn_active_platforms_after():
    result = []
    for slug, label in SN_PLATFORM_DEFS:
        url = (config.get("sn_url_" + slug) or "").strip()
        flag = config.get("sn_after_url_" + slug, False)
        if flag and url:
            item = {"label": label, "url": url}
            style = sn_btn_style_for(slug)
            if style:
                item["style"] = style
            result.append(item)
    return result


def sn_build_tg_keyboard(platforms):
    if not platforms:
        return None
    rows = []
    i = 0
    while i < len(platforms):
        btn = {"text": platforms[i]["label"], "url": platforms[i]["url"]}
        if platforms[i].get("style"):
            btn["style"] = platforms[i]["style"]
        row = [btn]
        if i + 1 < len(platforms):
            btn2 = {"text": platforms[i + 1]["label"], "url": platforms[i + 1]["url"]}
            if platforms[i + 1].get("style"):
                btn2["style"] = platforms[i + 1]["style"]
            row.append(btn2)
            i += 2
        else:
            i += 1
        rows.append(row)
    return {"inline_keyboard": rows}


def sn_build_dc_fields(platforms):
    return [{"name": p["label"], "value": "[Link]({})".format(p["url"]), "inline": True} for p in platforms]

# ----------------------------------------------------------------------
# Telegram / Discord — відправка та редагування
# ----------------------------------------------------------------------

def sn_tg_send_photo(img_path, caption_text, keyboard, save_msg_id):
    token = (config.get("sn_tg_token") or "").strip()
    if not token:
        log_status("StreamNotify", "Telegram token не вказано")
        return
    if not img_path or not os.path.isfile(img_path):
        log_status("StreamNotify", "Telegram: файл прев'ю не знайдено: {}".format(img_path))
        return
    url = "https://api.telegram.org/bot{}/sendPhoto".format(token)
    fields = {"chat_id": config.get("sn_tg_chat_id", ""), "caption": caption_text}
    if keyboard:
        fields["reply_markup"] = json.dumps(keyboard)
    result = http_post_multipart(url, fields, file_field_name="photo", file_path=img_path)
    if save_msg_id:
        if result.get("ok"):
            mid = result["result"]["message_id"]
            sn_state["tg_message_id"] = mid
            log_status("StreamNotify", "Telegram done, message_id={}".format(mid))
        else:
            sn_state["tg_message_id"] = None
            log_status("StreamNotify", "ПОМИЛКА Telegram: {}".format(result))
    else:
        log_status("StreamNotify", "Telegram post done" if result.get("ok") else "ПОМИЛКА Telegram: {}".format(result))


def sn_tg_edit_markup_only(keyboard):
    if not sn_state["tg_message_id"]:
        return
    token = (config.get("sn_tg_token") or "").strip()
    if not token:
        return
    url = "https://api.telegram.org/bot{}/editMessageReplyMarkup".format(token)
    markup = keyboard if keyboard else {"inline_keyboard": []}
    http_post_json(url, {
        "chat_id": config.get("sn_tg_chat_id", ""),
        "message_id": sn_state["tg_message_id"],
        "reply_markup": markup,
    })


def sn_edit_telegram_post_after_stream(extra_keyboard_override=None):
    if not sn_state["tg_message_id"]:
        log_status("StreamNotify", "TG edit after: message_id невідомий, пропускаємо")
        return
    platforms = sn_active_platforms_after()
    keyboard = extra_keyboard_override if extra_keyboard_override else sn_build_tg_keyboard(platforms)

    img = (config.get("sn_after_image_path") or "").strip()
    caption = (config.get("sn_after_text") or "").strip()
    can_edit_media = bool(img and os.path.isfile(img) and caption)

    if img and not os.path.isfile(img):
        log_status("StreamNotify", "TG edit after: файл картинки не знайдено: {} - оновлюю лише кнопки".format(img))
    elif not img:
        log_status("StreamNotify", "TG edit after: картинка не вказана - оновлюю лише кнопки")
    elif not caption:
        log_status("StreamNotify", "TG edit after: текст не вказано - оновлюю лише кнопки")

    if can_edit_media:
        log_status("StreamNotify", "Редагую Telegram пост після стриму (message_id={})...".format(sn_state["tg_message_id"]))
        token = (config.get("sn_tg_token") or "").strip()
        url = "https://api.telegram.org/bot{}/editMessageMedia".format(token)
        media = {"type": "photo", "caption": caption, "media": "attach://media"}
        fields = {
            "chat_id": config.get("sn_tg_chat_id", ""),
            "message_id": str(sn_state["tg_message_id"]),
            "media": json.dumps(media),
        }
        http_post_multipart(url, fields, file_field_name="media", file_path=img)

    # Кнопки оновлюємо ЗАВЖДИ (незалежно від картинки/тексту) - це окремий
    # виклик Telegram API (editMessageReplyMarkup), який не залежить від
    # медіа чи підпису. Раніше функція виходила раніше і не чіпала навіть
    # кнопки, якщо текст/картинка не вказані - хоча toggle'и "Після стриму:
    # показувати X" явно вказують, що користувач очікує зміни хоча б кнопок.
    sn_tg_edit_markup_only(keyboard)
    log_status("StreamNotify", "Telegram пост після стриму оновлено{}".format(" (медіа + кнопки)" if can_edit_media else " (лише кнопки)"))


def sn_delete_telegram():
    if not sn_state["tg_message_id"]:
        log_status("StreamNotify", "TG delete: message_id невідомий")
        return
    token = (config.get("sn_tg_token") or "").strip()
    log_status("StreamNotify", "Видаляю пост Telegram (message_id={})...".format(sn_state["tg_message_id"]))
    url = "https://api.telegram.org/bot{}/deleteMessage".format(token)
    http_post_json(url, {"chat_id": config.get("sn_tg_chat_id", ""), "message_id": sn_state["tg_message_id"]})
    sn_state["tg_message_id"] = None
    log_status("StreamNotify", "Telegram delete done")


def sn_dc_send_post(img_path, title_text, desc_text, fields, mention):
    webhook = (config.get("sn_dc_webhook") or "").strip()
    if not webhook:
        log_status("StreamNotify", "Discord webhook не вказано")
        return
    if "discord.com/api/webhooks/" not in webhook and "discordapp.com/api/webhooks/" not in webhook:
        log_status("StreamNotify", "!!! Discord webhook URL виглядає некоректно (не схожий на посилання discord.com/api/webhooks/...). Перевірте налаштування.")
    has_image = bool(img_path and os.path.isfile(img_path))
    embed = {
        "title": title_text,
        "description": desc_text,
        "color": 16711680,
        "fields": fields,
    }
    if has_image:
        # "attachment://..." only resolves when a matching file is actually
        # attached in this same request - referencing it without an attachment
        # makes Discord reject the ENTIRE message with 400 Invalid Form Body
        # (error 50035), which silently killed every Discord post whenever
        # no valid preview image was set (this was the regression).
        embed["image"] = {"url": "attachment://preview.jpg"}
    payload = {
        "username": config.get("sn_streamer_name", ""),
        "content": mention,
        "embeds": [embed],
    }
    if has_image:
        result = http_post_multipart(webhook, {"payload_json": json.dumps(payload)}, file_field_name="files[0]", file_path=img_path, file_name_override="preview.jpg")
    else:
        result = http_post_json(webhook, payload)
    if isinstance(result, dict) and result.get("ok") is False:
        status = result.get("status", "?")
        err = result.get("error", "невідома помилка")
        if status == 404:
            log_status("StreamNotify", "!!! Discord webhook HTTP 404 — вебхук видалено або URL неправильний. Створіть новий вебхук у налаштуваннях каналу Discord і вставте його в поле 'Discord Webhook URL'.")
        elif status == 401:
            log_status("StreamNotify", "!!! Discord webhook HTTP 401 — токен вебхука недійсний.")
        else:
            log_status("StreamNotify", "!!! Discord post ПОМИЛКА: HTTP {} — {}".format(status, err))
        return
    log_status("StreamNotify", "Discord post done (status={})".format(result.get("status", "?") if isinstance(result, dict) else "?"))


def sn_send_telegram(game, title):
    custom = (config.get("sn_custom_text") or "").strip()
    if custom:
        caption_text = custom
    else:
        caption_text = "СТРІМ ПОЧАВСЯ!\n\nГра: {}\nНазва: {}\n\nДивитись на платформах:".format(game, title)
    platforms = sn_active_platforms()
    keyboard = sn_build_tg_keyboard(platforms)
    log_status("StreamNotify", "Надсилаю Telegram...")
    sn_tg_send_photo(config.get("sn_preview_path", ""), caption_text, keyboard, True)


def sn_send_discord(game, title):
    mention_mode = config.get("sn_dc_mention", "none")
    mention = "@everyone " if mention_mode == "everyone" else ("@here " if mention_mode == "here" else "")
    custom = (config.get("sn_custom_text") or "").strip()
    if custom:
        desc_text = custom
    else:
        desc_text = "**Gra:** {}\n**Nazva:** {}\n\nPidklyuchaytes!".format(game, title)
    platforms = sn_active_platforms()
    fields = sn_build_dc_fields(platforms)
    log_status("StreamNotify", "Надсилаю Discord...")
    sn_dc_send_post(config.get("sn_preview_path", ""), title, desc_text, fields, mention)


def sn_do_send(game, title):
    sn_send_telegram(game, title)
    sn_send_discord(game, title)
    log_status("StreamNotify", "ALL SENT")


# ----------------------------------------------------------------------
# Події старту/зупинки стриму
# ----------------------------------------------------------------------

def sn_on_stream_start():
    if sn_state["already_sent"]:
        return
    sn_state["already_sent"] = True
    sn_state["stream_start_time"] = time.time()
    game = (config.get("sn_stream_game") or "").strip() or "\u2014"
    title = (config.get("sn_stream_title") or "").strip() or "\u2014"
    log_status("StreamNotify", "START game=[{}] title=[{}]".format(game, title))
    delay = int(config.get("sn_send_delay", 0) or 0)
    if delay > 0:
        log_status("StreamNotify", "Затримка {} сек...".format(delay))

        def sn_delayed_send():
            obs.timer_remove(sn_delayed_send)
            sn_do_send(game, title)

        obs.timer_add(sn_delayed_send, delay * 1000)
    else:
        sn_do_send(game, title)


def sn_on_stream_stop():
    sn_state["already_sent"] = False
    log_status("StreamNotify", "STOPPED")
    if config.get("sn_tg_edit_on_stop"):
        sn_edit_telegram_post_after_stream()
    elif config.get("sn_tg_delete_on_stop"):
        sn_delete_telegram()


# ----------------------------------------------------------------------
# Запланований пост (стан живе прямо в config, окремий файл не потрібен)
# ----------------------------------------------------------------------

def sn_get_schedule_timestamp():
    date_str = (config.get("sn_schedule_date") or "").strip()
    time_str = (config.get("sn_schedule_time") or "").strip()
    m1 = re.match(r"^(\d{4})-(\d{2})-(\d{2})$", date_str)
    m2 = re.match(r"^(\d{2}):(\d{2})$", time_str)
    if not m1 or not m2:
        return None
    y, mo, d = (int(x) for x in m1.groups())
    hh, mm = (int(x) for x in m2.groups())
    if not (0 <= hh <= 23 and 0 <= mm <= 59):
        return None
    try:
        return time.mktime((y, mo, d, hh, mm, 0, 0, 0, -1))
    except Exception:
        return None


def sn_publish_scheduled_post_now(image_path=None):
    img = (image_path or "").strip() if image_path else ""
    if not img:
        img = (config.get("sn_post_image_path") or "").strip() or (config.get("sn_preview_path") or "").strip()
    if not img:
        log_status("StreamNotify", "ПОМИЛКА: для запланованого посту не знайдено картинку")
        return False
    if not os.path.isfile(img):
        log_status("StreamNotify", "ПОМИЛКА: файл картинки не знайдено: {}".format(img))
        return False
    custom_text = (config.get("sn_custom_text") or "").strip()
    if not custom_text:
        log_status("StreamNotify", "ПОМИЛКА: потрібно заповнити 'Текст посту'")
        return False
    platforms = sn_active_platforms()
    keyboard = sn_build_tg_keyboard(platforms)
    fields = sn_build_dc_fields(platforms)
    mention_mode = config.get("sn_dc_mention", "none")
    mention = "@everyone " if mention_mode == "everyone" else ("@here " if mention_mode == "here" else "")
    log_status("StreamNotify", "Час запланованого посту настав. Публікую...")
    sn_tg_send_photo(img, custom_text, keyboard, False)
    title = (config.get("sn_stream_title") or "").strip() or "Новий пост"
    sn_dc_send_post(img, title, custom_text, fields, mention)
    log_status("StreamNotify", "Запланований пост опубліковано")
    return True


def sn_schedule_tick():
    if not (config.get("sn_schedule_date") or "").strip() or not (config.get("sn_schedule_time") or "").strip():
        return
    ts = sn_get_schedule_timestamp()
    if ts is None:
        return
    if time.time() >= ts:
        ok = sn_publish_scheduled_post_now()
        config["sn_schedule_date"] = ""
        config["sn_schedule_time"] = ""
        persist_runtime_configuration()
        if ok:
            log_status("StreamNotify", "Запланований пост завершено і знято з черги")


# ----------------------------------------------------------------------
# Дії для веб-панелі (кнопки "Тест", "Опублікувати", "Запланувати"...)
# ----------------------------------------------------------------------

def sn_action_test_send():
    sn_state["stream_start_time"] = time.time()
    game = (config.get("sn_stream_game") or "").strip() or "Тестова гра"
    title = (config.get("sn_stream_title") or "").strip() or "Тестовий стрім"
    sn_send_telegram(game, title)
    sn_send_discord(game, title)
    return {"ok": True}


def sn_action_test_after():
    if not sn_state["tg_message_id"]:
        return {"ok": False, "error": "Немає активного message_id. Спочатку надішли тестове повідомлення"}
    sn_edit_telegram_post_after_stream()
    return {"ok": True}


def sn_action_publish():
    img = (config.get("sn_post_image_path") or "").strip() or (config.get("sn_preview_path") or "").strip()
    if not img:
        return {"ok": False, "error": "Не вказано картинку (post_image_path або preview_path)"}
    if not os.path.isfile(img):
        return {"ok": False, "error": "Файл не знайдено: {}".format(img)}
    custom_text = (config.get("sn_custom_text") or "").strip()
    if not custom_text:
        return {"ok": False, "error": "Не вказано текст посту"}
    platforms = sn_active_platforms()
    keyboard = sn_build_tg_keyboard(platforms)
    fields = sn_build_dc_fields(platforms)
    mention_mode = config.get("sn_dc_mention", "none")
    mention = "@everyone " if mention_mode == "everyone" else ("@here " if mention_mode == "here" else "")
    title = (config.get("sn_stream_title") or "").strip() or "Новий пост"
    sn_tg_send_photo(img, custom_text, keyboard, False)
    sn_dc_send_post(img, title, custom_text, fields, mention)
    return {"ok": True}


def sn_action_schedule():
    img = (config.get("sn_post_image_path") or "").strip() or (config.get("sn_preview_path") or "").strip()
    custom_text = (config.get("sn_custom_text") or "").strip()
    if not custom_text:
        return {"ok": False, "error": "Потрібно заповнити 'Текст посту'"}
    if not img:
        return {"ok": False, "error": "Потрібно вибрати картинку"}
    if not os.path.isfile(img):
        return {"ok": False, "error": "Файл не знайдено: {}".format(img)}
    if not (config.get("sn_tg_token") or "").strip() and not (config.get("sn_dc_webhook") or "").strip():
        return {"ok": False, "error": "Потрібен Telegram Token або Discord Webhook"}
    ts = sn_get_schedule_timestamp()
    if ts is None:
        return {"ok": False, "error": "Невірний формат дати (РРРР-ММ-ДД) або часу (ГГ:ХХ)"}
    if ts <= time.time():
        return {"ok": False, "error": "Вказаний час уже минув"}
    return {"ok": True}


def sn_action_delete_schedule():
    config["sn_schedule_date"] = ""
    config["sn_schedule_time"] = ""
    persist_runtime_configuration()
    log_status("StreamNotify", "Запланований пост видалено")
    return {"ok": True}


AUDIO_MIME_BY_EXT = {
    '.mp3': 'audio/mpeg',
    '.wav': 'audio/wav',
    '.ogg': 'audio/ogg',
    '.oga': 'audio/ogg',
    '.opus': 'audio/ogg; codecs=opus',
    '.m4a': 'audio/mp4',
    '.aac': 'audio/mp4',
    '.flac': 'audio/flac',
    '.wma': 'audio/x-ms-wma',
}


def guess_audio_mime(file_path):
    """Визначає MIME-тип аудіофайлу за розширенням."""
    lower = (file_path or '').lower()
    for ext, mime in AUDIO_MIME_BY_EXT.items():
        if lower.endswith(ext):
            return mime
    return 'application/octet-stream'


def parse_range_header(raw_value, file_size):
    """Розбирає заголовок Range: bytes=START-END.

    Повертає (start, end) включно, або None якщо діапазон відсутній /
    некорректний / не підтримується (multipart, інші одиниці).
    """
    if not raw_value or file_size <= 0:
        return None
    raw_value = raw_value.strip()
    if not raw_value.lower().startswith('bytes='):
        return None
    spec = raw_value[6:].strip()
    if ',' in spec:  # multipart-діапазони не підтримуємо
        return None
    if '-' not in spec:
        return None
    first, _, last = spec.partition('-')
    first = first.strip()
    last = last.strip()
    try:
        if not first:
            # суфіксний діапазон: останні N байт
            if not last:
                return None
            length = int(last)
            if length <= 0:
                return None
            start = max(0, file_size - length)
            end = file_size - 1
        else:
            start = int(first)
            end = int(last) if last else file_size - 1
    except ValueError:
        return None
    if start < 0 or start >= file_size:
        return None
    if end >= file_size:
        end = file_size - 1
    if end < start:
        return None
    return start, end


def serve_audio_file(handler, file_path, content_type=None):
    """Віддає аудіофайл із підтримкою HTTP Range (206 Partial Content).

    Без Content-Length / Accept-Ranges браузерний <audio> не вміє
    перемотувати трек і неправильно буферизує початок — саме через це
    повзунок перемотки не працював, а перший трек «зациклювався».
    Повертає True якщо файл віддано.
    """
    try:
        file_size = os.path.getsize(file_path)
    except Exception as exc:
        print("[Audio] Не вдалося прочитати файл {}: {}".format(file_path, exc))
        return False

    if not content_type:
        content_type = guess_audio_mime(file_path)

    rng = parse_range_header(handler.headers.get('Range'), file_size)
    is_head = (getattr(handler, 'command', 'GET') or 'GET').upper() == 'HEAD'
    chunk_size = 256 * 1024

    try:
        if rng is None:
            start, end = 0, max(0, file_size - 1)
            handler.send_response(200)
        else:
            start, end = rng
            handler.send_response(206)
            handler.send_header('Content-Range', 'bytes {}-{}/{}'.format(start, end, file_size))
        length = 0 if file_size == 0 else (end - start + 1)
        handler.send_header('Content-type', content_type)
        handler.send_header('Accept-Ranges', 'bytes')
        handler.send_header('Content-Length', str(length))
        handler.send_header('Cache-Control', 'no-cache')
        handler.end_headers()
        if is_head or length <= 0:
            return True
        remaining = length
        with open(file_path, 'rb') as f:
            f.seek(start)
            while remaining > 0:
                data = f.read(min(chunk_size, remaining))
                if not data:
                    break
                handler.wfile.write(data)
                remaining -= len(data)
        return True
    except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
        # Браузер обірвав з'єднання (звична річ при перемотці) — не шумимо в лог
        return True
    except Exception as exc:
        print("[Audio] Помилка віддачі файлу {}: {}".format(file_path, exc))
        return True


# ============================================================================
# ВЕБ-СЕРВЕР
# ============================================================================
class EngineHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        return

    def send_json(self, payload, status=200):
        self.send_response(status)
        self.send_header('Content-type', 'application/json; charset=utf-8')
        self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
        self.end_headers()
        self.wfile.write(json.dumps(payload, ensure_ascii=False).encode('utf-8'))

    def send_html(self, payload, status=200):
        self.send_response(status)
        self.send_header('Content-type', 'text/html; charset=utf-8')
        self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
        self.end_headers()
        self.wfile.write((payload or '').encode('utf-8'))

    def read_json_body(self):
        content_length = int(self.headers.get('Content-Length', '0') or 0)
        raw_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
        try:
            return json.loads(raw_body.decode('utf-8', errors='ignore') or '{}')
        except Exception:
            return {}

    def handle_api_get(self, path, parsed):
        params = parse_qs(parsed.query)
        if path == '/api/events':
            self.send_json(event_bus.recent(
                limit=(params.get('limit') or ['100'])[0],
                after_id=(params.get('after_id') or ['0'])[0],
                platform=(params.get('platform') or [''])[0],
                event=(params.get('event') or [''])[0],
            ))
            return True
        if path == '/api/platforms':
            self.send_json(get_platform_status_payload())
            return True
        if path == '/api/netmon':
            if network_monitor_manager:
                self.send_json(network_monitor_manager.get_state())
            else:
                self.send_json({"enabled": False})
            return True
        if path == '/api/top_active':
            self.send_json(get_top_active())
            return True
        if path == '/api/top_likes':
            self.send_json(get_top_likes())
            return True
        if path == '/api/tiktok_history':
            requested_date = (parse_qs(parsed.query).get('date') or [''])[0].strip()
            with _tiktok_viewer_history_lock:
                snapshot = dict(tiktok_viewer_history)
            if requested_date and requested_date != 'all':
                roster = get_tiktok_day_summary(requested_date)
                top_messages = sorted(roster, key=lambda x: -x["message_count"])[:5]
                top_gifts = [r for r in sorted(roster, key=lambda x: -x["gift_diamonds"]) if r["gift_diamonds"] > 0][:5]
            else:
                roster = []
                for unique_id, entry in snapshot.items():
                    roster.append({
                        "unique_id": unique_id,
                        "nickname": entry.get("nickname") or unique_id,
                        "avatar_url": entry.get("avatar_url") or "",
                        "message_count": int(entry.get("message_count", 0) or 0),
                        "gift_count": int(entry.get("gift_count", 0) or 0),
                        "gift_diamonds": int(entry.get("gift_diamonds", 0) or 0),
                        "like_count": int(entry.get("like_count", 0) or 0),
                        "share_count": int(entry.get("share_count", 0) or 0),
                        "join_count": int(entry.get("join_count", 0) or 0),
                        "follow_count": int(entry.get("follow_count", 0) or 0),
                        "last_seen": entry.get("last_seen", 0),
                    })
                roster.sort(key=lambda x: -x["last_seen"])
                top_messages = get_tiktok_viewer_top("message_count", 5)
                top_gifts = get_tiktok_viewer_top("gift_diamonds", 5)
            try:
                top_all_networks = []
                for item in (get_top_active(limit_all_time=5).get("all_time") or []):
                    top_all_networks.append({
                        "platform": item.get("platform") or "",
                        "nickname": item.get("nickname") or item.get("display_name") or item.get("username") or "?",
                        "avatar_url": "",
                        "value": int(item.get("count", 0) or 0),
                    })
            except Exception:
                top_all_networks = []
            self.send_json({
                "roster": roster[:200],
                "top_all_networks": top_all_networks,
                "top_messages": top_messages,
                "top_gifts": top_gifts,
                "total_viewers_known": len(snapshot),
                "available_days": get_tiktok_days_available(),
                "selected_date": requested_date or 'all',
            })
            return True
        if path == '/api/tiktok_user_detail':
            uid = (parse_qs(parsed.query).get('unique_id') or [''])[0].strip()
            detail = get_tiktok_user_detail(uid)
            if not detail:
                self.send_json({"error": "not_found", "unique_id": uid, "messages": [], "gifts": []})
            else:
                self.send_json(detail)
            return True
        if path == '/api/music/state':
            self.send_json(music_get_state())
            return True
        if path == '/api/audio_ducking':
            self.send_json({"ducked": music_should_be_ducked()})
            return True
        if path == '/api/auth':
            self.send_json({
                "oauth": oauth_manager.status(),
                "authorize_urls": {
                    "twitch": "/auth/twitch/start",
                    "kick": "/auth/kick/start",
                },
                "pkce_supported": True,
                "multiple_accounts_supported": True,
            })
            return True
        if path == '/api/status':
            self.send_json({
                "status": "running",
                "port": PORT,
                "platforms": get_platform_status_payload(),
                "oauth": oauth_manager.status(),
                "dependencies": {"aiohttp": bool(aiohttp), "websockets": bool(websockets)},
                "analytics": analytics_manager.get_current_stats() if analytics_manager else {"status": "offline"},
            })
            return True
        if path == '/api/statistics':
            payload = event_bus.statistics()
            if analytics_manager:
                payload["analytics"] = analytics_manager.get_current_stats()
                payload["history"] = analytics_manager.get_stream_history()[-10:]
            self.send_json(payload)
            return True
        if path == '/api/viewers':
            self.send_json(get_viewer_payload())
            return True
        if path == '/api/chat':
            with buffer_lock:
                messages = list(messages_buffer)
            self.send_json({"messages": messages})
            return True
        if path == '/api/logs':
            errors = []
            try:
                if os.path.exists(ERROR_LOG_FILE):
                    with open(ERROR_LOG_FILE, "r", encoding="utf-8") as file:
                        errors = file.readlines()[-100:]
            except Exception:
                pass
            self.send_json({"errors": [line.rstrip("\n") for line in errors]})
            return True
        if path == '/api/browse_fs':
            req_path = (params.get('path') or [''])[0]
            only_dirs = (params.get('only_dirs') or ['0'])[0] == '1'
            ext_filter = (params.get('ext') or [''])[0]
            self.send_json(browse_filesystem(req_path, only_dirs=only_dirs, ext_filter=ext_filter))
            return True
        if path == '/api/platform_status':
            self.send_json({"ok": True, "platforms": platform_status_snapshot()})
            return True
        if path == '/api/tts_state':
            # Діагностика: скільки обривів клієнта, повторів і влучань у кеш.
            self.send_json({"ok": True, "tts": tts_state_snapshot()})
            return True
        if path == '/api/twitch_identity':
            # Діагностика: який login насправді використовується і які ID
            # закешовані (саме тут видно причину 400 Bad Identifiers).
            self.send_json({"ok": True, "twitch": twitch_id_cache_snapshot(),
                            "raw_config_value": config.get('twitch_channel', '')})
            return True
        if path == '/api/youtube_quota':
            self.send_json({"ok": True, "youtube": youtube_quota_state()})
            return True
        if path == '/api/stream_session':
            # Діагностика: чи сесія стриму та сама після перезапуску сервісів.
            self.send_json({"ok": True, "session": stream_session_snapshot()})
            return True
        if path == '/api/dedup_stats':
            # Діагностика: скільки ID тримає кеш і скільки дублів відсіяно
            # по кожній платформі. Дає змогу довести, що після реконнекту
            # старі повідомлення саме відсіюються, а не «зникають».
            self.send_json({"ok": True, "platforms": dedup_snapshot()})
            return True
        if path == '/api/settings':
            safe_config = {}
            for key, value in config.items():
                try:
                    json.dumps(value)
                    safe_config[key] = value
                except (TypeError, ValueError):
                    continue
            self.send_json({"ok": True, "settings": safe_config})
            return True
        if path == '/api/obs_sources':
            # Кеш наповнюється лише з головного потоку OBS (obs_sources_list_tick),
            # тут ми лише читаємо вже готовий список - obspython з цього потоку
            # НЕ викликаємо (заборонено, валило OBS на кнопці розіграшу).
            self.send_json({"ok": True, "names": list(obs_sources_cache.get("names") or [])})
            return True
        return False

    def handle_api_post(self, path, parsed):
        if path == '/api/events':
            payload = self.read_json_body()
            event_id = publish_unified_event(
                payload.get("platform", "manual"),
                payload.get("event", "manual"),
                username=payload.get("username", ""),
                avatar=payload.get("avatar"),
                amount=payload.get("amount"),
                currency=payload.get("currency"),
                message=payload.get("message"),
                metadata=payload.get("metadata") if isinstance(payload.get("metadata"), dict) else payload,
            )
            self.send_json({"ok": True, "id": event_id})
            return True
        if path == '/api/auth':
            payload = self.read_json_body()
            platform = (payload.get("platform") or "").lower()
            if platform in ("twitch", "kick") and payload.get("access_token"):
                oauth_manager.set_token(platform, payload, account_id=payload.get("account_id") or "default", client_id=payload.get("client_id") or config.get(platform + "_client_id", ""))
                restore_external_configuration()
                self.send_json({"ok": True, "platform": platform})
                return True
            self.send_json({"ok": False, "error": "platform and access_token are required"}, status=400)
            return True
        if path == '/api/giveaway/start':
            self.send_json(giveaway_start())
            return True
        if path == '/api/giveaway/stop':
            self.send_json(giveaway_stop())
            return True
        if path == '/api/streamnotify/test_send':
            self.send_json(sn_action_test_send())
            return True
        if path == '/api/streamnotify/test_after':
            self.send_json(sn_action_test_after())
            return True
        if path == '/api/streamnotify/publish':
            self.send_json(sn_action_publish())
            return True
        if path == '/api/streamnotify/schedule':
            self.send_json(sn_action_schedule())
            return True
        if path == '/api/streamnotify/delete_schedule':
            self.send_json(sn_action_delete_schedule())
            return True
        if path == '/api/upload_asset':
            payload = self.read_json_body()
            if not isinstance(payload, dict):
                self.send_json({"ok": False, "error": "Тіло запиту має бути JSON-об'єктом"}, status=400)
                return True
            filename = str(payload.get("filename") or "").strip()
            data_b64 = payload.get("data_base64") or ""
            kind = str(payload.get("kind") or "media").strip().lower()
            if kind not in ("audio", "media", "image"):
                kind = "media"
            if not filename or not data_b64:
                self.send_json({"ok": False, "error": "filename і data_base64 обов'язкові"}, status=400)
                return True
            try:
                raw_bytes = base64.b64decode(data_b64, validate=True)
            except Exception:
                self.send_json({"ok": False, "error": "Некоректний base64 вміст файлу"}, status=400)
                return True
            if len(raw_bytes) > 300 * 1024 * 1024:
                self.send_json({"ok": False, "error": "Файл завеликий (максимум 300 МБ)"}, status=400)
                return True
            base_name = os.path.basename(filename)
            safe_name = re.sub(r'[^A-Za-z0-9._-]+', '_', base_name).strip('_') or "file"
            safe_name = safe_name[-120:]
            unique_name = "{}_{}".format(int(time.time() * 1000), safe_name)
            dest_dir = os.path.join(ASSETS_DIR, kind)
            try:
                os.makedirs(dest_dir, exist_ok=True)
                dest_path = os.path.join(dest_dir, unique_name)
                with open(dest_path, "wb") as f:
                    f.write(raw_bytes)
            except OSError as e:
                self.send_json({"ok": False, "error": "Не вдалося зберегти файл: {}".format(e)}, status=500)
                return True
            self.send_json({"ok": True, "path": dest_path, "filename": unique_name})
            return True
        if path == '/api/settings':
            payload = self.read_json_body()
            if not isinstance(payload, dict) or not payload:
                self.send_json({"ok": False, "error": "Тіло запиту має бути непорожнім JSON-об'єктом"}, status=400)
                return True
            if 'dock_port' in payload:
                try:
                    port_value = int(payload['dock_port'])
                    if not (1024 <= port_value <= 65535):
                        raise ValueError("out of range")
                    payload['dock_port'] = port_value
                except (TypeError, ValueError):
                    self.send_json({"ok": False, "error": "dock_port має бути цілим числом від 1024 до 65535"}, status=400)
                    return True
            # Взаємовиключні перемикачі автоперекладу озвучки:
            # вмикання одного автоматично вимикає інший.
            if payload.get('tts_translate_uk'):
                payload['tts_translate_en'] = False
                payload['tts_auto_translate'] = False
            elif payload.get('tts_translate_en'):
                payload['tts_translate_uk'] = False
                payload['tts_auto_translate'] = False
            applied_keys = []
            unknown_keys = []
            with config_lock:
                for key, value in payload.items():
                    if key not in config:
                        unknown_keys.append(key)
                        continue
                    config[key] = value
                    applied_keys.append(key)
                persist_runtime_configuration()
            # НЕ перезапускаємо всі сервіси. Гаряче застосовуємо лише те,
            # чого реально стосуються змінені ключі. Окремий потік потрібен,
            # бо серед дій може бути перезапуск самого HTTP-сервера.
            threading.Thread(target=apply_settings_hot,
                             args=(list(applied_keys),),
                             kwargs={"reason": "settings_changed"},
                             daemon=True).start()
            self.send_json({"ok": True, "applied": applied_keys, "unknown": unknown_keys})
            return True
        return False

    def do_GET(self):
        global messages_buffer, config, blocked_users, no_tts_users, custom_nicknames
        try:
            parsed = urlparse(self.path)
            path = parsed.path.rstrip('/') or '/'

            if self.handle_api_get(path, parsed):
                return
            if path in ('/chat/widget', '/dashboard/widget', '/viewers/widget'):
                self.send_html(generate_simple_widget_html(path.strip('/').split('/')[0]))
                return

            if path == '/callback/twitch':
                params = parse_qs(parsed.query)
                code = ((params.get('code') or [''])[0] or '').strip()
                error = ((params.get('error') or [''])[0] or '').strip()
                state = ((params.get('state') or [''])[0] or '').strip()
                expected_state = (twitch_oauth_state_cache.get('state') or '').strip()
                state_is_valid = (not expected_state) or (state == expected_state and time.time() - float(twitch_oauth_state_cache.get('ts', 0) or 0) <= 1800)
                if error:
                    self.send_response(400)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.end_headers()
                    self.wfile.write(('<html><body><h2>Twitch OAuth error</h2><p>{}</p></body></html>'.format(error)).encode('utf-8'))
                    return
                if not state_is_valid:
                    self.send_response(400)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.end_headers()
                    self.wfile.write('<html><body><h2>Twitch OAuth error</h2><p>State mismatch. Спробуйте авторизацію ще раз.</p></body></html>'.encode('utf-8'))
                    return
                payload = twitch_exchange_authorization_code((config.get('twitch_client_id', '') or '').strip(), (config.get('twitch_client_secret', '') or '').strip(), code, redirect_uri=TWITCH_DEFAULT_REDIRECT_URI)
                access_token = ((payload or {}).get('access_token') or '').strip()
                validation = twitch_validate_user_token(access_token) if access_token else None
                login = ((validation or {}).get('login') or '').strip()
                scopes = (validation or {}).get('scopes') or ((payload or {}).get('scope') or [])
                if access_token:
                    config['twitch_irc_oauth'] = 'oauth:' + access_token
                if login:
                    config['twitch_irc_login'] = login
                self.send_response(200 if access_token else 500)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                if access_token:
                    self.wfile.write(("<html><body><h2>Twitch OAuth успішно завершено</h2><p>Login: {}</p><p>Scopes: {}</p><p>Token збережено в пам’яті поточного запуску скрипта. Можна закривати цю вкладку і перезапустити сервіси в OBS.</p></body></html>".format(login or 'unknown', ', '.join(scopes) if scopes else '-')).encode('utf-8'))
                else:
                    self.wfile.write('<html><body><h2>Twitch OAuth не завершено</h2><p>Не вдалося обміняти code на token. Перевір Client ID, Client Secret і Redirect URL.</p></body></html>'.encode('utf-8'))
            elif path == '/auth/twitch/start':
                auth_url = twitch_build_authorize_url((config.get('twitch_client_id', '') or '').strip(), redirect_uri=TWITCH_DEFAULT_REDIRECT_URI)
                if not auth_url:
                    self.send_response(400)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.end_headers()
                    self.wfile.write('<html><body><h2>Twitch auth unavailable</h2><p>Заповніть Twitch Client ID у налаштуваннях скрипта.</p></body></html>'.encode('utf-8'))
                    return
                self.send_response(302)
                self.send_header('Location', auth_url)
                self.end_headers()
            elif path == '/auth/kick/start':
                client_id = (config.get('kick_client_id', '') or '').strip()
                if not client_id:
                    self.send_response(400)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.end_headers()
                    self.wfile.write('<html><body><h2>Kick auth unavailable</h2><p>Заповніть Kick Client ID у налаштуваннях скрипта.</p></body></html>'.encode('utf-8'))
                    return
                state = secrets.token_urlsafe(24)
                code_verifier = secrets.token_urlsafe(64)
                code_challenge = base64.urlsafe_b64encode(hashlib.sha256(code_verifier.encode('utf-8')).digest()).decode('utf-8').rstrip('=')
                kick_user_oauth_cache['pkce_state'] = state
                kick_user_oauth_cache['pkce_verifier'] = code_verifier
                params = {
                    'response_type': 'code',
                    'client_id': client_id,
                    'redirect_uri': KICK_DEFAULT_REDIRECT_URI,
                    'scope': ' '.join(['user:read', 'channel:read', 'events:subscribe', 'moderation:ban', 'moderation:chat_message:manage', 'chat:write']),
                    'state': state,
                    'code_challenge': code_challenge,
                    'code_challenge_method': 'S256',
                }
                self.send_response(302)
                self.send_header('Location', 'https://id.kick.com/oauth/authorize?' + urllib.parse.urlencode(params))
                self.end_headers()
            elif path == '/callback/kick':
                params = parse_qs(parsed.query)
                code = ((params.get('code') or [''])[0] or '').strip()
                error = ((params.get('error') or [''])[0] or '').strip()
                state = ((params.get('state') or [''])[0] or '').strip()
                expected_state = (kick_user_oauth_cache.get('pkce_state') or '').strip()
                if error:
                    self.send_response(400)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.end_headers()
                    self.wfile.write(('<html><body><h2>Kick OAuth error</h2><p>{}</p></body></html>'.format(error)).encode('utf-8'))
                    return
                if expected_state and state != expected_state:
                    self.send_response(400)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.end_headers()
                    self.wfile.write('<html><body><h2>Kick OAuth error</h2><p>State mismatch. Спробуйте авторизацію ще раз.</p></body></html>'.encode('utf-8'))
                    return
                payload = kick_exchange_authorization_code(
                    (config.get('kick_client_id', '') or '').strip(),
                    (config.get('kick_client_secret', '') or '').strip(),
                    code,
                    redirect_uri=KICK_DEFAULT_REDIRECT_URI,
                    code_verifier=(kick_user_oauth_cache.get('pkce_verifier') or '').strip(),
                )
                ok = bool(payload and (payload.get('access_token') or '').strip())
                subs_ok, subs_err = (True, None)
                if ok:
                    try:
                        subs_ok, subs_err = kick_subscribe_to_events()
                    except Exception as e:
                        subs_ok, subs_err = False, str(e)
                self.send_response(200 if ok else 500)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                if ok:
                    subs_note = '' if subs_ok else '<p style="color:#c00">Увага: webhook-підписки (фоловери/підписки) не вдалося зареєструвати: {}</p>'.format(subs_err or '-')
                    self.wfile.write(('<html><body><h2>Kick OAuth успішно завершено</h2><p>Access token отримано. Можна закривати цю вкладку.</p>{}</body></html>'.format(subs_note)).encode('utf-8'))
                else:
                    self.wfile.write('<html><body><h2>Kick OAuth не завершено</h2><p>Не вдалося обміняти code на token. Перевір Client ID, Client Secret і Redirect URL.</p></body></html>'.encode('utf-8'))
            elif path == '/':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                self.wfile.write(HTML_CONTENT.encode('utf-8'))
            elif path == '/settings':
                self.send_html(SETTINGS_PAGE_HTML)
            elif path == '/giveaway/overlay':
                self.send_html(GIVEAWAY_OVERLAY_HTML)
            elif path == '/giveaway/data':
                self.send_json(giveaway_overlay_state)
            elif path == '/overlay':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                overlay_params = parse_qs(parsed.query)
                plain_param = (overlay_params.get('plain') or [''])[0].strip().lower()
                plain_flag = None
                if plain_param in ('1', 'true', 'yes', 'on'):
                    plain_flag = True
                elif plain_param in ('0', 'false', 'no', 'off'):
                    plain_flag = False
                self.wfile.write(generate_overlay_html(plain=plain_flag).encode('utf-8'))
            elif path == '/tiktok_history':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                self.wfile.write(generate_tiktok_history_html().encode('utf-8'))
            elif path == '/music_player':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                self.wfile.write(generate_music_player_html().encode('utf-8'))
            elif path == '/tts_audio':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                self.wfile.write(generate_tts_audio_html().encode('utf-8'))
            elif path == '/analytics/widget':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                if analytics_manager:
                    widget_html = analytics_manager.get_widget_html()
                else:
                    widget_html = "<html><body>Analytics not running</body></html>"
                self.wfile.write(widget_html.encode('utf-8'))
            elif path == '/top_likes_widget':
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.end_headers()
                self.wfile.write(generate_top_likes_widget_html().encode('utf-8'))
            elif path in ('/tiktok_alerts/widget', '/event_alerts/widget'):
                self.send_response(200)
                self.send_header('Content-type', 'text/html; charset=utf-8')
                self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
                self.end_headers()
                self.wfile.write(generate_tiktok_alert_widget_html().encode('utf-8'))
            elif path in ('/tiktok_alerts/events', '/event_alerts/events'):
                params = parse_qs(parsed.query)
                after_id = (params.get('after_id') or ['0'])[0]
                limit = (params.get('limit') or ['100'])[0]
                events = get_platform_widget_events(after_id=after_id, limit=limit)
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.send_header('Cache-Control', 'no-cache, no-store, must-revalidate')
                self.end_headers()
                self.wfile.write(json.dumps(events).encode('utf-8'))
            elif path == '/tiktok_alert_asset':
                kind = (parse_qs(parsed.query).get('kind') or [''])[0]
                serve_local_asset(self, get_tiktok_widget_asset_path(kind))
            elif path == '/event_alert_asset':
                params = parse_qs(parsed.query)
                platform = (params.get('platform') or [''])[0]
                event_type = (params.get('event') or [''])[0]
                asset_kind = (params.get('asset') or [''])[0]
                serve_local_asset(self, get_alert_widget_asset_path(platform, event_type, asset_kind))
            elif path == '/analytics/stats':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                if analytics_manager:
                    stats = analytics_manager.get_current_stats()
                else:
                    stats = {"status": "offline", "total_viewers": 0, "platforms": {}}
                self.wfile.write(json.dumps(stats).encode('utf-8'))
            elif path == '/analytics/config':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                widget_config = {
                    "mode": config.get("analytics_widget_mode", "compact"),
                    "updateInterval": 3000
                }
                self.wfile.write(json.dumps(widget_config).encode('utf-8'))
            elif path == '/analytics/history':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                if analytics_manager:
                    history = analytics_manager.get_stream_history()
                else:
                    history = []
                self.wfile.write(json.dumps(history).encode('utf-8'))
            elif path == '/get_messages':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                with buffer_lock:
                    self.wfile.write(json.dumps(messages_buffer).encode('utf-8'))
            elif path == '/get_config':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    "ttsTemplate": config["tts_template"], "ttsReadNicknames": config.get("tts_read_nicknames", True), "msgTimeout": config["msg_timeout"],
                    "ttsVolume": config["tts_volume"] / 100.0, "ttsEngine": normalize_tts_engine(config["tts_engine"]),
                    "ttsVoice": config["tts_voice"], "ttsSpeed": config["tts_speed"] / 100.0,
                    "ttsOutputToStream": config.get("tts_output_to_stream", True),
                    "ttsEnabled": config.get("tts_enabled", True),
                    "bgImage": bool(config["chat_bg_image"]), "msgColor": config["chat_msg_color"],
                    "fontSize": config["chat_font_size"],
                    "ringtoneChatOnly": bool(config.get("tts_ringtone_chat_only", True)),
                    "ringtoneUrl": '/ringtone' if config.get("tts_ringtone_path") and os.path.exists(config.get("tts_ringtone_path", "")) else None
                }).encode('utf-8'))
            elif path == '/local_bg':
                if config["chat_bg_image"] and os.path.exists(config["chat_bg_image"]):
                    try:
                        self.send_response(200)
                        if config["chat_bg_image"].lower().endswith('.png'):
                            self.send_header('Content-type', 'image/png')
                        else:
                            self.send_header('Content-type', 'image/jpeg')
                        self.end_headers()
                        with open(config["chat_bg_image"], 'rb') as f:
                            self.wfile.write(f.read())
                        return
                    except:
                        pass
                self.send_response(404)
                self.end_headers()
            elif path == '/music_file':
                requested_name = (parse_qs(parsed.query).get('name') or [''])[0]
                folder = (config.get('music_folder_path') or '').strip()
                served = False
                # Захист від path traversal: ім'я файлу МАЄ бути одним із
                # реально відсканованих у папці треків, без "..", "/" чи "\\".
                if requested_name and folder and os.path.isdir(folder) and '..' not in requested_name and '/' not in requested_name and '\\' not in requested_name:
                    if requested_name in music_scan_playlist():
                        full_path = os.path.join(folder, requested_name)
                        if os.path.isfile(full_path):
                            served = serve_audio_file(self, full_path)
                if not served:
                    self.send_response(404)
                    self.end_headers()
            elif path == '/ringtone':
                ring_path = config.get("tts_ringtone_path", "")
                if ring_path and os.path.isfile(ring_path):
                    serve_audio_file(self, ring_path)
                else:
                    self.send_response(404)
                    self.end_headers()
            elif path == '/tts':
                params = parse_qs(parsed.query)
                lang = params.get('lang', ['uk'])[0]
                text = params.get('q', [''])[0]
                engine = params.get('engine', ['google'])[0]
                voice = params.get('voice', ['uk-UA'])[0]
                try:
                    speed = float(params.get('speed', ['1.0'])[0])
                except (TypeError, ValueError):
                    speed = 1.0
                try:
                    audio_data, content_type = synthesize_tts_bytes(text, lang, engine, voice, speed)
                except Exception as e:
                    tts_note('failed')
                    print("Помилка TTS: {}".format(e))
                    try:
                        self.send_response(500)
                        self.end_headers()
                    except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
                        pass
                    return
                try:
                    self.send_response(200)
                    self.send_header('Content-type', content_type)
                    self.send_header('Content-Length', str(len(audio_data)))
                    self.end_headers()
                    self.wfile.write(audio_data)
                    tts_note('served')
                except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError) as e:
                    # Саме тут і виникав [WinError 10053]: Browser source в OBS
                    # закрив аудіо-запит (перезавантаження сторінки, наступна
                    # фраза, зміна сцени). Це НЕ збій скрипта: аудіо вже лежить
                    # у кеші, тому повторний запит візьме готові байти, а
                    # повторного синтезу і повторної озвучки не буде.
                    tts_note('client_aborts')
                    print("[TTS] Клієнт закрив аудіо-запит ({}: {}). Аудіо в кеші, "
                          "повторного синтезу не потрібно. Жодна підсистема не "
                          "перезапускається.".format(type(e).__name__, e))
                return
            elif path == '/api/tts/elevenlabs_test':
                try:
                    body = elevenlabs_diagnose_html().encode('utf-8')
                    self.send_response(200)
                    self.send_header('Content-type', 'text/html; charset=utf-8')
                    self.send_header('Content-Length', str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except Exception as e:
                    print("[TTS] Помилка перевірки ElevenLabs: {}".format(e))
                    msg = "Помилка перевірки: {}".format(e).encode('utf-8')
                    self.send_response(500)
                    self.send_header('Content-type', 'text/plain; charset=utf-8')
                    self.end_headers()
                    self.wfile.write(msg)
            elif path == '/blocked_users':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(list(blocked_users)).encode('utf-8'))
            elif path == '/no_tts_users':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(list(no_tts_users)).encode('utf-8'))
            elif path == '/custom_nicknames':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(get_custom_nicknames_list(), ensure_ascii=False).encode('utf-8'))
            elif path == '/voice_profiles':
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(get_available_voice_profiles(), ensure_ascii=False).encode('utf-8'))
            elif path == '/user_voice_assignment':
                params = parse_qs(parsed.query)
                platform = (params.get('platform') or [''])[0]
                username = (params.get('username') or [''])[0]
                display_name = (params.get('display_name') or [''])[0]
                voice_id = get_user_voice_assignment(platform, username, display_name)
                profile = None
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({
                    'voice_id': voice_id,
                    'title': profile.get('title', '') if profile else '',
                    'custom': bool(voice_id)
                }, ensure_ascii=False).encode('utf-8'))
        except (ConnectionAbortedError, BrokenPipeError):
            pass

    def do_POST(self):
        global blocked_users, no_tts_users, config, custom_nicknames, user_voice_assignments
        try:
            parsed = urlparse(self.path)
            path = parsed.path.rstrip('/') or '/'
            if self.handle_api_post(path, parsed):
                return
            if path in ('/webhook/twitch', '/webhook/youtube'):
                payload = self.read_json_body()
                platform = path.rsplit('/', 1)[-1]
                handled = handle_generic_webhook(platform, self.headers, payload)
                self.send_json({'ok': True, 'handled': bool(handled), 'platform': platform}, status=200 if handled else 202)
                return

            if self.path == '/block_user':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                username = data.get('username', '')
                if username:
                    block_user(username)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/unblock_user':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                username = data.get('username', '')
                if username:
                    unblock_user(username)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/api/tiktok_history/clear':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                raw = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(raw.decode('utf-8') or '{}')
                except Exception:
                    data = {}
                scope = (data.get('scope') or 'all').strip().lower()
                date_str = (data.get('date') or '').strip()
                if scope == 'day':
                    if not date_str or date_str == 'all':
                        date_str = time.strftime('%Y-%m-%d')
                    removed = clear_tiktok_day_history(date_str)
                    payload = {'ok': True, 'scope': 'day', 'date': date_str, 'removed': removed}
                elif scope == 'all_networks':
                    # Очищає лише крос-мережевий рейтинг ("🌐 Топ глядачів усіх мереж"),
                    # історія відвідувань TikTok при цьому не зачіпається.
                    removed = clear_user_activity()
                    payload = {'ok': True, 'scope': 'all_networks', 'removed': removed}
                else:
                    removed = clear_tiktok_viewer_history()
                    payload = {'ok': True, 'scope': 'all', 'removed': removed}
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(payload, ensure_ascii=False).encode('utf-8'))
            elif self.path == '/unblock_all_users':
                removed = unblock_all_users()
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'ok': True, 'removed': removed}).encode('utf-8'))
            elif self.path == '/enable_tts_all_users':
                removed = enable_tts_all_users()
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'ok': True, 'removed': removed}).encode('utf-8'))
            elif self.path == '/disable_tts_user':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                username = data.get('username', '')
                if username:
                    disable_tts_for_user(username)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/api/mod/action':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                post_data = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(post_data.decode('utf-8'))
                except Exception:
                    data = {}
                platform = (data.get('platform') or '').strip().lower()
                action = (data.get('action') or '').strip().lower()
                kwargs = {
                    'user_id': data.get('user_id', ''),
                    'message_id': data.get('message_id', ''),
                    'reason': data.get('reason', ''),
                    'duration_seconds': data.get('duration_seconds'),
                    'duration_minutes': data.get('duration_minutes'),
                    'text': data.get('text', ''),
                }
                if platform == 'twitch':
                    result = twitch_moderation_action(action, **kwargs)
                elif platform == 'kick':
                    result = kick_moderation_action(action, **kwargs)
                else:
                    result = {'ok': False, 'error': "Модерація підтримується лише для Twitch і Kick"}
                self.send_json(result)
            elif self.path == '/api/music/control':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                post_data = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(post_data.decode('utf-8'))
                except Exception:
                    data = {}
                action = (data.get('action') or '').strip().lower()
                from_index = data.get('from_index')
                if action == 'seek':
                    music_control('seek', from_index=data.get('position'))
                elif action in ('play', 'pause', 'next', 'prev', 'advance', 'goto'):
                    if action == 'goto' and from_index is None:
                        from_index = data.get('index')
                    music_control(action, from_index=from_index)
                self.send_json(music_get_state())
            elif self.path == '/api/music/remove_track':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                post_data = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(post_data.decode('utf-8'))
                except Exception:
                    data = {}
                result = music_remove_track(data.get('name'))
                if result.get("ok"):
                    result["state"] = music_get_state()
                    self.send_json(result)
                else:
                    self.send_json(result, status=400)
            elif self.path == '/api/music/restore_removed':
                result = music_restore_removed()
                result["state"] = music_get_state()
                self.send_json(result)
            elif self.path == '/api/music/volume':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                post_data = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(post_data.decode('utf-8'))
                except Exception:
                    data = {}
                self.send_json({"ok": True, "volume": music_set_volume(data.get('volume'))})
            elif self.path == '/api/music/reorder':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                post_data = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(post_data.decode('utf-8'))
                except Exception:
                    data = {}
                result = music_set_order(data.get('order') or [])
                if result.get("ok"):
                    result["state"] = music_get_state()
                    self.send_json(result)
                else:
                    self.send_json(result, status=400)
            elif self.path == '/api/audio_ducking':
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                post_data = self.rfile.read(content_length) if content_length else b'{}'
                try:
                    data = json.loads(post_data.decode('utf-8'))
                except Exception:
                    data = {}
                action = (data.get('action') or '').strip().lower()
                if action == 'begin':
                    audio_ducking_begin()
                elif action == 'end':
                    audio_ducking_end()
                self.send_response(200)
                self.end_headers()
            elif self.path == '/api/music/upload':
                raw_name = self.headers.get('X-Music-Filename', '')
                try:
                    requested_name = urllib.parse.unquote(raw_name)
                except Exception:
                    requested_name = raw_name
                folder = (config.get('music_folder_path') or '').strip()
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                MAX_UPLOAD_BYTES = 150 * 1024 * 1024  # 150 МБ - з запасом навіть під нестиснений WAV/FLAC
                error = None
                if not requested_name or '..' in requested_name or '/' in requested_name or '\\' in requested_name:
                    error = "Некоректна назва файлу"
                elif not requested_name.lower().endswith(MUSIC_AUDIO_EXTENSIONS):
                    error = "Непідтримуваний формат. Дозволено: {}".format(', '.join(MUSIC_AUDIO_EXTENSIONS))
                elif not folder:
                    error = "Спочатку вкажіть і збережіть папку для треків"
                elif content_length <= 0:
                    error = "Порожній файл"
                elif content_length > MAX_UPLOAD_BYTES:
                    error = "Файл завеликий (максимум 150 МБ)"
                if error:
                    # Тіло все одно треба прочитати й відкинути, інакше
                    # з'єднання лишається "забитим" недочитаними байтами.
                    if content_length > 0:
                        try:
                            self.rfile.read(content_length)
                        except Exception:
                            pass
                    self.send_json({"ok": False, "error": error}, status=400)
                    return True
                try:
                    os.makedirs(folder, exist_ok=True)
                    body = self.rfile.read(content_length)
                    dest_path = os.path.join(folder, requested_name)
                    with open(dest_path, 'wb') as f:
                        f.write(body)
                    self.send_json({"ok": True, "filename": requested_name})
                except Exception as e:
                    self.send_json({"ok": False, "error": "Помилка запису файлу: {}".format(e)}, status=500)
                return True
            elif self.path == '/api/upload_asset_stream':
                raw_name = self.headers.get('X-Asset-Filename', '')
                try:
                    requested_name = urllib.parse.unquote(raw_name)
                except Exception:
                    requested_name = raw_name
                kind = (self.headers.get('X-Asset-Kind', '') or 'media').strip().lower()
                if kind not in ('audio', 'media', 'image'):
                    kind = 'media'
                content_length = int(self.headers.get('Content-Length', 0) or 0)
                MAX_ASSET_BYTES = 300 * 1024 * 1024
                base_name = os.path.basename(requested_name or '')
                error = None
                if not base_name:
                    error = "Некоректна назва файлу"
                elif content_length <= 0:
                    error = "Порожній файл"
                elif content_length > MAX_ASSET_BYTES:
                    error = "Файл завеликий (максимум 300 МБ)"
                if error:
                    if content_length > 0:
                        try:
                            remaining = content_length
                            while remaining > 0:
                                chunk = self.rfile.read(min(262144, remaining))
                                if not chunk:
                                    break
                                remaining -= len(chunk)
                        except Exception:
                            pass
                    print("[Upload] Відхилено {}: {}".format(base_name or '?', error))
                    self.send_json({"ok": False, "error": error}, status=400)
                    return True
                safe_name = re.sub(r'[^A-Za-z0-9._-]+', '_', base_name).strip('_') or "file"
                safe_name = safe_name[-120:]
                unique_name = "{}_{}".format(int(time.time() * 1000), safe_name)
                dest_dir = os.path.join(ASSETS_DIR, kind)
                try:
                    os.makedirs(dest_dir, exist_ok=True)
                    dest_path = os.path.join(dest_dir, unique_name)
                    remaining = content_length
                    with open(dest_path, 'wb') as f:
                        while remaining > 0:
                            chunk = self.rfile.read(min(1048576, remaining))
                            if not chunk:
                                break
                            f.write(chunk)
                            remaining -= len(chunk)
                    print("[Upload] Медіафайл збережено: {} ({:.1f} МБ)".format(
                        dest_path, content_length / 1048576.0))
                    self.send_json({"ok": True, "path": dest_path, "filename": unique_name})
                except Exception as e:
                    print("[Upload] Помилка запису {}: {}".format(base_name, e))
                    self.send_json({"ok": False, "error": "Не вдалося зберегти файл: {}".format(e)}, status=500)
                return True
            elif self.path == '/api/tts/toggle':
                config["tts_enabled"] = not bool(config.get("tts_enabled", True))
                try:
                    persist_runtime_configuration()
                except Exception as e:
                    print("[TTS] Помилка збереження стану TTS: {}".format(e))
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"enabled": config["tts_enabled"]}).encode('utf-8'))
            elif self.path == '/enable_tts_user':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                username = data.get('username', '')
                if username:
                    enable_tts_for_user(username)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/set_custom_nickname':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                platform = data.get('platform', '')
                username = data.get('username', '')
                display_name = data.get('display_name', '')
                nickname = data.get('nickname', '')
                if username or display_name:
                    set_custom_nickname(platform, username, display_name, nickname)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/remove_custom_nickname':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                platform = data.get('platform', '')
                username = data.get('username', '')
                display_name = data.get('display_name', '')
                if username or display_name:
                    remove_custom_nickname(platform, username, display_name)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/set_user_voice_assignment':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                platform = data.get('platform', '')
                username = data.get('username', '')
                display_name = data.get('display_name', '')
                voice_id = data.get('voice_id', '')
                if username or display_name:
                    if voice_id:
                        set_user_voice_assignment(platform, username, display_name, voice_id)
                    else:
                        remove_user_voice_assignment(platform, username, display_name)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif self.path == '/remove_user_voice_assignment':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                platform = data.get('platform', '')
                username = data.get('username', '')
                display_name = data.get('display_name', '')
                if username or display_name:
                    remove_user_voice_assignment(platform, username, display_name)
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(400)
                    self.end_headers()
            elif (urlparse(self.path).path.rstrip('/') or '/') in ('/', '/kick/webhook', '/webhook/kick', '/event_alerts/widget'):
                parsed = urlparse(self.path)
                expected_secret = (config.get('kick_webhook_secret', '') or '').strip()
                provided_secret = self.headers.get('X-Webhook-Secret', '') or ((parse_qs(parsed.query).get('secret') or [''])[0])
                if expected_secret and provided_secret != expected_secret:
                    self.send_response(403)
                    self.end_headers()
                    return
                content_length = int(self.headers.get('Content-Length', '0') or 0)
                raw_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                try:
                    payload = json.loads(raw_body.decode('utf-8', errors='ignore') or '{}')
                except Exception:
                    payload = {}
                event_name = extract_kick_event_name(self.headers, payload)
                handled = handle_kick_webhook_event(event_name, payload)
                self.send_response(200 if handled else 202)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'ok': True, 'handled': bool(handled), 'event': event_name}).encode('utf-8'))
            elif self.path == '/clear_chat':
                clear_all_messages()
                self.send_response(200)
                self.end_headers()
            elif self.path == '/set_platform_filter':
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                data = json.loads(post_data.decode('utf-8'))
                platform = data.get('platform', '')
                enabled = data.get('enabled', True)
                if platform in config["filter_platforms"]:
                    config["filter_platforms"][platform] = enabled
                    self.send_response(200)
                    self.end_headers()
                else:
                    self.send_response(404)
                    self.end_headers()
        except (ConnectionAbortedError, BrokenPipeError):
            pass


class SafeHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = True


def get_lan_ip():
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.connect(('8.8.8.8', 80))
            ip = sock.getsockname()[0]
        finally:
            sock.close()
        if ip and not ip.startswith('127.'):
            return ip
    except:
        pass
    try:
        ip = socket.gethostbyname(socket.gethostname())
        if ip:
            return ip
    except:
        pass
    return '127.0.0.1'


def _restart_services_after_settings_change():
    """ЗАСТАРІЛО. Раніше викликалась з POST /api/settings і перезапускала
    ВСЕ (kill_services + run_services) на будь-яке збереження налаштувань.
    Залишена лише для сумісності/ручного повного перезапуску; штатний шлях -
    apply_settings_hot()."""
    try:
        kill_services()
        youtube_quota_clear_if_key_changed()
        time.sleep(0.1)
        run_services()
    except Exception as e:
        print("[MultiChat] Помилка перезапуску після зміни налаштувань: {}".format(e))


def reload_blacklist_words():
    """Перечитує «Чорний список слів» з config без перезапуску сервісів.
    ВАЖЛИВО: це список СЛІВ для фільтра тексту, а не список користувачів."""
    global blacklist_words
    blacklist_str = (config.get("blacklist", "") or "").strip()
    blacklist_words = set(
        word.strip().lower() for word in blacklist_str.split(',') if word.strip())
    if blacklist_words:
        print("[Модерація] Чорний список слів: {} шт. (на заблокованих користувачів НЕ впливає)".format(
            len(blacklist_words)))
    else:
        print("[Модерація] Чорний список слів порожній")
    return len(blacklist_words)


def apply_config_side_effects():
    """
    Побічні ефекти зміни конфігурації: парсинг чорного списку, очищення
    кешів дедуплікації та таймерів агрегації подарунків, лог про
    YouTube API ключ. Раніше цей код лежав прямо всередині
    script_update() і тому спрацьовував лише при зміні налаштувань
    через нативну панель OBS. Тепер налаштування можна міняти і через
    веб-панель (/settings), тож логіка винесена сюди і викликається з
    run_services() — єдина точка входу, спільна для обох шляхів.
    """
    global blocked_users, tiktok_last_comment_ts, tiktok_widget_event_counter

    # ВАЖЛИВО: поле "Чорний список слів" — це список СЛІВ для фільтра тексту,
    # а не список користувачів. Раніше цей рядок при кожному старті скрипта
    # ПЕРЕЗАПИСУВАВ набір заблокованих користувачів вмістом цього поля, через що
    # у «Заблокованих користувачах» самі собою з'являлись сотні записів
    # (насправді — лайливі слова), а ручне розблокування не зберігалось.
    # Тепер список слів живе окремо і на модерацію користувачів не впливає.
    reload_blacklist_words()

    with buffer_lock:
        tiktok_like_tracker.clear()
        repeated_message_tracker.clear()
        for tracker in tiktok_gift_tracker.values():
            timer = tracker.get("timer")
            if timer:
                try:
                    timer.cancel()
                except Exception:
                    pass
        tiktok_gift_tracker.clear()
        # НЕ чистимо кеші дедуплікації.
        # Раніше тут стояли processed_*_ids.clear() і оскільки
        # apply_config_side_effects() викликається з run_services(), будь-який
        # внутрішній перезапуск сервісів стирав пам'ять про вже озвучені
        # повідомлення - і читачі озвучували їх удруге. Саме це і був
        # першопричина скарги "скрипт повторно читає старі повідомлення".
        # Кеші тепер живуть у message_dedup_seen і скидаються тільки в
        # script_load() через dedup_reset_all().
        tiktok_last_comment_ts = 0.0
        tiktok_widget_events.clear()
        tiktok_widget_event_counter = 0

    if config.get("yt_api_key"):
        log_status("YouTube", "API ключ завантажено (використовується для Analytics і для пошуку активної трансляції каналу): {}...".format(config['yt_api_key'][:8]))
    else:
        log_status("YouTube", "API ключ НЕ завантажено (порожній рядок)")


# ---------------------------------------------------------------------------
# НАГЛЯДАЧ ПЛАТФОРМ (per-platform supervisor)
# ---------------------------------------------------------------------------
PLATFORM_WORKERS = {
    "twitch": twitch_worker,
    "twitch_eventsub": twitch_eventsub_worker,
    "kick": kick_worker,
    "youtube": youtube_worker,
    "youtube_stats": youtube_stats_worker,
    "tiktok": tiktok_worker,
    "bot_timers": bot_timer_worker,
}
PLATFORM_START_ORDER = ["twitch", "twitch_eventsub", "kick", "youtube",
                        "youtube_stats", "tiktok",
                        "bot_timers"]

# Які ключі налаштувань до якої платформи належать - використовується для
# «гарячого» застосування налаштувань без глобального перезапуску.
PLATFORM_CONFIG_PREFIXES = {
    "twitch": ("tw_", "twitch_"),
    "twitch_eventsub": ("tw_", "twitch_"),
    "kick": ("kick_",),
    "youtube": ("yt_", "youtube_"),
    "youtube_stats": ("yt_",),
    "tiktok": ("tt_", "tiktok_"),
}


def platform_is_running(name):
    with platform_lock:
        thread = platform_threads.get(name)
        sid = platform_sessions.get(name)
    return bool(thread and thread.is_alive() and sid is not None
                and session_is_current(sid))


def start_platform(name, reason='start'):
    """ІДЕМПОТЕНТНО. Повторний виклик для вже працюючої платформи НЕ створює
    другий екземпляр читача - лише пише в лог 'already running'."""
    worker = PLATFORM_WORKERS.get(name)
    if worker is None:
        print("[Recovery] platform={} reason=unknown_platform action=ignored".format(name))
        return False
    with platform_lock:
        if platform_is_running(name):
            print("[Recovery] platform={} action=already_running "
                  "(другий екземпляр читача не створюється)".format(name))
            return False
        session_id = next_session_id()
        with session_registry_lock:
            active_session_ids.add(session_id)
        platform_sessions[name] = session_id
        thread = threading.Thread(target=worker, args=(session_id,),
                                  daemon=True, name="mc-" + name)
        platform_threads[name] = thread
        platform_set_state(name, PLATFORM_STATE_START, reason)
        thread.start()
    return True


def stop_platform(name, reason='stop', join_timeout=5.0, wait=True):
    """Відкликає session_id рівно цієї платформи. Інші платформи, Analytics,
    OBS Stream State Monitor, черга TTS і HTTP-сервер не зачіпаються.

    wait=True (за замовчуванням) чекає join_timeout, поки потік читача сам
    вийде - це важливо перед повторним запуском тієї ж платформи (інакше
    можуть існувати два читачі одночасно). wait=False лише інвалідовує
    session_id/стан і повертається одразу - потік (він daemon) сам вийде на
    наступній ітерації свого циклу і помре разом з процесом; використовується
    при повному завершенні роботи (script_unload), де ніхто вже не
    перезапускається і чекати нема сенсу."""
    with platform_lock:
        session_id = platform_sessions.pop(name, None)
        thread = platform_threads.pop(name, None)
        if session_id is not None:
            with session_registry_lock:
                active_session_ids.discard(session_id)
        platform_set_state(name, PLATFORM_STATE_STOPPED, reason)
    if wait and thread and thread.is_alive() and thread is not threading.current_thread():
        # Даємо завислому читачеві час коректно вийти, перш ніж створювати новий.
        thread.join(timeout=join_timeout)
    return True


def restart_platform(name, reason='manual_restart'):
    """Ізольований перезапуск ОДНІЄЇ платформи."""
    print("[Recovery] platform={} reason={} action=reconnect_platform_only".format(
        name, reason))
    platform_set_state(name, PLATFORM_STATE_RECONNECTING, reason)
    stop_platform(name, reason=reason)
    return start_platform(name, reason=reason)


def start_all_platforms(reason='run_services'):
    for name in PLATFORM_START_ORDER:
        try:
            start_platform(name, reason=reason)
        except Exception as e:
            print("[Recovery] platform={} reason=start_failed:{} "
                  "action=isolated_skip".format(name, e))


def stop_all_platforms(reason='kill_services', wait=True, join_timeout=5.0):
    if not wait:
        # Повне завершення роботи: інвалідовуємо стан миттєво і не чекаємо
        # жодного потоку - вони daemon і самі підуть.
        for name in list(PLATFORM_START_ORDER):
            try:
                stop_platform(name, reason=reason, wait=False)
            except Exception as e:
                print("[Recovery] platform={} reason=stop_failed:{} "
                      "action=isolated_skip".format(name, e))
        return
    # Інвалідуємо всі платформи одразу (швидко, без очікування),
    # а потім чекаємо на живі потоки ПАРАЛЕЛЬНО - максимум join_timeout
    # разом на всі, а не на кожну платформу окремо.
    threads_to_join = []
    for name in list(PLATFORM_START_ORDER):
        try:
            with platform_lock:
                session_id = platform_sessions.pop(name, None)
                thread = platform_threads.pop(name, None)
                if session_id is not None:
                    with session_registry_lock:
                        active_session_ids.discard(session_id)
                platform_set_state(name, PLATFORM_STATE_STOPPED, reason)
            if thread and thread.is_alive() and thread is not threading.current_thread():
                threads_to_join.append(thread)
        except Exception as e:
            print("[Recovery] platform={} reason=stop_failed:{} "
                  "action=isolated_skip".format(name, e))
    if not threads_to_join:
        return
    deadline = time.monotonic() + join_timeout
    for thread in threads_to_join:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        thread.join(timeout=remaining)


# ---------------------------------------------------------------------------
# ГАРЯЧЕ ЗАСТОСУВАННЯ НАЛАШТУВАНЬ (hot-apply)
# ---------------------------------------------------------------------------
# Раніше будь-яке збереження налаштувань (навіть коли музичний плеєр
# відправляв самий лише music_folder_path) викликало
# _restart_services_after_settings_change() -> kill_services() + run_services().
# Це вбивало ВСІ читачі чату, аналітику, монітор трансляції та HTTP-сервер,
# заново відправляло "ТРАНСЛЯЦІЮ РОЗПОЧАТО!" і (через очищення дедуплікації)
# призводило до повторного озвучення старих повідомлень.
# Тепер config читається наживо, а перезапускається лише конкретна підсистема.

HOT_HTTP_KEYS = ("dock_port", "allow_network_access")
HOT_ANALYTICS_KEYS = ("analytics_enabled",)
HOT_BLACKLIST_KEYS = ("blacklist", "blacklist_action")
HOT_MUSIC_KEYS = ("music_folder_path",)


def restart_http_server(reason='settings_changed'):
    """Перезапускає ТІЛЬКИ HTTP-сервер. НІКОЛИ не викликати з потоку самого
    обробника запиту - сервер не зможе завершити власний запит (дедлок)."""
    global server_instance, server_thread, PORT
    print("[Recovery] subsystem=http_server reason={} action=restart_http_only".format(reason))
    if server_instance:
        try:
            server_instance.shutdown()
            server_instance.server_close()
        except Exception:
            pass
        server_instance = None
    try:
        PORT = int(config.get("dock_port", 8080) or 8080)
    except (TypeError, ValueError):
        PORT = 8080
    try:
        bind_host = '0.0.0.0' if config.get('allow_network_access') else '127.0.0.1'
        server_instance = SafeHTTPServer((bind_host, PORT), EngineHandler)
        server_thread = threading.Thread(target=server_instance.serve_forever, daemon=True)
        server_thread.start()
        print("[MultiChat] HTTP сервер перезапущено на {}:{}".format(bind_host, PORT))
        return True
    except Exception as e:
        print("[MultiChat] Помилка перезапуску HTTP сервера: {}".format(e))
        return False


def restart_analytics_subsystem(reason='settings_changed'):
    """Стартує/зупиняє ТІЛЬКИ аналітику."""
    global analytics_manager
    print("[Recovery] subsystem=analytics reason={} action=restart_analytics_only".format(reason))
    if analytics_manager:
        try:
            analytics_manager.stop()
        except Exception as e:
            print("[Analytics] Error stopping: {}".format(e))
        analytics_manager = None
    if config.get("analytics_enabled", True):
        try:
            analytics_manager = LiveAnalyticsManager(config)
            analytics_manager.start()
            print("[Analytics] ✅ LIVE Analytics перезапущено")
        except Exception as e:
            print("[Analytics] Помилка запуску Analytics: {}".format(e))
    return True


def restart_netmon_subsystem(reason='settings_changed'):
    """Стартує/зупиняє ТІЛЬКИ монітор інтернету."""
    global network_monitor_manager
    print("[Recovery] subsystem=netmon reason={} action=restart_netmon_only".format(reason))
    if network_monitor_manager:
        try:
            network_monitor_manager.stop()
        except Exception as e:
            print("[NetMon] Error stopping: {}".format(e))
        network_monitor_manager = None
    if config.get("netmon_enabled", False):
        try:
            network_monitor_manager = NetworkMonitorManager(config)
            network_monitor_manager.start()
        except Exception as e:
            print("[NetMon] Помилка запуску моніторингу інтернету: {}".format(e))
    return True


def _mark_youtube_api_key_seen():
    """Фіксує поточний API-ключ як «вже бачений», щоб наступний
    script_update() не скидав стан квоти без причини."""
    global _youtube_api_key_fingerprint
    key = (config.get('yt_api_key', '') or '').strip()
    _youtube_api_key_fingerprint = hashlib.sha1(key.encode('utf-8')).hexdigest() if key else ''


def twitch_invalidate_identity_if_channel_changed(applied_keys):
    """Якщо збережений канал Twitch змінився - скидаємо кеш ID, щоб EventSub
    не підписувався на попереднього broadcaster_user_id."""
    if any(k in ('twitch_channel', 'twitch_irc_login') for k in (applied_keys or [])):
        twitch_id_cache_clear('змінено канал Twitch')


def platforms_for_config_keys(keys):
    """Повертає множину платформ, яких стосуються змінені ключі."""
    affected = set()
    for key in keys:
        for platform, prefixes in PLATFORM_CONFIG_PREFIXES.items():
            for prefix in prefixes:
                if key.startswith(prefix):
                    affected.add(platform)
                    break
    return affected


def apply_settings_hot(applied_keys, reason='settings_changed'):
    """Застосовує змінені налаштування БЕЗ глобального перезапуску.

    НІКОЛИ не викликає run_services() / kill_services().
    Викликати з окремого потоку (не з потоку HTTP-обробника).
    """
    keys = [k for k in (applied_keys or [])]
    actions = []
    try:
        if any(k in keys for k in HOT_BLACKLIST_KEYS):
            reload_blacklist_words()
            actions.append("blacklist")

        twitch_invalidate_identity_if_channel_changed(keys)

        if any(k in keys for k in HOT_ANALYTICS_KEYS):
            restart_analytics_subsystem(reason)
            actions.append("analytics")

        if 'yt_api_key' in keys:
            youtube_quota_clear('api_key_changed')
            _mark_youtube_api_key_seen()
            actions.append("youtube_quota_state")

        if any(k.startswith("netmon_") for k in keys):
            restart_netmon_subsystem(reason)
            actions.append("netmon")

        if any(k in keys for k in HOT_MUSIC_KEYS):
            try:
                music_scan_playlist()
                actions.append("music_playlist")
            except Exception as e:
                print("[Music] Помилка пересканування плейліста: {}".format(e))

        for platform in sorted(platforms_for_config_keys(keys)):
            try:
                restart_platform(platform, reason=reason)
                actions.append("platform:" + platform)
            except Exception as e:
                print("[Recovery] platform={} reason={} action=restart_failed error={}".format(
                    platform, reason, e))

        # HTTP-сервер останнім: після нього змінюється порт/адреса панелі.
        if any(k in keys for k in HOT_HTTP_KEYS):
            restart_http_server(reason)
            actions.append("http_server")
    except Exception as e:
        print("[MultiChat] Помилка гарячого застосування налаштувань: {}".format(e))

    if actions:
        print("[Settings] Гаряче застосування: змінено {} ключ(ів), перезапущено: {}".format(
            len(keys), ", ".join(actions)))
    else:
        print("[Settings] Гаряче застосування: змінено {} ключ(ів), перезапуск не потрібен "
              "(значення читаються наживо)".format(len(keys)))
    return actions


def run_services():
    global server_instance, server_thread, threads, global_session_id, analytics_manager, network_monitor_manager, PORT
    # global_session_id залишено лише як лічильник поколінь для діагностики.
    # Життям воркерів керують ІНДИВІДУАЛЬНІ session_id з active_session_ids.
    global_session_id += 1
    restore_external_configuration()
    apply_config_side_effects()
    async_runtime.start()

    if server_instance:
        try:
            server_instance.shutdown()
            server_instance.server_close()
        except Exception:
            pass
        server_instance = None

    try:
        PORT = int(config.get("dock_port", 8080) or 8080)
    except (TypeError, ValueError):
        PORT = 8080
    try:
        bind_host = '0.0.0.0' if config.get('allow_network_access') else '127.0.0.1'
        server_instance = SafeHTTPServer((bind_host, PORT), EngineHandler)
        server_thread = threading.Thread(target=server_instance.serve_forever, daemon=True)
        server_thread.start()
        print("[MultiChat] HTTP сервер запущено на {}:{}".format(bind_host, PORT))
        print("[MultiChat] ⚙️ Панель налаштувань: http://127.0.0.1:{}/settings".format(PORT))
        if config.get('allow_network_access'):
            print("[MultiChat] 🌐 LAN-доступ до адмінки: http://{}:{}/".format(get_lan_ip(), PORT))
    except Exception as e:
        print("[MultiChat] Помилка запуску HTTP сервера: {}".format(e))

    try:
        ensure_tts_browser_source()
    except Exception as e:
        print("[MultiChat] [TTS] Помилка ініціалізації OBS audio source: {}".format(e))

    if config.get("analytics_enabled", True):
        try:
            analytics_manager = LiveAnalyticsManager(config)
            analytics_manager.start()
            print("[Analytics] ✅ LIVE Analytics запущено")
        except Exception as e:
            print("[Analytics] Помилка запуску Analytics: {}".format(e))

    if config.get("netmon_enabled", False):
        try:
            network_monitor_manager = NetworkMonitorManager(config)
            network_monitor_manager.start()
        except Exception as e:
            print("[NetMon] Помилка запуску моніторингу інтернету: {}".format(e))
    else:
        network_monitor_manager = None

    if config.get("music_enabled", False) and config.get("music_duck_on_alert", True) and (config.get("music_duck_source_names") or "").strip():
        try:
            source_audio_duck_monitor.start()
        except Exception as e:
            print("[Music Duck] Помилка запуску відстеження звуку джерел: {}".format(e))

    # Кожна платформа стартує через наглядача і отримує ВЛАСНИЙ session_id.
    # start_platform() ідемпотентний, тож повторний виклик не створить
    # другого читача тієї самої платформи.
    start_all_platforms(reason='run_services')


def kill_services(wait_platforms=True):
    global server_instance, global_session_id, analytics_manager, network_monitor_manager
    global_session_id += 1
    stop_all_platforms(reason='kill_services', wait=wait_platforms)
    async_runtime.stop()

    if analytics_manager:
        try:
            analytics_manager.stop()
            analytics_manager = None
            print("[Analytics] ⚫ Analytics зупинено")
        except Exception as e:
            print("[Analytics] Error stopping: {}".format(e))

    if network_monitor_manager:
        try:
            network_monitor_manager.stop()
            network_monitor_manager = None
        except Exception as e:
            print("[NetMon] Error stopping: {}".format(e))

    if source_audio_duck_monitor.is_running:
        try:
            source_audio_duck_monitor.stop()
        except Exception as e:
            print("[Music Duck] Error stopping: {}".format(e))

    if server_instance:
        try:
            server_instance.shutdown()
            server_instance.server_close()
        except:
            pass


def script_description():
    upd_url = "https://github.com/CriticalHit-one/Mult/blob/main/MUltchat.py"
    upd_html = ('<br><b>ОНОВЛЕННЯ СКРИПТА:</b> <a href="{0}">{0}</a><br>'.format(upd_url))
    lan_html = ""
    if config.get('allow_network_access'):
        lan_ip = get_lan_ip()
        lan_html = (
            "<br><b>ДОСТУП ПО МЕРЕЖІ (LAN):</b> замініть <code>127.0.0.1</code> на "
            "<code>{}</code> у будь-якій адресі вище — наприклад, "
            "<code>http://{}:{}/</code> з телефона.<br>".format(lan_ip, lan_ip, PORT)
        )
    return (
        "<b>MultiChat Ultimate + LIVE Analytics</b><br><i>Автор: Critical Hit</i><br><br>"

        "<b>ПАНЕЛІ (додавати як Custom Browser Dock: View → Docks → Custom Browser Docks...)</b><br>"
        "• <b>⚙️ Налаштування:</b> <code>http://127.0.0.1:{port}/settings</code><br>"
        "• <b>🖥️ Адмінка (чат, модерація, статистика):</b> <code>http://127.0.0.1:{port}/</code><br>"
        "• <b>🎵 Музичний плеєр (керування):</b> <code>http://127.0.0.1:{port}/music_player</code><br>"
        "• <b>📊 Історія глядачів TikTok:</b> <code>http://127.0.0.1:{port}/tiktok_history</code><br><br>"

        "<b>ДЖЕРЕЛА В СЦЕНУ (додавати як Browser Source)</b><br>"
        "• <b>💬 Оверлей чату:</b> <code>http://127.0.0.1:{port}/overlay</code><br>"
        "&nbsp;&nbsp;<i>Режим «без плашки» (лише текст + позначка платформи) вмикається галочкою в налаштуваннях — той самий URL.</i><br>"
        "• <b>🔊 Вивід звуку TTS:</b> <code>http://127.0.0.1:{port}/tts_audio</code> "
        "(обов'язкове джерело, щоб озвучку чули глядачі; зніміть галочку "
        "«Вимкнути джерело, коли воно не відображається»)<br>"
        "• <b>👥 LIVE-віджет глядачів:</b> <code>http://127.0.0.1:{port}/analytics/widget</code><br>"
        "• <b>❤️ Топ-10 за лайками (TikTok):</b> <code>http://127.0.0.1:{port}/top_likes_widget</code><br>"
        "• <b>🔔 Віджет алертів (підписки, донати, подарунки):</b> "
        "<code>http://127.0.0.1:{port}/event_alerts/widget</code> "
        "(стара адреса <code>/tiktok_alerts/widget</code> теж працює)<br>"
        "• <b>🎁 Оверлей розіграшу (Giveaway):</b> <code>http://127.0.0.1:{port}/giveaway/overlay</code><br>"
        "• <b>🎵 Музичний плеєр (звук у трансляцію):</b> <code>http://127.0.0.1:{port}/music_player</code> "
        "— додайте ДРУГИМ джерелом у сцену, щоб музику чули глядачі; "
        "у «Розширених властивостях аудіо» оберіть потрібні доріжки<br><br>"

        "<b>OAuth-авторизація (відкривати у браузері)</b><br>"
        "• <b>Twitch:</b> <code>http://127.0.0.1:{port}/auth/twitch/start</code><br>"
        "• <b>Kick:</b> <code>http://127.0.0.1:{port}/auth/kick/start</code><br>"
        "{lan}"
        "{upd}"
    ).format(port=PORT, lan=lan_html, upd=upd_html)


def open_local_url_in_browser(url):
    try:
        if webbrowser.open(url, new=2, autoraise=True):
            return True
    except Exception as e:
        print("[OAuth] webbrowser.open failed for {}: {}".format(url, e))
    try:
        if os.name == 'nt':
            os.startfile(url)
            return True
    except Exception as e:
        print("[OAuth] os.startfile failed for {}: {}".format(url, e))
    return False


def open_twitch_auth_button(props, prop):
    ok = open_local_url_in_browser("http://localhost:8080/auth/twitch/start")
    if not ok:
        print("[OAuth] Open manually: http://localhost:8080/auth/twitch/start")
    return True


def open_kick_auth_button(props, prop):
    ok = open_local_url_in_browser("http://127.0.0.1:8080/auth/kick/start")
    if not ok:
        print("[OAuth] Open manually: http://127.0.0.1:8080/auth/kick/start")
    return True


def script_properties():
    """
    Панель Tools -> Scripts у самому OBS тепер відповідає лише за
    порт локального сервера. Усі інші налаштування (YouTube, TikTok,
    Twitch, Kick, TTS, модерація чату, аналітика,
    LIVE-віджет, Giveaway, Stream Notify) перенесені у веб-панель, яка
    відкривається за адресою http://127.0.0.1:<порт>/settings і
    додається в OBS як Custom Browser Dock (View -> Docks -> Custom
    Browser Docks...). Текст нижче — довідник по кожному розділу тієї
    панелі: що і звідки вписувати для повноцінної роботи.
    """
    props = obs.obs_properties_create()
    port_value = int(config.get("dock_port", 8080) or 8080)
    info = obs.obs_properties_add_text(props, "_settings_info", " ", obs.OBS_TEXT_INFO)
    obs.obs_property_set_long_description(
        info,
        "ЯК ПІДКЛЮЧИТИ ПАНЕЛЬ НАЛАШТУВАНЬ:\n"
        "1. Збережіть цей скрипт хоча б раз, щоб запустився локальний сервер.\n"
        "2. В OBS: View -> Docks -> Custom Browser Docks...\n"
        "3. Будь-яка назва, адреса: http://127.0.0.1:{port}/settings\n"
        "4. Панель закріпиться в інтерфейсі OBS і запам'ятає своє місце.\n\n"
        "ДОВІДНИК ПО РОЗДІЛАХ ПАНЕЛІ (що і звідки вписувати):\n\n"

        "Загальне та мережа\n"
        "- Порт — міняти лише при конфлікті з іншою програмою.\n"
        "- Дозволити доступ по мережі — вмикати, якщо треба відкривати "
        "панель/оверлеї з телефону чи іншого ПК у тій самій Wi-Fi мережі.\n"
        "- Активні платформи — які чати взагалі підключати цього стріму.\n\n"

        "YouTube\n"
        "- Канал: @handle, ID каналу або посилання на нього.\n"
        "- API ключ: console.cloud.google.com -> створити проєкт -> "
        "увімкнути 'YouTube Data API v3' -> Credentials -> API key. "
        "Без ключа не працює пошук активної трансляції й аналітика переглядів.\n\n"

        "TikTok\n"
        "- Ім'я користувача TikTok (без @).\n"
        "- Euler Stream Sign API ключ (необов'язково, але бажано): "
        "безкоштовно на eulerstream.com. Без нього частіше трапляються "
        "помилки підключення SIGN_NOT_200.\n\n"

        "Twitch\n"
        "- Канал, IRC логін і OAuth токен бота (для читання чату) — токен "
        "можна отримати через twitchtokengenerator.com або аналогічний сервіс.\n"
        "- Client ID / Client Secret — dev.twitch.tv/console -> Register "
        "Your Application. Після заповнення натисніть кнопку авторизації "
        "у розділі Twitch веб-панелі (підписки/бали/рейди/бітси).\n\n"

        "Kick\n"
        "- Посилання на канал.\n"
        "- Client ID / Client Secret / Webhook Secret — dev.kick.com. "
        "Після заповнення так само авторизуйтесь кнопкою в панелі.\n\n"

        "TTS та голоси\n"
        "- Рушій: Google Translate (за замовчуванням), Браузерний, "
        "Windows SAPI як резерв.\n"

        "Модерація чату / Оверлей чату\n"
        "- Просто вмикайте потрібні фільтри (анти-капс, чорний список слів "
        "тощо) і підбирайте кольори/шрифт оверлею під тему стріму.\n\n"

        "Аналітика / LIVE-віджет\n"
        "- Інтервал оновлення, які платформи враховувати в лічильнику "
        "глядачів, режим віджета (compact/full).\n\n"

        "Giveaway (Telegram)\n"
        "- Bot Token: створити бота через @BotFather в Telegram, "
        "скопіювати токен.\n"
        "- Chat ID: ID каналу/групи, куди бот публікуватиме пост розіграшу "
        "(дізнатись, наприклад, через @userinfobot). Бот має бути "
        "адміністратором цього каналу/групи з правом публікації.\n"
        "- Приз, текст анонсу, картинка, тривалість — заповнюються перед "
        "кожним розіграшем, кнопки Старт/Стоп там же в панелі.\n\n"

        "Stream Notify\n"
        "- Telegram Token/Chat ID — той самий бот, що й для Giveaway, або "
        "окремий.\n"
        "- Discord Webhook: у Discord -> Налаштування каналу -> "
        "Інтеграції -> Вебхуки -> Створити.\n"
        "- YouTube Channel ID і Twitch Client ID/Secret/Username — лише "
        "якщо потрібен автопошук VOD-запису після завершення стріму.\n"
        "- Посилання на всі ваші платформи — для кнопок під постом.\n"
        "- Не забудьте увімкнути 'Модуль увімкнено' в потрібних розділах "
        "(Giveaway/Stream Notify) — інакше вони просто не працюватимуть.".format(port=port_value)
    )
    obs.obs_properties_add_int(props, "dock_port", "🔌 Порт локального сервера (панель налаштувань і оверлеї)", 1024, 65535, 1)
    return props


def script_defaults(settings):
    obs.obs_data_set_default_int(settings, "dock_port", 8080)

def script_update(settings):
    """
    Тепер нативна панель OBS відповідає лише за dock_port — решта
    налаштувань (усі 150+ полів) керуються через веб-панель
    http://127.0.0.1:<port>/settings і зберігаються в config/*.json
    (див. persist_runtime_configuration / restore_external_configuration).
    Це усуває дублювання джерела правди: раніше settings-об'єкт OBS і
    JSON-файли могли розходитись між собою.
    """
    global config
    try:
        config["dock_port"] = int(obs.obs_data_get_int(settings, "dock_port") or 8080)
    except (TypeError, ValueError):
        config["dock_port"] = 8080
    persist_runtime_configuration()
    kill_services()
    # НЕ скидаємо стан квоти беззастережно: OBS викликає script_update() сам,
    # і сліпе скидання одразу відновлювало дорогі запити search.list.
    youtube_quota_clear_if_key_changed()
    time.sleep(0.1)
    run_services()
    try:
        music_restore_last_session()
    except Exception as e:
        print("[MultiChat] [Music] Не вдалося відновити стан плеєра: {}".format(e))

hotkey_gw_start_id = obs.OBS_INVALID_HOTKEY_ID
hotkey_gw_stop_id = obs.OBS_INVALID_HOTKEY_ID


def on_hotkey_giveaway_start(pressed):
    # OBS hotkey callbacks fire on both key-down (pressed=True) and key-up
    # (pressed=False); only react on key-down, otherwise the giveaway would
    # start and immediately try to start again on key release.
    if not pressed:
        return
    try:
        result = giveaway_start()
        if isinstance(result, dict) and not result.get("ok", True):
            log_status("Giveaway", "Хоткей запуску: {}".format(result.get("error", "невідома помилка")))
    except Exception as e:
        log_error("Giveaway", "Хоткей запуску розіграшу впав: {}".format(e))


def on_hotkey_giveaway_stop(pressed):
    if not pressed:
        return
    try:
        result = giveaway_stop()
        if isinstance(result, dict) and not result.get("ok", True):
            log_status("Giveaway", "Хоткей зупинки: {}".format(result.get("error", "невідома помилка")))
    except Exception as e:
        log_error("Giveaway", "Хоткей зупинки розіграшу впав: {}".format(e))


def script_load(settings):
    global hotkey_gw_start_id, hotkey_gw_stop_id
    restore_external_configuration()
    # Тепер config уже містить music_folder_path — можна відновити плеєр
    try:
        load_music_runtime_state()
        music_restore_last_session()
    except Exception as e:
        print("[MultiChat] [Music] Не вдалося відновити стан плеєра: {}".format(e))
    try:
        obs.obs_frontend_add_event_callback(on_obs_frontend_event)
    except:
        pass
    try:
        ensure_tts_browser_source()
    except Exception as e:
        print("[MultiChat] [TTS] Не вдалося створити OBS audio source під час завантаження: {}".format(e))

    hotkey_gw_start_id = obs.obs_hotkey_register_frontend(
        "multichat_giveaway_start", "MultiChat Giveaway: Запустити розіграш", on_hotkey_giveaway_start
    )
    hotkey_gw_stop_id = obs.obs_hotkey_register_frontend(
        "multichat_giveaway_stop", "MultiChat Giveaway: Зупинити розіграш", on_hotkey_giveaway_stop
    )
    a = obs.obs_data_get_array(settings, "hotkey_gw_start")
    obs.obs_hotkey_load(hotkey_gw_start_id, a)
    obs.obs_data_array_release(a)
    a = obs.obs_data_get_array(settings, "hotkey_gw_stop")
    obs.obs_hotkey_load(hotkey_gw_stop_id, a)
    obs.obs_data_array_release(a)

    # Єдине місце, де пам'ять дедуплікації скидається: справжнє завантаження
    # скрипта. Внутрішній перезапуск сервісів її більше не торкається.
    dedup_reset_all()

    obs.timer_add(sn_schedule_tick, 15000)
    # Таймер розіграшу вішаємо один раз тут, у головному потоці OBS.
    # Поки розіграш неактивний, giveaway_tick виходить на першому ж рядку.
    obs.timer_add(giveaway_tick, 1000)
    # Статистику пропущених кадрів OBS можна читати лише з головного потоку -
    # тому це окремий таймер OBS, а не робота NetMon-потоку.
    obs.timer_add(netmon_obs_stats_tick, 2000)
    # Список джерел для чекбоксів дакінгу музики - теж лише з головного потоку.
    obs_sources_list_tick()
    obs.timer_add(obs_sources_list_tick, 5000)


def script_save(settings):
    a = obs.obs_hotkey_save(hotkey_gw_start_id)
    obs.obs_data_set_array(settings, "hotkey_gw_start", a)
    obs.obs_data_array_release(a)
    a = obs.obs_hotkey_save(hotkey_gw_stop_id)
    obs.obs_data_set_array(settings, "hotkey_gw_stop", a)
    obs.obs_data_array_release(a)


def script_unload():
    try:
        music_remember_playback(force=True)
    except Exception:
        pass
    try:
        save_music_runtime_state(force=True)
    except Exception as e:
        print("[MultiChat] [Music] Не вдалося зберегти стан плеєра: {}".format(e))
    # wait_platforms=False: скрипт вивантажується остаточно, нічого більше
    # не перезапускається, тож чекати join() кожного потоку читача сенсу
    # немає - раніше саме тут OBS могло "зависати" на закритті.
    kill_services(wait_platforms=False)
    if giveaway_state["active"]:
        giveaway_stop()