from __future__ import annotations 

import calendar 
import html 
import json 
import os 
import re 
import sqlite3 
import tempfile 
import threading 
import time 
import uuid 
from collections import Counter ,defaultdict 
from dataclasses import dataclass 
from datetime import datetime ,timedelta ,timezone 
from typing import Optional 
from zoneinfo import ZoneInfo 

import requests 
import speech_recognition as sr 
import telebot 
from pydub import AudioSegment 
from telebot import types 

try :
    from dotenv import load_dotenv 
    load_dotenv ()
except Exception :
    pass 


DEBUG =True 

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
YANDEX_API_KEY = os.getenv("YANDEX_API_KEY", "").strip()
YANDEX_FOLDER_ID = os.getenv("YANDEX_FOLDER_ID", "").strip()
YANDEX_MODEL_URI =os .getenv ("YANDEX_MODEL_URI","").strip ()or (
f"gpt://{YANDEX_FOLDER_ID }/yandexgpt-lite/latest"if YANDEX_FOLDER_ID else ""
)

APP_DIR =os .path .dirname (os .path .abspath (__file__ ))if "__file__"in globals ()else os .getcwd ()
DB_PATH =os .path .join (APP_DIR ,"denis_school_ip_clean_v4.sqlite3")
YANDEX_ENDPOINT =os .getenv ("YANDEX_ENDPOINT","").strip ()or "https://llm.api.cloud.yandex.net/foundationModels/v1/completion"

DETAILED_DATA_RETENTION_DAYS =62
SUMMARY_EVENT_TYPES ={"created","done","not_done","snoozed","deleted"}
PARSE_SUMMARY_METRICS ={"parse_local","parse_yandex","parse_yandex_reparse"}



DEFAULT_TIMEZONE_NAME ="Europe/Moscow"
DEFAULT_TIMEZONE_TITLE ="🇷🇺 Москва — МСК (UTC+3)"

TIMEZONE_OPTIONS ={
"tz:kaliningrad":("🇷🇺 Калининград — МСК-1 (UTC+2)","Europe/Kaliningrad"),
"tz:moscow":("🇷🇺 Москва — МСК (UTC+3)","Europe/Moscow"),
"tz:samara":("🇷🇺 Самара — МСК+1 (UTC+4)","Europe/Samara"),
"tz:yekaterinburg":("🇷🇺 Екатеринбург — МСК+2 (UTC+5)","Asia/Yekaterinburg"),
"tz:omsk":("🇷🇺 Омск — МСК+3 (UTC+6)","Asia/Omsk"),
"tz:krasnoyarsk":("🇷🇺 Красноярск — МСК+4 (UTC+7)","Asia/Krasnoyarsk"),
"tz:irkutsk":("🇷🇺 Иркутск — МСК+5 (UTC+8)","Asia/Irkutsk"),
"tz:yakutsk":("🇷🇺 Якутск — МСК+6 (UTC+9)","Asia/Yakutsk"),
"tz:vladivostok":("🇷🇺 Владивосток — МСК+7 (UTC+10)","Asia/Vladivostok"),
"tz:magadan":("🇷🇺 Магадан — МСК+8 (UTC+11)","Asia/Magadan"),
"tz:kamchatka":("🇷🇺 Камчатка — МСК+9 (UTC+12)","Asia/Kamchatka"),
"tz:utc":("🌍 UTC — базовое мировое время","UTC"),
}

CATEGORY_TITLES ={
"study":"📚 Учёба",
"exam":"📝 Контрольные и экзамены",
"meeting":"👥 Встречи",
"deadline":"⏰ Дедлайны",
"personal":"🏠 Личное",
"other":"📌 Другое",
}
CATEGORY_BUTTONS =[
("📚 Учёба","study"),
("📝 Контрольные и экзамены","exam"),
("👥 Встречи","meeting"),
("⏰ Дедлайны","deadline"),
("🏠 Личное","personal"),
("📌 Другое","other"),
]

PRIORITY_TITLES ={ "very_high":"⚡ Очень важно", "high":"🔴 Важно", "medium":"🟡 Обычно", "low":"🟢 Не важно" }
PRIORITY_BUTTONS =[("⚡ Очень важно","very_high"),("🔴 Важно","high"),("🟡 Обычно","medium"),("🟢 Не важно","low")]
PRIORITY_INTERVALS_SECONDS ={ "very_high":40 ,"high":60 ,"medium":300 ,"low":600 }
PRIORITY_INTERVAL_COLUMNS ={
"very_high":"priority_very_high_interval_seconds",
"high":"priority_high_interval_seconds",
"medium":"priority_medium_interval_seconds",
"low":"priority_low_interval_seconds",
}
PRIORITY_INTERVAL_MIN_SECONDS =5
PRIORITY_INTERVAL_MAX_SECONDS =30 * 60
PRIORITY_MAX_NOTIFY_COUNT ={"very_high":15 ,"high":10 ,"medium":10 ,"low":10 }

TIME_WORD_DEFAULTS ={"morning":"08:00","day":"13:00","evening":"18:00","night":"22:00"}
TIME_WORD_TITLES ={"morning":"🌅 Утро","day":"☀️ День","evening":"🌆 Вечер","night":"🌙 Ночь"}
TIME_WORD_COLUMNS ={"morning":"morning_time","day":"day_time","evening":"evening_time","night":"night_time"}

INTERVAL_NOTIFY_ATTEMPTS =5
INTERVAL_NOTIFY_INTERVAL_SECONDS =60
REMINDER_KIND_NORMAL ="normal"
REMINDER_KIND_INTERVAL ="interval"
REMINDER_KIND_BREAK_SINGLE ="break_single"
REMINDER_KIND_BREAK_EACH ="break_each"
REMINDER_KIND_LESSON_SINGLE ="lesson_single"
REMINDER_KIND_LESSON_EACH ="lesson_each"
DEFAULT_FIRST_LESSON_START ="08:30"
CUSTOM_BREAK_SELECTED_DAYS :dict [int ,set [int ]]={}

PRIORITY_MAX_COUNT_COLUMNS ={
"very_high":"priority_very_high_max_notify_count",
"high":"priority_high_max_notify_count",
"medium":"priority_medium_max_notify_count",
"low":"priority_low_max_notify_count",
}
PRIORITY_MAX_COUNT_MIN =1
PRIORITY_MAX_COUNT_MAX =30


def max_notify_count_for_priority (priority :str ,user_id :int =0 )->int :
    if user_id:
        return get_user_priority_max_count (int (user_id ),priority )
    return PRIORITY_MAX_NOTIFY_COUNT .get (priority ,10 )


def notify_interval_seconds_for_priority (priority :str ,user_id :int =0 )->int :
    if user_id:
        return get_user_priority_interval_seconds (int (user_id ),priority )
    return PRIORITY_INTERVALS_SECONDS .get (priority ,300 )

REPEAT_OPTIONS =[
("Один раз","none"),
("Каждый день","daily"),
("Каждую неделю","weekly"),
("Каждый месяц","monthly"),
("Каждый год","yearly"),
("По будням","weekdays"),
("По выходным","weekends"),
("Выбрать дни недели","custom_weekdays"),
("Каждые N дней","every_n_days"),
]

RESULT_TITLES ={
"done":"Выполнено",
"not_done":"Не выполнено",
"snoozed":"Перенесено",
"deleted":"Удалено",
}

WEEKDAYS ={0 :"понедельник",1 :"вторник",2 :"среда",3 :"четверг",4 :"пятница",5 :"суббота",6 :"воскресенье"}
WEEKDAY_SHORT ={0 :"пн",1 :"вт",2 :"ср",3 :"чт",4 :"пт",5 :"сб",6 :"вс"}
DEFAULT_SCHOOL_BREAK_RANGES =[("09:15","09:25"),("10:10","10:20"),("11:05","11:15"),("12:00","12:20"),("13:05","13:25"),("14:10","14:20"),("15:05","15:15"),("16:00","16:20")]
DEFAULT_SCHOOL_BREAK_WEEKDAYS ={0,1,2,3,4,5}
MONTHS_GENITIVE ={1 :"января",2 :"февраля",3 :"марта",4 :"апреля",5 :"мая",6 :"июня",7 :"июля",8 :"августа",9 :"сентября",10 :"октября",11 :"ноября",12 :"декабря"}


def require_config ()->None :
    missing =[]
    if not TELEGRAM_BOT_TOKEN :
        missing .append ("TELEGRAM_BOT_TOKEN")
    if not YANDEX_API_KEY :
        missing .append ("YANDEX_API_KEY")
    if not YANDEX_MODEL_URI :
        missing .append ("YANDEX_MODEL_URI или YANDEX_FOLDER_ID")
    if missing :
        raise RuntimeError ("Не заполнены настройки: "+", ".join (missing ))


require_config ()
bot =telebot .TeleBot (TELEGRAM_BOT_TOKEN ,parse_mode ="HTML")
recognizer =sr .Recognizer ()

SCREEN_MESSAGES :dict [int ,dict ]={}
GREETING_MESSAGES :dict [int ,dict ]={}
HELP_DOCUMENT_MESSAGES :dict [int ,dict ]={}
SCREEN_STACK :dict [int ,list [dict ]]={}
INPUT_STATES :dict [int ,dict ]={}
SESSIONS :dict [str ,dict ]={}
LAST_CLEANUP_DATE :Optional [str ]=None 

# Служебные message_id нужны только для аккуратной пересборки экрана.
# Историю не копим: храним только актуальные записи и чистим старые.
SERVICE_MESSAGE_RETENTION_DAYS =7
SERVICE_MESSAGE_MAX_ACTIVE_PER_CHAT =12
INTERVAL_DAY_MINUTES =24 * 60
INTERVAL_WEEK_MINUTES =7 * INTERVAL_DAY_MINUTES



# =========================================================
# База данных
# =========================================================

def get_db ()->sqlite3 .Connection :
    conn =sqlite3 .connect (DB_PATH ,check_same_thread =False )
    conn .row_factory =sqlite3 .Row 
    return conn 


def now_utc_str ()->str :
    return datetime .now (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")


def init_db ()->None :
    """
    Создаёт таблицы и обновляет старую базу.
    Исправляет старые обязательные поля local_remind_at / local_remind_date / local_remind_time.
    """
    conn =get_db ()
    cur =conn .cursor ()

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_user_settings (
            user_id INTEGER PRIMARY KEY,
            timezone_name TEXT NOT NULL DEFAULT 'Europe/Moscow',
            timezone_title TEXT NOT NULL DEFAULT '🇷🇺 Москва — МСК (UTC+3)',
            morning_time TEXT NOT NULL DEFAULT '08:00',
            day_time TEXT NOT NULL DEFAULT '13:00',
            evening_time TEXT NOT NULL DEFAULT '18:00',
            night_time TEXT NOT NULL DEFAULT '22:00',
            priority_very_high_interval_seconds INTEGER NOT NULL DEFAULT 40,
            priority_high_interval_seconds INTEGER NOT NULL DEFAULT 60,
            priority_medium_interval_seconds INTEGER NOT NULL DEFAULT 300,
            priority_low_interval_seconds INTEGER NOT NULL DEFAULT 600,
            priority_very_high_max_notify_count INTEGER NOT NULL DEFAULT 15,
            priority_high_max_notify_count INTEGER NOT NULL DEFAULT 10,
            priority_medium_max_notify_count INTEGER NOT NULL DEFAULT 10,
            priority_low_max_notify_count INTEGER NOT NULL DEFAULT 10,
            default_breaks_initialized INTEGER NOT NULL DEFAULT 0,
            updated_at_utc TEXT NOT NULL DEFAULT ''
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_reminders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL DEFAULT 0,
            topic TEXT NOT NULL DEFAULT 'Напоминание',
            reminder_text TEXT NOT NULL DEFAULT '',
            category TEXT NOT NULL DEFAULT 'other',
            priority TEXT NOT NULL DEFAULT 'medium',
            timezone_name TEXT NOT NULL DEFAULT 'Europe/Moscow',
            timezone_title TEXT NOT NULL DEFAULT '🇷🇺 Москва — МСК (UTC+3)',
            repeat_type TEXT NOT NULL DEFAULT 'none',
            repeat_value TEXT NOT NULL DEFAULT '',
            next_local_at TEXT NOT NULL DEFAULT '',
            next_utc_at TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'pending',
            notify_count INTEGER NOT NULL DEFAULT 0,
            max_notify_count INTEGER NOT NULL DEFAULT 10,
            active_trigger_local_at TEXT NOT NULL DEFAULT '',
            active_trigger_utc_at TEXT NOT NULL DEFAULT '',
            active_message_chat_id INTEGER NOT NULL DEFAULT 0,
            active_message_id INTEGER NOT NULL DEFAULT 0,
            next_notify_utc TEXT NOT NULL DEFAULT '',
            created_at_utc TEXT NOT NULL DEFAULT '',
            completed_at_utc TEXT NOT NULL DEFAULT '',
            parse_method TEXT NOT NULL DEFAULT '',
            yandex_reparse_used INTEGER NOT NULL DEFAULT 0
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_reminder_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            reminder_id INTEGER NOT NULL DEFAULT 0,
            user_id INTEGER NOT NULL DEFAULT 0,
            topic TEXT NOT NULL DEFAULT 'Напоминание',
            trigger_local_at TEXT NOT NULL DEFAULT '',
            trigger_utc_at TEXT NOT NULL DEFAULT '',
            result_status TEXT NOT NULL DEFAULT '',
            created_at_utc TEXT NOT NULL DEFAULT ''
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_users (
            user_id INTEGER PRIMARY KEY,
            username TEXT NOT NULL DEFAULT '',
            first_name TEXT NOT NULL DEFAULT '',
            last_name TEXT NOT NULL DEFAULT '',
            language_code TEXT NOT NULL DEFAULT '',
            first_seen_utc TEXT NOT NULL DEFAULT '',
            last_seen_utc TEXT NOT NULL DEFAULT '',
            messages_count INTEGER NOT NULL DEFAULT 0
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_analytics_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL DEFAULT 0,
            reminder_id INTEGER NOT NULL DEFAULT 0,
            event_type TEXT NOT NULL DEFAULT '',
            topic TEXT NOT NULL DEFAULT '',
            reminder_text TEXT NOT NULL DEFAULT '',
            reminder_local_at TEXT NOT NULL DEFAULT '',
            reminder_utc_at TEXT NOT NULL DEFAULT '',
            category TEXT NOT NULL DEFAULT '',
            priority TEXT NOT NULL DEFAULT '',
            repeat_type TEXT NOT NULL DEFAULT '',
            details TEXT NOT NULL DEFAULT '',
            created_at_utc TEXT NOT NULL DEFAULT ''
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_bot_service_messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL DEFAULT 0,
            chat_id INTEGER NOT NULL DEFAULT 0,
            message_id INTEGER NOT NULL DEFAULT 0,
            message_kind TEXT NOT NULL DEFAULT '',
            is_active INTEGER NOT NULL DEFAULT 1,
            created_at_utc TEXT NOT NULL DEFAULT '',
            removed_at_utc TEXT NOT NULL DEFAULT ''
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_summary_stats (
            metric TEXT PRIMARY KEY,
            value INTEGER NOT NULL DEFAULT 0
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_user_summary_stats (
            user_id INTEGER PRIMARY KEY,
            created INTEGER NOT NULL DEFAULT 0,
            done INTEGER NOT NULL DEFAULT 0,
            not_done INTEGER NOT NULL DEFAULT 0,
            snoozed INTEGER NOT NULL DEFAULT 0,
            deleted INTEGER NOT NULL DEFAULT 0
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_category_summary_stats (
            category TEXT PRIMARY KEY,
            value INTEGER NOT NULL DEFAULT 0
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_user_category_summary_stats (
            user_id INTEGER NOT NULL DEFAULT 0,
            category TEXT NOT NULL DEFAULT 'other',
            value INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY (user_id, category)
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_parse_usage_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL DEFAULT 0,
            parse_method TEXT NOT NULL DEFAULT '',
            created_at_utc TEXT NOT NULL DEFAULT ''
        )
    """)

    cur .execute ("""
        CREATE TABLE IF NOT EXISTS denis_v4_school_breaks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL DEFAULT 0,
            weekday INTEGER NOT NULL DEFAULT 0,
            break_index INTEGER NOT NULL DEFAULT 1,
            start_time TEXT NOT NULL DEFAULT '',
            end_time TEXT NOT NULL DEFAULT '',
            created_at_utc TEXT NOT NULL DEFAULT ''
        )
    """)

    def table_info (table_name :str )->list [sqlite3 .Row ]:
        cur .execute (f"PRAGMA table_info({table_name })")
        return cur .fetchall ()

    def existing_columns (table_name :str )->set [str ]:
        return {row [1 ]for row in table_info (table_name )}

    def ensure_column (table_name :str ,column_name :str ,column_sql :str )->None :
        if column_name not in existing_columns (table_name ):
            cur .execute (f"ALTER TABLE {table_name } ADD COLUMN {column_sql }")

    ensure_column ("denis_v4_user_settings","timezone_name","timezone_name TEXT NOT NULL DEFAULT 'Europe/Moscow'")
    ensure_column ("denis_v4_user_settings","timezone_title","timezone_title TEXT NOT NULL DEFAULT '🇷🇺 Москва — МСК (UTC+3)'")
    ensure_column ("denis_v4_user_settings","morning_time","morning_time TEXT NOT NULL DEFAULT '08:00'")
    ensure_column ("denis_v4_user_settings","day_time","day_time TEXT NOT NULL DEFAULT '13:00'")
    ensure_column ("denis_v4_user_settings","evening_time","evening_time TEXT NOT NULL DEFAULT '18:00'")
    ensure_column ("denis_v4_user_settings","night_time","night_time TEXT NOT NULL DEFAULT '22:00'")
    ensure_column ("denis_v4_user_settings","priority_very_high_interval_seconds","priority_very_high_interval_seconds INTEGER NOT NULL DEFAULT 40")
    ensure_column ("denis_v4_user_settings","priority_high_interval_seconds","priority_high_interval_seconds INTEGER NOT NULL DEFAULT 60")
    ensure_column ("denis_v4_user_settings","priority_medium_interval_seconds","priority_medium_interval_seconds INTEGER NOT NULL DEFAULT 300")
    ensure_column ("denis_v4_user_settings","priority_low_interval_seconds","priority_low_interval_seconds INTEGER NOT NULL DEFAULT 600")
    ensure_column ("denis_v4_user_settings","priority_very_high_max_notify_count","priority_very_high_max_notify_count INTEGER NOT NULL DEFAULT 15")
    ensure_column ("denis_v4_user_settings","priority_high_max_notify_count","priority_high_max_notify_count INTEGER NOT NULL DEFAULT 10")
    ensure_column ("denis_v4_user_settings","priority_medium_max_notify_count","priority_medium_max_notify_count INTEGER NOT NULL DEFAULT 10")
    ensure_column ("denis_v4_user_settings","priority_low_max_notify_count","priority_low_max_notify_count INTEGER NOT NULL DEFAULT 10")
    ensure_column ("denis_v4_user_settings","default_breaks_initialized","default_breaks_initialized INTEGER NOT NULL DEFAULT 0")
    ensure_column ("denis_v4_user_settings","updated_at_utc","updated_at_utc TEXT NOT NULL DEFAULT ''")

    cur .execute ("UPDATE denis_v4_user_settings SET morning_time='08:00' WHERE morning_time IS NULL OR morning_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET day_time='13:00' WHERE day_time IS NULL OR day_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET evening_time='18:00' WHERE evening_time IS NULL OR evening_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET night_time='22:00' WHERE night_time IS NULL OR night_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_very_high_interval_seconds=40 WHERE priority_very_high_interval_seconds IS NULL OR priority_very_high_interval_seconds<5 OR priority_very_high_interval_seconds>1800")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_high_interval_seconds=60 WHERE priority_high_interval_seconds IS NULL OR priority_high_interval_seconds<5 OR priority_high_interval_seconds>1800")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_medium_interval_seconds=300 WHERE priority_medium_interval_seconds IS NULL OR priority_medium_interval_seconds<5 OR priority_medium_interval_seconds>1800")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_low_interval_seconds=600 WHERE priority_low_interval_seconds IS NULL OR priority_low_interval_seconds<5 OR priority_low_interval_seconds>1800")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_very_high_max_notify_count=15 WHERE priority_very_high_max_notify_count IS NULL OR priority_very_high_max_notify_count<1 OR priority_very_high_max_notify_count>30")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_high_max_notify_count=10 WHERE priority_high_max_notify_count IS NULL OR priority_high_max_notify_count<1 OR priority_high_max_notify_count>30")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_medium_max_notify_count=10 WHERE priority_medium_max_notify_count IS NULL OR priority_medium_max_notify_count<1 OR priority_medium_max_notify_count>30")
    cur .execute ("UPDATE denis_v4_user_settings SET priority_low_max_notify_count=10 WHERE priority_low_max_notify_count IS NULL OR priority_low_max_notify_count<1 OR priority_low_max_notify_count>30")

    for column_name ,column_sql in [
    ("user_id","user_id INTEGER NOT NULL DEFAULT 0"),
    ("topic","topic TEXT NOT NULL DEFAULT 'Напоминание'"),
    ("reminder_text","reminder_text TEXT NOT NULL DEFAULT ''"),
    ("category","category TEXT NOT NULL DEFAULT 'other'"),
    ("priority","priority TEXT NOT NULL DEFAULT 'medium'"),
    ("timezone_name","timezone_name TEXT NOT NULL DEFAULT 'Europe/Moscow'"),
    ("timezone_title","timezone_title TEXT NOT NULL DEFAULT '🇷🇺 Москва — МСК (UTC+3)'"),
    ("repeat_type","repeat_type TEXT NOT NULL DEFAULT 'none'"),
    ("repeat_value","repeat_value TEXT NOT NULL DEFAULT ''"),
    ("next_local_at","next_local_at TEXT NOT NULL DEFAULT ''"),
    ("next_utc_at","next_utc_at TEXT NOT NULL DEFAULT ''"),
    ("status","status TEXT NOT NULL DEFAULT 'pending'"),
    ("notify_count","notify_count INTEGER NOT NULL DEFAULT 0"),
    ("max_notify_count","max_notify_count INTEGER NOT NULL DEFAULT 10"),
    ("active_trigger_local_at","active_trigger_local_at TEXT NOT NULL DEFAULT ''"),
    ("active_trigger_utc_at","active_trigger_utc_at TEXT NOT NULL DEFAULT ''"),
    ("active_message_chat_id","active_message_chat_id INTEGER NOT NULL DEFAULT 0"),
    ("active_message_id","active_message_id INTEGER NOT NULL DEFAULT 0"),
    ("next_notify_utc","next_notify_utc TEXT NOT NULL DEFAULT ''"),
    ("created_at_utc","created_at_utc TEXT NOT NULL DEFAULT ''"),
    ("completed_at_utc","completed_at_utc TEXT NOT NULL DEFAULT ''"),
    ("parse_method","parse_method TEXT NOT NULL DEFAULT ''"),
    ("yandex_reparse_used","yandex_reparse_used INTEGER NOT NULL DEFAULT 0"),
    ("snooze_count","snooze_count INTEGER NOT NULL DEFAULT 0"),
    ("last_snooze_text","last_snooze_text TEXT NOT NULL DEFAULT ''"),
    ("last_snooze_at_utc","last_snooze_at_utc TEXT NOT NULL DEFAULT ''"),
    ("reminder_kind","reminder_kind TEXT NOT NULL DEFAULT 'normal'"),
    ("interval_minutes","interval_minutes INTEGER NOT NULL DEFAULT 0"),
    ("window_start_time","window_start_time TEXT NOT NULL DEFAULT ''"),
    ("window_end_time","window_end_time TEXT NOT NULL DEFAULT ''"),
    ("window_days","window_days TEXT NOT NULL DEFAULT ''"),
    ("interval_occurrence_count","interval_occurrence_count INTEGER NOT NULL DEFAULT 0"),
    ("interval_done_count","interval_done_count INTEGER NOT NULL DEFAULT 0"),
    ("interval_not_done_count","interval_not_done_count INTEGER NOT NULL DEFAULT 0"),
    ("interval_snoozed_count","interval_snoozed_count INTEGER NOT NULL DEFAULT 0"),
    ("break_number","break_number INTEGER NOT NULL DEFAULT 0"),
    ("break_mode","break_mode TEXT NOT NULL DEFAULT ''"),
    ]:
        ensure_column ("denis_v4_reminders",column_name ,column_sql )

    cols =existing_columns ("denis_v4_reminders")
    cur .execute ("UPDATE denis_v4_reminders SET repeat_type='none' WHERE repeat_type IS NULL OR repeat_type=''")
    cur .execute ("UPDATE denis_v4_reminders SET repeat_value='' WHERE repeat_value IS NULL")
    cur .execute ("UPDATE denis_v4_reminders SET category='other' WHERE category IS NULL OR category=''")
    cur .execute ("UPDATE denis_v4_reminders SET priority='medium' WHERE priority IS NULL OR priority=''")
    cur .execute ("UPDATE denis_v4_reminders SET status='pending' WHERE status IS NULL OR status=''")
    cur .execute ("UPDATE denis_v4_reminders SET max_notify_count=10 WHERE max_notify_count IS NULL OR max_notify_count=0")
    cur .execute ("UPDATE denis_v4_reminders SET max_notify_count=10 WHERE max_notify_count IS NULL OR max_notify_count=0")
    cur .execute ("UPDATE denis_v4_reminders SET max_notify_count=10 WHERE max_notify_count < 10")
    cur .execute ("UPDATE denis_v4_reminders SET notify_count=0 WHERE notify_count IS NULL")
    cur .execute ("UPDATE denis_v4_reminders SET snooze_count=0 WHERE snooze_count IS NULL")
    cur .execute ("UPDATE denis_v4_reminders SET last_snooze_text='' WHERE last_snooze_text IS NULL")
    cur .execute ("UPDATE denis_v4_reminders SET last_snooze_at_utc='' WHERE last_snooze_at_utc IS NULL")
    cur .execute ("UPDATE denis_v4_reminders SET next_notify_utc=next_utc_at WHERE (next_notify_utc IS NULL OR next_notify_utc='') AND next_utc_at IS NOT NULL AND next_utc_at!=''")
    cur .execute ("UPDATE denis_v4_reminders SET created_at_utc=? WHERE created_at_utc IS NULL OR created_at_utc=''",(now_utc_str (),))

    if "local_remind_at"in cols :
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET local_remind_at = COALESCE(NULLIF(local_remind_at, ''), NULLIF(next_local_at, ''), '2099-01-01 09:00')
            WHERE local_remind_at IS NULL OR local_remind_at=''
        """)
    if "local_remind_date"in cols :
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET local_remind_date = COALESCE(NULLIF(local_remind_date, ''), substr(NULLIF(next_local_at, ''), 1, 10), '2099-01-01')
            WHERE local_remind_date IS NULL OR local_remind_date=''
        """)
    if "local_remind_time"in cols :
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET local_remind_time = COALESCE(NULLIF(local_remind_time, ''), substr(NULLIF(next_local_at, ''), 12, 5), '09:00')
            WHERE local_remind_time IS NULL OR local_remind_time=''
        """)
    if "utc_remind_at"in cols :
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET utc_remind_at = COALESCE(NULLIF(utc_remind_at, ''), NULLIF(next_utc_at, ''), '2099-01-01 06:00:00')
            WHERE utc_remind_at IS NULL OR utc_remind_at=''
        """)

    for column_name ,column_sql in [
    ("reminder_id","reminder_id INTEGER NOT NULL DEFAULT 0"),
    ("user_id","user_id INTEGER NOT NULL DEFAULT 0"),
    ("topic","topic TEXT NOT NULL DEFAULT 'Напоминание'"),
    ("trigger_local_at","trigger_local_at TEXT NOT NULL DEFAULT ''"),
    ("trigger_utc_at","trigger_utc_at TEXT NOT NULL DEFAULT ''"),
    ("result_status","result_status TEXT NOT NULL DEFAULT ''"),
    ("created_at_utc","created_at_utc TEXT NOT NULL DEFAULT ''"),
    ]:
        ensure_column ("denis_v4_reminder_history",column_name ,column_sql )

    for column_name ,column_sql in [
    ("username","username TEXT NOT NULL DEFAULT ''"),
    ("first_name","first_name TEXT NOT NULL DEFAULT ''"),
    ("last_name","last_name TEXT NOT NULL DEFAULT ''"),
    ("language_code","language_code TEXT NOT NULL DEFAULT ''"),
    ("first_seen_utc","first_seen_utc TEXT NOT NULL DEFAULT ''"),
    ("last_seen_utc","last_seen_utc TEXT NOT NULL DEFAULT ''"),
    ("messages_count","messages_count INTEGER NOT NULL DEFAULT 0"),
    ]:
        ensure_column ("denis_v4_users",column_name ,column_sql )

    for column_name ,column_sql in [
    ("user_id","user_id INTEGER NOT NULL DEFAULT 0"),
    ("reminder_id","reminder_id INTEGER NOT NULL DEFAULT 0"),
    ("event_type","event_type TEXT NOT NULL DEFAULT ''"),
    ("topic","topic TEXT NOT NULL DEFAULT ''"),
    ("reminder_text","reminder_text TEXT NOT NULL DEFAULT ''"),
    ("reminder_local_at","reminder_local_at TEXT NOT NULL DEFAULT ''"),
    ("reminder_utc_at","reminder_utc_at TEXT NOT NULL DEFAULT ''"),
    ("category","category TEXT NOT NULL DEFAULT ''"),
    ("priority","priority TEXT NOT NULL DEFAULT ''"),
    ("repeat_type","repeat_type TEXT NOT NULL DEFAULT ''"),
    ("details","details TEXT NOT NULL DEFAULT ''"),
    ("created_at_utc","created_at_utc TEXT NOT NULL DEFAULT ''"),
    ]:
        ensure_column ("denis_v4_analytics_events",column_name ,column_sql )

    for column_name ,column_sql in [
    ("user_id","user_id INTEGER NOT NULL DEFAULT 0"),
    ("chat_id","chat_id INTEGER NOT NULL DEFAULT 0"),
    ("message_id","message_id INTEGER NOT NULL DEFAULT 0"),
    ("message_kind","message_kind TEXT NOT NULL DEFAULT ''"),
    ("is_active","is_active INTEGER NOT NULL DEFAULT 1"),
    ("created_at_utc","created_at_utc TEXT NOT NULL DEFAULT ''"),
    ("removed_at_utc","removed_at_utc TEXT NOT NULL DEFAULT ''"),
    ]:
        ensure_column ("denis_v4_bot_service_messages",column_name ,column_sql )
    cur .execute ("""
        CREATE INDEX IF NOT EXISTS idx_bot_service_messages_user_active
        ON denis_v4_bot_service_messages (user_id, is_active, id)
    """)
    cur .execute ("""
        CREATE INDEX IF NOT EXISTS idx_bot_service_messages_chat_message
        ON denis_v4_bot_service_messages (chat_id, message_id)
    """)
    service_boundary =(datetime .now (timezone .utc )-timedelta (days =SERVICE_MESSAGE_RETENTION_DAYS )).strftime ("%Y-%m-%d %H:%M:%S")
    cur .execute ("DELETE FROM denis_v4_bot_service_messages WHERE is_active=0 OR created_at_utc < ?",(service_boundary ,))
    cur .execute ("""
        DELETE FROM denis_v4_bot_service_messages
        WHERE id NOT IN (
            SELECT MAX(id)
            FROM denis_v4_bot_service_messages
            GROUP BY user_id, chat_id, message_kind
        )
    """)
    cur .execute ("""
        CREATE UNIQUE INDEX IF NOT EXISTS idx_bot_service_messages_current_kind
        ON denis_v4_bot_service_messages (user_id, chat_id, message_kind)
    """)
    cur .execute ("""
        CREATE INDEX IF NOT EXISTS idx_parse_usage_events_created
        ON denis_v4_parse_usage_events (created_at_utc)
    """)
    cur .execute ("""
        CREATE INDEX IF NOT EXISTS idx_parse_usage_events_method
        ON denis_v4_parse_usage_events (parse_method)
    """)

    for column_name ,column_sql in [
    ("user_id","user_id INTEGER NOT NULL DEFAULT 0"),
    ("weekday","weekday INTEGER NOT NULL DEFAULT 0"),
    ("break_index","break_index INTEGER NOT NULL DEFAULT 1"),
    ("start_time","start_time TEXT NOT NULL DEFAULT ''"),
    ("end_time","end_time TEXT NOT NULL DEFAULT ''"),
    ("created_at_utc","created_at_utc TEXT NOT NULL DEFAULT ''"),
    ]:
        ensure_column ("denis_v4_school_breaks",column_name ,column_sql )
    cur .execute ("""
        CREATE UNIQUE INDEX IF NOT EXISTS idx_school_break_unique
        ON denis_v4_school_breaks (user_id, weekday, break_index)
    """)
    cur .execute ("""
        CREATE INDEX IF NOT EXISTS idx_school_break_user_day
        ON denis_v4_school_breaks (user_id, weekday, break_index)
    """)

    now_for_known_users =now_utc_str ()
    cur .execute ("""
        INSERT OR IGNORE INTO denis_v4_users (user_id, first_seen_utc, last_seen_utc)
        SELECT user_id, ?, ? FROM denis_v4_user_settings WHERE user_id IS NOT NULL AND user_id != 0
    """,(now_for_known_users ,now_for_known_users ))
    cur .execute ("""
        INSERT OR IGNORE INTO denis_v4_users (user_id, first_seen_utc, last_seen_utc)
        SELECT DISTINCT user_id, ?, ? FROM denis_v4_reminders WHERE user_id IS NOT NULL AND user_id != 0
    """,(now_for_known_users ,now_for_known_users ))

    cur .execute ("SELECT COUNT(*) AS c FROM denis_v4_analytics_events")
    analytics_count =int (cur .fetchone ()["c"]or 0 )
    if analytics_count ==0 :
        cur .execute ("""
            INSERT INTO denis_v4_analytics_events (
                user_id, reminder_id, event_type, topic, reminder_text, reminder_local_at, reminder_utc_at,
                category, priority, repeat_type, created_at_utc
            )
            SELECT user_id, id, 'created', topic, reminder_text, next_local_at, next_utc_at,
                   category, priority, repeat_type, COALESCE(NULLIF(created_at_utc, ''), ?)
            FROM denis_v4_reminders
            WHERE user_id IS NOT NULL AND user_id != 0
        """,(now_for_known_users ,))
        cur .execute ("""
            INSERT INTO denis_v4_analytics_events (
                user_id, reminder_id, event_type, topic, reminder_text, reminder_local_at, reminder_utc_at,
                category, priority, repeat_type, created_at_utc
            )
            SELECT user_id, reminder_id,
                   CASE WHEN result_status='no_response' THEN 'skipped' ELSE result_status END,
                   topic, '', trigger_local_at, trigger_utc_at, '', '', '',
                   COALESCE(NULLIF(created_at_utc, ''), ?)
            FROM denis_v4_reminder_history
            WHERE user_id IS NOT NULL AND user_id != 0 AND result_status IS NOT NULL AND result_status != ''
        """,(now_for_known_users ,))

    for metric in ["created","done","not_done","snoozed","deleted","parse_local","parse_yandex","parse_yandex_reparse","interval_created","interval_triggers"]:
        cur .execute ("INSERT OR IGNORE INTO denis_v4_summary_stats (metric, value) VALUES (?, 0)",(metric ,))

    for category_key in CATEGORY_TITLES.keys():
        cur .execute ("INSERT OR IGNORE INTO denis_v4_category_summary_stats (category, value) VALUES (?, 0)",(category_key ,))

    cur .execute ("""
        INSERT OR IGNORE INTO denis_v4_user_category_summary_stats (user_id, category, value)
        SELECT u.user_id, c.category, 0
        FROM denis_v4_users u
        CROSS JOIN denis_v4_category_summary_stats c
        WHERE u.user_id IS NOT NULL AND u.user_id != 0
    """)

    cur .execute ("SELECT value FROM denis_v4_summary_stats WHERE metric='__initialized'")
    summary_initialized =cur .fetchone ()
    if not summary_initialized :
        # Глобальные вечные счётчики. Старые ok/no_response/skipped специально не переносим.
        for metric in ["created","done","not_done","deleted"]:
            cur .execute ("SELECT COUNT(*) AS c FROM denis_v4_analytics_events WHERE event_type=?",(metric ,))
            cur .execute ("UPDATE denis_v4_summary_stats SET value=? WHERE metric=?",(int (cur .fetchone ()["c"]or 0 ),metric ))
        cur .execute ("SELECT COUNT(DISTINCT reminder_id) AS c FROM denis_v4_analytics_events WHERE event_type='snoozed' AND reminder_id != 0")
        cur .execute ("UPDATE denis_v4_summary_stats SET value=? WHERE metric='snoozed'",(int (cur .fetchone ()["c"]or 0 ),))

        # Вечные счётчики по пользователям.
        cur .execute ("INSERT OR IGNORE INTO denis_v4_user_summary_stats (user_id) SELECT user_id FROM denis_v4_users")
        for metric in ["created","done","not_done","deleted"]:
            cur .execute (f"""
                SELECT user_id, COUNT(*) AS c
                FROM denis_v4_analytics_events
                WHERE event_type=? AND user_id IS NOT NULL AND user_id != 0
                GROUP BY user_id
            """,(metric ,))
            for summary_row in cur .fetchall ():
                cur .execute ("INSERT OR IGNORE INTO denis_v4_user_summary_stats (user_id) VALUES (?)",(summary_row ["user_id"],))
                cur .execute (f"UPDATE denis_v4_user_summary_stats SET {metric}= ? WHERE user_id=?",(int (summary_row ["c"]or 0 ),summary_row ["user_id"]))
        cur .execute ("""
            SELECT user_id, COUNT(DISTINCT reminder_id) AS c
            FROM denis_v4_analytics_events
            WHERE event_type='snoozed' AND user_id IS NOT NULL AND user_id != 0 AND reminder_id != 0
            GROUP BY user_id
        """)
        for summary_row in cur .fetchall ():
            cur .execute ("INSERT OR IGNORE INTO denis_v4_user_summary_stats (user_id) VALUES (?)",(summary_row ["user_id"],))
            cur .execute ("UPDATE denis_v4_user_summary_stats SET snoozed=? WHERE user_id=?",(int (summary_row ["c"]or 0 ),summary_row ["user_id"]))

        # Вечные счётчики по категориям считаем по созданным напоминаниям.
        cur .execute ("UPDATE denis_v4_category_summary_stats SET value=0")
        cur .execute ("""
            SELECT category, COUNT(*) AS c
            FROM denis_v4_analytics_events
            WHERE event_type='created'
            GROUP BY category
        """)
        for category_row in cur .fetchall ():
            category_key =str (category_row ["category"] or "other")
            if category_key not in CATEGORY_TITLES:
                category_key ="other"
            cur .execute ("INSERT OR IGNORE INTO denis_v4_category_summary_stats (category, value) VALUES (?, 0)",(category_key ,))
            cur .execute ("UPDATE denis_v4_category_summary_stats SET value=value+? WHERE category=?",(int (category_row ["c"]or 0 ),category_key ))

        # Первичная реконструкция счётчиков категорий по пользователям.
        cur .execute ("DELETE FROM denis_v4_user_category_summary_stats")
        for category_key in CATEGORY_TITLES.keys():
            cur .execute ("""
                INSERT OR IGNORE INTO denis_v4_user_category_summary_stats (user_id, category, value)
                SELECT user_id, ?, 0 FROM denis_v4_users WHERE user_id IS NOT NULL AND user_id != 0
            """,(category_key ,))
        cur .execute ("""
            SELECT user_id, category, COUNT(*) AS c
            FROM denis_v4_analytics_events
            WHERE event_type='created' AND user_id IS NOT NULL AND user_id != 0
            GROUP BY user_id, category
        """)
        for category_row in cur .fetchall ():
            category_key =str (category_row ["category"] or "other")
            if category_key not in CATEGORY_TITLES:
                category_key ="other"
            cur .execute ("INSERT OR IGNORE INTO denis_v4_user_category_summary_stats (user_id, category, value) VALUES (?, ?, 0)",(category_row ["user_id"],category_key ))
            cur .execute ("UPDATE denis_v4_user_category_summary_stats SET value=value+? WHERE user_id=? AND category=?",(int (category_row ["c"]or 0 ),category_row ["user_id"],category_key ))

        # Первичная реконструкция истории способов разбора для периодной статистики.
        cur .execute ("SELECT COUNT(*) AS c FROM denis_v4_parse_usage_events")
        if int (cur .fetchone ()["c"]or 0 )==0 :
            cur .execute ("""
                INSERT INTO denis_v4_parse_usage_events (user_id, parse_method, created_at_utc)
                SELECT user_id,
                       CASE WHEN parse_method='local' THEN 'local'
                            WHEN parse_method='yandex_reparse' THEN 'yandex_reparse'
                            WHEN parse_method='yandex' THEN 'yandex'
                            ELSE '' END,
                       COALESCE(NULLIF(created_at_utc, ''), ?)
                FROM denis_v4_reminders
                WHERE parse_method IN ('local','yandex','yandex_reparse')
                  AND user_id IS NOT NULL AND user_id != 0
            """,(now_for_known_users ,))

        cur .execute ("INSERT OR REPLACE INTO denis_v4_summary_stats (metric, value) VALUES ('__initialized', 1)")

    conn .commit ()
    conn .close ()


init_db ()


def register_user_from_telegram_user (tg_user ,count_message :bool =False )->None :
    if not tg_user :
        return
    now =now_utc_str ()
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        INSERT INTO denis_v4_users (user_id, username, first_name, last_name, language_code, first_seen_utc, last_seen_utc, messages_count)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            username=excluded.username,
            first_name=excluded.first_name,
            last_name=excluded.last_name,
            language_code=excluded.language_code,
            last_seen_utc=excluded.last_seen_utc,
            messages_count=denis_v4_users.messages_count + ?
    """,(
        int (tg_user .id ),
        str (getattr (tg_user ,"username",None )or ""),
        str (getattr (tg_user ,"first_name",None )or ""),
        str (getattr (tg_user ,"last_name",None )or ""),
        str (getattr (tg_user ,"language_code",None )or ""),
        now ,
        now ,
        1 if count_message else 0 ,
        1 if count_message else 0 ,
    ))
    conn .commit ()
    conn .close ()


def register_user_from_message (message :telebot .types .Message ,count_message :bool =True )->None :
    try :
        register_user_from_telegram_user (message .from_user ,count_message )
    except Exception :
        pass


def increment_summary_counters (user_id :int ,event_type :str ,amount :int =1 )->None :
    if event_type not in SUMMARY_EVENT_TYPES and event_type not in PARSE_SUMMARY_METRICS or amount ==0 :
        return
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("INSERT OR IGNORE INTO denis_v4_summary_stats (metric, value) VALUES (?, 0)",(event_type ,))
    cur .execute ("UPDATE denis_v4_summary_stats SET value=value+? WHERE metric=?",(amount ,event_type ))
    if user_id and event_type in SUMMARY_EVENT_TYPES :
        cur .execute ("INSERT OR IGNORE INTO denis_v4_user_summary_stats (user_id) VALUES (?)",(int (user_id ),))
        cur .execute (f"UPDATE denis_v4_user_summary_stats SET {event_type}=COALESCE({event_type},0)+? WHERE user_id=?",(amount ,int (user_id )))
    conn .commit ()
    conn .close ()


def increment_category_summary_counter (category :str ,user_id :int =0 ,amount :int =1 )->None :
    category_key =str (category or "other")
    if category_key not in CATEGORY_TITLES:
        category_key ="other"
    if amount ==0 :
        return
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("INSERT OR IGNORE INTO denis_v4_category_summary_stats (category, value) VALUES (?, 0)",(category_key ,))
    cur .execute ("UPDATE denis_v4_category_summary_stats SET value=COALESCE(value,0)+? WHERE category=?",(amount ,category_key ))
    if user_id:
        cur .execute ("INSERT OR IGNORE INTO denis_v4_user_category_summary_stats (user_id, category, value) VALUES (?, ?, 0)",(int (user_id ),category_key ))
        cur .execute ("UPDATE denis_v4_user_category_summary_stats SET value=COALESCE(value,0)+? WHERE user_id=? AND category=?",(amount ,int (user_id ),category_key ))
    conn .commit ()
    conn .close ()


def format_category_counts_lines (category_counts :dict [str ,int ])->list [str ]:
    lines :list [str ]=[]
    for key ,title in CATEGORY_TITLES .items ():
        lines .append (f"{title}: <b>{category_counts .get (key ,0 )}</b>")
    return lines


def get_user_category_summary_counts ()->dict [int ,dict [str ,int ]]:
    conn =get_db ()
    cur =conn .cursor ()
    result :dict [int ,dict [str ,int ]]={}
    cur .execute ("SELECT user_id, category, value FROM denis_v4_user_category_summary_stats")
    for row in cur .fetchall ():
        uid =int (row ["user_id"]or 0 )
        category_key =str (row ["category"]or "other")
        if category_key not in CATEGORY_TITLES:
            category_key ="other"
        result .setdefault (uid ,{key:0 for key in CATEGORY_TITLES .keys ()})[category_key]=int (row ["value"]or 0 )
    conn .close ()
    return result


def record_parse_usage (user_id :int ,parse_method :str )->None :
    method =str (parse_method or "").strip ()
    if method =="local":
        metric ="parse_local"
    elif method =="yandex_reparse":
        metric ="parse_yandex_reparse"
    elif method =="yandex":
        metric ="parse_yandex"
    else :
        return
    increment_summary_counters (int (user_id or 0 ),metric ,1 )
    try :
        conn =get_db ()
        cur =conn .cursor ()
        cur .execute ("INSERT INTO denis_v4_parse_usage_events (user_id, parse_method, created_at_utc) VALUES (?, ?, ?)",(int (user_id or 0 ),method ,now_utc_str ()))
        conn .commit ()
        conn .close ()
    except Exception :
        pass


def record_analytics_event (
    user_id :int ,
    event_type :str ,
    reminder_id :int =0 ,
    topic :str ="",
    reminder_text :str ="",
    reminder_local_at :str ="",
    reminder_utc_at :str ="",
    category :str ="",
    priority :str ="",
    repeat_type :str ="",
    details :str ="",
)->None :
    # Старые/лишние события ok, skipped, no_response больше не пишем и не считаем.
    if event_type not in SUMMARY_EVENT_TYPES :
        return
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        INSERT INTO denis_v4_analytics_events (
            user_id, reminder_id, event_type, topic, reminder_text, reminder_local_at, reminder_utc_at,
            category, priority, repeat_type, details, created_at_utc
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """,(
        user_id ,reminder_id ,event_type ,topic or "",reminder_text or "",reminder_local_at or "",reminder_utc_at or "",
        category or "",priority or "",repeat_type or "",details or "",now_utc_str ()
    ))
    conn .commit ()
    conn .close ()
    increment_summary_counters (int (user_id or 0 ),event_type ,1)
    if event_type =="created":
        increment_category_summary_counter (category or "other",user_id ,1 )



def record_reminder_event_from_row (event_type :str ,row )->None :
    if not row :
        return
    try :
        record_analytics_event (
            int (row ["user_id"]),
            event_type ,
            int (row ["id"]),
            row ["topic"],
            row ["reminder_text"],
            row ["next_local_at"],
            row ["next_utc_at"],
            row ["category"],
            row ["priority"],
            row ["repeat_type"],
        )
    except Exception :
        pass


def anonymous_user_map ()->dict [int ,str ]:
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT user_id FROM denis_v4_users ORDER BY first_seen_utc ASC, user_id ASC")
    rows =cur .fetchall ()
    conn .close ()
    return {int (row ["user_id"]):f"user{i}"for i ,row in enumerate (rows ,start =1 )}



def upsert_user_timezone (user_id :int ,timezone_name :str ,timezone_title :str )->None :
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        INSERT INTO denis_v4_user_settings (user_id, timezone_name, timezone_title, updated_at_utc)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            timezone_name=excluded.timezone_name,
            timezone_title=excluded.timezone_title,
            updated_at_utc=excluded.updated_at_utc
    """,(user_id ,timezone_name ,timezone_title ,now_utc_str ()))
    conn .commit ()
    conn .close ()


def get_user_timezone (user_id :int )->tuple [str ,str ]:
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT timezone_name, timezone_title FROM denis_v4_user_settings WHERE user_id = ?",(user_id ,))
    row =cur .fetchone ()
    conn .close ()
    if row :
        return row ["timezone_name"],row ["timezone_title"]
    return DEFAULT_TIMEZONE_NAME ,DEFAULT_TIMEZONE_TITLE 


def user_timezone_is_selected (user_id :int )->bool :
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT 1 FROM denis_v4_user_settings WHERE user_id = ?",(user_id ,))
    row =cur .fetchone ()
    conn .close ()
    return row is not None 


def get_user_time_words (user_id :int )->dict [str ,str ]:
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT morning_time, day_time, evening_time, night_time FROM denis_v4_user_settings WHERE user_id = ?",(user_id ,))
    row =cur .fetchone ()
    conn .close ()

    result =dict (TIME_WORD_DEFAULTS )
    if row :
        for key ,column_name in TIME_WORD_COLUMNS .items ():
            value =str (row [column_name ]or "").strip ()
            if re .fullmatch (r"\d{2}:\d{2}",value ):
                result [key ]=value 
    return result 


def update_user_time_word(user_id: int, word_key: str, time_value: str) -> None:
    """
    Сохраняет пользовательское значение для слова времени.
    Работает даже если строки пользователя в настройках ещё нет.
    """
    if word_key not in TIME_WORD_COLUMNS:
        return

    column_name = TIME_WORD_COLUMNS[word_key]
    values = dict(TIME_WORD_DEFAULTS)
    values[word_key] = time_value

    conn = get_db()
    cur = conn.cursor()
    cur.execute(f"""
        INSERT INTO denis_v4_user_settings (
            user_id, timezone_name, timezone_title,
            morning_time, day_time, evening_time, night_time,
            updated_at_utc
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            {column_name}=excluded.{column_name},
            updated_at_utc=excluded.updated_at_utc
    """, (
        user_id,
        DEFAULT_TIMEZONE_NAME,
        DEFAULT_TIMEZONE_TITLE,
        values["morning"],
        values["day"],
        values["evening"],
        values["night"],
        now_utc_str(),
    ))
    conn.commit()
    conn.close()

def reset_user_time_words(user_id: int) -> None:
    """
    Сбрасывает все пользовательские слова времени к стандартным значениям.
    Работает даже если строки пользователя в настройках ещё нет.
    """
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO denis_v4_user_settings (
            user_id, timezone_name, timezone_title,
            morning_time, day_time, evening_time, night_time,
            updated_at_utc
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            morning_time=excluded.morning_time,
            day_time=excluded.day_time,
            evening_time=excluded.evening_time,
            night_time=excluded.night_time,
            updated_at_utc=excluded.updated_at_utc
    """, (
        user_id,
        DEFAULT_TIMEZONE_NAME,
        DEFAULT_TIMEZONE_TITLE,
        TIME_WORD_DEFAULTS["morning"],
        TIME_WORD_DEFAULTS["day"],
        TIME_WORD_DEFAULTS["evening"],
        TIME_WORD_DEFAULTS["night"],
        now_utc_str(),
    ))
    conn.commit()
    conn.close()



def clamp_priority_interval_seconds(value: int, priority: str = "medium") -> int:
    default_value = PRIORITY_INTERVALS_SECONDS.get(priority, PRIORITY_INTERVALS_SECONDS["medium"])
    try:
        seconds = int(value)
    except Exception:
        return default_value
    if seconds < PRIORITY_INTERVAL_MIN_SECONDS or seconds > PRIORITY_INTERVAL_MAX_SECONDS:
        return default_value
    return seconds


def format_priority_interval(seconds: int) -> str:
    seconds = int(seconds or 0)
    if seconds < 60:
        return f"{seconds} сек."
    if seconds % 60 == 0:
        minutes = seconds // 60
        return f"{minutes} мин."
    minutes = seconds // 60
    rest = seconds % 60
    return f"{minutes} мин. {rest} сек."


def parse_priority_interval_value(text_value: str) -> tuple[Optional[int], Optional[str]]:
    text = normalize_spaces((text_value or "").lower().replace("ё", "е"))
    text = re.sub(r"^раз\s+в\s+", "", text).strip()
    if not text:
        return None, "Напиши интервал: например 5 минут или 10 секунд."
    word_numbers = {"один":1,"одну":1,"одно":1,"два":2,"две":2,"три":3,"четыре":4,"пять":5,"шесть":6,"семь":7,"восемь":8,"девять":9,"десять":10,"пятнадцать":15,"двадцать":20,"тридцать":30}
    number_pattern = r"\d{1,4}|" + "|".join(sorted(word_numbers.keys(), key=len, reverse=True))
    m = re.search(rf"\b({number_pattern})\s*(секунд(?:у|ы)?|сек|с|минут(?:у|ы)?|мин|м)\b", text)
    if not m:
        return None, "Не понял интервал. Подходят варианты: 10 секунд, 5 минут, раз в 2 минуты."
    raw_number = m.group(1)
    number = int(raw_number) if raw_number.isdigit() else int(word_numbers.get(raw_number, 0))
    unit = m.group(2)
    seconds = number if unit.startswith("сек") or unit == "с" else number * 60
    if seconds < PRIORITY_INTERVAL_MIN_SECONDS:
        return None, "Минимальный интервал — 5 секунд."
    if seconds > PRIORITY_INTERVAL_MAX_SECONDS:
        return None, "Максимальный интервал — 30 минут."
    return seconds, None


def get_user_priority_intervals(user_id: int) -> dict[str, int]:
    result = dict(PRIORITY_INTERVALS_SECONDS)
    conn = get_db()
    cur = conn.cursor()
    try:
        columns = ", ".join(PRIORITY_INTERVAL_COLUMNS.values())
        cur.execute(f"SELECT {columns} FROM denis_v4_user_settings WHERE user_id=?", (int(user_id),))
        row = cur.fetchone()
    except Exception:
        row = None
    conn.close()
    if row:
        for priority, column_name in PRIORITY_INTERVAL_COLUMNS.items():
            try:
                result[priority] = clamp_priority_interval_seconds(int(row[column_name] or 0), priority)
            except Exception:
                result[priority] = PRIORITY_INTERVALS_SECONDS.get(priority, 300)
    return result


def get_user_priority_interval_seconds(user_id: int, priority: str) -> int:
    priority_key = priority if priority in PRIORITY_INTERVALS_SECONDS else "medium"
    return get_user_priority_intervals(user_id).get(priority_key, PRIORITY_INTERVALS_SECONDS.get(priority_key, 300))


def update_user_priority_interval(user_id: int, priority: str, seconds: int) -> None:
    if priority not in PRIORITY_INTERVAL_COLUMNS:
        return
    seconds = max(PRIORITY_INTERVAL_MIN_SECONDS, min(PRIORITY_INTERVAL_MAX_SECONDS, int(seconds)))
    column_name = PRIORITY_INTERVAL_COLUMNS[priority]
    defaults = dict(PRIORITY_INTERVALS_SECONDS)
    defaults[priority] = seconds
    conn = get_db()
    cur = conn.cursor()
    cur.execute(f"""
        INSERT INTO denis_v4_user_settings (
            user_id, timezone_name, timezone_title,
            morning_time, day_time, evening_time, night_time,
            priority_very_high_interval_seconds, priority_high_interval_seconds,
            priority_medium_interval_seconds, priority_low_interval_seconds,
            updated_at_utc
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            {column_name}=excluded.{column_name},
            updated_at_utc=excluded.updated_at_utc
    """, (
        int(user_id), DEFAULT_TIMEZONE_NAME, DEFAULT_TIMEZONE_TITLE,
        TIME_WORD_DEFAULTS["morning"], TIME_WORD_DEFAULTS["day"], TIME_WORD_DEFAULTS["evening"], TIME_WORD_DEFAULTS["night"],
        defaults["very_high"], defaults["high"], defaults["medium"], defaults["low"], now_utc_str(),
    ))
    conn.commit()
    conn.close()


def clamp_priority_max_count(value: int, priority: str = "medium") -> int:
    default_value = PRIORITY_MAX_NOTIFY_COUNT.get(priority, PRIORITY_MAX_NOTIFY_COUNT["medium"])
    try:
        count = int(value)
    except Exception:
        return default_value
    if count < PRIORITY_MAX_COUNT_MIN or count > PRIORITY_MAX_COUNT_MAX:
        return default_value
    return count


def parse_priority_max_count_value(text_value: str) -> tuple[Optional[int], Optional[str]]:
    text = normalize_spaces((text_value or "").lower().replace("ё", "е"))
    if not text:
        return None, "Напиши количество сообщений числом: например 5 или 10."
    m = re.search(r"\b(\d{1,2})\b", text)
    if not m:
        return None, "Не понял количество. Напиши число от 1 до 30."
    count = int(m.group(1))
    if count < PRIORITY_MAX_COUNT_MIN:
        return None, "Минимум — 1 сообщение."
    if count > PRIORITY_MAX_COUNT_MAX:
        return None, "Максимум — 30 сообщений."
    return count, None


def get_user_priority_max_counts(user_id: int) -> dict[str, int]:
    result = dict(PRIORITY_MAX_NOTIFY_COUNT)
    conn = get_db()
    cur = conn.cursor()
    try:
        columns = ", ".join(PRIORITY_MAX_COUNT_COLUMNS.values())
        cur.execute(f"SELECT {columns} FROM denis_v4_user_settings WHERE user_id=?", (int(user_id),))
        row = cur.fetchone()
    except Exception:
        row = None
    conn.close()
    if row:
        for priority, column_name in PRIORITY_MAX_COUNT_COLUMNS.items():
            try:
                result[priority] = clamp_priority_max_count(int(row[column_name] or 0), priority)
            except Exception:
                result[priority] = PRIORITY_MAX_NOTIFY_COUNT.get(priority, 10)
    return result


def get_user_priority_max_count(user_id: int, priority: str) -> int:
    priority_key = priority if priority in PRIORITY_MAX_NOTIFY_COUNT else "medium"
    return get_user_priority_max_counts(user_id).get(priority_key, PRIORITY_MAX_NOTIFY_COUNT.get(priority_key, 10))


def update_user_priority_max_count(user_id: int, priority: str, count: int) -> None:
    if priority not in PRIORITY_MAX_COUNT_COLUMNS:
        return
    count = max(PRIORITY_MAX_COUNT_MIN, min(PRIORITY_MAX_COUNT_MAX, int(count)))
    column_name = PRIORITY_MAX_COUNT_COLUMNS[priority]
    defaults = dict(PRIORITY_MAX_NOTIFY_COUNT)
    defaults[priority] = count
    conn = get_db()
    cur = conn.cursor()
    cur.execute(f"""
        INSERT INTO denis_v4_user_settings (
            user_id, timezone_name, timezone_title,
            morning_time, day_time, evening_time, night_time,
            priority_very_high_max_notify_count, priority_high_max_notify_count,
            priority_medium_max_notify_count, priority_low_max_notify_count,
            updated_at_utc
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            {column_name}=excluded.{column_name},
            updated_at_utc=excluded.updated_at_utc
    """, (
        int(user_id), DEFAULT_TIMEZONE_NAME, DEFAULT_TIMEZONE_TITLE,
        TIME_WORD_DEFAULTS["morning"], TIME_WORD_DEFAULTS["day"], TIME_WORD_DEFAULTS["evening"], TIME_WORD_DEFAULTS["night"],
        defaults["very_high"], defaults["high"], defaults["medium"], defaults["low"], now_utc_str(),
    ))
    conn.commit()
    conn.close()

def insert_reminder (data :dict )->int :
    """
    Динамическая вставка с поддержкой старых схем denis_v4_reminders.db.
    Исправляет NOT NULL constraint failed: denis_v4_reminders.local_remind_at и похожие ошибки.
    """
    conn =get_db ()
    cur =conn .cursor ()

    info =cur .execute ("PRAGMA table_info(denis_v4_reminders)").fetchall ()
    cols ={row [1 ]for row in info }

    values ={
    "user_id":data ["user_id"],
    "topic":data ["topic"],
    "reminder_text":data ["reminder_text"],
    "category":data ["category"],
    "priority":data ["priority"],
    "timezone_name":data ["timezone_name"],
    "timezone_title":data ["timezone_title"],
    "repeat_type":data ["repeat_type"],
    "repeat_value":data ["repeat_value"],
    "next_local_at":data ["next_local_at"],
    "next_utc_at":data ["next_utc_at"],
    "status":"pending",
    "notify_count":0 ,
    "max_notify_count":max_notify_count_for_priority (data ["priority"],int (data .get ("user_id",0 )or 0 )),
    "active_trigger_local_at":"",
    "active_trigger_utc_at":"",
    "active_message_chat_id":0 ,
    "active_message_id":0 ,
    "next_notify_utc":data ["next_utc_at"],
    "created_at_utc":now_utc_str (),
    "completed_at_utc":"",
    "parse_method":data .get ("parse_method",""),
    "yandex_reparse_used":1 if data .get ("yandex_reparse_used") else 0,
    "reminder_kind":data .get ("reminder_kind","normal") or "normal",
    "interval_minutes":int (data .get ("interval_minutes",0 )or 0 ),
    "window_start_time":data .get ("window_start_time","") or "",
    "window_end_time":data .get ("window_end_time","") or "",
    "window_days":data .get ("window_days","") or "",
    "break_number":int (data .get ("break_number",0 )or 0 ),
    "break_mode":data .get ("break_mode","") or "",
    "local_remind_at":data ["next_local_at"],
    "local_remind_date":data ["next_local_at"][:10 ],
    "local_remind_time":data ["next_local_at"][11 :16 ],
    "utc_remind_at":data ["next_utc_at"],
    "remind_at":data ["next_utc_at"],
    "remind_date":data ["next_local_at"][:10 ],
    "remind_time":data ["next_local_at"][11 :16 ],
    }

    for row in info :
        name =row [1 ]
        not_null =bool (row [3 ])
        default_value =row [4 ]
        is_pk =bool (row [5 ])
        if is_pk or name in values :
            continue 
        if not_null and default_value is None :
            if "time"in name :
                values [name ]=data ["next_local_at"][11 :16 ]
            elif "date"in name :
                values [name ]=data ["next_local_at"][:10 ]
            elif "utc"in name or "at"in name :
                values [name ]=data ["next_utc_at"]
            elif "count"in name or "number"in name :
                values [name ]=0 
            else :
                values [name ]=""

    insert_cols =[c for c in values .keys ()if c in cols ]
    placeholders =", ".join (["?"]*len (insert_cols ))
    sql =f"INSERT INTO denis_v4_reminders ({', '.join (insert_cols )}) VALUES ({placeholders })"
    cur .execute (sql ,[values [c ]for c in insert_cols ])
    reminder_id =int (cur .lastrowid or 0 )

    conn .commit ()
    conn .close ()

    record_analytics_event (
    int (data ["user_id"]),
    "created",
    reminder_id ,
    data .get ("topic","") ,
    data .get ("reminder_text","") ,
    data .get ("next_local_at","") ,
    data .get ("next_utc_at","") ,
    data .get ("category","") ,
    data .get ("priority","") ,
    data .get ("repeat_type","") ,
    )
    if data.get("reminder_kind") in {REMINDER_KIND_INTERVAL, REMINDER_KIND_BREAK_EACH, REMINDER_KIND_BREAK_SINGLE}:
        increment_summary_counters(int(data["user_id"]), "interval_created", 1)
    return reminder_id



def update_reminder (reminder_id :int ,user_id :int ,data :dict )->bool :
    conn =get_db ()
    cur =conn .cursor ()

    cols ={row [1 ]for row in cur .execute ("PRAGMA table_info(denis_v4_reminders)").fetchall ()}

    values ={
    "topic":data ["topic"],
    "reminder_text":data ["reminder_text"],
    "category":data ["category"],
    "priority":data ["priority"],
    "repeat_type":data ["repeat_type"],
    "repeat_value":data ["repeat_value"],
    "next_local_at":data ["next_local_at"],
    "next_utc_at":data ["next_utc_at"],
    "next_notify_utc":data ["next_utc_at"],
    "active_trigger_local_at":"",
    "active_trigger_utc_at":"",
    "active_message_chat_id":0 ,
    "active_message_id":0 ,
    "notify_count":0 ,
    "max_notify_count":max_notify_count_for_priority (data ["priority"],int (data .get ("user_id",0 )or 0 )),
    "reminder_kind":data .get ("reminder_kind","normal") or "normal",
    "interval_minutes":int (data .get ("interval_minutes",0 )or 0 ),
    "window_start_time":data .get ("window_start_time","") or "",
    "window_end_time":data .get ("window_end_time","") or "",
    "window_days":data .get ("window_days","") or "",
    "break_number":int (data .get ("break_number",0 )or 0 ),
    "break_mode":data .get ("break_mode","") or "",
    "local_remind_at":data ["next_local_at"],
    "local_remind_date":data ["next_local_at"][:10 ],
    "local_remind_time":data ["next_local_at"][11 :16 ],
    "utc_remind_at":data ["next_utc_at"],
    "remind_at":data ["next_utc_at"],
    "remind_date":data ["next_local_at"][:10 ],
    "remind_time":data ["next_local_at"][11 :16 ],
    }

    update_cols =[c for c in values .keys ()if c in cols ]
    set_sql =", ".join ([f"{c }=?"for c in update_cols ])
    params =[values [c ]for c in update_cols ]+[reminder_id ,user_id ]

    cur .execute (
    f"UPDATE denis_v4_reminders SET {set_sql } WHERE id=? AND user_id=? AND status='pending'",
    params ,
    )
    ok =cur .rowcount >0 
    conn .commit ()
    conn .close ()
    return ok 


def get_reminder_by_id (reminder_id :int ,user_id :int )->Optional [sqlite3 .Row ]:
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT * FROM denis_v4_reminders WHERE id=? AND user_id=? AND status='pending'",(reminder_id ,user_id ))
    row =cur .fetchone ()
    conn .close ()
    return row 


def get_all_active_reminders (user_id :int )->list [sqlite3 .Row ]:
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT * FROM denis_v4_reminders WHERE user_id=? AND status='pending' ORDER BY next_utc_at ASC",(user_id ,))
    rows =cur .fetchall ()
    conn .close ()
    return rows 


def get_due_reminders (now_utc :str )->list [sqlite3 .Row ]:
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("SELECT * FROM denis_v4_reminders WHERE status='pending' AND next_notify_utc <= ? ORDER BY next_notify_utc ASC",(now_utc ,))
    rows =cur .fetchall ()
    conn .close ()
    return rows 



def delete_pending_reminder (reminder_id :int ,user_id :int )->bool :
    row_for_analytics =get_reminder_by_id (reminder_id ,user_id )
    clear_active_message_for_reminder (reminder_id ,user_id ,fallback_text ="Напоминание удалено.")

    conn =get_db ()
    cur =conn .cursor ()
    cur .execute (
    "UPDATE denis_v4_reminders SET status='deleted', completed_at_utc=?, active_message_chat_id=0, active_message_id=0 WHERE id=? AND user_id=? AND status='pending'",
    (now_utc_str (),reminder_id ,user_id ),
    )
    ok =cur .rowcount >0 
    conn .commit ()
    conn .close ()
    if ok and row_for_analytics :
        record_reminder_event_from_row ("deleted",row_for_analytics )
    return ok 



def clear_all_pending (user_id :int )->int :
    rows =get_all_active_reminders (user_id )
    for row in rows :
        clear_active_message_for_reminder (row ["id"],user_id ,fallback_text ="Напоминание удалено.")

    conn =get_db ()
    cur =conn .cursor ()
    cur .execute (
    "UPDATE denis_v4_reminders SET status='deleted', completed_at_utc=?, active_message_chat_id=0, active_message_id=0 WHERE user_id=? AND status='pending'",
    (now_utc_str (),user_id ),
    )
    count =cur .rowcount 
    conn .commit ()
    conn .close ()
    for row in rows :
        record_reminder_event_from_row ("deleted",row )
    return count 


def add_history (reminder_id :int ,user_id :int ,topic :str ,trigger_local_at :str ,trigger_utc_at :str ,result_status :str )->None :
    if result_status not in {"done","not_done","snoozed","deleted"}:
        return
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        INSERT INTO denis_v4_reminder_history (reminder_id, user_id, topic, trigger_local_at, trigger_utc_at, result_status, created_at_utc)
        VALUES (?, ?, ?, ?, ?, ?, ?)
    """,(reminder_id ,user_id ,topic ,trigger_local_at ,trigger_utc_at ,result_status ,now_utc_str ()))
    conn .commit ()
    conn .close ()
    record_analytics_event (
    user_id ,
    result_status ,
    reminder_id ,
    topic ,
    "",
    trigger_local_at ,
    trigger_utc_at ,
    "",
    "",
    "",
    )



def get_recent_history (user_id :int ,days :int =7 )->list [sqlite3 .Row ]:
    boundary =(datetime .now (timezone .utc )-timedelta (days =days )).strftime ("%Y-%m-%d %H:%M:%S")
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute (
    "SELECT * FROM denis_v4_reminder_history WHERE user_id=? AND created_at_utc >= ? ORDER BY created_at_utc DESC",
    (user_id ,boundary ),
    )
    rows =cur .fetchall ()
    conn .close ()
    return rows 


def cleanup_old_history ()->None :
    global LAST_CLEANUP_DATE
    today =datetime .now (timezone .utc ).strftime ("%Y-%m-%d")
    if LAST_CLEANUP_DATE ==today :
        return
    LAST_CLEANUP_DATE =today
    boundary =(datetime .now (timezone .utc )-timedelta (days =DETAILED_DATA_RETENTION_DAYS )).strftime ("%Y-%m-%d %H:%M:%S")
    conn =get_db ()
    cur =conn .cursor ()

    # Подробные события храним только 2 месяца.
    cur .execute ("DELETE FROM denis_v4_reminder_history WHERE created_at_utc < ?",(boundary ,))
    cur .execute ("DELETE FROM denis_v4_analytics_events WHERE created_at_utc < ?",(boundary ,))

    # Завершённые подробные напоминания старше 2 месяцев удаляем из детальной таблицы.
    # Активные будущие напоминания не трогаем.
    cur .execute ("""
        DELETE FROM denis_v4_reminders
        WHERE status != 'pending'
          AND COALESCE(NULLIF(completed_at_utc, ''), NULLIF(created_at_utc, ''), '1900-01-01 00:00:00') < ?
    """,(boundary ,))
    conn .commit ()
    conn .close ()



    # =========================================================
    # Помощники
    # =========================================================

def escape_html (value :str )->str :
    return html .escape (value or "")



def safe_delete_message (chat_id :int ,message_id :int )->bool :
    """
    Пытаемся удалить сообщение несколько раз.
    Telegram иногда не успевает обработать удаление сразу, поэтому делаем короткие повторы.
    """
    if not chat_id or not message_id :
        return True 

    for _ in range (4 ):
        try :
            bot .delete_message (chat_id ,message_id )
            return True 
        except Exception :
            time .sleep (0.25 )

    return False 


def collapse_message_if_not_deleted (chat_id :int ,message_id :int ,text :str ="Сообщение закрыто.")->None :
    """
    Если удалить не удалось, хотя мы пытались, хотя бы убираем содержимое и кнопки.
    Это запасной вариант на случай ограничений Telegram.
    """
    if not chat_id or not message_id :
        return 
    try :
        bot .edit_message_text (
        text ,
        chat_id =chat_id ,
        message_id =message_id ,
        reply_markup =None ,
        parse_mode ="HTML",
        )
    except Exception :
        pass 


def delete_or_collapse_message (chat_id :int ,message_id :int ,fallback_text :str ="Сообщение закрыто.")->None :
    if not safe_delete_message (chat_id ,message_id ):
        collapse_message_if_not_deleted (chat_id ,message_id ,fallback_text )


def prune_bot_service_messages (user_id :int =0 ,chat_id :int =0 )->None :
    """
    Чистит таблицу служебных сообщений.
    Она не должна быть историей: в ней нужны только актуальные message_id,
    чтобы /start мог удалить старые служебные окна бота.
    """
    try :
        conn =get_db ()
        cur =conn .cursor ()
        boundary =(datetime .now (timezone .utc )-timedelta (days =SERVICE_MESSAGE_RETENTION_DAYS )).strftime ("%Y-%m-%d %H:%M:%S")
        cur .execute ("DELETE FROM denis_v4_bot_service_messages WHERE is_active=0 OR created_at_utc < ?",(boundary ,))
        if user_id and chat_id :
            cur .execute ("""
                DELETE FROM denis_v4_bot_service_messages
                WHERE user_id=? AND chat_id=?
                  AND id NOT IN (
                      SELECT id FROM (
                          SELECT id
                          FROM denis_v4_bot_service_messages
                          WHERE user_id=? AND chat_id=? AND is_active=1
                          ORDER BY id DESC
                          LIMIT ?
                      ) keep_rows
                  )
            """,(int (user_id ),int (chat_id ),int (user_id ),int (chat_id ),SERVICE_MESSAGE_MAX_ACTIVE_PER_CHAT ))
        conn .commit ()
        conn .close ()
    except Exception :
        pass


def remember_bot_service_message (user_id :int ,chat_id :int ,message_id :int ,message_kind :str )->None :
    """
    Запоминает только актуальное служебное сообщение данного типа.
    Старые записи того же типа заменяются, поэтому база не разрастается от
    каждого редактирования меню/черновика/приветствия.
    """
    try :
        if not user_id or not chat_id or not message_id :
            return
        kind =str (message_kind or "service")
        now =now_utc_str ()
        conn =get_db ()
        cur =conn .cursor ()
        cur .execute ("""
            DELETE FROM denis_v4_bot_service_messages
            WHERE user_id=? AND chat_id=? AND message_kind=?
        """,(int (user_id ),int (chat_id ),kind ))
        cur .execute ("""
            INSERT INTO denis_v4_bot_service_messages
                (user_id, chat_id, message_id, message_kind, is_active, created_at_utc, removed_at_utc)
            VALUES (?, ?, ?, ?, 1, ?, '')
        """,(int (user_id ),int (chat_id ),int (message_id ),kind ,now ))
        conn .commit ()
        conn .close ()
        prune_bot_service_messages (int (user_id ),int (chat_id ))
    except Exception :
        pass


def mark_bot_service_message_removed (chat_id :int ,message_id :int )->None :
    try :
        if not chat_id or not message_id :
            return
        conn =get_db ()
        cur =conn .cursor ()
        cur .execute ("""
            DELETE FROM denis_v4_bot_service_messages
            WHERE chat_id=? AND message_id=?
        """,(int (chat_id ),int (message_id )))
        conn .commit ()
        conn .close ()
    except Exception :
        pass


def get_active_bot_service_message_ids (user_id :int ,chat_id :int )->list [int ]:
    try :
        prune_bot_service_messages (int (user_id ),int (chat_id ))
        conn =get_db ()
        cur =conn .cursor ()
        cur .execute ("""
            SELECT message_id
            FROM denis_v4_bot_service_messages
            WHERE user_id=? AND chat_id=? AND is_active=1 AND message_id != 0
            ORDER BY id DESC
            LIMIT ?
        """,(int (user_id ),int (chat_id ),SERVICE_MESSAGE_MAX_ACTIVE_PER_CHAT ))
        rows =cur .fetchall ()
        conn .close ()
        result :list [int ]=[]
        seen :set [int ]=set ()
        for row in rows :
            mid =int (row ["message_id"]or 0 )
            if mid and mid not in seen :
                seen .add (mid )
                result .append (mid )
        return result
    except Exception :
        return []


def mark_all_bot_service_messages_inactive (user_id :int ,chat_id :int )->None :
    try :
        conn =get_db ()
        cur =conn .cursor ()
        cur .execute ("""
            DELETE FROM denis_v4_bot_service_messages
            WHERE user_id=? AND chat_id=?
        """,(int (user_id ),int (chat_id )))
        conn .commit ()
        conn .close ()
    except Exception :
        pass

def set_active_message_for_reminder (reminder_id :int ,user_id :int ,chat_id :int ,message_id :int )->None :
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        UPDATE denis_v4_reminders
        SET active_message_chat_id=?, active_message_id=?
        WHERE id=? AND user_id=? AND status='pending'
    """,(chat_id ,message_id ,reminder_id ,user_id ))
    conn .commit ()
    conn .close ()


def clear_active_message_for_reminder (
reminder_id :int ,
user_id :int ,
current_chat_id :Optional [int ]=None ,
current_message_id :Optional [int ]=None ,
fallback_text :str ="Напоминание закрыто.",
)->None :
    """
    Удаляет только активное сообщение конкретного напоминания.

    Это важно:
    - одно и то же напоминание при повторной отправке заменяется одним новым сообщением;
    - разные напоминания не трогаются, у каждого свой reminder_id и свой active_message_id.
    """
    conn =get_db ()
    cur =conn .cursor ()
    cur .execute (
    "SELECT active_message_chat_id, active_message_id FROM denis_v4_reminders WHERE id=? AND user_id=?",
    (reminder_id ,user_id ),
    )
    row =cur .fetchone ()
    conn .close ()

    deleted_keys :set [tuple [int ,int ]]=set ()

    if row :
        try :
            stored_chat_id =int (row ["active_message_chat_id"]or 0 )
            stored_message_id =int (row ["active_message_id"]or 0 )
        except Exception :
            stored_chat_id =0 
            stored_message_id =0 

        if stored_chat_id and stored_message_id :
            delete_or_collapse_message (stored_chat_id ,stored_message_id ,fallback_text )
            deleted_keys .add ((stored_chat_id ,stored_message_id ))

    if current_chat_id and current_message_id :
        key =(int (current_chat_id ),int (current_message_id ))
        if key not in deleted_keys :
            delete_or_collapse_message (int (current_chat_id ),int (current_message_id ),fallback_text )

    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        UPDATE denis_v4_reminders
        SET active_message_chat_id=0, active_message_id=0
        WHERE id=? AND user_id=?
    """,(reminder_id ,user_id ))
    conn .commit ()
    conn .close ()


def safe_delete_user_message (message :telebot .types .Message )->None :
    try :
        bot .delete_message (message .chat .id ,message .message_id )
    except Exception :
        pass 


def clear_help_document_message (user_id :int )->None :
    doc_msg =HELP_DOCUMENT_MESSAGES .pop (user_id ,None )
    if not doc_msg :
        return 
    try :
        chat_id =int (doc_msg .get ("chat_id",0 )or 0 )
        message_id =int (doc_msg .get ("message_id",0 )or 0 )
    except Exception :
        chat_id =0 
        message_id =0 
    if chat_id and message_id :
        safe_delete_message (chat_id ,message_id )


def show_screen (user_id :int ,chat_id :int ,text :str ,markup =None ,push_history :bool =True )->None :
    """
    Чистый чат:
    - все служебные экраны идут в одном сообщении;
    - если можно, редактируем старое сообщение;
    - если нельзя, отправляем новое и удаляем старое;
    - предыдущий экран сохраняем для кнопки Назад.
    """
    clear_help_document_message (user_id )
    prev =SCREEN_MESSAGES .get (user_id )

    if push_history and prev and prev .get ("chat_id")==chat_id and prev .get ("text")!=text :
        SCREEN_STACK .setdefault (user_id ,[]).append ({
        "chat_id":prev .get ("chat_id"),
        "message_id":prev .get ("message_id"),
        "text":prev .get ("text",""),
        "markup":prev .get ("markup"),
        })
        if len (SCREEN_STACK [user_id ])>20 :
            SCREEN_STACK [user_id ]=SCREEN_STACK [user_id ][-20 :]

    if prev and prev .get ("chat_id")==chat_id :
        try :
            bot .edit_message_text (
            text =text ,
            chat_id =chat_id ,
            message_id =prev ["message_id"],
            reply_markup =markup ,
            parse_mode ="HTML",
            )
            SCREEN_MESSAGES [user_id ]={
            "chat_id":chat_id ,
            "message_id":prev ["message_id"],
            "text":text ,
            "markup":markup ,
            }
            remember_bot_service_message (user_id ,chat_id ,prev ["message_id"],"screen")
            return 
        except Exception :
            pass 

    sent =bot .send_message (chat_id ,text ,reply_markup =markup )
    remember_bot_service_message (user_id ,chat_id ,sent .message_id ,"screen")
    SCREEN_MESSAGES [user_id ]={
    "chat_id":chat_id ,
    "message_id":sent .message_id ,
    "text":text ,
    "markup":markup ,
    }
    if prev and prev .get ("chat_id")==chat_id and prev .get ("message_id")!=sent .message_id :
        delete_or_collapse_message (chat_id ,prev ["message_id"],"Сообщение обновлено.")
        mark_bot_service_message_removed (chat_id ,prev ["message_id"])


def show_previous_screen (user_id :int ,chat_id :int )->bool :
    stack =SCREEN_STACK .get (user_id )or []
    while stack :
        prev_screen =stack .pop ()
        text =prev_screen .get ("text")or ""
        markup =prev_screen .get ("markup")
        if text :
            show_screen (user_id ,chat_id ,text ,markup ,push_history =False )
            return True 
    return False 


def debug_text (title :str ,details :str )->str :
    return f"❌ {title }\n\n{details }"if DEBUG else f"❌ {title }"


def normalize_spaces (text :str )->str :
    return re .sub (r"\s+"," ",text ).strip ()


def format_human_datetime (dt_str :str ,timezone_name :Optional [str ]=None )->str :
    dt =datetime .strptime (dt_str ,"%Y-%m-%d %H:%M")
    if timezone_name :
        dt =dt .replace (tzinfo =ZoneInfo (timezone_name ))
    return f"{WEEKDAYS [dt .weekday ()]}, {dt .day } {MONTHS_GENITIVE [dt .month ]} {dt .year } года в {dt .strftime ('%H:%M')}"


def format_group_title (local_dt_str :str ,timezone_name :str )->str :
    dt =datetime .strptime (local_dt_str ,"%Y-%m-%d %H:%M").replace (tzinfo =ZoneInfo (timezone_name ))
    now_local =datetime .now (ZoneInfo (timezone_name ))
    delta_days =(dt .date ()-now_local .date ()).days 
    if delta_days ==0 :
        return f"Сегодня ({dt .day } {MONTHS_GENITIVE [dt .month ]})"
    if delta_days ==1 :
        return f"Завтра ({dt .day } {MONTHS_GENITIVE [dt .month ]})"
    return f"{WEEKDAYS [dt .weekday ()].capitalize ()} ({dt .day } {MONTHS_GENITIVE [dt .month ]})"


def format_time_until (local_at :str ,timezone_name :str )->str :
    tz =ZoneInfo (timezone_name )
    try :
        target =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    except Exception :
        return "сейчас"

    now_local =datetime .now (tz ).replace (second =0 ,microsecond =0 )
    if target <=now_local :
        return "сейчас"

    total_seconds =int ((target -now_local ).total_seconds ())
    if total_seconds <60 :
        return "меньше минуты"

    months =0 
    cursor =now_local 
    while True :
        next_cursor =add_months (cursor ,1 )
        if next_cursor <=target :
            months +=1 
            cursor =next_cursor 
        else :
            break 

    rest =target -cursor 
    days =rest .days 
    hours =rest .seconds //3600 
    minutes =(rest .seconds %3600 )//60 

    parts =[]
    if months :
        parts .append (f"{months } мес.")
    if days or months :
        parts .append (f"{days } дн.")
    if hours or days or months :
        parts .append (f"{hours } ч.")
    parts .append (f"{minutes } мин.")
    return " ".join (parts )


def should_show_time_until (priority: str) -> bool:
    return priority == "very_high"


def render_time_until_line (local_at :str ,timezone_name :str ,priority: str = "") -> str:
    if not should_show_time_until(priority):
        return ""
    return f"<b>До события:</b> {escape_html (format_time_until (local_at ,timezone_name ))}"


def repeat_title (repeat_type :str ,repeat_value :str )->str :
    if repeat_type =="none":
        return "один раз"
    if repeat_type =="daily":
        return "каждый день"
    if repeat_type =="weekly":
        return "каждую неделю"
    if repeat_type =="monthly":
        return "каждый месяц"
    if repeat_type =="yearly":
        return "каждый год"
    if repeat_type =="weekdays":
        return "по будням"
    if repeat_type =="weekends":
        return "по выходным"
    if repeat_type =="custom_weekdays":
        nums =[]
        for x in repeat_value .split (","):
            x =x .strip ()
            if x .isdigit ():
                nums .append (int (x ))
        nums =sorted (set (n for n in nums if 0 <=n <=6 ))
        return ", ".join (WEEKDAY_SHORT [n ]for n in nums )if nums else "выбранные дни недели"
    if repeat_type =="every_n_days":
        return f"каждые {repeat_value } дн."if repeat_value else "каждые N дней"
    return "один раз"


def add_months (dt :datetime ,months :int )->datetime :
    month =dt .month -1 +months 
    year =dt .year +month //12 
    month =month %12 +1 
    day =min (dt .day ,calendar .monthrange (year ,month )[1 ])
    return dt .replace (year =year ,month =month ,day =day )


def compute_next_occurrence (repeat_type :str ,repeat_value :str ,current_local :str ,timezone_name :str )->tuple [str ,str ]:
    tz =ZoneInfo (timezone_name )
    base =datetime .strptime (current_local ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )

    if repeat_type =="daily":
        candidate =base +timedelta (days =1 )
    elif repeat_type =="weekly":
        candidate =base +timedelta (weeks =1 )
    elif repeat_type =="monthly":
        candidate =add_months (base ,1 )
    elif repeat_type =="yearly":
        try :
            candidate =base .replace (year =base .year +1 )
        except Exception :
            candidate =base .replace (month =2 ,day =28 ,year =base .year +1 )
    elif repeat_type =="weekdays":
        candidate =base +timedelta (days =1 )
        while candidate .weekday ()>=5 :
            candidate +=timedelta (days =1 )
    elif repeat_type =="weekends":
        candidate =base +timedelta (days =1 )
        while candidate .weekday ()<5 :
            candidate +=timedelta (days =1 )
    elif repeat_type =="custom_weekdays":
        days =[]
        for x in repeat_value .split (","):
            x =x .strip ()
            if x .isdigit ():
                days .append (int (x ))
        days =sorted (set (d for d in days if 0 <=d <=6 ))
        candidate =base +timedelta (days =1 )
        for _ in range (370 ):
            if candidate .weekday ()in days :
                break 
            candidate +=timedelta (days =1 )
    elif repeat_type =="every_n_days":
        try :
            n =max (1 ,min (365 ,int (repeat_value )))
        except Exception :
            n =1 
        candidate =base +timedelta (days =n )
    else :
        candidate =base 

    return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")



def parse_weekday_value (repeat_value :str )->list [int ]:
    days =[]
    for x in (repeat_value or "").split (","):
        x =x .strip ()
        if x .isdigit ():
            value =int (x )
            if 0 <=value <=6 :
                days .append (value )
    return sorted (set (days ))


def datetime_to_local_utc_strings (dt :datetime )->tuple [str ,str ]:
    return dt .strftime ("%Y-%m-%d %H:%M"),dt .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")



def recalc_next_after_repeat_change (local_at :str ,timezone_name :str ,repeat_type :str ,repeat_value :str )->tuple [str ,str ]:
    tz =ZoneInfo (timezone_name )
    now_local =datetime .now (tz )
    base =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )

    hour =base .hour 
    minute =base .minute 

    def today_with_time ()->datetime :
        return now_local .replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )

    if repeat_type =="none":
        candidate =base 
        if candidate <=now_local :
            candidate =today_with_time ()
            if candidate <=now_local :
                candidate +=timedelta (days =1 )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type =="daily":
        candidate =today_with_time ()
        if candidate <=now_local :
            candidate +=timedelta (days =1 )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type =="weekdays":
        candidate =today_with_time ()
        for _ in range (14 ):
            if candidate >now_local and candidate .weekday ()<5 :
                return datetime_to_local_utc_strings (candidate )
            candidate +=timedelta (days =1 )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type =="weekends":
        candidate =today_with_time ()
        for _ in range (14 ):
            if candidate >now_local and candidate .weekday ()>=5 :
                return datetime_to_local_utc_strings (candidate )
            candidate +=timedelta (days =1 )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type =="custom_weekdays":
        days =parse_weekday_value (repeat_value )
        candidate =today_with_time ()
        if not days :
            if candidate <=now_local :
                candidate +=timedelta (days =1 )
            return datetime_to_local_utc_strings (candidate )
        for _ in range (370 ):
            if candidate >now_local and candidate .weekday ()in days :
                return datetime_to_local_utc_strings (candidate )
            candidate +=timedelta (days =1 )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type =="weekly":
        target_weekday =base .weekday ()
        candidate =today_with_time ()
        for _ in range (14 ):
            if candidate >now_local and candidate .weekday ()==target_weekday :
                return datetime_to_local_utc_strings (candidate )
            candidate +=timedelta (days =1 )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type =="every_n_days":
        try :
            n =max (1 ,min (365 ,int (repeat_value )))
        except Exception :
            n =1 
        candidate =now_local .replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )+timedelta (days =n )
        return datetime_to_local_utc_strings (candidate )

    if repeat_type in {"monthly","yearly"}:
        candidate_local =local_at 
        candidate_dt =datetime .strptime (candidate_local ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
        guard =0 
        while candidate_dt <=now_local and guard <800 :
            candidate_local ,_ =compute_next_occurrence (repeat_type ,repeat_value ,candidate_local ,timezone_name )
            candidate_dt =datetime .strptime (candidate_local ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
            guard +=1 
        return datetime_to_local_utc_strings (candidate_dt )

    candidate =base 
    if candidate <=now_local :
        candidate =today_with_time ()
        if candidate <=now_local :
            candidate +=timedelta (days =1 )
    return datetime_to_local_utc_strings (candidate )


def apply_repeat_to_session_data (data :dict ,repeat_type :str ,repeat_value :str )->None :
    data ["repeat_type"]=repeat_type 
    data ["repeat_value"]=repeat_value or ""
    data ["next_local_at"],data ["next_utc_at"]=recalc_next_after_repeat_change (
    data ["next_local_at"],
    data ["timezone_name"],
    data ["repeat_type"],
    data ["repeat_value"],
    )

def ensure_future_for_repeat (local_at :str ,timezone_name :str ,repeat_type :str ,repeat_value :str )->tuple [str ,str ]:
    """
    Защита от ошибки "время уже прошло":
    - одноразовое прошедшее время блокируем;
    - повторяющееся прошедшее время двигаем к ближайшему будущему срабатыванию.
    """
    tz =ZoneInfo (timezone_name )
    local_dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    now_local =datetime .now (tz )

    if repeat_type =="none":
        if local_dt <=now_local :
            raise ValueError ("Указанное время уже прошло. Исправь дату или время.")
        return local_at ,local_dt .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")

    next_local =local_at 
    next_utc =local_dt .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")
    guard =0 
    while datetime .strptime (next_local ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )<=now_local and guard <800 :
        next_local ,next_utc =compute_next_occurrence (repeat_type ,repeat_value ,next_local ,timezone_name )
        guard +=1 
    return next_local ,next_utc 


def classify_category (text :str )->str :
    t =text .lower ().replace ("ё","е")
    if any (word in t for word in ["экзам","зачет","зачёт","контрольн","самостоятельн","олимпиад","тест","егэ","огэ","впр"]):
        return "exam"
    if any (word in t for word in ["дедлайн","сдать","срок","отправить работу","сдача"]):
        return "deadline"
    if any (word in t for word in ["созвон","встреч","собран","совещан","команд","репетитор","переговор"]):
        return "meeting"
    if any (word in t for word in ["школ","лицей","класс","урок","пара","лекц","семинар","расписан","дз","домаш","домашка","реферат","доклад","лаба","лаборат","курсов","проект","учеб","презентац","учебник","тетрад","дневник","математ","алгебр","геометр","физик","русский","литератур","английск","немецк","истор","обществ","информат","биолог","хими","географ"]):
        return "study"
    if any (word in t for word in ["день рождения","поесть","спорт","трениров","врач","стоматолог","поликлиник","магазин","позвонить","купить","личн","витамин","таблет","лекарств","воду","пить воду","воды","прогул","убор","душ","документы","паспорт"]):
        return "personal"
    return "other"


def classify_priority (text :str ,category :str )->str :
    t =text .lower ().replace ("ё","е")
    if any (word in t for word in ["очень важно","крайне важно","максимально важно","сверхважно","супер важно","критически важно","срочно"]):
        return "very_high"
    if any (word in t for word in ["не срочно","когда будет время","если успею","необязательно"]):
        return "low"
    if category in {"exam","deadline"}:
        return "high"
    if any (word in t for word in ["обязательно","важно","не забыть","дедлайн"]):
        return "high"
    return "medium"



    # =========================================================
    # YandexGPT
    # =========================================================

@dataclass 
class ParsedReminder :
    topic :str 
    reminder_text :str 
    category :str 
    priority :str 
    repeat_type :str 
    repeat_value :str 
    next_local_at :str 
    next_utc_at :str 
    parse_method :str ="yandex"
    reminder_kind :str ="normal"
    interval_minutes :int =0
    window_start_time :str =""
    window_end_time :str =""
    window_days :str =""
    break_number :int =0
    break_mode :str =""



def ask_yandex (messages :list [dict ],temperature :float =0.05 ,max_tokens :int =170 ,connect_timeout:int =4 ,read_timeout:int =22 )->tuple [Optional [str ],Optional [str ]]:
    payload ={
    "modelUri":YANDEX_MODEL_URI ,
    "completionOptions":{"stream":False ,"temperature":temperature ,"maxTokens":max_tokens },
    "messages":messages ,
    }
    headers ={"Authorization":f"Api-Key {YANDEX_API_KEY }","Content-Type":"application/json"}

    try :
        response =requests .post (YANDEX_ENDPOINT ,headers =headers ,json =payload ,timeout =(connect_timeout ,read_timeout ))
    except requests .Timeout :
        return None ,"Ошибка распознавания: нейросеть не успела ответить. Попробуйте написать фразу короче или разделить её на несколько напоминаний."
    except requests .RequestException as e :
        return None ,f"Сетевой сбой: {e }"

    if response .status_code >=400 :
        return None ,f"Yandex API вернул HTTP {response .status_code }.\n{response .text }"

    try :
        data =response .json ()
        return data ["result"]["alternatives"][0 ]["message"]["text"],None 
    except Exception :
        return None ,f"Неожиданная структура ответа Yandex.\n{response .text }"


def extract_json (text :str )->Optional [dict ]:
    if not text :
        return None 
    cleaned =text .strip ()
    cleaned =re .sub (r"^```(?:json)?","",cleaned ,flags =re .IGNORECASE ).strip ()
    cleaned =re .sub (r"```$","",cleaned ).strip ()
    try :
        return json .loads (cleaned )
    except json .JSONDecodeError :
        pass 

    match =re .search (r"\{.*\}",cleaned ,re .DOTALL )
    if not match :
        return None 
    try :
        return json .loads (match .group (0 ))
    except json .JSONDecodeError :
        return None 


def current_context_for_prompt (timezone_name :str )->str :
    tz =ZoneInfo (timezone_name )
    now_local =datetime .now (tz )
    tomorrow =now_local +timedelta (days =1 )
    after_tomorrow =now_local +timedelta (days =2 )
    return (
    f"Сейчас: {now_local .strftime ('%Y-%m-%d %H:%M')}.\n"
    f"Сегодня: {now_local .strftime ('%Y-%m-%d')}.\n"
    f"Завтра: {tomorrow .strftime ('%Y-%m-%d')}.\n"
    f"Послезавтра: {after_tomorrow .strftime ('%Y-%m-%d')}.\n"
    f"День недели сегодня: {WEEKDAYS [now_local .weekday ()]}.\n"
    )



def parse_hhmm_string (value :str )->Optional [tuple [int ,int ]]:
    value =str (value or "").strip ()
    match =re .fullmatch (r"(\d{1,2}):(\d{2})",value )
    if not match :
        return None 
    hour =int (match .group (1 ))
    minute =int (match .group (2 ))
    if 0 <=hour <=23 and 0 <=minute <=59 :
        return hour ,minute 
    return None 


def format_hhmm (hour :int ,minute :int )->str :
    return f"{hour :02d}:{minute :02d}"


def time_words_for_prompt (custom_times :Optional [dict [str ,str ]]=None )->dict [str ,str ]:
    result =dict (TIME_WORD_DEFAULTS )
    if custom_times :
        for key in result :
            parsed =parse_hhmm_string (custom_times .get (key ,""))
            if parsed :
                result [key ]=format_hhmm (*parsed )
    return result 


def build_time_words_prompt_block(custom_times: Optional[dict[str, str]] = None) -> str:
    times = time_words_for_prompt(custom_times)
    return (
        "НАСТРОЙКИ СЛОВ ВРЕМЕНИ ПОЛЬЗОВАТЕЛЯ. ЭТО ВАЖНЕЕ СТАНДАРТНЫХ ЗНАЧЕНИЙ:\n"
        f"- 'утро', 'утром', 'с утра' без точного времени = {times['morning']};\n"
        f"- 'день', 'днём', 'днем', 'после обеда' без точного времени = {times['day']};\n"
        f"- 'вечер', 'вечером', 'к вечеру' без точного времени = {times['evening']};\n"
        f"- 'ночь', 'ночью' без точного времени = {times['night']}.\n\n"
        "ЖЁСТКИЕ ПРАВИЛА ДЛЯ СЛОВ ВРЕМЕНИ:\n"
        "1. Если в части фразы есть словесное время ('утром', 'вечером', 'ночью'), оно относится только к этой части фразы.\n"
        "2. Не переноси точное время из одной части сложной фразы в другую часть, если во второй части есть своё словесное время.\n"
        "3. Если рядом есть точное время, например 'в 8 утра', используй точное время 08:00, а НЕ настройку слова 'утро'.\n"
        "4. Если точное время стоит рядом со словами утра/дня/вечера/ночи, эти слова ОБЯЗАТЕЛЬНО переводят 12-часовой формат в 24-часовой.\n"
        "5. Слова 'утром', 'днём', 'вечером', 'ночью' без числа используют настройки выше. Но если рядом есть число, например 'в 9 вечера', это НЕ настройка вечера, а точное время 21:00.\n"
        "6. Если в отдельной части фразы есть дата, но нет времени, используй настройку 'утро'.\n"
        "7. Если отдельная часть сложной фразы содержит только время, но не дату, наследуй дату из предыдущей части, если это логично по смыслу.\n\n"
        "ОБЯЗАТЕЛЬНЫЕ ПРИМЕРЫ 12-ЧАСОВОГО ВРЕМЕНИ, ОСОБЕННО ПОСЛЕ ГОЛОСОВОГО ВВОДА:\n"
        "- 'в 9 утра', 'утром в 9', 'к девяти утра' = 09:00;\n"
        "- 'в 9 вечера', 'вечером в 9', 'к девяти вечера' = 21:00;\n"
        "- 'в 8 вечера', 'вечером в восемь' = 20:00;\n"
        "- 'в 9:30 вечера', 'в 9 30 вечера', 'в девять тридцать вечера' = 21:30;\n"
        "- 'в 12 ночи', 'в двенадцать ночи' = 00:00;\n"
        "- 'в 1 ночи', 'в час ночи' = 01:00;\n"
        "- 'в 12 дня', 'в полдень' = 12:00;\n"
        "- 'в 1 дня', 'в час дня' = 13:00;\n"
        "- 'в 10 ночи' = 22:00;\n"
        "- 'в 7 вечера' нельзя возвращать как 07:00, это 19:00;\n"
        "- 'в 9 вечера' нельзя возвращать как 09:00 или как настройку вечера, это строго 21:00."
    )


def build_prompt (user_text :str ,timezone_name :str ,timezone_title :str ,custom_times :Optional [dict [str ,str ]]=None )->str :
    context =current_context_for_prompt (timezone_name )
    time_words_block =build_time_words_prompt_block (custom_times )
    return f"""
Ты — строгий модуль извлечения напоминаний для Telegram-бота.
Твоя задача — понять фразу пользователя и вернуть ТОЛЬКО JSON. Никакого текста до или после JSON.

КОНТЕКСТ ВРЕМЕНИ ПОЛЬЗОВАТЕЛЯ:
{context }
Часовой пояс пользователя: {timezone_title }
{time_words_block }

ОБЯЗАТЕЛЬНЫЙ ФОРМАТ ОТВЕТА:
{{
  "reminders": [
    {{
      "topic": "краткое название напоминания",
      "datetime_local": "YYYY-MM-DD HH:MM",
      "category": "study/exam/meeting/deadline/personal/other",
      "priority": "very_high/high/medium/low",
      "repeat_type": "none/daily/weekly/monthly/yearly/weekdays/weekends/custom_weekdays/every_n_days",
      "repeat_value": "",
      "reminder_kind": "normal/interval/break_single/break_each/lesson_single/lesson_each",
      "interval_minutes": 0,
      "window_start_time": "HH:MM или пусто",
      "window_end_time": "HH:MM или пусто",
      "break_number": 0,
      "break_mode": "single/each или пусто",
      "reminder_text": "часть исходного текста, которая относится именно к этому напоминанию"
    }}
  ]
}}

ГЛАВНЫЕ ПРАВИЛА:
1. Верни только JSON.
2. datetime_local всегда в формате YYYY-MM-DD HH:MM.
3. datetime_local должен быть в часовом поясе пользователя.
4. Нельзя возвращать время в прошлом.
5. Если пользователь указал только время без даты, выбери сегодня, если это время ещё впереди; если это время сегодня уже прошло — выбери завтра.
5.1. Если пользователь пишет время как "15 24", это строго 15:24. Если пишет "1524", это 15:24. Не округляй минуты и не угадывай другой час.
5.2. Локально найденное время важнее ответа нейросети.
5.3. Если пользователь говорит время в 12-часовом формате со словом части дня, обязательно переводи его в 24-часовой формат: "в 7 вечера" = 19:00, "в 8 вечера" = 20:00, "в 9 вечера" = 21:00, "в 10 вечера" = 22:00, "в 11 вечера" = 23:00.
5.4. Для голосового ввода часто приходят фразы "в девять вечера", "вечером в девять", "в девять тридцать вечера". Их нельзя считать утром: это 21:00 или 21:30.
5.5. "в 12 ночи" = 00:00, "в час ночи" = 01:00, "в час дня" = 13:00.
5.6. Разговорные голосовые формы со словами "час/минут" разбирай как точное время: "в час 30 минут ночи" = 01:30, "в один час тридцать минут ночи" = 01:30, "в девять часов тридцать минут вечера" = 21:30, "в два часа пятнадцать дня" = 14:15.
5.7. Формы без слова "минут" тоже точное время: "в девять тридцать вечера" = 21:30, "в два пятнадцать дня" = 14:15, "час тридцать ночи" = 01:30.
5.8. Формы "без ..." и "пол ..." разбирай по-русски: "без десяти девять вечера" = 20:50, "без четверти девять" = 08:45 или 20:45 при слове "вечера", "пол второго ночи" = 01:30, "пол девятого вечера" = 20:30.
6. Если пользователь указал дату без времени, используй настройку пользователя для слова "утро" из блока выше.
7. Если пользователь написал одно из слов времени без точного времени, используй настройки пользователя из блока выше.
8. "после обеда" используй как настройку слова "день".
9. "к вечеру" используй как настройку слова "вечер".
10. "завтра" — дата завтра из контекста.
11. "послезавтра" — дата послезавтра из контекста.
12. "через 2 часа", "через 30 минут", "через 3 дня" считай от текущего времени из контекста. Если сказано "через 3 дня в 8:30", дата = через 3 дня, время = 08:30. Если сказано "через 3 дня утром", дата = через 3 дня, время = настройка "утро".
13. Если указан день недели без даты, выбери ближайшую будущую дату этого дня недели.
14. Если указан день и месяц без года, выбери ближайшую будущую такую дату.
15. reminder_text должен быть частью исходного текста, которая относится именно к этому напоминанию. Если напоминание одно — можно вернуть весь текст пользователя.
16. topic — короткая понятная тема без даты, времени и лишних слов.
17. Если фраза сложная или непонятная, не думай долго: верни JSON так, как понял. Если не понял дату/время — поставь datetime_local = "", но остальные поля заполни по смыслу.

ДОПОЛНИТЕЛЬНЫЕ ПРАВИЛА ВРЕМЕНИ ДЛЯ СЛОЖНЫХ ФРАЗ:
1. В сложной фразе каждое событие разбирай отдельно: своя дата, своё время, своя тема.
2. Если часть фразы содержит дату, но не содержит время, ставь время настройки "утро".
3. Если часть фразы содержит время, но не содержит дату, используй ближайшую подходящую дату. Если предыдущая часть явно задала общую дату, наследуй её.
4. Если фраза "завтра утром школа, а вечером тренировка", второе событие тоже завтра вечером.
5. Если фраза "завтра в 15 уроки, а в понедельник утром школа", первое событие завтра в 15:00, второе в ближайший понедельник во время настройки "утро".
6. Если фраза "в субботу утром школа, а в понедельник вечером тренировка", первое событие в ближайшую субботу во время настройки "утро", второе в ближайший понедельник во время настройки "вечер".
7. Если фраза "сегодня и завтра в 18:00 позвонить", создай два напоминания на 18:00.
8. Если фраза "сегодня утром и вечером пить таблетки", создай два напоминания: сегодня утром и сегодня вечером.
9. Если фраза "каждый день утром пить витамины", это одно повторяющееся напоминание daily, а не несколько отдельных.
10. Если фраза "каждую среду вечером английский", это одно повторяющееся напоминание custom_weekdays со средой и временем настройки "вечер".
11. Для "через 3 дня в 8:30" дата = сегодня + 3 дня, время = 08:30. Для "через 3 дня утром" дата = сегодня + 3 дня, время = настройка "утро".

ИНТЕРВАЛЬНЫЕ НАПОМИНАНИЯ:
1. Фразы вида "каждые 2 часа пить воду", "раз в 30 минут повторять", "каждые полчаса" — это reminder_kind="interval".
2. Для interval укажи interval_minutes, window_start_time и window_end_time.
3. Если период не указан, считай период с пользовательского "утра" до пользовательского "вечера".
4. Если написано "в течение дня" или "весь день", конец периода = пользовательский "вечер".
5. Если написано "до вечера", конец периода = пользовательский "вечер". Если "до ночи", конец = пользовательская "ночь".
6. "каждый день каждые 2 часа с 9 до 18" = interval + repeat_type="daily".
7. "по будням каждые 2 часа с 9 до 18" = interval + repeat_type="weekdays".
8. "в понедельник каждые 2 часа до вечера" = interval на ближайший понедельник, repeat_type="none".
9. "каждый понедельник каждые 2 часа до вечера" = interval + repeat_type="custom_weekdays", repeat_value="0".
10. Обычное одноразовое напоминание не должно иметь reminder_kind="interval".

НАПОМИНАНИЯ ПО ШКОЛЬНЫМ ПЕРЕМЕНАМ:
1. "во 2 перемену сделать русский" = reminder_kind="break_single", break_number=2, break_mode="single".
2. "каждую перемену повторять русский" = reminder_kind="break_each", break_mode="each".
3. Если в фразе указан день недели, используй перемены именно этого дня.
4. Время перемен берётся из настроек пользователя, поэтому datetime_local можно вернуть пустым, если точное время неизвестно.

КОМБИНИРОВАННЫЕ ФРАЗЫ:
1. Если пользователь говорит "каждую субботу и среду", "каждый понедельник и пятницу", "по вторникам и четвергам" — это ОДНО повторяющееся напоминание custom_weekdays, а не несколько напоминаний.
2. Массив reminders из нескольких объектов используй только для одноразовых разных дат: "сегодня и завтра", "сегодня и в субботу", "в понедельник и среду" без слов повтора.
3. Если пользователь перечисляет несколько одноразовых дат или разных дел, создай несколько объектов в reminders.
3.1. Разделяй разные одноразовые события по словам "а", "потом", "ещё", "еще", "также", а также по запятым и точкам с запятой, если рядом разные даты/дни недели/дела.
3.2. Фраза "в субботу мне в школу а в понедельник на работу" => два одноразовых напоминания: первое про школу в ближайшую субботу, второе про работу в ближайший понедельник.
3.2.1. Фраза "завтра в 15 сделать уроки, а в понедельник утром пойти в школу" => два одноразовых напоминания: первое завтра в 15:00 про уроки, второе в ближайший понедельник во время настройки "утро" про школу. Не переноси время 15:00 на второе событие.
3.2.2. Фраза "завтра утром школа, а вечером тренировка" => два напоминания на завтра: первое во время настройки "утро", второе во время настройки "вечер".
3.2.3. Фраза "в субботу утром школа, а в понедельник вечером тренировка" => два напоминания: суббота во время настройки "утро", понедельник во время настройки "вечер".
3.2.4. Фраза "сегодня утром и вечером пить таблетки" => два напоминания на сегодня: утром и вечером.
3.3. Если общее время указано один раз, например "в субботу и понедельник в 9:00", примени 9:00 к каждому одноразовому напоминанию. Это НЕ повтор, если нет слов "каждый", "по", "еженедельно".
3.4. Если у каждого события своё время, например "в субботу в 9 школа, а в понедельник в 12 работа", создай два напоминания с разным временем.
4. "сегодня и завтра в 18:00 позвонить клиенту" => два одноразовых напоминания: сегодня 18:00 и завтра 18:00.
5. "сегодня, завтра и послезавтра в 9:00 пить витамины" => три одноразовых напоминания.
6. "сегодня и в субботу в 18:00 позвонить клиенту" => два одноразовых напоминания: сегодня 18:00 и ближайшая будущая суббота 18:00.
7. "в понедельник и среду в 8:00" без слов "каждый/по/еженедельно" => два одноразовых напоминания на ближайшие понедельник и среду.
8. Если есть слова "каждый", "каждую", "каждое", "по понедельникам", "по четвергам", "еженедельно", тогда это повтор, а не несколько одноразовых дат.
8.1. День недели сам по себе НЕ означает повтор. "в четверг сделать уроки", "на четверг уроки", "четверг уроки" — это одноразовое напоминание на ближайший четверг.
8.2. Обычное слово "по" в школьных предметах НЕ означает повтор: "по математике", "по русскому", "по истории" — это часть темы или категории, а не repeat_type.
9. Если фраза конфликтная, например "сегодня и завтра каждый день в 10:00", лучше верни одно напоминание с repeat_type="daily", datetime_local=ближайшее будущее время 10:00.
10. Для каждого объекта reminders используй свой reminder_text — только кусок фразы про конкретное событие. Например: "в субботу мне в школу, а в понедельник на работу" => для первого reminder_text="в субботу мне в школу", для второго reminder_text="в понедельник на работу".

КАТЕГОРИИ:
- study — учёба, уроки, домашнее задание, доклад, проект, лабораторная, реферат
- exam — контрольная, экзамен, зачёт, тест, олимпиада
- meeting — встреча, созвон, собрание, репетитор, переговоры
- deadline — дедлайн, срок, сдать, отправить работу
- personal — личное, здоровье, спорт, покупки, звонки, бытовые дела, витамины
- other — если категория не ясна

ПРИОРИТЕТ:
- very_high — если пользователь пишет "очень важно", "крайне важно", "максимально важно", "критически важно", "сверхважно", "супер важно"
- high — важно, срочно, обязательно, контрольная, экзамен, дедлайн, не забыть
- medium — обычная важность
- low — не срочно, можно потом, необязательно

ПОВТОРЫ:
1. Если повтор не указан: repeat_type = "none", repeat_value = "".
2. "каждый день", "ежедневно", "каждое утро", "каждый вечер" => repeat_type = "daily", repeat_value = "".
3. "каждую неделю", "раз в неделю" без конкретного дня недели => repeat_type = "weekly", repeat_value = "".
4. "каждый месяц", "раз в месяц", "ежемесячно" => repeat_type = "monthly", repeat_value = "".
5. "каждый год", "раз в год", "ежегодно" => repeat_type = "yearly", repeat_value = "".
6. "по будням", "каждый будний день", "в будни", "в будние дни" => repeat_type = "weekdays", repeat_value = "".
7. "по выходным", "каждые выходные", "в выходные" => repeat_type = "weekends", repeat_value = "".
8. Если указан конкретный день недели с маркером повтора, НЕ ставь weekly. Всегда ставь custom_weekdays, кроме случая "суббота и воскресенье", где ставь weekends.
9. Дни недели кодируются так: понедельник=0, вторник=1, среда=2, четверг=3, пятница=4, суббота=5, воскресенье=6.
10. "каждый понедельник", "каждую неделю по понедельникам", "по понедельникам", "каждый пн" => custom_weekdays, repeat_value = "0".
11. "каждый вторник", "по вторникам", "каждый вт" => custom_weekdays, repeat_value = "1".
12. "каждую среду", "по средам", "каждый ср" => custom_weekdays, repeat_value = "2".
13. "каждый четверг", "по четвергам", "каждый чт" => custom_weekdays, repeat_value = "3".
14. "каждую пятницу", "по пятницам", "каждый пт" => custom_weekdays, repeat_value = "4".
15. "каждую субботу", "по субботам", "каждый сб" => custom_weekdays, repeat_value = "5".
16. "каждое воскресенье", "по воскресеньям", "каждый вс" => custom_weekdays, repeat_value = "6".
17. "каждый понедельник, среду и пятницу" => custom_weekdays, repeat_value = "0,2,4".
18. "каждую субботу и воскресенье", "по субботам и воскресеньям", "каждый сб и вс" => repeat_type = "weekends", repeat_value = "".
19. "каждые 3 дня", "через каждые 3 дня" => every_n_days, repeat_value = "3".
20. "через день" без слов "каждый/каждые" — это одноразовое напоминание на завтра, а не повтор.
20. repeat_value для custom_weekdays всегда возвращай отсортированным: "0,2,4", а не "4,0,2".

ТЕКСТ ПОЛЬЗОВАТЕЛЯ:
{user_text }
""".strip ()


def build_fallback_prompt (user_text :str ,timezone_name :str ,timezone_title :str ,custom_times :Optional [dict [str ,str ]]=None )->str :
    context =current_context_for_prompt (timezone_name )
    time_words_block =build_time_words_prompt_block (custom_times )
    return f"""
Верни только JSON. Это запасной короткий разбор.

КОНТЕКСТ:
{context }
Часовой пояс: {timezone_title }
{time_words_block }

ФОРМАТ:
{{
  "topic": "краткая тема",
  "datetime_local": "YYYY-MM-DD HH:MM",
  "priority": "very_high/high/medium/low",
  "reminder_text": "полный текст пользователя"
}}

ПРАВИЛА:
1. Только JSON.
2. datetime_local строго YYYY-MM-DD HH:MM.
3. Если указано только время, ставь сегодня, если ещё не прошло, иначе завтра.
4. Если указана дата без времени, используй настройку пользователя для слова "утро".
5. Если есть слова "утро", "день", "вечер", "ночь", "после обеда" или "к вечеру" без точного времени, используй настройки пользователя из блока выше.
5.1. Если рядом с числом есть слово части дня, это точное 12-часовое время, а не настройка слова: "в 9 вечера" = 21:00, "вечером в 8" = 20:00, "в 9 утра" = 09:00, "в час ночи" = 01:00, "в час дня" = 13:00.
5.2. После голосового ввода особенно внимательно обрабатывай фразы словами: "в девять вечера" = 21:00, "в восемь вечера" = 20:00, "в девять тридцать вечера" = 21:30.
5.3. Разговорные формы со словами "час/минут" — это точное время: "в час 30 минут ночи" = 01:30, "в один час тридцать минут ночи" = 01:30, "в девять часов тридцать минут вечера" = 21:30.
5.4. "без десяти девять вечера" = 20:50, "без четверти девять вечера" = 20:45, "пол второго ночи" = 01:30, "пол девятого вечера" = 20:30.
6. "завтра", "послезавтра", "через 2 часа", "через 3 дня" нужно пересчитать в точную дату и время. Для "через 3 дня в 8:30" бери дату через 3 дня, но точное время 08:30.
7. very_high ставь для фраз "очень важно", "крайне важно", "максимально важно", "критически важно".
8. Если приоритет непонятен, ставь medium.
9. Если дату и время совсем нельзя понять, datetime_local = "".
10. Нельзя возвращать время в прошлом.
11. Если написано "каждую субботу", "каждый понедельник", "по вторникам" и т.п., datetime_local должен быть ближайшим будущим указанным днём недели.
12. Если написано "каждую субботу" без точного времени, используй настройку слова "утро" только если сказано "утром"; иначе используй 10:00.
13. Если сложно понять фразу, не рассуждай долго: верни JSON так, как понял. Если не понял дату/время, datetime_local = "".

ТЕКСТ:
{user_text }
""".strip ()


def build_time_edit_prompt(current_data: dict, user_fix: str, custom_times: Optional[dict[str, str]] = None) -> str:
    timezone_name = current_data["timezone_name"]
    context = current_context_for_prompt(timezone_name)
    time_words_block = build_time_words_prompt_block(custom_times)
    return f"""
Верни только JSON.
Нужно изменить только datetime_local. Пользователь может написать только время или полную дату с временем.

Контекст:
{context}
Часовой пояс: {current_data['timezone_title']}.
{time_words_block}

Текущее напоминание:
topic: {current_data['topic']}
datetime_local: {current_data['next_local_at']}
repeat_type: {current_data['repeat_type']}
repeat_value: {current_data['repeat_value']}
reminder_text: {current_data['reminder_text']}

Новая правка пользователя:
{user_fix}

Формат:
{{ "datetime_local": "YYYY-MM-DD HH:MM" }}

Правила:
- если пользователь пишет только время, например "23:00", оставь старую дату и измени только время;
- если пользователь пишет дату и время, например "10 мая в 23:00", измени и дату, и время;
- если пользователь пишет дату без времени, например "10 мая", оставь старое время;
- если пользователь пишет "завтра утром" или "10 мая вечером", используй настройки слов времени пользователя;
- если пользователь пишет "на час позже", прибавь час к текущему datetime_local;
- если пользователь указал дату и время, например "10 мая в 23:00", измени и дату, и время;
- если пользователь указал дату без года, выбери ближайшую будущую такую дату;
- если "завтра в 19:30", поставь завтрашнюю дату из контекста;
- если "через 2 часа", считай от текущего времени из контекста;
- если пользователь пишет время двумя числами через пробел, например "15 24", это строго 15:24;
- "1524" означает 15:24, "0930" означает 09:30;
- если пользователь пишет "в 9 вечера", "вечером в 9", "в девять вечера", ставь 21:00, а не 09:00;
- если пользователь пишет "в 8 вечера", "вечером в восемь", ставь 20:00, а не 08:00;
- если пользователь пишет "в 12 ночи", ставь 00:00; если "в час ночи", ставь 01:00; если "в час дня", ставь 13:00;
- если пользователь пишет "в час 30 минут ночи", "в один час тридцать минут ночи" или "час тридцать ночи", ставь 01:30;
- если пользователь пишет "в девять часов тридцать минут вечера" или "в девять тридцать вечера", ставь 21:30;
- если пользователь пишет "без десяти девять вечера", ставь 20:50; если "без четверти девять вечера", ставь 20:45; если "пол второго ночи", ставь 01:30;
- если пользователь пишет "утром", "днём", "вечером", "ночью", "после обеда" или "к вечеру" без точного времени, используй настройки пользователя из блока выше;
- не округляй и не заменяй минуты: "15 24" нельзя превращать в 15:00, 16:00 или 16:24;
- если локально не понял время, верни своё лучшее понимание;
- если указано только время, используй текущую дату напоминания, а если получится прошлое время — ближайшее будущее;
- если не понял время, верни пустую строку.
""".strip()


def parse_exact_local_datetime(raw: str, timezone_name: str) -> tuple[Optional[str], Optional[str]]:
    raw = raw.strip()
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}\s\d{2}:\d{2}", raw):
        dt = datetime.strptime(raw, "%Y-%m-%d %H:%M").replace(tzinfo=ZoneInfo(timezone_name))
        return dt.strftime("%Y-%m-%d %H:%M"), dt.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    return None, None


def parse_relative_datetime_from_now(text: str, timezone_name: str, custom_times: Optional[dict[str, str]] = None) -> Optional[tuple[str, str, str]]:
    """
    Локальный разбор фраз вида "через 2 минуты", "через час", "через 3 дня".

    Важное правило:
    - "через 2 минуты" считается от текущего момента;
    - "через 3 дня в 8:30" берёт дату через 3 дня, но время ставит 08:30;
    - "через 3 дня утром" берёт дату через 3 дня и пользовательскую настройку "утро".
    """
    raw = text or ""
    t = normalize_spaces(raw.lower().replace("ё", "е"))
    if not t:
        return None

    # Не путаем относительное время с повтором: "каждые 2 дня", "через каждые 2 дня".
    if re.search(r"\b(кажд(?:ый|ая|ое|ые|ую)?|каждые|раз\s+в|через\s+каждые)\b", t):
        return None

    tz = ZoneInfo(timezone_name)
    now_local = datetime.now(tz).replace(second=0, microsecond=0)

    def apply_specific_time_if_day_based(candidate: datetime) -> datetime:
        explicit = extract_explicit_time_from_text(t)
        if explicit:
            hour, minute = explicit
            return candidate.replace(hour=hour, minute=minute, second=0, microsecond=0)
        default_words = extract_default_time_from_words(t, custom_times)
        if default_words:
            hour, minute = default_words
            return candidate.replace(hour=hour, minute=minute, second=0, microsecond=0)
        return candidate

    if re.search(r"\b(?:через\s+)?(?:пол\s*часа|полчаса)\b", t):
        candidate = now_local + timedelta(minutes=30)
        return candidate.strftime("%Y-%m-%d %H:%M"), candidate.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), "через 30 минут"

    if re.search(r"\bчерез\s+час\b", t):
        candidate = now_local + timedelta(hours=1)
        return candidate.strftime("%Y-%m-%d %H:%M"), candidate.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), "через 1 час"

    if re.search(r"\bчерез\s+день\b", t):
        candidate = apply_specific_time_if_day_based(now_local + timedelta(days=1))
        return candidate.strftime("%Y-%m-%d %H:%M"), candidate.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), "через 1 день"

    word_numbers = {
        "один": 1, "одну": 1, "одно": 1,
        "два": 2, "две": 2, "пару": 2,
        "три": 3, "четыре": 4, "пять": 5,
        "шесть": 6, "семь": 7, "восемь": 8, "девять": 9, "десять": 10,
    }
    number_pattern = r"\d{1,3}|" + "|".join(word_numbers.keys())
    m = re.search(
        rf"\bчерез\s+({number_pattern})\s*"
        r"(минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|неделю|недели|недель)\b",
        t,
    )
    if not m:
        return None

    raw_number = m.group(1)
    n = int(raw_number) if raw_number.isdigit() else word_numbers.get(raw_number)
    if not n or n <= 0:
        return None

    unit = m.group(2)
    if unit.startswith("мин") or unit == "м":
        candidate = now_local + timedelta(minutes=n)
        details = f"через {n} мин."
    elif unit == "ч" or unit.startswith("час"):
        candidate = now_local + timedelta(hours=n)
        details = f"через {n} ч."
    elif unit.startswith("недел"):
        candidate = apply_specific_time_if_day_based(now_local + timedelta(weeks=n))
        details = f"через {n} нед."
    else:
        candidate = apply_specific_time_if_day_based(now_local + timedelta(days=n))
        details = f"через {n} дн."

    return candidate.strftime("%Y-%m-%d %H:%M"), candidate.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), details


MONTH_WORD_TO_NUMBER = {
    "января": 1, "январь": 1, "янв": 1,
    "февраля": 2, "февраль": 2, "фев": 2,
    "марта": 3, "март": 3, "мар": 3,
    "апреля": 4, "апрель": 4, "апр": 4,
    "мая": 5, "май": 5,
    "июня": 6, "июнь": 6, "июн": 6,
    "июля": 7, "июль": 7, "июл": 7,
    "августа": 8, "август": 8, "авг": 8,
    "сентября": 9, "сентябрь": 9, "сен": 9, "сент": 9,
    "октября": 10, "октябрь": 10, "окт": 10,
    "ноября": 11, "ноябрь": 11, "ноя": 11,
    "декабря": 12, "декабрь": 12, "дек": 12,
}


def normalize_edit_year(raw_year: Optional[str], now_year: int) -> tuple[int, bool]:
    if not raw_year:
        return now_year, False
    year = int(raw_year)
    if year < 100:
        year = 2000 + year
    return year, True


def safe_datetime_date_base(year: int, month: int, day: int, tz) -> Optional[datetime]:
    try:
        return datetime(year, month, day, 0, 0, tzinfo=tz)
    except ValueError:
        return None


def extract_date_base_from_edit_text(text: str, now_local: datetime, current_base: datetime) -> Optional[tuple[datetime, str, bool]]:
    """
    Достаёт дату из текста при ручном редактировании времени.
    Нужно, чтобы фразы вроде "10 мая в 23:00" меняли не только часы, но и день.
    """
    t = text.lower().replace("ё", "е")
    t = re.sub(r"\s+", " ", t).strip()
    tz = now_local.tzinfo or current_base.tzinfo or ZoneInfo(DEFAULT_TIMEZONE_NAME)

    if "послезавтра" in t:
        return (now_local + timedelta(days=2)).replace(hour=0, minute=0, second=0, microsecond=0), "relative", False
    if "завтра" in t:
        return (now_local + timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0), "relative", False
    if "сегодня" in t:
        return now_local.replace(hour=0, minute=0, second=0, microsecond=0), "relative", False

    m = re.search(r"(?<!\d)(20\d{2})[.\-/](\d{1,2})[.\-/](\d{1,2})(?!\d)", t)
    if m:
        year = int(m.group(1))
        month = int(m.group(2))
        day = int(m.group(3))
        dt = safe_datetime_date_base(year, month, day, tz)
        if dt:
            return dt, "absolute", True

    m = re.search(r"(?<!\d)(\d{1,2})[.\-/](\d{1,2})(?:[.\-/](\d{2,4}))?(?!\d)", t)
    if m:
        day = int(m.group(1))
        month = int(m.group(2))
        year, has_year = normalize_edit_year(m.group(3), now_local.year)
        dt = safe_datetime_date_base(year, month, day, tz)
        if dt:
            return dt, "absolute", has_year

    month_names = "|".join(sorted((re.escape(name) for name in MONTH_WORD_TO_NUMBER), key=len, reverse=True))
    m = re.search(rf"(?<!\d)(\d{{1,2}})\s+({month_names})(?:\s+(20\d{{2}}|\d{{2}}))?(?!\d)", t)
    if m:
        day = int(m.group(1))
        month = MONTH_WORD_TO_NUMBER[m.group(2)]
        year, has_year = normalize_edit_year(m.group(3), now_local.year)
        dt = safe_datetime_date_base(year, month, day, tz)
        if dt:
            return dt, "absolute", has_year

    weekday_patterns = {
        0: r"\b(понедельник|понедельника|понедельнику|пн)\b",
        1: r"\b(вторник|вторника|вторнику|вт)\b",
        2: r"\b(среда|среду|среде|ср)\b",
        3: r"\b(четверг|четверга|четвергу|чт)\b",
        4: r"\b(пятница|пятницу|пятнице|пт)\b",
        5: r"\b(суббота|субботу|субботе|сб)\b",
        6: r"\b(воскресенье|воскресенья|воскресенью|вс)\b",
    }
    for day_num, pattern in weekday_patterns.items():
        if re.search(pattern, t):
            candidate = now_local.replace(hour=0, minute=0, second=0, microsecond=0)
            for _ in range(8):
                if candidate.weekday() == day_num:
                    return candidate, "weekday", False
                candidate += timedelta(days=1)

    return None



def extract_date_from_text(text: str, now_local: datetime) -> Optional[tuple[datetime, str, bool]]:
    """
    Общий локальный разбор даты для создания интервальных напоминаний.
    Возвращает базовую дату без времени: сегодня, завтра, послезавтра,
    дату вида 10 мая / 10.05 / 2026-05-10 или ближайший день недели.
    """
    base = now_local.replace(hour=0, minute=0, second=0, microsecond=0)
    return extract_date_base_from_edit_text(text, now_local, base)


def extract_explicit_time_from_text(text: str) -> Optional[tuple[int, int]]:
    """
    Локальный приоритетный разбор времени.

    Усиленная версия v7:
    - понимает числовые и словесные часы: "в 9 вечера", "в девять вечера", "в час ночи";
    - понимает разговорные минуты: "в час 30 минут ночи", "в девять тридцать вечера";
    - понимает формы "без десяти девять вечера", "без четверти девять", "пол второго ночи";
    - учитывает часть суток рядом с числом: утро/день/вечер/ночь;
    - не превращает "в 1 ночи" в 13:00.
    """
    t = text.lower().replace("ё", "е").strip()
    t = re.sub(r"\s+", " ", t)
    # Убираем длительность вида "на 2 дня", чтобы она не распознавалась как "в 2 дня" = 14:00.
    t = re.sub(
        r"\bна\s+(?:\d{1,3}|один|одну|одно|два|две|три|четыре|пять|шесть|семь|восемь|девять|десять|пару)\s+(?:день|дня|дней|сутки|суток)\b",
        " ",
        t,
    )
    t = re.sub(r"\s+", " ", t).strip()

    if re.search(r"\b(в\s+)?полдень\b", t):
        return 12, 0
    if re.search(r"\b(в\s+)?полночь\b", t):
        return 0, 0

    day_part_patterns = {
        "morning": r"\b(утра|утром|утро)\b",
        "day": r"\b(дня|днем|дн[её]м|день|после\s+обеда)\b",
        "evening": r"\b(вечера|вечером|вечер|к\s+вечеру)\b",
        "night": r"\b(ночи|ночью|ночь)\b",
    }

    def detect_day_part(fragment: str) -> str:
        for part, pattern in day_part_patterns.items():
            if re.search(pattern, fragment):
                return part
        return ""

    def detect_day_part_around(start: int, end: int) -> str:
        after = t[end:min(len(t), end + 45)]
        before = t[max(0, start - 45):start]
        # Сначала смотрим после числа: "9 вечера" точнее, чем общий контекст слева.
        return detect_day_part(after) or detect_day_part(before)

    def adjust_hour_by_day_part(hour: int, day_part: str) -> int:
        if not day_part:
            return hour
        if day_part == "morning":
            if hour == 12:
                return 0
            return hour
        if day_part == "day":
            if 1 <= hour <= 11:
                return hour + 12
            return hour
        if day_part == "evening":
            if hour == 12:
                return 0
            if 1 <= hour <= 11:
                return hour + 12
            return hour
        if day_part == "night":
            if hour == 12:
                return 0
            # "в 1 ночи", "в 2 ночи" — это 01:00, 02:00, а не 13:00, 14:00.
            if 1 <= hour <= 5:
                return hour
            # Нестандартные фразы типа "в 10 ночи" чаще означают поздний вечер.
            if 6 <= hour <= 11:
                return hour + 12
            return hour
        return hour

    token_matches = list(re.finditer(r"\d+|[а-яa-z]+", t))
    tokens = [m.group(0) for m in token_matches]

    number_words = {
        "ноль": 0, "нуль": 0,
        "один": 1, "одна": 1, "одно": 1, "одного": 1, "одной": 1, "одному": 1, "одну": 1,
        "два": 2, "две": 2, "двух": 2, "двум": 2,
        "три": 3, "трех": 3, "трем": 3,
        "четыре": 4, "четырех": 4, "четырем": 4,
        "пять": 5, "пяти": 5,
        "шесть": 6, "шести": 6,
        "семь": 7, "семи": 7,
        "восемь": 8, "восьми": 8,
        "девять": 9, "девяти": 9,
        "десять": 10, "десяти": 10,
        "одиннадцать": 11, "одиннадцати": 11,
        "двенадцать": 12, "двенадцати": 12,
        "тринадцать": 13, "тринадцати": 13,
        "четырнадцать": 14, "четырнадцати": 14,
        "пятнадцать": 15, "пятнадцати": 15,
        "шестнадцать": 16, "шестнадцати": 16,
        "семнадцать": 17, "семнадцати": 17,
        "восемнадцать": 18, "восемнадцати": 18,
        "девятнадцать": 19, "девятнадцати": 19,
        "двадцать": 20, "двадцати": 20,
        "тридцать": 30, "тридцати": 30,
        "сорок": 40, "сорока": 40,
        "пятьдесят": 50, "пятидесяти": 50,
    }
    unit_words = {word: value for word, value in number_words.items() if 0 <= value <= 9}
    tens_words = {word: value for word, value in number_words.items() if value in {20, 30, 40, 50}}
    hour_words = dict(number_words)
    hour_words.update({"час": 1, "часу": 1, "часа": 1})
    ordinal_hour_words = {
        "первого": 1, "первой": 1,
        "второго": 2, "второй": 2,
        "третьего": 3, "третьей": 3,
        "четвертого": 4, "четвертой": 4,
        "пятого": 5, "пятой": 5,
        "шестого": 6, "шестой": 6,
        "седьмого": 7, "седьмой": 7,
        "восьмого": 8, "восьмой": 8,
        "девятого": 9, "девятой": 9,
        "десятого": 10, "десятой": 10,
        "одиннадцатого": 11, "одиннадцатой": 11,
        "двенадцатого": 12, "двенадцатой": 12,
    }
    minute_markers = {"минута", "минуту", "минуты", "минут", "мин", "м"}
    hour_markers = {"час", "часа", "часов", "часу", "ч"}
    prep_tokens = {"в", "во", "к", "ко", "на"}
    duration_bad_before = {"через", "каждые", "каждый", "каждую", "каждое", "каждыи", "раз"}

    def token_window(start_index: int, end_index: int, extra: int = 6) -> str:
        if not tokens:
            return ""
        left = max(0, start_index - extra)
        right = min(len(tokens), end_index + extra)
        return " ".join(tokens[left:right])

    def day_part_near_tokens(start_index: int, end_index: int) -> str:
        if not tokens:
            return ""
        return detect_day_part(token_window(start_index, end_index, 6))

    def parse_number_at(index: int, max_value: int = 59) -> Optional[tuple[int, int]]:
        if index >= len(tokens):
            return None
        token = tokens[index]
        if token.isdigit():
            value = int(token)
            if 0 <= value <= max_value:
                return value, index + 1
            return None
        if token in number_words:
            value = number_words[token]
            end_index = index + 1
            if token in tens_words and end_index < len(tokens) and tokens[end_index] in unit_words:
                value += unit_words[tokens[end_index]]
                end_index += 1
            if 0 <= value <= max_value:
                return value, end_index
        return None

    def parse_hour_at(index: int) -> Optional[tuple[int, int]]:
        if index >= len(tokens):
            return None
        token = tokens[index]
        if token.isdigit():
            value = int(token)
            if 0 <= value <= 23:
                return value, index + 1
            return None
        if token in hour_words:
            value = hour_words[token]
            if 0 <= value <= 23:
                return value, index + 1
        return None

    def skip_markers(index: int, markers: set[str]) -> int:
        while index < len(tokens) and tokens[index] in markers:
            index += 1
        return index

    def token_start(index: int) -> int:
        return token_matches[index].start() if 0 <= index < len(token_matches) else 0

    def token_end(index: int) -> int:
        return token_matches[index - 1].end() if 0 < index <= len(token_matches) else len(t)

    def has_clock_context(start_index: int, end_index: int, had_preposition: bool, minute_found: bool) -> bool:
        if start_index > 0 and tokens[start_index - 1] in duration_bad_before:
            return False
        if start_index > 1 and tokens[start_index - 2] in duration_bad_before:
            return False
        if had_preposition:
            return True
        if day_part_near_tokens(start_index, end_index):
            return True
        # "девять тридцать" без части суток тоже похоже на время, но "три дня" — нет.
        if minute_found:
            return True
        return False

    # "без десяти девять вечера", "без 15 минут 9", "без четверти девять".
    for i, token in enumerate(tokens):
        if token != "без":
            continue
        minute = None
        j = i + 1
        if j < len(tokens) and tokens[j] in {"четверти", "четверть"}:
            minute = 15
            j += 1
        else:
            parsed_minute = parse_number_at(j, 59)
            if parsed_minute:
                minute, j = parsed_minute
        if minute is None or not (1 <= minute <= 59):
            continue
        j = skip_markers(j, minute_markers)
        parsed_hour = parse_hour_at(j)
        if not parsed_hour:
            continue
        target_hour, end_index = parsed_hour
        day_part = day_part_near_tokens(i, end_index) or detect_day_part_around(token_start(i), token_end(end_index))
        target_hour = adjust_hour_by_day_part(target_hour, day_part)
        total_minutes = target_hour * 60 - minute
        total_minutes %= 24 * 60
        return total_minutes // 60, total_minutes % 60

    # "пол второго ночи", "половина девятого вечера", "пол 9 вечера".
    for i, token in enumerate(tokens):
        if token not in {"пол", "половина", "половину"}:
            continue
        j = i + 1
        target_hour = None
        if j < len(tokens) and tokens[j] in ordinal_hour_words:
            target_hour = ordinal_hour_words[tokens[j]]
            end_index = j + 1
        else:
            parsed_hour = parse_hour_at(j)
            if not parsed_hour:
                continue
            target_hour, end_index = parsed_hour
        day_part = day_part_near_tokens(i, end_index) or detect_day_part_around(token_start(i), token_end(end_index))
        target_hour = adjust_hour_by_day_part(target_hour, day_part)
        hour = (target_hour - 1) % 24
        return hour, 30

    # "четверть девятого вечера" = 20:15.
    for i, token in enumerate(tokens):
        if token not in {"четверть", "четверти"}:
            continue
        if i > 0 and tokens[i - 1] == "без":
            continue
        j = i + 1
        if j >= len(tokens) or tokens[j] not in ordinal_hour_words:
            continue
        target_hour = ordinal_hour_words[tokens[j]]
        end_index = j + 1
        day_part = day_part_near_tokens(i, end_index) or detect_day_part_around(token_start(i), token_end(end_index))
        target_hour = adjust_hour_by_day_part(target_hour, day_part)
        hour = (target_hour - 1) % 24
        return hour, 15

    # Разговорный формат: "в час 30 минут ночи", "в девять тридцать вечера",
    # "девять часов тридцать минут вечера", "вечером в девять тридцать".
    for i in range(len(tokens)):
        had_preposition = False
        start_index = i
        hour_index = i
        if tokens[i] in prep_tokens:
            had_preposition = True
            hour_index = i + 1
        elif i > 0 and tokens[i - 1] in prep_tokens:
            had_preposition = True
        if hour_index >= len(tokens):
            continue
        parsed_hour = parse_hour_at(hour_index)
        if not parsed_hour:
            continue
        hour, j = parsed_hour
        j = skip_markers(j, hour_markers)

        minute = 0
        minute_found = False
        # "с половиной" / "половиной" после часа.
        if j < len(tokens) and tokens[j] == "с" and j + 1 < len(tokens) and tokens[j + 1] in {"половиной", "половина"}:
            minute = 30
            minute_found = True
            j += 2
        elif j < len(tokens) and tokens[j] in {"половиной", "половина"}:
            minute = 30
            minute_found = True
            j += 1
        else:
            parsed_minute = parse_number_at(j, 59)
            if parsed_minute:
                candidate_minute, new_j = parsed_minute
                # Для "в 9 дней" не считаем слово "дней" минутами; нужен маркер минут,
                # часть суток или явная конструкция с предлогом/часами.
                marker_after = new_j < len(tokens) and tokens[new_j] in minute_markers
                day_part_after = day_part_near_tokens(hour_index, new_j)
                if candidate_minute <= 59 and (candidate_minute >= 10 or marker_after or day_part_after or had_preposition):
                    minute = candidate_minute
                    minute_found = True
                    j = skip_markers(new_j, minute_markers)

        end_index = j
        if not has_clock_context(hour_index, end_index, had_preposition, minute_found):
            continue
        # Не превращаем "в 9 дней" / "на 2 дня" в время.
        prep_token = ""
        if had_preposition:
            if start_index < len(tokens) and tokens[start_index] in prep_tokens:
                prep_token = tokens[start_index]
            elif hour_index > 0 and tokens[hour_index - 1] in prep_tokens:
                prep_token = tokens[hour_index - 1]
        if prep_token == "на" and end_index < len(tokens) and tokens[end_index] in {"дней", "день", "дня", "суток", "сутки"}:
            continue
        if end_index < len(tokens) and tokens[end_index] in {"дней", "день", "суток", "сутки"} and not day_part_near_tokens(hour_index, end_index + 1):
            continue
        day_part = day_part_near_tokens(hour_index, end_index) or detect_day_part_around(token_start(hour_index), token_end(end_index))
        hour = adjust_hour_by_day_part(hour, day_part)
        if 0 <= hour <= 23 and 0 <= minute <= 59:
            return hour, minute

    # Сначала ищем точное время с минутами. Важно учитывать слова после времени:
    # "9:30 вечера" => 21:30, а не 09:30.
    patterns = [
        r"(?<!\d)([01]?\d|2[0-3])\s*[:.]\s*([0-5]\d)(?!\d)",
        r"(?<!\d)([01]?\d|2[0-3])\s*[-]\s*([0-5]\d)(?!\d)",
        r"(?<!\d)([01]?\d|2[0-3])\s*[чh]\s*([0-5]\d)(?!\d)",
        r"(?<!\d)([01]?\d|2[0-3])\s+([0-5]\d)(?!\d)",
    ]
    for pattern in patterns:
        m = re.search(pattern, t)
        if m:
            hour = int(m.group(1))
            minute = int(m.group(2))
            hour = adjust_hour_by_day_part(hour, detect_day_part_around(m.start(), m.end()))
            return hour, minute

    # Компактный формат 0930 / 2130 тоже поддерживаем.
    m = re.search(r"(?<!\d)([01]\d|2[0-3])([0-5]\d)(?!\d)", t)
    if m:
        hour = int(m.group(1))
        minute = int(m.group(2))
        hour = adjust_hour_by_day_part(hour, detect_day_part_around(m.start(), m.end()))
        return hour, minute

    # Числовой час без минут: "в 9 вечера", "в 9 часов вечера", "вечером в 9".
    numeric_hour_pattern = re.compile(
        r"\b(в|во|к|ко|на)\s+([01]?\d|2[0-3])\s*"
        r"(?:час(?:а|ов)?)?\s*"
        r"(утра|утром|вечера|вечером|дня|днем|дн[её]м|ночи|ночью)?\b"
    )
    for m in numeric_hour_pattern.finditer(t):
        tail = t[m.end():m.end() + 12]
        if m.group(1) == "на" and re.match(r"\s*(?:день|дня|дней|сутки|суток)\b", tail):
            continue
        if re.match(r"\s*(?:дней|суток)\b", tail):
            continue
        hour = int(m.group(2))
        explicit_part = detect_day_part(m.group(3) or "")
        around_part = detect_day_part_around(m.start(), m.end())
        hour = adjust_hour_by_day_part(hour, explicit_part or around_part)
        return hour, 0

    # Час словами: "в девять вечера", "к восьми утра", "в час дня".
    word_pattern = "|".join(sorted((re.escape(word) for word in hour_words), key=len, reverse=True))
    word_hour_pattern = re.compile(
        rf"\b(в|во|к|ко|на)\s+({word_pattern})\s*"
        r"(утра|утром|вечера|вечером|дня|днем|дн[её]м|ночи|ночью)?\b"
    )
    for m in word_hour_pattern.finditer(t):
        tail = t[m.end():m.end() + 12]
        if m.group(1) == "на" and re.match(r"\s*(?:день|дня|дней|сутки|суток)\b", tail):
            continue
        if re.match(r"\s*(?:дней|суток)\b", tail):
            continue
        hour = hour_words[m.group(2)]
        explicit_part = detect_day_part(m.group(3) or "")
        around_part = detect_day_part_around(m.start(), m.end())
        hour = adjust_hour_by_day_part(hour, explicit_part or around_part)
        return hour, 0

    return None

def extract_default_time_from_words(text: str, custom_times: Optional[dict[str, str]] = None) -> Optional[tuple[int, int]]:
    t = text.lower().replace("ё", "е")
    times = time_words_for_prompt(custom_times)

    def get_time(key: str) -> tuple[int, int]:
        parsed = parse_hhmm_string(times[key])
        return parsed if parsed else parse_hhmm_string(TIME_WORD_DEFAULTS[key])  # type: ignore[return-value]

    if re.search(r"\bпосле\s+обеда\b", t):
        return get_time("day")
    if re.search(r"\bутром\b|\bутро\b", t):
        return get_time("morning")
    if re.search(r"\bднем\b|\bдн[её]м\b|\b(?:в|на|к)\s+день\b", t):
        return get_time("day")
    if re.search(r"\bвечером\b|\bвечер\b|\bк\s+вечеру\b", t):
        return get_time("evening")
    if re.search(r"\bночью\b|\bночь\b", t):
        return get_time("night")
    return None


def user_text_has_any_time_hint(text: str, custom_times: Optional[dict[str, str]] = None) -> bool:
    t = text.lower().replace("ё", "е")
    if extract_explicit_time_from_text(t):
        return True
    if extract_default_time_from_words(t, custom_times):
        return True
    return bool(re.search(
        r"\b(полдень|полночь|час|часа|часов|минут|утра|вечера|дня|ночи|обед|время|времени|к\s+\w+)\b",
        t,
    ))


def yandex_time_context_text(item_source_text: str, full_user_text: str, custom_times: Optional[dict[str, str]] = None) -> str:
    """
    Защита после ответа YandexGPT.
    Иногда нейросеть возвращает reminder_text без времени, например только "сделать бутер",
    хотя в полной голосовой фразе было "завтра в 9 вечера сделать бутер".
    Для проверки и исправления времени используем полную фразу, если в куске от нейросети нет времени.
    """
    item_text = str(item_source_text or "").strip()
    full_text = str(full_user_text or "").strip()
    if not full_text:
        return item_text
    if not item_text:
        return full_text
    if user_text_has_any_time_hint(item_text, custom_times):
        return item_text
    if user_text_has_any_time_hint(full_text, custom_times):
        return full_text
    return item_text


def replace_time_in_local_at(local_at: str, timezone_name: str, hour: int, minute: int) -> tuple[str, str]:
    tz = ZoneInfo(timezone_name)
    dt = datetime.strptime(local_at, "%Y-%m-%d %H:%M").replace(tzinfo=tz)
    dt = dt.replace(hour=hour, minute=minute, second=0, microsecond=0)
    return dt.strftime("%Y-%m-%d %H:%M"), dt.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def override_time_from_user_text(local_at: str, user_text: str, timezone_name: str, custom_times: Optional[dict[str, str]] = None) -> tuple[str, str]:
    explicit = extract_explicit_time_from_text(user_text)
    if not explicit:
        dt = datetime.strptime(local_at, "%Y-%m-%d %H:%M").replace(tzinfo=ZoneInfo(timezone_name))
        return dt.strftime("%Y-%m-%d %H:%M"), dt.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    hour, minute = explicit
    return replace_time_in_local_at(local_at, timezone_name, hour, minute)


def local_edit_time_from_user_text(current_data: dict, user_fix: str, custom_times: Optional[dict[str, str]] = None) -> Optional[str]:
    """
    Локальный разбор правки даты и времени.
    Поддерживает не только "15 24" или "утром", но и полную дату:
    "10 мая в 23:00", "10.05 23:00", "2026-05-10 23:00", "в понедельник в 8:30".
    Фразы вида "через 2 минуты" считаются от текущего момента пользователя.
    """
    relative = parse_relative_datetime_from_now(user_fix, current_data["timezone_name"], custom_times)
    if relative:
        local_at, _utc_at, _details = relative
        return local_at

    explicit = extract_explicit_time_from_text(user_fix)
    default_words = None if explicit else extract_default_time_from_words(user_fix, custom_times)

    timezone_name = current_data["timezone_name"]
    tz = ZoneInfo(timezone_name)
    now_local = datetime.now(tz)
    current_base = datetime.strptime(current_data["next_local_at"], "%Y-%m-%d %H:%M").replace(tzinfo=tz)

    date_info = extract_date_base_from_edit_text(user_fix, now_local, current_base)

    if not explicit and not default_words and not date_info:
        return None

    if explicit or default_words:
        hour, minute = explicit or default_words  # type: ignore[misc]
    else:
        hour, minute = current_base.hour, current_base.minute

    if date_info:
        base, date_kind, has_explicit_year = date_info
    else:
        base = current_base
        date_kind = "current"
        has_explicit_year = True

    candidate = base.replace(hour=hour, minute=minute, second=0, microsecond=0)

    if current_data.get("repeat_type") == "none" and candidate <= now_local:
        if date_kind == "weekday":
            candidate += timedelta(days=7)
        elif date_kind == "absolute" and not has_explicit_year:
            try:
                candidate = candidate.replace(year=candidate.year + 1)
            except ValueError:
                candidate = candidate.replace(year=candidate.year + 1, month=2, day=28)
        elif date_kind in {"current", "relative"}:
            candidate += timedelta(days=1)
        else:
            return None

    return candidate.strftime("%Y-%m-%d %H:%M")


def has_explicit_repeat_marker(text: str) -> bool:
    """
    Возвращает True только тогда, когда пользователь явно просит повтор.

    Важно: обычное слово "по" НЕ считается маркером повтора само по себе,
    потому что школьные фразы часто содержат "по математике", "по русскому",
    "по истории". Повтор по дням недели включается только для форм вроде
    "по четвергам", "каждый четверг", "еженедельно по четвергам".
    """
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if not t:
        return False

    repeat_markers = [
        r"\bкажд(?:ый|ая|ое|ую|ые)?\b",
        r"\bежедневно\b", r"\bеженедельно\b", r"\bежемесячно\b", r"\bежегодно\b",
        r"\bрегулярно\b",
        r"\bраз\s+в\s+(?:день|неделю|месяц|год)\b",
        r"\bраз\s+в\s+\d{1,3}\s+(?:день|дня|дней|неделю|недели|месяц|месяца|месяцев)\b",
        r"\bчерез\s+кажд(?:ый|ую|ое|ые)?\b",
        r"\bкаждые\s+\d{1,3}\s+(?:день|дня|дней|сутки|суток|неделю|недели|месяц|месяца|месяцев)\b",
        r"\bпо\s+будням\b", r"\bпо\s+выходным\b",
        r"\bпо\s+(?:понедельникам|вторникам|средам|четвергам|пятницам|субботам|воскресеньям)\b",
        r"\bпо\s+(?:пн|вт|ср|чт|пт|сб|вс)\b",
    ]
    return any(re.search(pattern, t) for pattern in repeat_markers)


def has_explicit_weekday_repeat_marker(text: str) -> bool:
    """
    Возвращает True только для настоящих недельных повторов по дням недели.
    Важно: фраза «в понедельник каждые 2 часа» не является еженедельным повтором.
    """
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    weekday_words = (
        r"понедельник(?:ам|а|у|и)?|пн|вторник(?:ам|а|у|и)?|вт|"
        r"сред(?:ам|а|у|е|ы)?|ср|четверг(?:ам|а|у|и)?|чт|"
        r"пятниц(?:ам|а|у|е|ы)?|пт|суббот(?:ам|а|у|е|ы)?|сб|"
        r"воскресень(?:ям|е|я|ю)?|вс"
    )
    return bool(
        re.search(rf"\bкажд(?:ый|ую|ую|ое|ые)?\s+(?:{weekday_words})\b", t)
        or re.search(rf"\bпо\s+(?:{weekday_words})\b", t)
        or re.search(rf"\bеженедельно\s+(?:по\s+)?(?:{weekday_words})\b", t)
        or re.search(rf"\bраз\s+в\s+неделю\s+(?:по\s+)?(?:{weekday_words})\b", t)
    )


def detect_repeat_from_text(user_text: str) -> Optional[tuple[str, str]]:
    """
    Локальное определение повторов.

    Главный принцип безопасности:
    - день недели без явного маркера повтора = одноразовая дата;
    - "в четверг сделать уроки" НЕ повтор;
    - "в четверг сделать уроки по математике" НЕ повтор, несмотря на слово "по";
    - повтор включается только по явным формулировкам: "каждый четверг",
      "по четвергам", "по будням", "каждые 3 дня" и т.п.
    """
    text = normalize_spaces((user_text or "").lower().replace("ё", "е"))
    text = re.sub(r"[^а-яa-z0-9\s,.-]", " ", text)
    text = normalize_spaces(text)
    if not text:
        return None

    if not has_explicit_repeat_marker(text):
        return None

    if re.search(r"\b(по\s+будням|в\s+будни|будние\s+дни|каждый\s+будний\s+день|каждые\s+будни)\b", text):
        return "weekdays", ""

    if re.search(r"\b(по\s+выходным|каждые\s+выходные|каждый\s+выходной|в\s+выходные|на\s+выходных)\b", text):
        return "weekends", ""

    if re.search(r"\b(каждый\s+день|каждое\s+утро|каждый\s+вечер|каждую\s+ночь|ежедневно|каждые\s+сутки)\b", text):
        return "daily", ""

    # "через день" в школьной речи чаще значит одноразово завтра, а не повтор.
    # Повтор через N дней включаем только при явных формах "каждые N дней" / "через каждые N дней".
    n_match = re.search(
        r"\b(?:каждые|через\s+каждые)\s+(\d{1,3})\s+(?:день|дня|дней|сутки|суток)\b",
        text,
    )
    if n_match:
        n = int(n_match.group(1))
        if 1 <= n <= 365:
            return "every_n_days", str(n)

    if re.search(r"\b(?:каждую\s+неделю|каждая\s+неделя|раз\s+в\s+неделю|еженедельно)\b", text) and not re.search(
        r"\b(?:понедельник|понедельникам|пн|вторник|вторникам|вт|сред[ауеам]*|ср|четверг|четвергам|чт|пятниц[ауеам]*|пт|суббот[ауеам]*|сб|воскресень[еяям]*|вс)\b",
        text,
    ):
        return "weekly", ""

    weekday_patterns = {
        0: [r"\bпонедельник[а-я]*\b", r"\bпн\b", r"\bпо\s+понедельникам\b"],
        1: [r"\bвторник[а-я]*\b", r"\bвт\b", r"\bпо\s+вторникам\b"],
        2: [r"\bсред[а-я]*\b", r"\bср\b", r"\bпо\s+средам\b"],
        3: [r"\bчетверг[а-я]*\b", r"\bчт\b", r"\bпо\s+четвергам\b"],
        4: [r"\bпятниц[а-я]*\b", r"\bпт\b", r"\bпо\s+пятницам\b"],
        5: [r"\bсуббот[а-я]*\b", r"\bсб\b", r"\bпо\s+субботам\b"],
        6: [r"\bвоскресень[а-я]*\b", r"\bвс\b", r"\bпо\s+воскресеньям\b"],
    }

    found_days = []
    for day_num, patterns in weekday_patterns.items():
        if any(re.search(pattern, text) for pattern in patterns):
            found_days.append(day_num)

    found_days = sorted(set(found_days))
    if found_days == [5, 6]:
        return "weekends", ""
    if found_days:
        return "custom_weekdays", ",".join(str(day) for day in found_days)

    if re.search(r"\b(каждый\s+месяц|каждого\s+месяца|раз\s+в\s+месяц|ежемесячно)\b", text):
        return "monthly", ""

    if re.search(r"\b(каждый\s+год|каждого\s+года|раз\s+в\s+год|ежегодно)\b", text):
        return "yearly", ""

    return None


def protect_repeat_from_false_positive(user_text: str, repeat_type: str, repeat_value: str) -> tuple[str, str]:
    """
    Защитная проверка перед показом черновика и после ответа YandexGPT.
    Если повтор появился без явных слов повтора, сбрасываем его в одноразовый режим.
    Это защищает фразы вроде "в четверг сделать уроки по математике".
    """
    if repeat_type and repeat_type != "none" and not has_explicit_repeat_marker(user_text):
        return "none", ""
    if repeat_type == "custom_weekdays" and not has_explicit_weekday_repeat_marker(user_text):
        return "none", ""
    return repeat_type or "none", repeat_value or ""



def text_has_explicit_clock_time (user_text :str )->bool :
    return extract_explicit_time_from_text (user_text )is not None 


def apply_default_time_from_text (local_at :str ,user_text :str ,timezone_name :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [str ,str ]:
    """
    Итоговый выбор времени при создании напоминания:

    1. Локальное точное время важнее нейросети.
    2. Пользовательские настройки слов времени важнее нейросети.
    3. Если локально время не найдено, но есть явный намёк на время — берём время нейросети.
    4. Если времени нет вообще — ставим 10:00.
    """
    explicit =extract_explicit_time_from_text (user_text )
    if explicit :
        hour ,minute =explicit 
        return replace_time_in_local_at (local_at ,timezone_name ,hour ,minute )

    default_words =extract_default_time_from_words (user_text ,custom_times )
    if default_words :
        hour ,minute =default_words 
        return replace_time_in_local_at (local_at ,timezone_name ,hour ,minute )

    if user_text_has_any_time_hint (user_text ,custom_times ):
        dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =ZoneInfo (timezone_name ))
        return dt .strftime ("%Y-%m-%d %H:%M"),dt .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")

    hour ,minute =custom_morning_time (custom_times )
    return replace_time_in_local_at (local_at ,timezone_name ,hour ,minute )


def has_repeat_words_for_combined (user_text :str )->bool :
    text =user_text .lower ().replace ("ё","е")
    return bool (re .search (
    r"\b(кажд|каждый|каждую|каждое|каждые|ежедневно|еженедельно|ежемесячно|ежегодно|по\s+\w+ам|по\s+будням|по\s+выходным|раз\s+в)\b",
    text ,
    ))


def detect_oneoff_combined_targets (user_text :str ,timezone_name :str ,base_local_at :str )->list [str ]:
    """
    Локальная страховка для одноразовых комбинированных фраз:
    сегодня и завтра; сегодня, завтра и послезавтра; сегодня и в субботу; в понедельник и среду.
    Если есть слова повтора ("каждый", "по средам" и т.п.), функция ничего не делает.
    """
    if has_repeat_words_for_combined (user_text ):
        return []

    text =user_text .lower ().replace ("ё","е")
    text =re .sub (r"[^а-яa-z0-9\s,.-]"," ",text )
    text =re .sub (r"\s+"," ",text ).strip ()

    if not re .search (r"(\b(и|а|потом|также|еще|ещё)\b|[,;])",text ):
        return []

    tz =ZoneInfo (timezone_name )
    now_local =datetime .now (tz )
    base_dt =datetime .strptime (base_local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    hour ,minute =base_dt .hour ,base_dt .minute 

    targets :list [datetime ]=[]

    def add_candidate_date (date_value ):
        candidate =datetime (date_value .year ,date_value .month ,date_value .day ,hour ,minute ,tzinfo =tz )
        if candidate <=now_local :
            candidate +=timedelta (days =1 )
        targets .append (candidate )

    if re .search (r"\bсегодня\b",text ):
        add_candidate_date (now_local .date ())
    if re .search (r"\bзавтра\b",text ):
        add_candidate_date ((now_local +timedelta (days =1 )).date ())
    if re .search (r"\bпослезавтра\b",text ):
        add_candidate_date ((now_local +timedelta (days =2 )).date ())

    weekday_patterns ={
    0 :[r"\bпонедельник[а-я]*\b",r"\bпн\b"],
    1 :[r"\bвторник[а-я]*\b",r"\bвт\b"],
    2 :[r"\bсред[а-я]*\b",r"\bср\b"],
    3 :[r"\bчетверг[а-я]*\b",r"\bчт\b"],
    4 :[r"\bпятниц[а-я]*\b",r"\bпт\b"],
    5 :[r"\bсуббот[а-я]*\b",r"\bсб\b"],
    6 :[r"\bвоскресень[а-я]*\b",r"\bвс\b"],
    }

    for day_num ,patterns in weekday_patterns .items ():
        if any (re .search (pattern ,text )for pattern in patterns ):
            candidate =now_local .replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )
            for _ in range (8 ):
                if candidate .weekday ()==day_num and candidate >now_local :
                    targets .append (candidate )
                    break 
                candidate +=timedelta (days =1 )

    unique :list [datetime ]=[]
    seen =set ()
    for dt in sorted (targets ):
        while dt .strftime ("%Y-%m-%d %H:%M")in seen :
            dt +=timedelta (days =1 )
        key =dt .strftime ("%Y-%m-%d %H:%M")
        seen .add (key )
        unique .append (dt )

    if len (unique )<2 :
        return []

    return [dt .strftime ("%Y-%m-%d %H:%M")for dt in unique ]


def dedupe_parsed_reminders (items :list [ParsedReminder ])->list [ParsedReminder ]:
    result :list [ParsedReminder ]=[]
    seen =set ()
    for item in items :
        key =(
        item .topic .strip ().lower (),
        item .next_local_at ,
        item .repeat_type ,
        item .repeat_value ,
        item .reminder_text .strip ().lower (),
        )
        if key in seen :
            continue 
        seen .add (key )
        result .append (item )
    return result 



def parse_method_title(parse_method: str) -> str:
    if parse_method == "local":
        return "быстрая"
    if parse_method == "yandex_reparse":
        return "YandexGPT после уточнения"
    if parse_method == "yandex":
        return "YandexGPT"
    return "не указан"


def custom_morning_time(custom_times: Optional[dict[str, str]] = None) -> tuple[int, int]:
    times = time_words_for_prompt(custom_times)
    parsed = parse_hhmm_string(times.get("morning", ""))
    if parsed:
        return parsed
    return 8, 0


def parse_local_datetime_for_create(text: str, timezone_name: str, custom_times: Optional[dict[str, str]], repeat_type: str, repeat_value: str) -> Optional[tuple[str, str]]:
    """
    Локальный разбор даты и времени для создания напоминания.
    Если указана только дата, время берётся из пользовательской настройки "утро".
    Фразы "через N минут/часов/дней" считаются от текущего момента.
    """
    relative = parse_relative_datetime_from_now(text, timezone_name, custom_times)
    if relative and repeat_type == "none":
        local_at, utc_at, _details = relative
        return local_at, utc_at

    tz = ZoneInfo(timezone_name)
    now_local = datetime.now(tz).replace(second=0, microsecond=0)
    current_base = now_local.replace(second=0, microsecond=0)
    date_info = extract_date_base_from_edit_text(text, now_local, current_base)
    explicit = extract_explicit_time_from_text(text)
    default_words = None if explicit else extract_default_time_from_words(text, custom_times)

    if explicit:
        hour, minute = explicit
    elif default_words:
        hour, minute = default_words
    else:
        hour, minute = custom_morning_time(custom_times)

    if date_info:
        base, date_kind, has_explicit_year = date_info
    elif explicit or default_words or repeat_type != "none":
        base = now_local.replace(hour=0, minute=0, second=0, microsecond=0)
        date_kind = "current"
        has_explicit_year = False
    else:
        return None

    candidate = base.replace(hour=hour, minute=minute, second=0, microsecond=0)

    if repeat_type == "none":
        if candidate <= now_local:
            if date_info and date_kind == "weekday":
                candidate += timedelta(days=7)
            elif date_info and date_kind == "absolute" and not has_explicit_year:
                try:
                    candidate = candidate.replace(year=candidate.year + 1)
                except ValueError:
                    candidate = candidate.replace(year=candidate.year + 1, month=2, day=28)
            elif not date_info or date_kind in {"current", "relative"}:
                candidate += timedelta(days=1)
            else:
                return None
        return candidate.strftime("%Y-%m-%d %H:%M"), candidate.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")

    local_at = candidate.strftime("%Y-%m-%d %H:%M")
    try:
        local_at, utc_at = recalc_next_after_repeat_change(local_at, timezone_name, repeat_type, repeat_value)
        local_at, utc_at = ensure_future_for_repeat(local_at, timezone_name, repeat_type, repeat_value)
        return local_at, utc_at
    except Exception:
        return None


def local_remove_patterns(text: str) -> str:
    t = " " + normalize_spaces((text or "").lower().replace("ё", "е")) + " "
    month_names = "|".join(sorted((re.escape(name) for name in MONTH_WORD_TO_NUMBER), key=len, reverse=True))
    patterns = [
        r"\b(?:без\s+(?:\d{1,2}|четверти|десяти|пяти|пятнадцати|двадцати|тридцати|сорока|пятидесяти)(?:\s+минут?)?\s+(?:\d{1,2}|час|один|одна|два|две|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать)(?:\s+(?:утра|дня|вечера|ночи))?)\b",
        r"\b(?:пол|половина|половину)\s+(?:первого|второго|третьего|четвертого|пятого|шестого|седьмого|восьмого|девятого|десятого|одиннадцатого|двенадцатого|\d{1,2})(?:\s+(?:утра|дня|вечера|ночи))?\b",
        r"\b(?:в|во|к|ко|на)?\s*(?:\d{1,2}|час|часу|один|одна|два|две|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать)\s*(?:час(?:а|ов)?|часу)?\s+(?:\d{1,2}|пять|пяти|десять|десяти|пятнадцать|пятнадцати|двадцать|двадцати|тридцать|тридцати|сорок|сорока|пятьдесят|пятидесяти)(?:\s+(?:минут(?:у|ы)?|минут|мин))?(?:\s+(?:утра|дня|вечера|ночи))?\b",
        r"\bнапомни(?:ть)?\b", r"\bпоставь\s+напоминание\b", r"\bсоздай\s+напоминание\b",
        r"\bмне\b", r"\bпожалуйста\b", r"\bнадо\b", r"\bнужно\b",
        r"\bчерез\s+(?:\d{1,3}|один|одну|одно|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять)\s*(?:минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|неделю|недели|недель)\b",
        r"\b(?:через\s+)?(?:пол\s*часа|полчаса)\b", r"\bчерез\s+час\b", r"\bчерез\s+день\b",
        r"\bсегодня\b", r"\bзавтра\b", r"\bпослезавтра\b",
        rf"\b\d{{1,2}}\s+(?:{month_names})(?:\s+(?:20\d{{2}}|\d{{2}}))?\b",
        r"\b(?:20\d{2}[.\-/]\d{1,2}[.\-/]\d{1,2}|\d{1,2}[.\-/]\d{1,2}(?:[.\-/]\d{2,4})?)\b",
        r"\b(?:в\s+)?(?:понедельник|понедельника|понедельнику|пн|вторник|вторника|вторнику|вт|среда|среду|среде|ср|четверг|четверга|четвергу|чт|пятница|пятницу|пятнице|пт|суббота|субботу|субботе|сб|воскресенье|воскресенья|воскресенью|вс)\b",
        r"\b(?:в|во|к|ко|на)\s+(?:[01]?\d|2[0-3])\s*[:.]\s*[0-5]\d\b",
        r"\b(?:в|во|к|ко|на)\s+(?:[01]?\d|2[0-3])\s*[чh]\s*[0-5]\d\b",
        r"\b(?:в|во|к|ко|на)\s+(?:[01]?\d|2[0-3])\s+[0-5]\d\b",
        r"(?<!\d)(?:[01]?\d|2[0-3])\s*[:.]\s*[0-5]\d(?!\d)",
        r"(?<!\d)(?:[01]?\d|2[0-3])\s*[чh]\s*[0-5]\d(?!\d)",
        r"(?<!\d)(?:[01]?\d|2[0-3])\s+[0-5]\d(?!\d)",
        r"\b(?:в|во|к|ко|на)\s+(?:[01]?\d|2[0-3])\s*(?:час(?:а|ов)?|утра|вечера|дня|ночи)?\b",
        r"\bполдень\b", r"\bполночь\b",
        r"\bутром\b|\bутро\b|\bс\s+утра\b", r"\bднем\b|\bдн[её]м\b|\bпосле\s+обеда\b",
        r"\bвечером\b|\bвечер\b|\bк\s+вечеру\b", r"\bночью\b|\bночь\b",
        r"\bкаждый\s+день\b|\bежедневно\b|\bкаждое\s+утро\b|\bкаждый\s+вечер\b|\bкаждую\s+ночь\b",
        r"\bпо\s+будням\b|\bв\s+будни\b|\bбудние\s+дни\b|\bпо\s+выходным\b|\bв\s+выходные\b",
        r"\bпо\s+(?:понедельникам|вторникам|средам|четвергам|пятницам|субботам|воскресеньям|пн|вт|ср|чт|пт|сб|вс)\b",
        r"\bкажд(?:ый|ую|ое|ые)?\s+(?:понедельник|вторник|среду|четверг|пятницу|субботу|воскресенье)\b",
        r"\b(?:каждые|через\s+каждые)\s+\d{1,3}\s+(?:день|дня|дней|сутки|суток)\b",
        r"\bкаждую\s+неделю\b|\bраз\s+в\s+неделю\b|\bеженедельно\b|\bкаждый\s+месяц\b|\bраз\s+в\s+месяц\b|\bежемесячно\b|\bкаждый\s+год\b|\bежегодно\b",
        r"\bочень\s+важно\b|\bкрайне\s+важно\b|\bмаксимально\s+важно\b|\bсупер\s+важно\b|\bкритически\s+важно\b|\bсрочно\b|\bважно\b|\bне\s+срочно\b|\bесли\s+успею\b|\bкогда\s+будет\s+время\b",
    ]
    for pattern in patterns:
        t = re.sub(pattern, " ", t, flags=re.IGNORECASE)
    t = re.sub(r"\b(?:каждый|каждую|каждые|каждое)\b", " ", t, flags=re.IGNORECASE)
    t = re.sub(r"[;,]+", " ", t)
    t = re.sub(r"\s+", " ", t).strip(" .,-")
    t = cleanup_local_topic_junk(t)
    return t


def cleanup_local_topic_junk(topic: str) -> str:
    """
    Финальная очистка темы после локального разбора.
    Убирает остаточные служебные слова, которые остаются после удаления даты и времени:
    например, в фразе "контрольная в 23 10" после удаления времени не должна оставаться буква "в".
    """
    t = normalize_spaces((topic or "").lower().replace("ё", "е")).strip(" .,-;:")

    # В начале темы предлоги могут быть смысловыми: "в школу", "на тренировку", "к врачу".
    # Поэтому слева убираем только связки, а справа убираем и предлоги, оставшиеся после времени.
    service_start = r"(?:и|а|потом|также|еще|ещё|затем)"
    service_end = r"(?:и|а|потом|также|еще|ещё|затем|в|во|на|к|ко|по|с|со|у|от|до|для)"

    for _ in range(5):
        old_t = t
        t = re.sub(rf"^{service_start}\s+", "", t, flags=re.IGNORECASE).strip(" .,-;:")
        t = re.sub(rf"\s+{service_end}$", "", t, flags=re.IGNORECASE).strip(" .,-;:")
        if t == old_t:
            break

    # Убираем случайные остатки формата времени, если они всё же остались после нестандартного ввода.
    t = re.sub(r"(?<!\d)(?:[01]?\d|2[0-3])\s*[:.]\s*[0-5]\d(?!\d)", " ", t)
    t = re.sub(r"(?<!\d)(?:[01]?\d|2[0-3])\s+[0-5]\d(?!\d)", " ", t)
    t = re.sub(r"\b(?:час|часа|часов|минуту|минуты|минут|мин)\b", " ", t)

    # Повторная очистка после удаления возможных остатков времени.
    t = normalize_spaces(t).strip(" .,-;:")
    for _ in range(3):
        old_t = t
        t = re.sub(rf"^{service_start}\s+", "", t, flags=re.IGNORECASE).strip(" .,-;:")
        t = re.sub(rf"\s+{service_end}$", "", t, flags=re.IGNORECASE).strip(" .,-;:")
        if t == old_t:
            break

    if t in {"в", "во", "на", "к", "ко", "по", "с", "со", "у", "от", "до", "для", "и", "а"}:
        return ""
    return normalize_spaces(t)


def extract_local_topic(text: str) -> Optional[str]:
    topic = cleanup_local_topic_junk(local_remove_patterns(text))
    topic = normalize_spaces(topic)
    if not topic or len(topic) < 2:
        return None
    if topic in {"в", "во", "на", "к", "ко", "по", "с", "со", "у", "от", "до", "для", "и", "а"}:
        return None
    return topic[:1].upper() + topic[1:120]


def count_local_time_markers(text: str) -> int:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    count = 0
    count += len(re.findall(r"(?<!\d)(?:[01]?\d|2[0-3])\s*[:.]\s*[0-5]\d(?!\d)", t))
    count += len(re.findall(r"\b(?:сегодня|завтра|послезавтра)\b", t))
    count += len(re.findall(r"\bчерез\s+(?:\d{1,3}|один|одну|одно|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять)\s*(?:минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|неделю|недели|недель)\b", t))
    count += len(re.findall(r"\b(?:утром|днем|днём|вечером|ночью|после\s+обеда|к\s+вечеру)\b", t))
    count += len(re.findall(r"\b(?:понедельник|понедельника|понедельнику|пн|вторник|вторника|вторнику|вт|среда|среду|среде|ср|четверг|четверга|четвергу|чт|пятница|пятницу|пятнице|пт|суббота|субботу|субботе|сб|воскресенье|воскресенья|воскресенью|вс)\b", t))
    month_names = "|".join(sorted((re.escape(name) for name in MONTH_WORD_TO_NUMBER), key=len, reverse=True))
    count += len(re.findall(rf"(?<!\d)\d{{1,2}}\s+(?:{month_names})(?:\s+(?:20\d{{2}}|\d{{2}}))?(?!\d)", t))
    return count


def is_complex_reminder_text(user_text: str) -> bool:
    """
    Определяет, что фраза похожа на несколько разных событий или слишком сложную команду.
    Такие сообщения лучше сразу отдавать YandexGPT, чтобы локальный разбор не угадывал неправильно.

    Одно событие вида "через три дня в 8:30" сложным не считается.
    """
    t = normalize_spaces((user_text or "").lower().replace("ё", "е"))
    if not t:
        return False

    # Явные разделители разных событий.
    if re.search(r"(;|\s+а\s+|\s+потом\s+|\s+также\s+|\s+ещ[её]\s+|\s+затем\s+)", t):
        return True

    # Запятая часто разделяет два дела, но простые уточнения времени не считаем сложностью.
    if "," in t and count_local_time_markers(t) >= 2:
        return True

    # Несколько слов "через" обычно означает несколько отдельных относительных сроков.
    if len(re.findall(r"\bчерез\b", t)) > 1:
        return True

    # Несколько точных времён почти всегда означает несколько событий.
    exact_times = re.findall(r"(?<!\d)(?:[01]?\d|2[0-3])\s*[:.]\s*[0-5]\d(?!\d)", t)
    if len(exact_times) > 1:
        return True

    # Разные даты/дни недели в одной фразе без явного повтора лучше отдавать нейросети.
    if not has_repeat_words_for_combined(t):
        date_markers = 0
        date_markers += len(re.findall(r"\b(?:сегодня|завтра|послезавтра)\b", t))
        date_markers += len(re.findall(r"\b(?:понедельник|понедельника|понедельнику|пн|вторник|вторника|вторнику|вт|среда|среду|среде|ср|четверг|четверга|четвергу|чт|пятница|пятницу|пятнице|пт|суббота|субботу|субботе|сб|воскресенье|воскресенья|воскресенью|вс)\b", t))
        month_names = "|".join(sorted((re.escape(name) for name in MONTH_WORD_TO_NUMBER), key=len, reverse=True))
        date_markers += len(re.findall(rf"(?<!\d)\d{{1,2}}\s+(?:{month_names})(?:\s+(?:20\d{{2}}|\d{{2}}))?(?!\d)", t))
        if date_markers > 1 and re.search(r"\s+и\s+", t):
            return True

    # Пример: "завтра утром ... и вечером ..." — два времени в один день.
    time_word_count = len(re.findall(r"\b(?:утром|днем|днём|вечером|ночью|после\s+обеда|к\s+вечеру)\b", t))
    if time_word_count > 1 and re.search(r"\s+и\s+", t):
        return True

    return False


def split_local_segments(user_text: str) -> list[str]:
    """
    Аккуратно делит сложную фразу на логические куски.

    Важно:
    - повторяющиеся фразы без явного второго события не режем;
    - разделители "а/потом/ещё/также/затем/;" почти всегда означают новое дело;
    - запятую используем только когда в тексте несколько временных/датных маркеров,
      иначе простые уточнения вроде "завтра, в 9" не разрываем.
    """
    raw = normalize_spaces(user_text)
    if not raw:
        return []

    lower = normalize_spaces(raw.lower().replace("ё", "е"))

    # Если это обычный повтор без второго отдельного события, оставляем фразу целой.
    if has_repeat_words_for_combined(lower) and not re.search(r"(;|\s+а\s+|\s+потом\s+|\s+также\s+|\s+ещ[её]\s+|\s+затем\s+)", lower):
        # Исключение: "каждый день утром и вечером..." — это два повторяющихся напоминания.
        time_word_count = len(re.findall(r"\b(?:утром|днем|днём|вечером|ночью|после\s+обеда|к\s+вечеру)\b", lower))
        exact_time_count = len(re.findall(r"(?<!\d)(?:[01]?\d|2[0-3])\s*[:.]\s*[0-5]\d(?!\d)", lower))
        if not (time_word_count > 1 and re.search(r"\s+и\s+", lower)) and exact_time_count <= 1:
            return [user_text]

    parts = re.split(r"\s*(?:;|\s+а\s+|\s+потом\s+|\s+также\s+|\s+ещ[её]\s+|\s+затем\s+)\s*", raw, flags=re.IGNORECASE)
    parts = [part.strip(" ,.;") for part in parts if part.strip(" ,.;")]

    if len(parts) == 1 and "," in raw and count_local_time_markers(raw) >= 2:
        comma_parts = [part.strip(" ,.;") for part in re.split(r"\s*,\s*", raw) if part.strip(" ,.;")]
        if len(comma_parts) > 1:
            parts = comma_parts

    return parts if len(parts) > 1 else [user_text]


def local_parse_one_reminder(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> tuple[Optional[ParsedReminder], Optional[str]]:
    repeat = detect_repeat_from_text(user_text)
    repeat_type, repeat_value = repeat if repeat else ("none", "")
    repeat_type, repeat_value = protect_repeat_from_false_positive(user_text, repeat_type, repeat_value)
    datetime_result = parse_local_datetime_for_create(user_text, timezone_name, custom_times, repeat_type, repeat_value)
    if not datetime_result:
        return None, "need_datetime"
    topic = extract_local_topic(user_text)
    if not topic:
        return None, "need_topic"
    category = classify_category(user_text)
    priority = classify_priority(user_text, category)
    local_at, utc_at = datetime_result
    return ParsedReminder(
        topic=topic,
        reminder_text=normalize_spaces(user_text),
        category=category,
        priority=priority,
        repeat_type=repeat_type,
        repeat_value=repeat_value,
        next_local_at=local_at,
        next_utc_at=utc_at,
        parse_method="local",
    ), None


def local_parse_many_reminders(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> tuple[list[ParsedReminder], Optional[str], bool]:
    """
    Возвращает (items, error_code, should_try_yandex).
    Локально разбираем только уверенные одиночные напоминания.
    Сложные и комбинированные фразы сразу отдаём YandexGPT.
    """
    # Перемены и интервальные напоминания пытаемся разобрать локально до сложного фильтра.
    # Для перемен нужен user_id; здесь его нет, поэтому этот тип обрабатывается в process_user_new_request.
    interval_parsed, interval_err = local_parse_interval_reminder(user_text, timezone_name, timezone_title, custom_times)
    if interval_parsed:
        return [interval_parsed], None, False

    if is_complex_reminder_text(user_text):
        return [], "complex", True

    parsed, err = local_parse_one_reminder(user_text, timezone_name, timezone_title, custom_times)
    if not parsed:
        if err in {"need_datetime", "need_topic"}:
            return [], err, False
        return [], err or "complex", True

    return [parsed], None, False


def build_fast_yandex_many_prompt(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    context = current_context_for_prompt(timezone_name)
    time_words_block = build_time_words_prompt_block(custom_times)
    return f"""
Ты разбираешь сложные фразы для Telegram-бота напоминаний. Верни только JSON без пояснений.

КОНТЕКСТ:
{context}
Часовой пояс: {timezone_title}
{time_words_block}

ФОРМАТ:
{{
  "reminders": [
    {{
      "topic": "краткая тема без даты и времени",
      "datetime_local": "YYYY-MM-DD HH:MM",
      "category": "study/exam/meeting/deadline/personal/other",
      "priority": "very_high/high/medium/low",
      "repeat_type": "none/daily/weekly/monthly/yearly/weekdays/weekends/custom_weekdays/every_n_days",
      "repeat_value": "",
      "reminder_text": "кусок исходного текста для этого напоминания"
    }}
  ]
}}

ПРАВИЛА:
1. Если в тексте несколько событий, верни несколько объектов в reminders.
2. Разделители событий: "а", "потом", "ещё", "также", ";", разные даты или разные времена.
3. Если написано "через 3 дня в 8:30", дата = сейчас + 3 дня, время = 08:30.
4. Если написано "через 3 дня" без времени, время = текущее время из контекста.
5. Если дата без времени, используй пользовательское время слова "утро".
6. Если есть "утром", "днём", "вечером", "ночью", "после обеда", "к вечеру" без числа, используй настройки выше.
6.1. Если рядом с числом есть часть дня, переводи 12-часовой формат в 24-часовой: "в 9 вечера" = 21:00, "вечером в 8" = 20:00, "в 9 утра" = 09:00, "в час ночи" = 01:00, "в час дня" = 13:00.
6.2. Голосовые варианты словами тоже обязательны: "в девять вечера" = 21:00, "в восемь вечера" = 20:00, "в девять тридцать вечера" = 21:30.
7. Повторы: "каждый день" = daily, "по будням" = weekdays, "по выходным" = weekends, "каждую пятницу" = custom_weekdays repeat_value "4", "каждые 3 дня" = every_n_days repeat_value "3".
8. Категории: учеба = study, контрольные/экзамены/тесты = exam, встречи/созвоны = meeting, дедлайны/сдать = deadline, личное = personal, иначе other.
9. Приоритет: "очень важно", "срочно", "крайне важно" = very_high; просто "важно" = high; "не срочно" = low; иначе medium.
10. Не возвращай время в прошлом. Если не понял дату/время, datetime_local = "".
11. Не добавляй лишний текст вне JSON.

ТЕКСТ:
{user_text}
""".strip()


def yandex_spoken_time_rules() -> str:
    return """
РАЗГОВОРНОЕ ВРЕМЯ ПОСЛЕ ГОЛОСА:
- "в 9 вечера" = 21:00, "вечером в 8" = 20:00;
- "в 9:30 вечера", "в 9 30 вечера", "в девять тридцать вечера" = 21:30;
- "в час 30 минут ночи", "в один час тридцать минут ночи" = 01:30;
- "в час дня" = 13:00, "в два часа дня" = 14:00;
- "в 12 ночи" = 00:00, "в 12 дня" = 12:00;
- "без десяти девять вечера" = 20:50, "без четверти девять вечера" = 20:45;
- "пол второго ночи" = 01:30, "половина девятого вечера" = 20:30.
Не превращай вечер/день в утро. Слова "вечера", "дня", "ночи", "утра" меняют час.
""".strip()


def yandex_category_priority_rules() -> str:
    return """
КАТЕГОРИИ И ПРИОРИТЕТ:
- category="study": школа, уроки, домашнее задание, доклад, проект, лабораторная, реферат, тетради, учебные дела;
- category="exam": контрольная, самостоятельная, экзамен, зачёт, тест, олимпиада, ВПР, ОГЭ, ЕГЭ;
- category="meeting": встреча, созвон, собрание, репетитор, переговоры, занятие с человеком;
- category="deadline": дедлайн, срок, сдать, отправить работу, крайний срок;
- category="personal": личное, здоровье, спорт, покупки, звонки, вода, витамины, бытовые дела;
- category="other": только если категория реально неясна.
- priority="very_high": очень важно, срочно, крайне важно, критически важно, максимально важно;
- priority="high": важно, обязательно, не забыть, экзамен, контрольная, дедлайн;
- priority="low": не срочно, можно потом, если успею, необязательно;
- priority="medium": обычная важность.
""".strip()


def yandex_repeat_rules() -> str:
    return """
ПОВТОРЫ:
- День недели без слов повтора = одноразовое напоминание. "в понедельник сдать" => repeat_type="none".
- "каждый день", "ежедневно", "каждое утро", "каждый вечер" => repeat_type="daily".
- "по будням", "в будни", "каждый будний день" => repeat_type="weekdays".
- "по выходным", "каждые выходные" => repeat_type="weekends".
- "каждый понедельник", "по понедельникам" => repeat_type="custom_weekdays", repeat_value="0".
- Дни недели: понедельник=0, вторник=1, среда=2, четверг=3, пятница=4, суббота=5, воскресенье=6.
- Несколько дней с повтором: "каждый понедельник, среду и пятницу" => repeat_value="0,2,4".
- "каждую субботу и воскресенье" => repeat_type="weekends".
- В свободном тексте фразы "каждые N дней", "раз в N дней", "через каждые N дней" считаются interval, а не repeat_type="every_n_days".
- repeat_type="every_n_days" оставляем только для ручной настройки повтора через кнопки или если пользователь явно просит обычный календарный повтор без слова "каждые".
- "через день" без явного контекста повтора можно считать одноразово завтра; "через день пить воду" можно считать interval на 2 дня.
""".strip()


def yandex_interval_rules() -> str:
    return """
ПРАВИЛА ИНТЕРВАЛЬНЫХ НАПОМИНАНИЙ:
- Интервальное напоминание — это reminder_kind="interval".
- Интервальные маркеры: "каждые N секунд", "каждые N минут", "каждые N часов", "каждые N дней", "раз в N минут", "раз в N часов", "раз в N дней", "раз в день", "раз в неделю", "через каждые N дней", "каждые полчаса", "каждый час", "раз в сутки".
- interval_minutes всегда хранится в МИНУТАХ: 10 секунд округляй минимум до 1 минуты; 30 минут = 30; 2 часа = 120; 1 день/сутки = 1440; 3 дня = 4320; 2 недели = 20160.
- "каждые N дней" и "раз в N дней" — это interval, а не normal с repeat_type="every_n_days".
- Для дневных интервалов (interval_minutes >= 1440) window_start_time и window_end_time должны быть временем одного срабатывания: если сказано "в 20:00" — оба поля "20:00"; если время не указано — пользовательское "утро".
- Для минутных/часовых интервалов window_start_time и window_end_time задают период внутри дня.
- Обязательно понимай окна: "с 9 до 18", "до вечера", "до ночи", "в течение дня", "весь день", "в течение 6 часов", "в течение 5 дней", "5 дней подряд", "на 5 дней", "на протяжении 30 минут", "следующие 4 часа", "ближайшие 5 дней".
- Если начало периода не указано — начало = пользовательское "утро", кроме фраз "в течение N часов/минут/дней" без даты: тогда начало = текущий момент.
- Если конец периода не указан — конец = пользовательский "вечер".
- "до вечера" = конец периода пользовательское "вечер"; "до ночи" = пользовательская "ночь".
- "с 9 до 18" = window_start_time="09:00", window_end_time="18:00".
- "каждые 2 часа в течение 6 часов" = interval: первое срабатывание через 2 часа от текущего момента, серия длится 6 часов.
- "каждые 2 часа в течение 5 дней" = interval: серия длится 5 дней от старта, срабатывания идут каждые 2 часа до конца этих 5 дней.
- "каждые 3 дня в течение 15 дней" = interval: срабатывания идут каждые 3 дня, серия завершается через 15 дней.
- "завтра каждые 2 часа в течение 5 дней" = interval: начало завтра утром, конец через 5 дней после начала.
- "с 9 каждые 2 часа в течение 5 дней" = interval: старт 09:00, серия длится 5 дней.
- "каждый день каждые 2 часа с 9 до 18" = interval + repeat_type="daily".
- "по будням каждые 45 минут" = interval + repeat_type="weekdays".
- "каждые 3 дня в 20:00 пить витамины" = interval + repeat_type="none", interval_minutes=4320, window_start_time="20:00", window_end_time="20:00".
- Если есть и шаг, и длительность, не путай их: в "каждые 2 часа в течение 5 дней" шаг = 2 часа, длительность серии = 5 дней.
- topic должен быть без слов интервала и периода: не включай "каждые 30 минут", "каждые 3 дня", "с 9 до 18", "до вечера", "в течение 6 часов", "в течение 5 дней".
""".strip()

def yandex_break_rules() -> str:
    return """
ШКОЛЬНЫЕ ПЕРЕМЕНЫ И УРОКИ:
- "на 2 перемене", "во 2 перемену", "на второй перемене", "к 2 перемене" => reminder_kind="break_single", break_number=2, break_mode="single".
- "каждую перемену" => reminder_kind="break_each", break_number=0, break_mode="each".
- "на 3 уроке", "к третьему уроку", "во 2 урок", "к 4 уроку", "после 1 урока" => reminder_kind="lesson_single", break_number=номер урока, break_mode="single".
- "каждый урок", "на каждом уроке" => reminder_kind="lesson_each", break_number=0, break_mode="each".
- "сделать уроки", "выучить уроки", "уроки по математике" без номера урока и без слов "каждый урок" — это НЕ lesson_single, а обычное normal-напоминание.
- Для break_single/break_each/lesson_single/lesson_each datetime_local можно оставить пустым: точное время берётся из настроек перемен и математически рассчитанных уроков.
- 1 урок начинается в 08:30. Дальше уроки считаются по переменам: конец урока = начало следующей перемены, начало следующего урока = конец предыдущей перемены.
- Если есть дата или день недели, они должны относиться к перемене/уроку: "завтра на 2 перемене" = именно завтра.
- Если фраза содержит ещё одно обычное событие, сделай отдельный объект normal для него.
""".strip()


def yandex_quality_rules() -> str:
    return """
КАЧЕСТВО РАЗБОРА:
1. Верни только JSON, без пояснений и Markdown.
2. Всегда используй схему reminders: массив объектов.
3. topic — короткая тема конкретного дела без даты, времени, повтора и слов "напомни/надо/нужно".
4. reminder_text — только кусок исходной фразы для конкретного напоминания, не весь текст, если событий несколько.
5. Если событий несколько, у каждого объекта отдельные topic и reminder_text.
6. Не склеивай два дела в одно напоминание.
7. Не копируй одинаковый reminder_text во все объекты.
8. Не возвращай время в прошлом. Если время одноразовое уже прошло, выбери ближайшее будущее по смыслу.
9. Если дату/время для normal/interval совсем нельзя понять, datetime_local="".
10. Для normal reminder_kind="normal", interval_minutes=0, window_start_time="", window_end_time="", break_number=0, break_mode="".
""".strip()


def yandex_prompt_level(user_text: str) -> str:
    """Выбирает минимальный целевой промпт под механику фразы."""
    t = normalize_spaces((user_text or "").lower().replace("ё", "е"))
    if not t:
        return "simple"

    # Несколько событий важнее конкретного типа: complex-промпт умеет смешивать normal/break/interval/repeat.
    if is_complex_reminder_text(t):
        return "complex"
    if has_school_period_reference(t):
        return "break"
    if has_interval_marker_from_text(t):
        return "interval"
    if detect_repeat_from_text(t):
        return "repeat"
    return "simple"


def yandex_common_json_schema() -> str:
    return """{
  "reminders": [
    {
      "topic": "краткая тема без даты и времени",
      "datetime_local": "YYYY-MM-DD HH:MM или пусто только для break_single/break_each/lesson_single/lesson_each",
      "category": "study/exam/meeting/deadline/personal/other",
      "priority": "very_high/high/medium/low",
      "repeat_type": "none/daily/weekly/monthly/yearly/weekdays/weekends/custom_weekdays/every_n_days",
      "repeat_value": "",
      "reminder_kind": "normal/interval/break_single/break_each/lesson_single/lesson_each",
      "interval_minutes": 0,
      "window_start_time": "HH:MM или пусто",
      "window_end_time": "HH:MM или пусто",
      "break_number": 0,
      "break_mode": "single/each или пусто",
      "reminder_text": "кусок исходной фразы только для этого напоминания"
    }
  ]
}"""


def yandex_prompt_header(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]], title: str) -> str:
    return f"""
Ты — строгий модуль разбора напоминаний для Telegram-бота. Тип задачи: {title}.
Верни только JSON по схеме, без текста до и после JSON.

КОНТЕКСТ:
{current_context_for_prompt(timezone_name)}
Часовой пояс: {timezone_title}
{build_time_words_prompt_block(custom_times)}
{yandex_spoken_time_rules()}

ФОРМАТ:
{yandex_common_json_schema()}
""".strip()


def build_yandex_simple_prompt(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    return f"""
{yandex_prompt_header(user_text, timezone_name, timezone_title, custom_times, "одно простое напоминание")}

{yandex_quality_rules()}
{yandex_category_priority_rules()}

ПРАВИЛА ДЛЯ ПРОСТОГО НАПОМИНАНИЯ:
- Верни ровно один объект в reminders.
- reminder_kind="normal".
- repeat_type="none", если пользователь явно не просит повтор.
- Если видишь явный повтор, всё равно можешь поставить repeat_type, но не создавай несколько объектов без необходимости.
- Дата без времени => используй пользовательскую настройку "утро".
- День недели без слов повтора => ближайшая будущая дата этого дня.

ТЕКСТ:
{user_text}
""".strip()


def build_yandex_repeat_prompt(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    return f"""
{yandex_prompt_header(user_text, timezone_name, timezone_title, custom_times, "обычное повторяющееся напоминание")}

{yandex_quality_rules()}
{yandex_category_priority_rules()}
{yandex_repeat_rules()}

ПРАВИЛА ДЛЯ ПОВТОРА:
- reminder_kind="normal".
- Верни один объект, если это одно повторяющееся дело.
- Если в одной повторяющейся фразе два разных времени, например "каждый день утром и вечером пить таблетки", верни два объекта daily: утром и вечером.
- datetime_local — ближайшее будущее срабатывание в часовом поясе пользователя.
- repeat_value для custom_weekdays всегда отсортирован: "0,2,4".

ТЕКСТ:
{user_text}
""".strip()


def build_yandex_interval_prompt(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    return f"""
{yandex_prompt_header(user_text, timezone_name, timezone_title, custom_times, "интервальное напоминание")}

{yandex_quality_rules()}
{yandex_category_priority_rules()}
{yandex_repeat_rules()}
{yandex_interval_rules()}

ПРАВИЛА ДЛЯ ИНТЕРВАЛА:
- Обычно верни один объект reminder_kind="interval".
- topic — только действие, без слов "каждые", "раз в", "до вечера", "с 9 до 18".
- datetime_local — первое срабатывание интервала.
- Если период будущий, первое срабатывание должно быть в начале окна.

ТЕКСТ:
{user_text}
""".strip()


def build_yandex_break_prompt(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    return f"""
{yandex_prompt_header(user_text, timezone_name, timezone_title, custom_times, "напоминание по школьной перемене или уроку")}

{yandex_quality_rules()}
{yandex_category_priority_rules()}
{yandex_repeat_rules()}
{yandex_break_rules()}

ПРАВИЛА ДЛЯ ОДНОЙ ФРАЗЫ ПРО ПЕРЕМЕНУ ИЛИ УРОК:
- Если это одно событие на перемене, верни один объект break_single или break_each.
- Если это одно событие на уроке, верни один объект lesson_single или lesson_each.
- topic очищай от слов "перемена", "урок", "на 2", "завтра", "каждую/каждый".
- Пример: "завтра на 2 перемене сдать тетради" => topic="Сдать тетради", reminder_kind="break_single", break_number=2.
- Пример: "завтра на 3 уроке повторить правило" => topic="Повторить правило", reminder_kind="lesson_single", break_number=3.
- Пример: "каждый урок пить воду" => topic="Пить воду", reminder_kind="lesson_each", break_number=0.
- Не путай фразу "сделать уроки" с уроком по расписанию: без номера урока или слов "каждый урок" это обычное normal-напоминание.

ТЕКСТ:
{user_text}
""".strip()


def build_yandex_complex_prompt(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    return f"""
{yandex_prompt_header(user_text, timezone_name, timezone_title, custom_times, "сложная фраза с несколькими напоминаниями")}

{yandex_quality_rules()}
{yandex_category_priority_rules()}
{yandex_repeat_rules()}
{yandex_interval_rules()}
{yandex_break_rules()}

ГЛАВНОЕ ПРАВИЛО СЛОЖНОЙ ФРАЗЫ:
Если в тексте несколько дел, дат, времён или частей через "а", "потом", "ещё", "также", ";", запятую — верни отдельный объект для каждого напоминания.

ОСОБЫЕ ПРАВИЛА:
- Если первая часть задаёт общую дату, а вторая часть содержит только время или слово времени, наследуй дату: "завтра утром школа, а вечером тренировка" => оба завтра.
- Если одна часть про перемену или урок, а другая обычная, первая break_single/break_each или lesson_single/lesson_each, вторая normal.
- Если одна часть интервальная, только она получает reminder_kind="interval".
- Если повтор явно общий для нескольких времён, можно вернуть несколько повторяющихся объектов.
- Если повтор относится к одному делу, не дроби его на много одноразовых объектов.

ПРИМЕР:
Текст: "завтра на 2 перемене сдать тетради, а вечером в 8 тренировка"
Ответ: два объекта:
1) topic="Сдать тетради", reminder_text="завтра на 2 перемене сдать тетради", reminder_kind="break_single", break_number=2.
2) topic="Тренировка", reminder_text="вечером в 8 тренировка", reminder_kind="normal", datetime_local на завтра 20:00.

ТЕКСТ:
{user_text}
""".strip()


def build_yandex_prompt_by_level(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> str:
    level = yandex_prompt_level(user_text)
    if level == "complex":
        return build_yandex_complex_prompt(user_text, timezone_name, timezone_title, custom_times)
    if level == "break":
        return build_yandex_break_prompt(user_text, timezone_name, timezone_title, custom_times)
    if level == "interval":
        return build_yandex_interval_prompt(user_text, timezone_name, timezone_title, custom_times)
    if level == "repeat":
        return build_yandex_repeat_prompt(user_text, timezone_name, timezone_title, custom_times)
    return build_yandex_simple_prompt(user_text, timezone_name, timezone_title, custom_times)


def force_yandex_parse_many(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None, parse_method: str = "yandex") -> tuple[list[ParsedReminder], Optional[str]]:
    """
    Надёжный разбор сложных фраз через YandexGPT.
    Для сложных и комбинированных напоминаний используем подробный промпт,
    потому что короткий быстрый промпт хуже разбирает разные даты и время.
    """
    result_text, error = ask_yandex(
        [
            {"role": "system", "text": "Ты строгий модуль разбора напоминаний. Возвращай только корректный JSON по схеме. Не добавляй пояснения. Для нескольких дел создавай несколько объектов reminders."},
            {"role": "user", "text": build_yandex_prompt_by_level(user_text, timezone_name, timezone_title, custom_times)},
        ],
        temperature=0.03,
        max_tokens=1600,
        connect_timeout=5,
        read_timeout=55,
    )
    if error:
        return [], error

    raw = extract_json(result_text or "")
    if not raw:
        return [], "Нейросеть не вернула корректный JSON. Попробуйте разделить сложную фразу на несколько коротких сообщений."

    parsed_many, err = normalize_many_reminders(raw, user_text, timezone_name, custom_times)
    if not parsed_many:
        return [], err or "Не удалось разобрать напоминание через YandexGPT."

    for item in parsed_many:
        item.parse_method = parse_method
    return parsed_many, None


def clone_parsed_with_local_at (item :ParsedReminder ,local_at :str ,timezone_name :str )->ParsedReminder :
    dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =ZoneInfo (timezone_name ))
    return ParsedReminder (
    topic =item .topic ,
    reminder_text =item .reminder_text ,
    category =item .category ,
    priority =item .priority ,
    repeat_type ="none",
    repeat_value ="",
    next_local_at =dt .strftime ("%Y-%m-%d %H:%M"),
    next_utc_at =dt .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),
    parse_method =item .parse_method ,
    )


def detect_month_day_from_text (user_text :str )->Optional [int ]:
    text =user_text .lower ().replace ("ё","е")
    m =re .search (r"\b(?:каждый\s+месяц|каждого\s+месяца|ежемесячно|раз\s+в\s+месяц)[^\d]{0,20}(\d{1,2})\s*(?:числа|число)?\b",text )
    if not m :
        m =re .search (r"\b(\d{1,2})\s*(?:числа|число)\s+(?:каждый\s+месяц|каждого\s+месяца|ежемесячно|раз\s+в\s+месяц)\b",text )
    if not m :
        return None 
    day =int (m .group (1 ))
    return day if 1 <=day <=31 else None 


def apply_month_day_if_needed (local_at :str ,user_text :str ,timezone_name :str ,repeat_type :str )->tuple [str ,str ]:
    tz =ZoneInfo (timezone_name )
    base =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    if repeat_type !="monthly":
        return base .strftime ("%Y-%m-%d %H:%M"),base .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")

    day =detect_month_day_from_text (user_text )
    if not day :
        return base .strftime ("%Y-%m-%d %H:%M"),base .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")

    now_local =datetime .now (tz )
    year ,month =now_local .year ,now_local .month 
    for _ in range (24 ):
        max_day =calendar .monthrange (year ,month )[1 ]
        candidate =base .replace (year =year ,month =month ,day =min (day ,max_day ))
        if candidate >now_local :
            return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")
        month +=1 
        if month >12 :
            month =1 
            year +=1 
    return base .strftime ("%Y-%m-%d %H:%M"),base .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")


def move_past_oneoff_datetime_to_future(local_at: str, user_text: str, timezone_name: str) -> str:
    """
    Исправляет одноразовое время в прошлом после ответа YandexGPT.
    Для дней недели переносит на следующую неделю, для дат с месяцем — на следующий год,
    для остальных случаев двигает по дням до ближайшего будущего.
    """
    tz = ZoneInfo(timezone_name)
    dt = datetime.strptime(local_at, "%Y-%m-%d %H:%M").replace(tzinfo=tz)
    now_local = datetime.now(tz)
    if dt > now_local:
        return local_at

    t = normalize_spaces((user_text or "").lower().replace("ё", "е"))
    has_month_date = bool(re.search(r"\b\d{1,2}\s+(?:" + "|".join(re.escape(name) for name in MONTH_WORD_TO_NUMBER) + r")\b", t))
    has_numeric_date = bool(re.search(r"(?<!\d)\d{1,2}[./-]\d{1,2}(?:[./-]\d{2,4})?(?!\d)", t))
    has_explicit_year = bool(re.search(r"\b20\d{2}\b", t))
    has_weekday = bool(re.search(r"\b(?:понедельник|понедельника|понедельнику|пн|вторник|вторника|вторнику|вт|среда|среду|среде|ср|четверг|четверга|четвергу|чт|пятница|пятницу|пятнице|пт|суббота|субботу|субботе|сб|воскресенье|воскресенья|воскресенью|вс)\b", t))

    if (has_month_date or has_numeric_date) and not has_explicit_year:
        while dt <= now_local:
            try:
                dt = dt.replace(year=dt.year + 1)
            except ValueError:
                dt = dt.replace(year=dt.year + 1, month=2, day=28)
    elif has_weekday:
        while dt <= now_local:
            dt += timedelta(days=7)
    else:
        while dt <= now_local:
            dt += timedelta(days=1)

    return dt.strftime("%Y-%m-%d %H:%M")


def normalize_parsed (raw :dict ,user_text :str ,timezone_name :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [Optional [ParsedReminder ],Optional [str ]]:
    topic =str (raw .get ("topic","")).strip ()or "Напоминание"
    reminder_text =str (raw .get ("reminder_text","")).strip ()or normalize_spaces (user_text )
    category =str (raw .get ("category","")).strip ()or classify_category (user_text )
    priority =str (raw .get ("priority","")).strip ()or classify_priority (user_text ,category )
    repeat_type =str (raw .get ("repeat_type","")).strip ()or "none"
    repeat_value =str (raw .get ("repeat_value","")).strip ()
    datetime_local =str (raw .get ("datetime_local","")).strip ()
    reminder_kind =str (raw .get ("reminder_kind","normal")).strip ()or "normal"
    if reminder_kind not in {"normal","interval","break_single","break_each","lesson_single","lesson_each"}:
        reminder_kind ="normal"
    try:
        interval_minutes =int (raw .get ("interval_minutes",0 )or 0)
    except Exception:
        interval_minutes =0
    window_start_time =str (raw .get ("window_start_time","")).strip ()
    window_end_time =str (raw .get ("window_end_time","")).strip ()
    window_days =str (raw .get ("window_days","")).strip ()
    try:
        break_number =int (raw .get ("break_number",0 )or 0)
    except Exception:
        break_number =0
    break_mode =str (raw .get ("break_mode","")).strip ()

    # Для перемен datetime может быть пустым: время вычисляется из настроек перемен пользователя.
    if reminder_kind in {"break_single","break_each","lesson_single","lesson_each"} and not datetime_local:
        # normalize_many_reminders передаёт сюда кусок исходного текста, но user_id здесь нет.
        # Поэтому сложные случаи по переменам лучше разбираются локально до вызова Yandex.
        return None ,"Для напоминания по перемене нужно настроенное время перемены."

    if not datetime_local :
        return None ,"Нейросеть не смогла выделить дату и время."

    if category not in CATEGORY_TITLES :
        category ="other"
    if priority not in PRIORITY_TITLES :
        priority ="medium"
    if repeat_type not in {"none","daily","weekly","monthly","yearly","weekdays","weekends","custom_weekdays","every_n_days"}:
        repeat_type ="none"
        repeat_value =""

        # Локальная страховка: если в тексте явно указан повтор по дням недели,
        # исправляем результат YandexGPT.
    detected_repeat =detect_repeat_from_text (user_text )
    if detected_repeat and reminder_kind != REMINDER_KIND_INTERVAL:
        repeat_type ,repeat_value =detected_repeat 
    if reminder_kind == REMINDER_KIND_INTERVAL:
        # "каждые N дней" внутри interval не превращаем обратно в repeat every_n_days.
        if is_long_interval_minutes(interval_minutes):
            repeat_type, repeat_value = "none", ""
        duration_minutes = interval_duration_minutes_from_text(user_text)
        base_dt_for_window = detect_base_date_for_interval(user_text, timezone_name, repeat_type, repeat_value)
        if duration_minutes:
            raw_start_time = window_start_time or interval_single_time_from_text(user_text, custom_times)[0]
            if not is_long_interval_minutes(interval_minutes):
                parsed_start_for_duration, _parsed_end_for_duration, _parsed_explicit_for_duration, _parsed_duration_for_duration = parse_interval_window_from_text(user_text, custom_times, timezone_name, base_dt_for_window)
                raw_start_time = window_start_time or parsed_start_for_duration
            series_start_dt = set_time_on_date(base_dt_for_window.date(), raw_start_time, ZoneInfo(timezone_name))
            window_days = build_interval_window_days(duration_minutes, series_start_dt)
        if not window_start_time or not window_end_time:
            if is_long_interval_minutes(interval_minutes):
                single_time, _ = interval_single_time_from_text(user_text, custom_times)
                window_start_time = window_start_time or single_time
                window_end_time = window_end_time or single_time
            else:
                parsed_start, parsed_end, _parsed_explicit, parsed_duration = parse_interval_window_from_text(user_text, custom_times, timezone_name, base_dt_for_window)
                window_start_time = window_start_time or parsed_start
                window_end_time = window_end_time or parsed_end
                if parsed_duration:
                    series_start_dt = set_time_on_date(base_dt_for_window.date(), parsed_start, ZoneInfo(timezone_name))
                    window_days = build_interval_window_days(parsed_duration, series_start_dt)
    repeat_type, repeat_value = protect_repeat_from_false_positive(user_text, repeat_type, repeat_value)

    if repeat_type =="every_n_days":
        if not repeat_value .isdigit ()or not (1 <=int (repeat_value )<=365 ):
            repeat_type ="none"
            repeat_value =""

    if repeat_type =="custom_weekdays":
        days =[]
        for x in repeat_value .split (","):
            x =x .strip ()
            if x .isdigit ()and 0 <=int (x )<=6 :
                days .append (str (int (x )))
        repeat_value =",".join (sorted (set (days ),key =int ))
        if not repeat_value :
            repeat_type ="none"

    local_at ,utc_at =parse_exact_local_datetime (datetime_local ,timezone_name )
    if not local_at or not utc_at :
        return None ,"Нейросеть вернула дату и время не в формате YYYY-MM-DD HH:MM."

    relative_datetime =parse_relative_datetime_from_now (user_text ,timezone_name ,custom_times )
    if relative_datetime and repeat_type =="none":
        local_at ,utc_at ,_details =relative_datetime
    else:
        local_at ,utc_at =apply_default_time_from_text (local_at ,user_text ,timezone_name ,custom_times )
        local_at ,utc_at =apply_month_day_if_needed (local_at ,user_text ,timezone_name ,repeat_type )

    tz =ZoneInfo (timezone_name )
    local_dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    now_local =datetime .now (tz )

    # Если YandexGPT вернул одноразовое время в прошлом, исправляем на ближайшее будущее.
    if repeat_type =="none"and local_dt <=now_local:
        local_at =move_past_oneoff_datetime_to_future(local_at, user_text, timezone_name)
        local_dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
        utc_at =local_dt .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S")

    try :
        if repeat_type !="none":
            local_at ,utc_at =recalc_next_after_repeat_change (local_at ,timezone_name ,repeat_type ,repeat_value )
        local_at ,utc_at =ensure_future_for_repeat (local_at ,timezone_name ,repeat_type ,repeat_value )
    except ValueError as e :
        return None ,str (e )

    return ParsedReminder (
    topic =topic [:120 ],
    reminder_text =reminder_text ,
    category =category ,
    priority =priority ,
    repeat_type =repeat_type ,
    repeat_value =repeat_value ,
    next_local_at =local_at ,
    next_utc_at =utc_at ,
    parse_method =str (raw .get ("parse_method","yandex") or "yandex"),
    reminder_kind =reminder_kind,
    interval_minutes =interval_minutes,
    window_start_time =window_start_time,
    window_end_time =window_end_time,
    window_days =window_days,
    break_number =break_number,
    break_mode =break_mode,
    ),None 


def normalize_many_reminders (raw :dict ,user_text :str ,timezone_name :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [list [ParsedReminder ],Optional [str ]]:
    """
    Принимает {"reminders": [...]} / {"denis_v4_reminders": [...]} или одиночный JSON.

    Исправления:
    - "каждую субботу и среду" => одно повторяющееся напоминание;
    - одинаковые дубли от Yandex удаляются;
    - "сегодня и завтра" с одинаковыми датами от Yandex пересобирается локально в разные даты.
    """
    items =raw .get ("reminders")
    if not isinstance (items ,list ):
        items =raw .get ("denis_v4_reminders")
    if isinstance (items ,list ):
        raw_items =[x for x in items if isinstance (x ,dict )]
    else :
        raw_items =[raw ]

    parsed_items :list [ParsedReminder ]=[]
    errors :list [str ]=[]

    segments = split_local_segments(user_text) if len(raw_items) > 1 else []

    for idx, item in enumerate(raw_items):
        item_source_text = str(item.get("reminder_text", "")).strip() or user_text
        if segments and idx < len(segments):
            normalized_item_text = normalize_spaces(item_source_text.lower().replace("ё", "е"))
            normalized_full_text = normalize_spaces(user_text.lower().replace("ё", "е"))
            # Если Yandex скопировал всю исходную фразу в каждый объект или дал слишком длинный кусок,
            # заменяем reminder_text на локально выделенный сегмент. Это стабилизирует карточки черновиков.
            if (not item_source_text
                or normalized_item_text == normalized_full_text
                or len(item_source_text) > max(25, len(segments[idx]) * 2)
                or (idx > 0 and normalized_item_text in normalized_full_text and not normalized_item_text.startswith(normalize_spaces(segments[idx].lower().replace("ё", "е"))[:10]))):
                item_source_text = segments[idx]
        time_context_text = yandex_time_context_text(item_source_text, user_text, custom_times)
        parsed ,err =normalize_parsed (item ,time_context_text ,timezone_name ,custom_times )
        if parsed :
            if not str(item.get("reminder_text", "")).strip() and item_source_text != user_text:
                parsed.reminder_text = item_source_text
            parsed_items .append (parsed )
        elif err :
            errors .append (err )

    if not parsed_items :
        return [],errors [0 ]if errors else "Нейросеть не вернула ни одного корректного напоминания."

    detected_repeat =detect_repeat_from_text (user_text )
    if detected_repeat :
        first =parsed_items [0 ]
        repeat_type ,repeat_value =detected_repeat 
        repeat_type, repeat_value = protect_repeat_from_false_positive(user_text, repeat_type, repeat_value)
        first .repeat_type =repeat_type 
        first .repeat_value =repeat_value 
        if repeat_type !="none":
            first .next_local_at ,first .next_utc_at =recalc_next_after_repeat_change (
            first .next_local_at ,
            timezone_name ,
            repeat_type ,
            repeat_value ,
            )
        return [first ],None 

    local_targets =detect_oneoff_combined_targets (user_text ,timezone_name ,parsed_items [0 ].next_local_at )
    if len (parsed_items )==1 and len (local_targets )>=2 :
        rebuilt =[clone_parsed_with_local_at (parsed_items [0 ],local_at ,timezone_name )for local_at in local_targets ]
        return dedupe_parsed_reminders (rebuilt ),None 

    return dedupe_parsed_reminders (parsed_items ),None 


def local_or_yandex_parse_many (user_text :str ,timezone_name :str ,timezone_title :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [list [ParsedReminder ],Optional [str ]]:
    """
    Основной разбор текста.
    Сначала пробуем локальный разбор. Если дата/время и тема найдены уверенно,
    YandexGPT не вызывается. Если локальный разбор явно не понял обязательное поле,
    просим пользователя уточнить. Для сложных фраз остаётся YandexGPT как запасной вариант.
    """
    local_items, local_error, should_try_yandex = local_parse_many_reminders(user_text, timezone_name, timezone_title, custom_times)
    if local_items:
        return local_items, None

    if local_error == "need_datetime":
        return [], (
            "Я понял текст, но не понял дату или время.\n\n"
            "Напиши точнее, когда напомнить. Например: <code>завтра утром</code>, "
            "<code>в 18:00</code> или <code>через 2 часа</code>."
        )
    if local_error == "need_topic":
        return [], "Я понял дату и время, но не понял, что именно нужно напомнить. Напиши задачу подробнее."

    if should_try_yandex:
        return force_yandex_parse_many(user_text, timezone_name, timezone_title, custom_times, "yandex")

    return [], "Не удалось разобрать сообщение. Попробуйте написать дату, время и задачу подробнее."


def local_or_yandex_parse (user_text :str ,timezone_name :str ,timezone_title :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [Optional [ParsedReminder ],Optional [str ]]:
    """
    Обратная совместимость для старых мест кода:
    возвращает первое напоминание из local_or_yandex_parse_many().
    """
    parsed_many ,err =local_or_yandex_parse_many (user_text ,timezone_name ,timezone_title ,custom_times )
    if parsed_many :
        return parsed_many [0 ],None 
    return None ,err 


def ask_yandex_edit_time (current_data :dict ,user_fix :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [Optional [str ],Optional [str ]]:
    """
    Изменение времени:
    1. Сначала пробуем локально.
    2. Если локально получилось — Yandex не вызываем.
    3. Если локально не получилось — используем Yandex.
    """
    local_result =local_edit_time_from_user_text (current_data ,user_fix ,custom_times )
    if local_result :
        return local_result ,None 

    result_text ,error =ask_yandex (
    [
    {"role":"system","text":"Измени только datetime_local. Ответ строго JSON. Не угадывай время."},
    {"role":"user","text":build_time_edit_prompt (current_data ,user_fix ,custom_times )},
    ],
    temperature =0.0 ,
    max_tokens =80 ,
    )
    if error :
        return None ,error 

    raw =extract_json (result_text or "")
    if not raw :
        return None ,"Нейросеть не вернула корректный JSON при изменении времени."

    datetime_local =str (raw .get ("datetime_local","")).strip ()
    if not datetime_local :
        return None ,"Нейросеть не смогла выделить новую дату и время."

    local_at ,_utc =parse_exact_local_datetime (datetime_local ,current_data ["timezone_name"])
    if not local_at :
        return None ,"Не удалось понять новую дату и время."

    explicit =extract_explicit_time_from_text (user_fix )
    default_words =None if explicit else extract_default_time_from_words (user_fix ,custom_times )
    if explicit or default_words :
        hour ,minute =explicit or default_words # type: ignore[misc]
        local_at ,_ =replace_time_in_local_at (local_at ,current_data ["timezone_name"],hour ,minute )

    tz =ZoneInfo (current_data ["timezone_name"])
    dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    now_local =datetime .now (tz )

    if current_data .get ("repeat_type")=="none"and dt <=now_local and dt .date ()==now_local .date ():
        dt =dt +timedelta (days =1 )
        local_at =dt .strftime ("%Y-%m-%d %H:%M")

    return local_at ,None 


    # =========================================================
    # Кнопки
    # =========================================================


def build_main_menu_reply (user_id :Optional [int ]=None )->types .ReplyKeyboardMarkup :
    kb =types .ReplyKeyboardMarkup (resize_keyboard =True )
    kb .row ("📋 Список","📅 На сегодня")
    kb .row ("📊 Статистика","🎨 Кастомизация")
    kb .row ("ℹ️ Помощь")
    return kb 


def build_main_nav_markup ()->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (
    types .InlineKeyboardButton ("📋 Список",callback_data ="nav:list"),
    types .InlineKeyboardButton ("📅 На сегодня",callback_data ="nav:today"),
    )
    markup .add (
    types .InlineKeyboardButton ("📊 Статистика",callback_data ="nav:stats"),
    types .InlineKeyboardButton ("🎨 Кастомизация",callback_data ="nav:customization"),
    )
    markup .add (
    types .InlineKeyboardButton ("🌍 Часовой пояс",callback_data ="nav:timezone"),
    types .InlineKeyboardButton ("ℹ️ Помощь",callback_data ="nav:help"),
    )
    return markup 


def build_timezone_markup ()->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for key in [
    "tz:kaliningrad","tz:moscow","tz:samara","tz:yekaterinburg","tz:omsk",
    "tz:krasnoyarsk","tz:irkutsk","tz:yakutsk","tz:vladivostok",
    "tz:magadan","tz:kamchatka","tz:utc",
    ]:
        title ,_ =TIMEZONE_OPTIONS [key ]
        markup .add (types .InlineKeyboardButton (title ,callback_data =key ))
    markup .add (types .InlineKeyboardButton ("↩️ На главную",callback_data ="nav:main"))
    return markup 


def is_interval_kind_value(value: object) -> bool:
    return str(value or "normal") in {REMINDER_KIND_INTERVAL, REMINDER_KIND_BREAK_EACH, REMINDER_KIND_LESSON_EACH}


def is_periodic_kind_value(value: object) -> bool:
    return str(value or "normal") in {REMINDER_KIND_INTERVAL, REMINDER_KIND_BREAK_EACH, REMINDER_KIND_BREAK_SINGLE, REMINDER_KIND_LESSON_EACH, REMINDER_KIND_LESSON_SINGLE}


def reminder_kind_from_row(row) -> str:
    try:
        return str(row["reminder_kind"] or "normal")
    except Exception:
        return "normal"


def interval_max_count_for_row(row) -> int:
    if is_interval_kind_value(reminder_kind_from_row(row)):
        return INTERVAL_NOTIFY_ATTEMPTS
    return max_notify_count_for_priority(row["priority"], int(row["user_id"] or 0))


def notify_interval_for_row(row) -> int:
    if is_interval_kind_value(reminder_kind_from_row(row)):
        return INTERVAL_NOTIFY_INTERVAL_SECONDS
    try:
        return get_user_priority_interval_seconds(int(row["user_id"] or 0), row["priority"])
    except Exception:
        return notify_interval_seconds_for_priority(row["priority"])


def interval_title_from_minutes(minutes: int) -> str:
    try:
        minutes = int(minutes or 0)
    except Exception:
        minutes = 0
    if minutes <= 0:
        return "не задан"
    if minutes % INTERVAL_WEEK_MINUTES == 0:
        weeks = minutes // INTERVAL_WEEK_MINUTES
        return f"каждые {weeks} нед."
    if minutes % INTERVAL_DAY_MINUTES == 0:
        days = minutes // INTERVAL_DAY_MINUTES
        return f"каждые {days} дн."
    if minutes % 60 == 0:
        hours = minutes // 60
        return f"каждые {hours} ч."
    return f"каждые {minutes} мин."


def reminder_kind_title(data: dict | sqlite3.Row) -> str:
    kind = data.get("reminder_kind", "normal") if isinstance(data, dict) else reminder_kind_from_row(data)
    if kind == REMINDER_KIND_INTERVAL:
        return "интервальное"
    if kind == REMINDER_KIND_BREAK_SINGLE:
        return "по перемене"
    if kind == REMINDER_KIND_BREAK_EACH:
        return "каждую перемену"
    if kind == REMINDER_KIND_LESSON_SINGLE:
        return "по уроку"
    if kind == REMINDER_KIND_LESSON_EACH:
        return "каждый урок"
    return "обычное"


def ensure_default_school_breaks(user_id: int) -> None:
    """Создаёт расписание перемен по умолчанию один раз для будней и субботы."""
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT default_breaks_initialized FROM denis_v4_user_settings WHERE user_id=?", (user_id,))
    row = cur.fetchone()
    if row and int(row["default_breaks_initialized"] or 0) == 1:
        conn.close()
        return
    if not row:
        cur.execute(
            "INSERT OR IGNORE INTO denis_v4_user_settings (user_id, timezone_name, timezone_title, default_breaks_initialized, updated_at_utc) VALUES (?, ?, ?, 0, ?)",
            (user_id, DEFAULT_TIMEZONE_NAME, DEFAULT_TIMEZONE_TITLE, now_utc_str()),
        )
    cur.execute("SELECT COUNT(*) AS c FROM denis_v4_school_breaks WHERE user_id=?", (user_id,))
    exists = int(cur.fetchone()["c"] or 0)
    if not exists:
        for weekday in sorted(DEFAULT_SCHOOL_BREAK_WEEKDAYS):
            for idx, (start_time, end_time) in enumerate(DEFAULT_SCHOOL_BREAK_RANGES, start=1):
                cur.execute(
                    "INSERT INTO denis_v4_school_breaks (user_id, weekday, break_index, start_time, end_time, created_at_utc) VALUES (?, ?, ?, ?, ?, ?)",
                    (user_id, weekday, idx, start_time, end_time, now_utc_str()),
                )
    cur.execute("UPDATE denis_v4_user_settings SET default_breaks_initialized=1, updated_at_utc=? WHERE user_id=?", (now_utc_str(), user_id))
    conn.commit()
    conn.close()


def get_school_breaks(user_id: int, weekday: Optional[int] = None) -> list[sqlite3.Row]:
    conn = get_db()
    cur = conn.cursor()
    if weekday is None:
        cur.execute("SELECT * FROM denis_v4_school_breaks WHERE user_id=? ORDER BY weekday, break_index", (user_id,))
    else:
        cur.execute("SELECT * FROM denis_v4_school_breaks WHERE user_id=? AND weekday=? ORDER BY break_index", (user_id, weekday))
    rows = cur.fetchall()
    conn.close()
    return rows


def count_configured_break_days(user_id: int) -> int:
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT COUNT(DISTINCT weekday) AS c FROM denis_v4_school_breaks WHERE user_id=?", (user_id,))
    value = int(cur.fetchone()["c"] or 0)
    conn.close()
    return value


def renumber_school_breaks(cur, user_id: int, weekday: int) -> None:
    cur.execute("SELECT id FROM denis_v4_school_breaks WHERE user_id=? AND weekday=? ORDER BY start_time, end_time, id", (user_id, weekday))
    ids = [int(r["id"]) for r in cur.fetchall()]
    for idx, rid in enumerate(ids, start=1):
        cur.execute("UPDATE denis_v4_school_breaks SET break_index=? WHERE id=?", (idx, rid))


def add_school_breaks_for_days(user_id: int, weekdays: set[int], ranges: list[tuple[str, str]]) -> tuple[int, int]:
    conn = get_db()
    cur = conn.cursor()
    added = 0
    duplicates = 0
    for weekday in sorted(weekdays):
        for start_time, end_time in ranges:
            cur.execute("SELECT 1 FROM denis_v4_school_breaks WHERE user_id=? AND weekday=? AND start_time=? AND end_time=?", (user_id, weekday, start_time, end_time))
            if cur.fetchone():
                duplicates += 1
                continue
            cur.execute("SELECT COALESCE(MAX(break_index),0)+1 AS idx FROM denis_v4_school_breaks WHERE user_id=? AND weekday=?", (user_id, weekday))
            idx = int(cur.fetchone()["idx"] or 1)
            cur.execute("INSERT INTO denis_v4_school_breaks (user_id, weekday, break_index, start_time, end_time, created_at_utc) VALUES (?, ?, ?, ?, ?, ?)", (user_id, weekday, idx, start_time, end_time, now_utc_str()))
            added += 1
        renumber_school_breaks(cur, user_id, weekday)
    conn.commit()
    conn.close()
    return added, duplicates


def delete_school_break_for_days(user_id: int, weekdays: set[int], break_index: int) -> int:
    conn = get_db()
    cur = conn.cursor()
    deleted = 0
    for weekday in sorted(weekdays):
        cur.execute("DELETE FROM denis_v4_school_breaks WHERE user_id=? AND weekday=? AND break_index=?", (user_id, weekday, break_index))
        deleted += cur.rowcount
        renumber_school_breaks(cur, user_id, weekday)
    conn.commit()
    conn.close()
    return deleted


def parse_break_ranges_text(text: str) -> tuple[list[tuple[str, str]], Optional[str]]:
    ranges: list[tuple[str, str]] = []
    for line in (text or "").splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.search(r"(\d{1,2})\s*[:.]?\s*(\d{2})\s*[-–— ]+\s*(\d{1,2})\s*[:.]?\s*(\d{2})", line)
        if not m:
            return [], f"Не понял строку: {line}"
        sh, sm, eh, em = map(int, m.groups())
        if not (0 <= sh <= 23 and 0 <= sm <= 59 and 0 <= eh <= 23 and 0 <= em <= 59):
            return [], f"Время вне диапазона: {line}"
        start = f"{sh:02d}:{sm:02d}"
        end = f"{eh:02d}:{em:02d}"
        if end <= start:
            return [], f"Конец перемены должен быть позже начала: {line}"
        ranges.append((start, end))
    if not ranges:
        return [], "Напиши хотя бы одну перемену."
    return ranges, None


def selected_break_days(user_id: int) -> set[int]:
    return CUSTOM_BREAK_SELECTED_DAYS.setdefault(user_id, set())


def set_time_on_date(date_value, hhmm: str, tz: ZoneInfo) -> datetime:
    hour, minute = parse_hhmm_string(hhmm) or (0, 0)
    return datetime(date_value.year, date_value.month, date_value.day, hour, minute, tzinfo=tz)


def next_matching_date(start_dt: datetime, repeat_type: str, repeat_value: str) -> Optional[datetime]:
    candidate = start_dt + timedelta(days=1)
    for _ in range(370):
        if repeat_type == "daily":
            return candidate
        if repeat_type == "weekdays" and candidate.weekday() < 5:
            return candidate
        if repeat_type == "weekends" and candidate.weekday() >= 5:
            return candidate
        if repeat_type == "custom_weekdays":
            days = {int(x) for x in str(repeat_value or "").split(",") if x.strip().isdigit()}
            if candidate.weekday() in days:
                return candidate
        candidate += timedelta(days=1)
    return None


def compute_next_interval_occurrence_from_values(timezone_name: str, current_local_at: str, repeat_type: str, repeat_value: str, interval_minutes: int, start_time: str, end_time: str, window_days: str = "") -> tuple[Optional[str], Optional[str]]:
    tz = ZoneInfo(timezone_name)
    try:
        current = datetime.strptime(current_local_at, "%Y-%m-%d %H:%M").replace(tzinfo=tz)
    except Exception:
        return None, None
    interval_minutes = max(1, int(interval_minutes or 1))

    duration_minutes = duration_from_window_days(window_days)
    stored_start = interval_start_from_window_days(window_days, timezone_name)

    # Дневные интервалы: "каждые N дней/недель" идут ровно от текущего срабатывания.
    # Если задана длительность серии, например "каждые 3 дня в течение 15 дней", серия завершается по лимиту duration.
    if is_long_interval_minutes(interval_minutes):
        next_dt = current + timedelta(minutes=interval_minutes)
        if duration_minutes:
            series_start = stored_start or set_time_on_date(current.date(), start_time, tz)
            if next_dt > series_start + timedelta(minutes=duration_minutes):
                return None, None
        return datetime_to_local_utc_strings(next_dt)

    if duration_minutes:
        period_start = stored_start or set_time_on_date(current.date(), start_time, tz)
        # Если старта нет в window_days и окно пересекает полночь, текущее срабатывание может относиться к вчерашнему окну.
        if not stored_start and current < period_start:
            previous_start = set_time_on_date((current - timedelta(days=1)).date(), start_time, tz)
            if current <= previous_start + timedelta(minutes=duration_minutes):
                period_start = previous_start
        end_dt = period_start + timedelta(minutes=duration_minutes)
    else:
        end_dt = set_time_on_date(current.date(), end_time, tz)

    next_dt = current + timedelta(minutes=interval_minutes)
    if next_dt <= end_dt:
        return datetime_to_local_utc_strings(next_dt)
    if repeat_type == "none":
        return None, None
    next_day = next_matching_date(current, repeat_type, repeat_value)
    if not next_day:
        return None, None
    start_dt = set_time_on_date(next_day.date(), start_time, tz)
    return datetime_to_local_utc_strings(start_dt)

def compute_next_break_occurrence(row: sqlite3.Row) -> tuple[Optional[str], Optional[str]]:
    kind = reminder_kind_from_row(row)
    tz = ZoneInfo(row["timezone_name"])
    try:
        current = datetime.strptime(row["active_trigger_local_at"] or row["next_local_at"], "%Y-%m-%d %H:%M").replace(tzinfo=tz)
    except Exception:
        current = datetime.now(tz)
    number = int(row["break_number"] or 0) if "break_number" in row.keys() else 0
    user_id = int(row["user_id"])
    period_type = "lesson" if kind in {REMINDER_KIND_LESSON_SINGLE, REMINDER_KIND_LESSON_EACH} else "break"
    single_kind = kind in {REMINDER_KIND_BREAK_SINGLE, REMINDER_KIND_LESSON_SINGLE}

    for p in school_periods_for_day(user_id, current.weekday(), period_type):
        if single_kind and number and int(p.get("period_index") or 0) != number:
            continue
        candidate = set_time_on_date(current.date(), str(p.get("start_time") or ""), tz)
        if candidate > current:
            return datetime_to_local_utc_strings(candidate)
    if row["repeat_type"] == "none":
        return None, None
    next_day = next_matching_date(current, row["repeat_type"], row["repeat_value"])
    if not next_day:
        return None, None
    for _ in range(14):
        periods = school_periods_for_day(user_id, next_day.weekday(), period_type)
        if periods:
            chosen = None
            if single_kind and number:
                for p in periods:
                    if int(p.get("period_index") or 0) == number:
                        chosen = p
                        break
            else:
                chosen = periods[0]
            if chosen:
                candidate = set_time_on_date(next_day.date(), str(chosen.get("start_time") or ""), tz)
                return datetime_to_local_utc_strings(candidate)
        next_day = next_day + timedelta(days=1)
    return None, None


def compute_next_periodic_occurrence(row: sqlite3.Row) -> tuple[Optional[str], Optional[str]]:
    kind = reminder_kind_from_row(row)
    if kind == REMINDER_KIND_INTERVAL:
        return compute_next_interval_occurrence_from_values(row["timezone_name"], row["active_trigger_local_at"] or row["next_local_at"], row["repeat_type"], row["repeat_value"], int(row["interval_minutes"] or 0), row["window_start_time"] or "08:00", row["window_end_time"] or "18:00", row["window_days"] if "window_days" in row.keys() else "")
    if kind in {REMINDER_KIND_BREAK_SINGLE, REMINDER_KIND_BREAK_EACH}:
        return compute_next_break_occurrence(row)
    return None, None


def interval_number_from_word(value: str) -> Optional[int]:
    value = normalize_spaces(str(value or "").lower().replace("ё", "е"))
    if value.isdigit():
        return int(value)
    numbers = {
        "один": 1, "одна": 1, "одно": 1, "одну": 1,
        "два": 2, "две": 2, "пару": 2,
        "три": 3, "четыре": 4, "пять": 5,
        "шесть": 6, "семь": 7, "восемь": 8, "девять": 9, "десять": 10,
        "одиннадцать": 11, "двенадцать": 12,
        "пятнадцать": 15, "двадцать": 20, "тридцать": 30,
    }
    return numbers.get(value)


def interval_amount_pattern() -> str:
    return r"(?:\d{1,3}|один|одна|одно|одну|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать|пятнадцать|двадцать|тридцать)"


def has_interval_marker_from_text(text: str) -> bool:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    number = interval_amount_pattern()
    if re.search(r"\b(?:кажд(?:ые|ый|ую)?|раз\s+в|через\s+кажд(?:ые|ый|ую)?)\s+(?:полчаса|полтора\s+часа|час|минуту|сутки)\b", t):
        return True
    if re.search(r"\bраз\s+в\s+(?:день|сутки|недел(?:ю|ю))\b", t):
        return True
    if re.search(rf"\b(?:кажд(?:ые|ый|ую)?|раз\s+в|через\s+кажд(?:ые|ый|ую)?)\s+({number})\s*(?:секунд(?:у|ы)?|сек|с|минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|недел(?:ю|и|ь)?)\b", t):
        return True
    if re.search(r"\bчерез\s+день\b", t) and not re.search(r"\bнапомни(?:ть)?\b", t):
        return True
    return False


def parse_interval_minutes_from_text(text: str) -> Optional[int]:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if re.search(r"\b(?:кажд(?:ые|ый|ую)?|раз\s+в|через\s+кажд(?:ые|ый|ую)?)\s+полчаса\b", t):
        return 30
    if re.search(r"\b(?:кажд(?:ые|ый|ую)?|раз\s+в|через\s+кажд(?:ые|ый|ую)?)\s+полтора\s+часа\b", t):
        return 90
    if re.search(r"\b(?:каждый|каждые|раз\s+в|через\s+каждый)\s+час\b", t):
        return 60
    if re.search(r"\b(?:каждую|каждые|раз\s+в|через\s+каждую)\s+минуту\b", t):
        return 1
    if re.search(r"\b(?:каждые|раз\s+в|через\s+каждые)\s+сутки\b", t):
        return INTERVAL_DAY_MINUTES
    if re.search(r"\bраз\s+в\s+день\b", t):
        return INTERVAL_DAY_MINUTES
    if re.search(r"\bраз\s+в\s+недел(?:ю|ю)\b", t):
        return INTERVAL_WEEK_MINUTES
    if re.search(r"\bчерез\s+день\b", t) and not re.search(r"\bнапомни(?:ть)?\b", t):
        return 2 * INTERVAL_DAY_MINUTES

    number = interval_amount_pattern()
    m = re.search(rf"\b(?:кажд(?:ые|ый|ую)?|раз\s+в|через\s+кажд(?:ые|ый|ую)?)\s+({number})\s*(секунд(?:у|ы)?|сек|с|минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|недел(?:ю|и|ь)?)\b", t)
    if not m:
        return None
    n = interval_number_from_word(m.group(1))
    if not n or n <= 0:
        return None
    unit = m.group(2)
    if unit.startswith("сек") or unit == "с":
        return max(1, round(n / 60))
    if unit.startswith("мин") or unit == "м":
        return n
    if unit.startswith("час") or unit == "ч":
        return n * 60
    if unit.startswith("недел"):
        return n * INTERVAL_WEEK_MINUTES
    return n * INTERVAL_DAY_MINUTES


def is_long_interval_minutes(minutes: int) -> bool:
    try:
        return int(minutes or 0) >= INTERVAL_DAY_MINUTES
    except Exception:
        return False


def interval_single_time_from_text(text: str, custom_times: Optional[dict[str, str]] = None) -> tuple[str, bool]:
    explicit = extract_explicit_time_from_text(text)
    if explicit:
        return format_hhmm(explicit[0], explicit[1]), True
    default_words = extract_default_time_from_words(text, custom_times)
    if default_words:
        return format_hhmm(default_words[0], default_words[1]), True
    hour, minute = custom_morning_time(custom_times)
    return format_hhmm(hour, minute), False

def interval_duration_minutes_from_text(text: str) -> int:
    """Достаёт длительность серии/окна: "в течение 6 часов", "в течение 5 дней", "5 дней подряд", "на 5 дней"."""
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    number = interval_amount_pattern()
    special_patterns = [
        (r"\b(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи])\s+полчаса\b", 30),
        (r"\b(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи])\s+полтора\s+часа\b", 90),
        (r"\b(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи])\s+часа?\b", 60),
        (r"\b(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи])\s+дня?\b", INTERVAL_DAY_MINUTES),
        (r"\b(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи])\s+недел(?:ю|и|ь)?\b", INTERVAL_WEEK_MINUTES),
    ]
    for pattern, value in special_patterns:
        if re.search(pattern, t):
            return value

    duration_leads = r"(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи]|следующ(?:ие|их)|ближайш(?:ие|их))"
    m = re.search(
        rf"\b{duration_leads}\s+({number})\s*"
        r"(секунд(?:у|ы)?|сек|с|минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|недел(?:ю|и|ь)?)\b",
        t,
    )
    if not m:
        m = re.search(
            rf"\b(?:на\s+(?:ближайш(?:ие|их)\s+)?|)(?P<num>{number})\s*"
            r"(?P<unit>день|дня|дней|сутки|суток|недел(?:ю|и|ь)?|час(?:а|ов)?|ч|минут(?:у|ы)?|мин|м)\s+(?:подряд|серией|периодом)\b",
            t,
        )
        if not m:
            m = re.search(
                rf"\bна\s+(?:ближайш(?:ие|их)\s+)?(?P<num>{number})\s*"
                r"(?P<unit>день|дня|дней|сутки|суток|недел(?:ю|и|ь)?|час(?:а|ов)?|ч|минут(?:у|ы)?|мин|м)\b",
                t,
            )
        if not m:
            return 0
        raw_num = m.group("num")
        unit = m.group("unit")
    else:
        raw_num = m.group(1)
        unit = m.group(2)

    n = interval_number_from_word(raw_num)
    if not n or n <= 0:
        return 0
    if unit.startswith("сек") or unit == "с":
        return max(1, round(n / 60))
    if unit.startswith("мин") or unit == "м":
        return n
    if unit.startswith("час") or unit == "ч":
        return n * 60
    if unit.startswith("недел"):
        return n * INTERVAL_WEEK_MINUTES
    return n * INTERVAL_DAY_MINUTES


def duration_from_window_days(value: str) -> int:
    value = str(value or "").strip()
    match = re.search(r"(?:^|;)duration:(\d+)(?:;|$)", value)
    if not match:
        return 0
    try:
        return int(match.group(1))
    except Exception:
        return 0


def interval_start_from_window_days(value: str, timezone_name: str) -> Optional[datetime]:
    value = str(value or "").strip()
    match = re.search(r"(?:^|;)start:([0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2})(?:;|$)", value)
    if not match:
        return None
    try:
        return datetime.strptime(match.group(1), "%Y-%m-%d %H:%M").replace(tzinfo=ZoneInfo(timezone_name))
    except Exception:
        return None


def build_interval_window_days(duration_minutes: int, start_dt: Optional[datetime] = None) -> str:
    if not duration_minutes:
        return ""
    value = f"duration:{int(duration_minutes)}"
    if start_dt:
        value += f";start:{start_dt.strftime('%Y-%m-%d %H:%M')}"
    return value


def interval_window_start_only_from_text(text: str, custom_times: Optional[dict[str, str]] = None) -> tuple[Optional[str], bool]:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    times = time_words_for_prompt(custom_times)
    if re.search(r"\b(?:с|начиная\s+с)\s+утра\b", t):
        return times["morning"], True
    if re.search(r"\b(?:с|начиная\s+с)\s+(?:дня|обеда)\b", t):
        return times["day"], True
    if re.search(r"\b(?:с|начиная\s+с)\s+вечера\b", t):
        return times["evening"], True
    if re.search(r"\b(?:с|начиная\s+с)\s+ночи\b", t):
        return times["night"], True
    m = re.search(r"\b(?:с|начиная\s+с)\s+(\d{1,2})(?::|\s)?([0-5]\d)?\b(?!\s+до)", t)
    if m:
        h = int(m.group(1)); mi = int(m.group(2) or 0)
        if 0 <= h <= 23 and 0 <= mi <= 59:
            return f"{h:02d}:{mi:02d}", True
    return None, False


def parse_interval_window_from_text(
    text: str,
    custom_times: Optional[dict[str, str]] = None,
    timezone_name: Optional[str] = None,
    base_dt: Optional[datetime] = None,
) -> tuple[str, str, bool, int]:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    times = time_words_for_prompt(custom_times)
    start_time = times["morning"]
    end_time = times["evening"]
    explicit_start = False

    m = re.search(r"\bс\s+(\d{1,2})(?::|\s)?([0-5]\d)?\s+до\s+(\d{1,2})(?::|\s)?([0-5]\d)?\b", t)
    if m:
        sh = int(m.group(1)); sm = int(m.group(2) or 0); eh = int(m.group(3)); em = int(m.group(4) or 0)
        start_time = f"{sh:02d}:{sm:02d}"; end_time = f"{eh:02d}:{em:02d}"; explicit_start = True
    elif re.search(r"\bс\s+утра\s+до\s+вечера\b", t):
        start_time = times["morning"]; end_time = times["evening"]; explicit_start = True
    elif re.search(r"\bс\s+утра\s+до\s+ночи\b", t):
        start_time = times["morning"]; end_time = times["night"]; explicit_start = True

    if re.search(r"\bдо\s+вечера\b|\bв\s+течени[еи]\s+дня\b|\bвесь\s+день\b", t):
        end_time = times["evening"]
    if re.search(r"\bдо\s+ночи\b", t):
        end_time = times["night"]

    duration_minutes = interval_duration_minutes_from_text(t)
    if duration_minutes:
        tz = ZoneInfo(timezone_name or DEFAULT_TIMEZONE_NAME)
        now = datetime.now(tz).replace(second=0, microsecond=0)
        base = base_dt or now
        start_only, start_only_ok = interval_window_start_only_from_text(t, custom_times)
        if start_only_ok and start_only:
            start_time = start_only
            explicit_start = True
        elif not explicit_start:
            # Для "каждые 2 часа в течение 6 часов" без даты начинаем от текущего момента.
            # Для будущей даты начинаем с пользовательского утра.
            if base.date() == now.date() and "завтра" not in t and "послезавтра" not in t:
                start_time = now.strftime("%H:%M")
            else:
                start_time = times["morning"]
            explicit_start = True
        start_dt = set_time_on_date(base.date(), start_time, tz)
        if start_dt < now and base.date() == now.date() and not start_only_ok and not re.search(r"\bс\s+", t):
            start_dt = now
            start_time = now.strftime("%H:%M")
        end_dt = start_dt + timedelta(minutes=duration_minutes)
        end_time = end_dt.strftime("%H:%M")

    return start_time, end_time, explicit_start, duration_minutes


def parse_period_times_from_text(text: str, custom_times: Optional[dict[str, str]] = None) -> tuple[str, str, bool]:
    start_time, end_time, explicit_start, _duration = parse_interval_window_from_text(text, custom_times)
    return start_time, end_time, explicit_start

def detect_interval_repeat_from_text(text: str) -> tuple[str, str]:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if re.search(r"\b(каждый\s+день|ежедневно)\b", t):
        return "daily", ""
    if re.search(r"\b(по\s+будням|в\s+будни|каждый\s+будний\s+день)\b", t):
        return "weekdays", ""
    if re.search(r"\b(по\s+выходным|каждые\s+выходные|каждый\s+выходной)\b", t):
        return "weekends", ""
    repeat = detect_repeat_from_text(text)
    # Для интервальных напоминаний день недели без явного маркера повтора — это дата серии,
    # а не регулярный еженедельный повтор.
    if repeat and repeat[0] == "custom_weekdays" and has_explicit_weekday_repeat_marker(text):
        return repeat
    return "none", ""


def repeat_matches_date(dt: datetime, repeat_type: str, repeat_value: str) -> bool:
    if repeat_type == "daily":
        return True
    if repeat_type == "weekdays":
        return dt.weekday() < 5
    if repeat_type == "weekends":
        return dt.weekday() >= 5
    if repeat_type == "custom_weekdays":
        days = {int(x) for x in str(repeat_value or "").split(",") if x.strip().isdigit()}
        return dt.weekday() in days
    return True


def first_matching_date_including_today(now: datetime, repeat_type: str, repeat_value: str) -> datetime:
    candidate = now
    for _ in range(370):
        if repeat_matches_date(candidate, repeat_type, repeat_value):
            return candidate
        candidate += timedelta(days=1)
    return now


def detect_base_date_for_interval(text: str, timezone_name: str, repeat_type: str, repeat_value: str) -> datetime:
    tz = ZoneInfo(timezone_name)
    now = datetime.now(tz).replace(second=0, microsecond=0)
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if repeat_type != "none":
        return first_matching_date_including_today(now, repeat_type, repeat_value)
    if "завтра" in t:
        return now + timedelta(days=1)
    if "послезавтра" in t:
        return now + timedelta(days=2)
    date_info = extract_date_from_text(t, now)
    if date_info:
        return date_info[0]
    return now


def first_interval_occurrence(timezone_name: str, base_dt: datetime, interval_minutes: int, start_time: str, end_time: str, explicit_start: bool, text: str, repeat_type: str = "none", repeat_value: str = "", duration_minutes: int = 0) -> tuple[str, str]:
    tz = ZoneInfo(timezone_name)
    now = datetime.now(tz).replace(second=0, microsecond=0)
    start_dt = set_time_on_date(base_dt.date(), start_time, tz)
    end_dt = start_dt + timedelta(minutes=duration_minutes) if duration_minutes else set_time_on_date(base_dt.date(), end_time, tz)
    interval_minutes = max(1, int(interval_minutes or 1))
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if is_long_interval_minutes(interval_minutes):
        # Для "каждые N дней" первое срабатывание — ближайшее будущее выбранного времени,
        # а следующие срабатывания идут ровно через N дней.
        candidate = start_dt
        while candidate <= now:
            candidate += timedelta(days=1)
        return datetime_to_local_utc_strings(candidate)
    current_period = bool(re.search(r"\bв\s+течени[еи]\s+дня\b|\bвесь\s+день\b", t))
    if current_period and base_dt.date() == now.date() and not duration_minutes:
        # «в течение дня» начинается от текущего момента и длится до вечера.
        candidate = now + timedelta(minutes=interval_minutes)
    elif explicit_start:
        # При явном периоде «с 10 до 18» или «в течение 6 часов» идём по сетке от начала периода.
        candidate = start_dt
        while candidate <= now:
            candidate += timedelta(minutes=interval_minutes)
    else:
        if base_dt.date() == now.date():
            # Если период не указан, для сегодняшнего дня начинаем от текущего момента.
            candidate = now + timedelta(minutes=interval_minutes)
        else:
            # Для будущего дня период начинается ровно с начала окна.
            candidate = start_dt
        while candidate <= now:
            candidate += timedelta(minutes=interval_minutes)
    if candidate > end_dt:
        # Если текущий период уже закончился, переносим на следующий подходящий день.
        if repeat_type != "none":
            next_base = next_matching_date(base_dt, repeat_type, repeat_value) or (base_dt + timedelta(days=1))
        else:
            next_base = base_dt + timedelta(days=1)
        candidate = set_time_on_date(next_base.date(), start_time, tz)
    return datetime_to_local_utc_strings(candidate)

def local_parse_interval_reminder(user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> tuple[Optional[ParsedReminder], Optional[str]]:
    interval_minutes = parse_interval_minutes_from_text(user_text)
    if not interval_minutes:
        return None, None
    repeat_type, repeat_value = detect_interval_repeat_from_text(user_text)
    base_dt = detect_base_date_for_interval(user_text, timezone_name, repeat_type, repeat_value)
    start_time, end_time, explicit_start, duration_minutes = parse_interval_window_from_text(user_text, custom_times, timezone_name, base_dt)
    series_start_dt = set_time_on_date(base_dt.date(), start_time, ZoneInfo(timezone_name)) if duration_minutes else None
    window_days_value = build_interval_window_days(duration_minutes, series_start_dt)
    if is_long_interval_minutes(interval_minutes):
        start_time, explicit_start = interval_single_time_from_text(user_text, custom_times)
        end_time = start_time
        series_start_dt = set_time_on_date(base_dt.date(), start_time, ZoneInfo(timezone_name)) if duration_minutes else None
        window_days_value = build_interval_window_days(duration_minutes, series_start_dt)
        repeat_type, repeat_value = "none", ""
    local_at, utc_at = first_interval_occurrence(timezone_name, base_dt, interval_minutes, start_time, end_time, explicit_start, user_text, repeat_type, repeat_value, duration_minutes)
    if duration_minutes:
        # Если первое срабатывание сдвинулось в будущее из-за уже прошедшего старта, фиксируем фактический старт серии.
        try:
            first_dt = datetime.strptime(local_at, "%Y-%m-%d %H:%M").replace(tzinfo=ZoneInfo(timezone_name))
            stored_start = series_start_dt or first_dt
            if stored_start + timedelta(minutes=duration_minutes) < first_dt:
                stored_start = first_dt
            window_days_value = build_interval_window_days(duration_minutes, stored_start)
        except Exception:
            pass
    topic_source = re.sub(r"\b(?:кажд(?:ые|ый|ую)?|раз\s+в|через\s+кажд(?:ые|ый|ую)?)\s+(?:(?:\d{1,3}|один|одна|одно|одну|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать|пятнадцать|двадцать|тридцать)\s*)?(?:полчаса|полтора\s+часа|секунд(?:у|ы)?|сек|с|минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|недел(?:ю|и|ь)?)\b", " ", user_text, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bчерез\s+день\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bраз\s+в\s+(?:день|сутки|недел(?:ю|ю))\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bс\s+\d{1,2}(?::|\s)?[0-5]?\d?\s+до\s+\d{1,2}(?::|\s)?[0-5]?\d?\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bс\s+утра\s+до\s+(?:вечера|ночи)\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bдо\s+(?:вечера|ночи)\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\b(?:в\s+течени[еи]|на\s+протяжении|в\s+продолжени[еи]|следующ(?:ие|их)|ближайш(?:ие|их))\s+(?:(?:\d{1,3}|один|одна|одно|одну|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать|пятнадцать|двадцать|тридцать)\s*)?(?:полчаса|полтора\s+часа|секунд(?:у|ы)?|сек|с|минут(?:у|ы)?|мин|м|час(?:а|ов)?|ч|день|дня|дней|сутки|суток|недел(?:ю|и|ь)?)\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\b(?:на\s+(?:ближайш(?:ие|их)\s+)?(?:\d{1,3}|один|одна|одно|одну|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать|пятнадцать|двадцать|тридцать)\s*(?:день|дня|дней|сутки|суток|недел(?:ю|и|ь)?|час(?:а|ов)?|ч|минут(?:у|ы)?|мин|м)|(?:\d{1,3}|один|одна|одно|одну|два|две|пару|три|четыре|пять|шесть|семь|восемь|девять|десять|одиннадцать|двенадцать|пятнадцать|двадцать|тридцать)\s*(?:день|дня|дней|сутки|суток|недел(?:ю|и|ь)?|час(?:а|ов)?|ч|минут(?:у|ы)?|мин|м)\s+(?:подряд|серией|периодом))\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bв\s+течени[еи]\s+дня\b|\bвесь\s+день\b", " ", topic_source, flags=re.IGNORECASE)
    topic_source = re.sub(r"\bкаждый\s+день\b|\bежедневно\b|\bпо\s+будням\b|\bв\s+будни\b|\bпо\s+выходным\b", " ", topic_source, flags=re.IGNORECASE)
    topic = extract_local_topic(topic_source) or extract_local_topic(user_text) or "Напоминание"
    category = classify_category(user_text)
    priority = classify_priority(user_text, category)
    return ParsedReminder(
        topic=topic,
        reminder_text=normalize_spaces(user_text),
        category=category,
        priority=priority,
        repeat_type=repeat_type,
        repeat_value=repeat_value,
        next_local_at=local_at,
        next_utc_at=utc_at,
        parse_method="local",
        reminder_kind=REMINDER_KIND_INTERVAL,
        interval_minutes=interval_minutes,
        window_start_time=start_time,
        window_end_time=end_time,
        window_days=window_days_value,
    ), None


def weekday_from_text(text: str) -> Optional[int]:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    patterns = {
        0: r"\b(?:понедельник|понедельника|понедельнику|пн)\b",
        1: r"\b(?:вторник|вторника|вторнику|вт)\b",
        2: r"\b(?:среда|среду|среде|ср)\b",
        3: r"\b(?:четверг|четверга|четвергу|чт)\b",
        4: r"\b(?:пятница|пятницу|пятнице|пт)\b",
        5: r"\b(?:суббота|субботу|субботе|сб)\b",
        6: r"\b(?:воскресенье|воскресенья|воскресенью|вс)\b",
    }
    for k, pat in patterns.items():
        if re.search(pat, t):
            return k
    return None



def has_break_reference(text: str) -> bool:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    return bool(re.search(r"\bперемен", t))


def has_lesson_period_reference(text: str) -> bool:
    """True только для урока как школьного периода, а не для обычной фразы "сделать уроки"."""
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if not re.search(r"\bурок", t):
        return False
    if re.search(r"\bкажд\w*\s+урок", t) or re.search(r"\bна\s+кажд\w*\s+урок", t):
        return True
    return extract_lesson_number(t) is not None


def has_school_period_reference(text: str) -> bool:
    return has_break_reference(text) or has_lesson_period_reference(text)


def extract_break_number(text: str) -> Optional[int]:
    """
    Достаёт номер школьной перемены из живой русской фразы.

    Поддерживает:
    - "во 2 перемену", "на 2 перемене", "к 2 перемене";
    - "на 2-й перемене", "на 2ую перемену";
    - "на второй перемене", "во вторую перемену";
    - "2 перемена", "2-я перемена".
    """
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if "перемен" not in t:
        return None

    numeric_patterns = [
        r"\b(?:во|в|на|к|ко)\s+(\d{1,2})\s*(?:[-–]?\s*(?:я|й|ю|ую|ую|ой|е|ая|ую))?\s+перемен",
        r"\b(\d{1,2})\s*(?:[-–]?\s*(?:я|й|ю|ую|ой|е|ая|ую))?\s+перемен",
    ]
    for pattern in numeric_patterns:
        m = re.search(pattern, t)
        if m:
            value = int(m.group(1))
            if 1 <= value <= 20:
                return value

    word_patterns = [
        (1, r"перв\w*"),
        (2, r"втор\w*"),
        (3, r"трет\w*"),
        (4, r"четверт\w*"),
        (5, r"пят\w*"),
        (6, r"шест\w*"),
        (7, r"седьм\w*"),
        (8, r"восьм\w*"),
        (9, r"девят\w*"),
        (10, r"десят\w*"),
        (11, r"одиннадцат\w*"),
        (12, r"двенадцат\w*"),
    ]
    for value, pattern in word_patterns:
        if re.search(rf"\b(?:во|в|на|к|ко)?\s*{pattern}\s+перемен", t):
            return value
    return None


def break_text_has_explicit_date(text: str, timezone_name: str) -> Optional[datetime]:
    """Возвращает конкретный день для фраз вроде "завтра", "в понедельник", "10 мая"."""
    tz = ZoneInfo(timezone_name)
    now = datetime.now(tz).replace(second=0, microsecond=0)
    date_info = extract_date_from_text(text, now)
    if not date_info:
        return None
    base, _kind, _has_year = date_info
    return base.replace(hour=0, minute=0, second=0, microsecond=0)



def text_has_date_hint(text: str) -> bool:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if re.search(r"\b(?:сегодня|завтра|послезавтра)\b", t):
        return True
    if re.search(r"\b(?:понедельник|понедельника|понедельнику|пн|вторник|вторника|вторнику|вт|среда|среду|среде|ср|четверг|четверга|четвергу|чт|пятница|пятницу|пятнице|пт|суббота|субботу|субботе|сб|воскресенье|воскресенья|воскресенью|вс)\b", t):
        return True
    month_names = "|".join(sorted((re.escape(name) for name in MONTH_WORD_TO_NUMBER), key=len, reverse=True))
    if re.search(rf"(?<!\d)\d{{1,2}}\s+(?:{month_names})(?:\s+(?:20\d{{2}}|\d{{2}}))?(?!\d)", t):
        return True
    if re.search(r"(?<!\d)\d{1,2}[./-]\d{1,2}(?:[./-]\d{2,4})?(?!\d)", t):
        return True
    return False


def common_date_prefix_for_segments(text: str) -> str:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if re.search(r"\bпослезавтра\b", t):
        return "послезавтра"
    if re.search(r"\bзавтра\b", t):
        return "завтра"
    if re.search(r"\bсегодня\b", t):
        return "сегодня"
    m = re.search(r"\b(?:в\s+)?(понедельник|понедельника|понедельнику|пн|вторник|вторника|вторнику|вт|среда|среду|среде|ср|четверг|четверга|четвергу|чт|пятница|пятницу|пятнице|пт|суббота|субботу|субботе|сб|воскресенье|воскресенья|воскресенью|вс)\b", t)
    if m:
        return m.group(0)
    return ""


def cleanup_break_topic(text: str) -> str:
    """Убирает из темы слова про дату, перемену или урок, но оставляет само действие."""
    t = str(text or "")
    ordinal_part = r"(?:\d{1,2}\s*(?:[-–]?\s*(?:я|й|ю|ую|ой|е|ая|ый|м|ом|ого|ему|а|у))?|перв\w*|втор\w*|трет\w*|четверт\w*|пят\w*|шест\w*|седьм\w*|восьм\w*|девят\w*|десят\w*|одиннадцат\w*|двенадцат\w*)"
    t = re.sub(
        rf"\b(?:во|в|на|к|ко|перед|до|после)?\s*{ordinal_part}\s+(?:перемен|урок)\w*",
        " ",
        t,
        flags=re.IGNORECASE,
    )
    t = re.sub(r"\bкажд\w*\s+(?:перемен|урок)\w*", " ", t, flags=re.IGNORECASE)
    t = re.sub(r"\bна\s+кажд\w*\s+(?:перемен|урок)\w*", " ", t, flags=re.IGNORECASE)
    topic = extract_local_topic(t) or cleanup_local_topic_junk(normalize_spaces(t))
    if not topic:
        return "Напоминание"
    return topic[:1].upper() + topic[1:120]

def find_school_period_datetime(user_id: int, timezone_name: str, text: str, mode: str, number: int = 0, period_type: str = "break") -> tuple[Optional[str], Optional[str], Optional[str]]:
    tz = ZoneInfo(timezone_name)
    now = datetime.now(tz).replace(second=0, microsecond=0)
    explicit_day = break_text_has_explicit_date(text, timezone_name)

    def periods_for_day(day_dt: datetime) -> list[tuple[datetime, dict]]:
        result: list[tuple[datetime, dict]] = []
        for p in school_periods_for_day(user_id, day_dt.weekday(), period_type):
            if mode == "single" and number and int(p.get("period_index") or 0) != number:
                continue
            candidate = set_time_on_date(day_dt.date(), str(p.get("start_time") or ""), tz)
            result.append((candidate, p))
        return result

    if explicit_day is not None:
        candidates = periods_for_day(explicit_day)
        title = "уроки" if period_type == "lesson" else "перемены"
        if not candidates:
            return None, None, f"Для этого дня {title} не настроены. Настрой расписание в кастомизации."
        future_candidates = [x for x in candidates if x[0] > now or x[0].date() > now.date()]
        if not future_candidates:
            return None, None, f"Этот {'урок' if period_type == 'lesson' else 'перемена'} уже прошёл. Укажи другую дату."
        candidate, _p = sorted(future_candidates, key=lambda x: x[0])[0]
        return (*datetime_to_local_utc_strings(candidate), None)

    for offset in range(14):
        day = now + timedelta(days=offset)
        candidates = [(dt, p) for dt, p in periods_for_day(day) if dt > now]
        if candidates:
            candidate, _p = sorted(candidates, key=lambda x: x[0])[0]
            return (*datetime_to_local_utc_strings(candidate), None)

    return None, None, "Подходящее время не найдено. Проверь расписание в кастомизации."


def find_break_datetime(user_id: int, timezone_name: str, text: str, mode: str, break_number: int = 0) -> tuple[Optional[str], Optional[str], Optional[str]]:
    return find_school_period_datetime(user_id, timezone_name, text, mode, break_number, "break")


def local_parse_break_reminder(user_id: int, user_text: str, timezone_name: str, timezone_title: str) -> tuple[Optional[ParsedReminder], Optional[str]]:
    t = normalize_spaces((user_text or "").lower().replace("ё", "е"))
    if not has_school_period_reference(t):
        return None, None
    period_type = school_period_kind_from_text(t)
    each = bool(re.search(r"\bкажд\w*\s+(?:перемен|урок)", t))
    number = extract_lesson_number(t) if period_type == "lesson" else extract_break_number(t)
    if not each and not number:
        return None, None
    mode = "each" if each else "single"
    local_at, utc_at, err = find_school_period_datetime(user_id, timezone_name, user_text, mode, number or 0, period_type)
    if err:
        return None, err
    topic = cleanup_break_topic(user_text)
    category = classify_category(user_text)
    priority = classify_priority(user_text, category)
    if period_type == "lesson":
        reminder_kind = REMINDER_KIND_LESSON_EACH if each else REMINDER_KIND_LESSON_SINGLE
    else:
        reminder_kind = REMINDER_KIND_BREAK_EACH if each else REMINDER_KIND_BREAK_SINGLE
    return ParsedReminder(
        topic=topic,
        reminder_text=normalize_spaces(user_text),
        category=category,
        priority=priority,
        repeat_type="none",
        repeat_value="",
        next_local_at=local_at or "",
        next_utc_at=utc_at or "",
        parse_method="local",
        reminder_kind=reminder_kind,
        break_number=number or 0,
        break_mode=mode,
    ), None


def parse_mixed_break_segments(user_id: int, user_text: str, timezone_name: str, timezone_title: str, custom_times: Optional[dict[str, str]] = None) -> tuple[list[ParsedReminder], Optional[str]]:
    """
    Разбирает сложные фразы, где одно из событий связано с переменой,
    а второе обычное: "завтра на 2 перемене сдать тетради, а в 18:00 тренировка".
    """
    if not has_school_period_reference(user_text):
        return [], None
    segments = split_local_segments(user_text)
    if len(segments) <= 1:
        return [], None

    parsed: list[ParsedReminder] = []
    errors: list[str] = []
    common_date_prefix = common_date_prefix_for_segments(user_text)
    for segment in segments:
        parse_segment = segment
        if common_date_prefix and not text_has_date_hint(segment):
            parse_segment = f"{common_date_prefix} {segment}"
        if has_school_period_reference(segment):
            item, err = local_parse_break_reminder(user_id, parse_segment, timezone_name, timezone_title)
            if item:
                item.reminder_text = normalize_spaces(segment)
                parsed.append(item)
            elif err:
                errors.append(err)
        else:
            many, err = local_or_yandex_parse_many(parse_segment, timezone_name, timezone_title, custom_times)
            if many:
                for item in many:
                    item.reminder_text = normalize_spaces(segment)
                parsed.extend(many)
            elif err:
                errors.append(err)

    if parsed:
        return dedupe_parsed_reminders(parsed), None
    return [], errors[0] if errors else None

def build_customization_markup (user_id :int )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("🕓 Время дня",callback_data ="custom_nav:time"))
    markup .add (types .InlineKeyboardButton ("🏫 Перемены",callback_data ="custom_nav:breaks"))
    markup .add (types .InlineKeyboardButton ("⚡ Приоритеты",callback_data ="custom_nav:priorities"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:main"))
    return markup 


def build_priority_settings_markup (user_id :int )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("⏱ Настроить время",callback_data ="custom_priority:time_menu"))
    markup .add (types .InlineKeyboardButton ("🔢 Настроить кол-во сообщений",callback_data ="custom_priority:count_menu"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:customization"))
    return markup


def build_priority_time_settings_markup (user_id :int )->types .InlineKeyboardMarkup :
    intervals =get_user_priority_intervals (user_id )
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for title ,priority in PRIORITY_BUTTONS:
        value =format_priority_interval (intervals .get (priority ,PRIORITY_INTERVALS_SECONDS .get (priority ,300 )))
        markup .add (types .InlineKeyboardButton (f"{title} — раз в {value}",callback_data =f"custom_priority_time:set:{priority}"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="custom_nav:priorities"))
    return markup


def build_priority_count_settings_markup (user_id :int )->types .InlineKeyboardMarkup :
    counts =get_user_priority_max_counts (user_id )
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for title ,priority in PRIORITY_BUTTONS:
        count =counts .get (priority ,PRIORITY_MAX_NOTIFY_COUNT .get (priority ,10 ))
        markup .add (types .InlineKeyboardButton (f"{title} — {count} сообщ.",callback_data =f"custom_priority_count:set:{priority}"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="custom_nav:priorities"))
    return markup

def build_time_words_markup (user_id :int )->types .InlineKeyboardMarkup :
    times =get_user_time_words (user_id )
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for key in ["morning","day","evening","night"]:
        markup .add (types .InlineKeyboardButton (f"{TIME_WORD_TITLES [key ]} — {times [key ]}",callback_data =f"custom_time:set:{key }"))
    markup .row (types .InlineKeyboardButton ("🔄 Сбросить",callback_data ="custom_time:reset"),types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:customization"))
    return markup 


def build_break_days_markup (user_id:int)->types.InlineKeyboardMarkup:
    chosen=selected_break_days(user_id)
    markup=types.InlineKeyboardMarkup(row_width=4)
    buttons=[]
    for i in range(7):
        label = f"✅ {WEEKDAY_SHORT[i]}" if i in chosen else WEEKDAY_SHORT[i]
        buttons.append(types.InlineKeyboardButton(label,callback_data=f"breaks:toggle:{i}"))
    markup.add(*buttons[:4]); markup.add(*buttons[4:])
    markup.add(types.InlineKeyboardButton("🕘 Настроить время перемен",callback_data="breaks:configure"))
    markup.add(types.InlineKeyboardButton("↩️ Назад",callback_data="nav:customization"))
    return markup


def build_break_times_markup(user_id:int)->types.InlineKeyboardMarkup:
    markup=types.InlineKeyboardMarkup(row_width=2)
    markup.add(types.InlineKeyboardButton("➕ Добавить",callback_data="breaks:add"),types.InlineKeyboardButton("🗑 Удалить",callback_data="breaks:delete"))
    markup.add(types.InlineKeyboardButton("↩️ Назад",callback_data="custom_nav:breaks"))
    return markup



def build_custom_reset_confirm_markup() -> types.InlineKeyboardMarkup:
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(
        types.InlineKeyboardButton("✅ Да, сбросить", callback_data="custom_time:reset:yes"),
        types.InlineKeyboardButton("↩️ Нет", callback_data="custom_time:reset:no"),
    )
    return markup

def build_clear_confirm_markup ()->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (
    types .InlineKeyboardButton ("🗑 Да, очистить",callback_data ="clear:yes"),
    types .InlineKeyboardButton ("↩️ Нет",callback_data ="clear:no"),
    )
    return markup 



def build_due_close_markup (reminder_id :int )->types .InlineKeyboardMarkup :
    # Оставлено только для обратной совместимости со старыми сообщениями.
    # Новые уведомления больше не используют кнопку закрытия без результата.
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("Закрыть",callback_data =f"close_no_response:{reminder_id }"))
    return markup 


def build_due_actions_markup (reminder_id :int ,row: Optional[sqlite3.Row]=None)->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("✅ Выполнено",callback_data =f"result:done:{reminder_id }"))
    markup .add (types .InlineKeyboardButton ("❌ Не выполнено",callback_data =f"result:not_done:{reminder_id }"))
    markup .add (types .InlineKeyboardButton ("⏰ Перенести",callback_data =f"snooze_custom:{reminder_id }"))
    if row is not None and is_interval_kind_value(reminder_kind_from_row(row)):
        markup .add (types .InlineKeyboardButton ("⛔ Завершить серию",callback_data =f"interval_finish_due:{reminder_id }"))
    return markup 


def build_snooze_prompt_markup (reminder_id :int )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("❌ Отмена переноса",callback_data =f"snooze_cancel:{reminder_id }"))
    return markup


def render_due_notification_text (row :sqlite3 .Row ,attempt_number :Optional [int ]=None )->str :
    max_count =interval_max_count_for_row (row)
    if attempt_number is None:
        try :
            attempt_number =int (row ["notify_count"]or 1 )
        except Exception :
            attempt_number =1
    if attempt_number <1 :
        attempt_number =1
    if attempt_number >=max_count :
        message_footer =(
        f"Сообщение {attempt_number } из {max_count }\n"
        "Автоматические повторы завершены. Выбери действие ниже, когда увидишь напоминание."
        )
    else :
        message_footer =f"Сообщение {attempt_number } из {max_count }"
    timer_line =render_time_until_line (row ['next_local_at'],row ['timezone_name'],row ['priority'])
    kind =reminder_kind_from_row (row )
    lines =[
        "🔔 <b>Напоминание ждёт подтверждения</b>",
        "",
        f"<b>Тема:</b> {escape_html (row ['topic'])}",
        f"<b>Время:</b> {escape_html (format_human_datetime (row ['next_local_at'],row ['timezone_name']))}",
    ]
    if timer_line:
        lines .append (timer_line )
    lines .append (f"<b>Часовой пояс:</b> {escape_html (row ['timezone_title'])}")
    lines .append (f"<b>Приоритет:</b> {escape_html (PRIORITY_TITLES .get (row ['priority'],'🟡 Обычно'))}")
    lines .append (f"<b>Категория:</b> {escape_html (CATEGORY_TITLES .get (row ['category'],'📌 Другое'))}")
    if kind ==REMINDER_KIND_INTERVAL:
        lines .append (f"<b>Тип:</b> интервальное")
        lines .append (f"<b>Интервал:</b> {escape_html (interval_title_from_minutes (int (row ['interval_minutes']or 0 )))}")
        lines .extend (interval_period_lines_from_data (row))
        if row ['repeat_type']!='none':
            lines .append (f"<b>Повтор:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}")
    elif kind in {REMINDER_KIND_BREAK_SINGLE,REMINDER_KIND_BREAK_EACH,REMINDER_KIND_LESSON_SINGLE,REMINDER_KIND_LESSON_EACH}:
        lines .append (f"<b>Тип:</b> {escape_html (reminder_kind_title (row ))}")
        if kind ==REMINDER_KIND_BREAK_SINGLE and int (row ['break_number']or 0 )>0:
            lines .append (f"<b>Перемена:</b> {int (row ['break_number']or 0 )}-я")
        if kind ==REMINDER_KIND_LESSON_SINGLE and int (row ['break_number']or 0 )>0:
            lines .append (f"<b>Урок:</b> {int (row ['break_number']or 0 )}-й")
    elif row ['repeat_type']!='none':
        lines .append (f"<b>Повтор:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}")
    lines .append (f"<b>Текст:</b> {escape_html (row ['reminder_text'])}")
    lines .append ("")
    lines .append (message_footer )
    return "\n".join (lines )


def render_snooze_prompt_text (row :sqlite3 .Row )->str :
    return (
    "<b>⏰ Перенос напоминания</b>\n\n"
    f"<b>Тема:</b> {escape_html (row ['topic'])}\n\n"
    "Напиши текстом, на сколько или на когда перенести.\n\n"
    "Примеры:\n"
    "• <code>30 минут</code>\n"
    "• <code>на 2 часа</code>\n"
    "• <code>на час</code>\n"
    "• <code>на полчаса</code>\n"
    "• <code>завтра в 9</code>\n"
    "• <code>завтра утром</code>\n"
    "• <code>в понедельник в 8:30</code>\n\n"
    "Для отмены напиши: <b>Отмена</b>"
    )



def build_draft_preview_markup (session_id :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("✅ Подтвердить",callback_data =f"draft_confirm:{session_id }"))
    s =SESSIONS .get (session_id )
    data =s .get ("data",{}) if isinstance (s ,dict ) else {}
    if data .get ("parse_method")=="local" and not data .get ("yandex_reparse_used"):
        markup .add (types .InlineKeyboardButton ("🤖 Разбор не подходит",callback_data =f"draft_yandex_reparse:{session_id }"))
    markup .add (types .InlineKeyboardButton ("✏️ Изменить",callback_data =f"draft_edit:{session_id }"))
    markup .add (types .InlineKeyboardButton ("❌ Отмена",callback_data =f"draft_back_cancel:{session_id }"))
    return markup 


def build_edit_menu_markup (session_id :str ,mode :str )->types .InlineKeyboardMarkup :
    if mode =="draft":
        confirm_callback =f"draft_confirm:{session_id }"
        reset_callback =f"draft_reset:{session_id }"
        back_callback =f"draft_back:{session_id }"
    elif mode =="bulk_item":
        confirm_callback =f"bulk_item_confirm:{session_id }"
        reset_callback =f"bulk_item_reset:{session_id }"
        back_callback =f"bulk_item_back:{session_id }"
    else :
        confirm_callback =f"saved_confirm:{session_id }"
        reset_callback =f"saved_reset:{session_id }"
        back_callback =f"saved_back:{session_id }"

    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (types .InlineKeyboardButton ("✅ Подтвердить",callback_data =confirm_callback ))
    markup .add (
    types .InlineKeyboardButton ("📝 Тема",callback_data =f"edit_field:topic:{session_id }"),
    types .InlineKeyboardButton ("🕒 Дата и время",callback_data =f"edit_field:time:{session_id }"),
    )
    markup .add (
    types .InlineKeyboardButton ("⚡ Приоритет",callback_data =f"edit_field:priority:{session_id }"),
    types .InlineKeyboardButton ("📂 Категория",callback_data =f"edit_field:category:{session_id }"),
    )
    markup .add (
    types .InlineKeyboardButton ("✏️ Текст",callback_data =f"edit_field:text:{session_id }"),
    types .InlineKeyboardButton ("🔁 Повтор",callback_data =f"edit_field:repeat:{session_id }"),
    )
    s = SESSIONS.get(session_id, {})
    d = s.get("data", {}) if isinstance(s, dict) else {}
    if d.get("reminder_kind") == REMINDER_KIND_INTERVAL:
        markup .add (types .InlineKeyboardButton ("🔁 Интервал",callback_data =f"edit_field:interval:{session_id }"),types .InlineKeyboardButton ("⏱ Период",callback_data =f"edit_field:period:{session_id }"))
    if d.get("reminder_kind") in {REMINDER_KIND_BREAK_SINGLE, REMINDER_KIND_BREAK_EACH}:
        markup .add (types .InlineKeyboardButton ("🔔 Перемена/урок",callback_data =f"edit_field:break:{session_id }"))
    markup .add (
    types .InlineKeyboardButton ("↩️ Сбросить изменения",callback_data =reset_callback ),
    types .InlineKeyboardButton ("⬅️ Назад",callback_data =back_callback ),
    )
    return markup 


def build_edit_input_cancel_markup(session_id: str) -> types.InlineKeyboardMarkup:
    markup = types.InlineKeyboardMarkup(row_width=1)
    markup.add(types.InlineKeyboardButton("↩️ Назад", callback_data=f"edit_menu_back:{session_id}"))
    return markup


def build_priority_markup (session_id :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for title ,value in PRIORITY_BUTTONS :
        markup .add (types .InlineKeyboardButton (title ,callback_data =f"set_priority:{value }:{session_id }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"edit_menu_back:{session_id }"))
    return markup 


def build_category_markup (session_id :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for title ,value in CATEGORY_BUTTONS :
        markup .add (types .InlineKeyboardButton (title ,callback_data =f"set_category:{value }:{session_id }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"edit_menu_back:{session_id }"))
    return markup 


def build_repeat_markup (session_id :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for label ,value in REPEAT_OPTIONS :
        markup .add (types .InlineKeyboardButton (label ,callback_data =f"set_repeat:{value }:{session_id }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"edit_menu_back:{session_id }"))
    return markup 


def build_custom_weekdays_markup (session_id :str ,current_value :str )->types .InlineKeyboardMarkup :
    chosen =set ()
    for x in current_value .split (","):
        x =x .strip ()
        if x .isdigit ():
            chosen .add (int (x ))

    markup =types .InlineKeyboardMarkup (row_width =4 )
    buttons =[]
    for i in range (7 ):
        label =WEEKDAY_SHORT [i ]
        if i in chosen :
            label =f"✅ {label }"
        buttons .append (types .InlineKeyboardButton (label ,callback_data =f"toggle_weekday:{i }:{session_id }"))
    markup .add (*buttons [:4 ])
    markup .add (*buttons [4 :])
    markup .add (types .InlineKeyboardButton ("Готово",callback_data =f"finish_weekdays:{session_id }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"edit_menu_back:{session_id }"))
    return markup 


def build_delete_confirm_markup (reminder_id :int ,list_type :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (
    types .InlineKeyboardButton ("🗑 Удалить",callback_data =f"delete_confirm:{reminder_id }:{list_type }"),
    types .InlineKeyboardButton ("↩️ Назад",callback_data =f"nav:{'today'if list_type =='today'else 'list'}"),
    )
    return markup 



def render_reminder_full_card (row :sqlite3 .Row )->str :
    kind =reminder_kind_from_row (row )
    timer_line =render_time_until_line (row ['next_local_at'],row ['timezone_name'],row ['priority'])
    lines =[
        f"<b>{escape_html (row ['topic'])}</b>",
        "",
        f"<b>Текст:</b> {escape_html (row ['reminder_text'])}",
        f"<b>Когда:</b> {escape_html (format_human_datetime (row ['next_local_at'],row ['timezone_name']))}",
    ]
    if kind ==REMINDER_KIND_INTERVAL:
        lines .append (f"<b>Тип:</b> интервальное напоминание")
        lines .append (f"<b>Интервал:</b> {escape_html (interval_title_from_minutes (int (row ['interval_minutes']or 0 )))}")
        lines .extend (interval_period_lines_from_data (row))
        if row ['repeat_type']!='none':
            lines .append (f"<b>Дни:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}")
        lines .append (f"<b>Срабатываний:</b> {int (row ['interval_occurrence_count']or 0 )}")
    elif kind in {REMINDER_KIND_BREAK_SINGLE,REMINDER_KIND_BREAK_EACH,REMINDER_KIND_LESSON_SINGLE,REMINDER_KIND_LESSON_EACH}:
        lines .append (f"<b>Тип:</b> {escape_html (reminder_kind_title (row ))}")
        if kind ==REMINDER_KIND_BREAK_SINGLE and int (row ['break_number']or 0 )>0:
            lines .append (f"<b>Перемена:</b> {int (row ['break_number']or 0 )}-я")
        if kind ==REMINDER_KIND_LESSON_SINGLE and int (row ['break_number']or 0 )>0:
            lines .append (f"<b>Урок:</b> {int (row ['break_number']or 0 )}-й")
        if row ['repeat_type']!='none':
            lines .append (f"<b>Повтор:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}")
    else:
        if row ['repeat_type']!='none':
            lines .append (f"<b>Повтор:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}")
    if timer_line:
        lines .append (timer_line)
    lines .append (f"<b>Приоритет:</b> {escape_html (PRIORITY_TITLES .get (row ['priority'],'🟡 Обычно'))}")
    lines .append (f"<b>Категория:</b> {escape_html (CATEGORY_TITLES .get (row ['category'],'📌 Другое'))}")
    return "\n".join (lines )


def build_view_reminder_markup (reminder_id :int ,list_type :str ,row: Optional[sqlite3.Row]=None )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (
    types .InlineKeyboardButton ("✏️ Изменить",callback_data =f"view_edit:{reminder_id }:{list_type }"),
    types .InlineKeyboardButton ("🗑 Удалить",callback_data =f"view_delete:{reminder_id }:{list_type }"),
    )
    if row is not None and is_interval_kind_value(reminder_kind_from_row(row)):
        markup .add (types .InlineKeyboardButton ("⛔ Завершить серию",callback_data =f"interval_finish:{reminder_id}:{list_type}"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад к списку",callback_data =f"nav:{'today'if list_type =='today'else 'list'}"))
    return markup 

def build_select_reminder_markup (user_id :int ,mode :str ,list_type :str )->types .InlineKeyboardMarkup :
    rows =get_all_active_reminders (user_id )
    timezone_name ,_ =get_user_timezone (user_id )
    if list_type =="today":
        today =datetime .now (ZoneInfo (timezone_name )).date ()
        rows =[r for r in rows if datetime .strptime (r ["next_local_at"],"%Y-%m-%d %H:%M").date ()==today ]

    markup =types .InlineKeyboardMarkup (row_width =1 )
    for row in rows [:50 ]:
        label =f"{row ['topic']} — {row ['next_local_at'][5 :16 ]}"
        if len (label )>60 :
            label =label [:57 ]+"..."
        markup .add (types .InlineKeyboardButton (label ,callback_data =f"select_reminder:{mode }:{row ['id']}:{list_type }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"nav:{'today'if list_type =='today'else 'list'}"))
    return markup 


    # =========================================================
    # Экраны
    # =========================================================



def _data_value(data, key: str, default=""):
    try:
        return data.get(key, default) if isinstance(data, dict) else data[key]
    except Exception:
        return default


def format_duration_minutes_human(minutes: int) -> str:
    try:
        minutes = int(minutes or 0)
    except Exception:
        minutes = 0
    if minutes <= 0:
        return "не задано"
    if minutes % INTERVAL_WEEK_MINUTES == 0:
        return f"{minutes // INTERVAL_WEEK_MINUTES} нед."
    if minutes % INTERVAL_DAY_MINUTES == 0:
        return f"{minutes // INTERVAL_DAY_MINUTES} дн."
    if minutes % 60 == 0:
        return f"{minutes // 60} ч."
    return f"{minutes} мин."


def interval_period_lines_from_data(data) -> list[str]:
    timezone_name = str(_data_value(data, "timezone_name", DEFAULT_TIMEZONE_NAME) or DEFAULT_TIMEZONE_NAME)
    start_time = str(_data_value(data, "window_start_time", "") or "")
    end_time = str(_data_value(data, "window_end_time", "") or "")
    window_days = str(_data_value(data, "window_days", "") or "")
    next_local_at = str(_data_value(data, "next_local_at", "") or "")
    interval_minutes = int(_data_value(data, "interval_minutes", 0) or 0)
    duration_minutes = duration_from_window_days(window_days)
    lines: list[str] = []
    if duration_minutes:
        start_dt = interval_start_from_window_days(window_days, timezone_name)
        if not start_dt and next_local_at:
            try:
                start_dt = datetime.strptime(next_local_at, "%Y-%m-%d %H:%M").replace(tzinfo=ZoneInfo(timezone_name))
            except Exception:
                start_dt = None
        if start_dt:
            end_dt = start_dt + timedelta(minutes=duration_minutes)
            lines.append(f"<b>От:</b> {escape_html(format_human_datetime(start_dt.strftime('%Y-%m-%d %H:%M'), timezone_name))}")
            lines.append(f"<b>До:</b> {escape_html(format_human_datetime(end_dt.strftime('%Y-%m-%d %H:%M'), timezone_name))}")
        lines.append(f"<b>Длительность серии:</b> {escape_html(format_duration_minutes_human(duration_minutes))}")
    elif is_long_interval_minutes(interval_minutes):
        lines.append(f"<b>Время срабатывания:</b> {escape_html(start_time or end_time or 'утро')}")
    else:
        lines.append(f"<b>От:</b> {escape_html(start_time or 'утро')}")
        lines.append(f"<b>До:</b> {escape_html(end_time or 'вечер')}")
    return lines


def school_period_kind_from_text(text: str) -> str:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if re.search(r"\bурок", t):
        return "lesson"
    return "break"


def has_lesson_reference(text: str) -> bool:
    return has_lesson_period_reference(text)


def extract_lesson_number(text: str) -> Optional[int]:
    t = normalize_spaces((text or "").lower().replace("ё", "е"))
    if "урок" not in t:
        return None
    numeric_patterns = [
        r"\b(?:на|к|ко|во|в|перед|до|после)\s+(\d{1,2})\s*(?:[-–]?\s*(?:й|м|ом|ый|ой|ого|ему|е|а|у))?\s+урок",
        r"\b(\d{1,2})\s*(?:[-–]?\s*(?:й|м|ом|ый|ой|ого|ему|е))?\s+урок",
    ]
    for pattern in numeric_patterns:
        m = re.search(pattern, t)
        if m:
            value = int(m.group(1))
            if 1 <= value <= 20:
                return value
    word_patterns = [
        (1, r"перв\w*"), (2, r"втор\w*"), (3, r"трет\w*"), (4, r"четверт\w*"),
        (5, r"пят\w*"), (6, r"шест\w*"), (7, r"седьм\w*"), (8, r"восьм\w*"),
        (9, r"девят\w*"), (10, r"десят\w*"), (11, r"одиннадцат\w*"), (12, r"двенадцат\w*"),
    ]
    for value, pattern in word_patterns:
        if re.search(rf"\b(?:на|к|ко|во|в|перед|до|после)?\s*{pattern}\s+урок", t):
            return value
    return None


def get_school_lessons(user_id: int, weekday: int) -> list[dict]:
    breaks = get_school_breaks(user_id, weekday)
    lessons: list[dict] = []
    current_start = DEFAULT_FIRST_LESSON_START
    for b in breaks:
        try:
            idx = int(b["break_index"] or 0)
        except Exception:
            idx = len(lessons) + 1
        lessons.append({"period_index": idx, "start_time": current_start, "end_time": str(b["start_time"] or "")})
        current_start = str(b["end_time"] or current_start)
    return [x for x in lessons if x.get("start_time") and x.get("end_time") and x["end_time"] > x["start_time"]]


def school_periods_for_day(user_id: int, weekday: int, period_type: str) -> list[dict]:
    if period_type == "lesson":
        return get_school_lessons(user_id, weekday)
    return [{"period_index": int(b["break_index"] or 0), "start_time": str(b["start_time"] or ""), "end_time": str(b["end_time"] or "")} for b in get_school_breaks(user_id, weekday)]


def find_school_period_end(row) -> Optional[datetime]:
    kind = reminder_kind_from_row(row)
    if kind not in {REMINDER_KIND_BREAK_SINGLE, REMINDER_KIND_BREAK_EACH, REMINDER_KIND_LESSON_SINGLE, REMINDER_KIND_LESSON_EACH}:
        return None
    period_type = "lesson" if kind in {REMINDER_KIND_LESSON_SINGLE, REMINDER_KIND_LESSON_EACH} else "break"
    try:
        tz = ZoneInfo(row["timezone_name"])
        trigger_local = row["active_trigger_local_at"] or row["next_local_at"]
        trigger = datetime.strptime(trigger_local, "%Y-%m-%d %H:%M").replace(tzinfo=tz)
        number = int(row["break_number"] or 0) if kind in {REMINDER_KIND_BREAK_SINGLE, REMINDER_KIND_LESSON_SINGLE} else 0
    except Exception:
        return None
    for period in school_periods_for_day(int(row["user_id"]), trigger.weekday(), period_type):
        if number and int(period["period_index"] or 0) != number:
            continue
        start_dt = set_time_on_date(trigger.date(), period["start_time"], tz)
        end_dt = set_time_on_date(trigger.date(), period["end_time"], tz)
        if start_dt <= trigger <= end_dt or abs((start_dt - trigger).total_seconds()) < 60:
            return end_dt
    return None


def should_stop_due_repeats_by_school_period(row) -> bool:
    end_dt = find_school_period_end(row)
    if not end_dt:
        return False
    return datetime.now(end_dt.tzinfo).replace(second=0, microsecond=0) >= end_dt

def render_session_text (data :dict ,title :str )->str :
    timer_line =render_time_until_line (data ['next_local_at'],data ['timezone_name'],data ['priority'])
    parse_line =""
    if data .get ("parse_method"):
        parse_line =f"<b>Обработка:</b> {escape_html (parse_method_title (str (data .get ('parse_method',''))))}"
    kind =str (data .get ("reminder_kind","normal") or "normal")
    lines =[
        f"<b>{escape_html (title )}</b>",
        "",
        f"<b>Тема:</b> {escape_html (data ['topic'])}",
        f"<b>Время:</b> {escape_html (format_human_datetime (data ['next_local_at'],data ['timezone_name']))}",
    ]
    if timer_line:
        lines .append (timer_line )
    lines .append (f"<b>Часовой пояс:</b> {escape_html (data ['timezone_title'])}")
    lines .append (f"<b>Приоритет:</b> {escape_html (PRIORITY_TITLES [data ['priority']])}")
    lines .append (f"<b>Категория:</b> {escape_html (CATEGORY_TITLES [data ['category']])}")
    if kind ==REMINDER_KIND_INTERVAL:
        lines .append ("<b>Тип:</b> интервальное напоминание")
        lines .append (f"<b>Интервал:</b> {escape_html (interval_title_from_minutes (int (data .get ('interval_minutes',0 )or 0 )))}")
        lines .extend (interval_period_lines_from_data (data))
        if data .get ('repeat_type','none')!='none':
            lines .append (f"<b>Повтор:</b> {escape_html (repeat_title (data ['repeat_type'],data ['repeat_value']))}")
    elif kind in {REMINDER_KIND_BREAK_SINGLE,REMINDER_KIND_BREAK_EACH,REMINDER_KIND_LESSON_SINGLE,REMINDER_KIND_LESSON_EACH}:
        lines .append (f"<b>Тип:</b> {escape_html (reminder_kind_title (data ))}")
        if kind ==REMINDER_KIND_BREAK_SINGLE and int (data .get ('break_number',0 )or 0 )>0:
            lines .append (f"<b>Перемена:</b> {int (data .get ('break_number',0 )or 0 )}-я")
        if kind ==REMINDER_KIND_LESSON_SINGLE and int (data .get ('break_number',0 )or 0 )>0:
            lines .append (f"<b>Урок:</b> {int (data .get ('break_number',0 )or 0 )}-й")
    elif data .get ('repeat_type','none')!='none':
        lines .append (f"<b>Повтор:</b> {escape_html (repeat_title (data ['repeat_type'],data ['repeat_value']))}")
    if parse_line:
        lines .append (parse_line )
    lines .append (f"<b>Текст:</b> {escape_html (data ['reminder_text'])}")
    return "\n".join (lines )


def show_main_screen (user_id :int ,chat_id :int )->None :
    timezone_name ,timezone_title =get_user_timezone (user_id )
    text =(
    "<b>Умный бот-напоминалка</b>\n\n"
    "Отправь текст или голосовое сообщение, чтобы создать напоминание.\n\n"
    "Примеры:\n"
    "• завтра в 18:30 позвонить клиенту\n"
    "• через 2 часа проверить задачу\n"
    "• каждый понедельник в 8:00 расписание\n"
    "• по будням в 7:30 витамины\n\n"
    f"Текущий часовой пояс: <b>{escape_html (timezone_title )}</b>."
    )
    show_screen (user_id ,chat_id ,text ,build_main_nav_markup ())



def show_customization_screen(user_id: int, chat_id: int) -> None:
    text = (
        "<b>🎨 Кастомизация</b>\n\n"
        "Здесь можно настроить время дня, школьные перемены и частоту повторов по приоритетам.\n\n"
        "Выбери нужный раздел кнопкой ниже."
    )
    show_screen(user_id, chat_id, text, build_customization_markup(user_id))


def show_priority_settings_screen(user_id: int, chat_id: int) -> None:
    show_screen(user_id, chat_id, "<b>⚡ Приоритеты</b>\n\nНастрой частоту повторов и количество сообщений для каждого приоритета.", build_priority_settings_markup(user_id))


def show_priority_time_settings_screen(user_id: int, chat_id: int) -> None:
    show_screen(user_id, chat_id, "<b>⏱ Время повторов</b>\n\nВыбери приоритет. Актуальная частота показана на кнопках.", build_priority_time_settings_markup(user_id))


def show_priority_count_settings_screen(user_id: int, chat_id: int) -> None:
    show_screen(user_id, chat_id, "<b>🔢 Количество сообщений</b>\n\nВыбери приоритет. Актуальное количество показано на кнопках.", build_priority_count_settings_markup(user_id))


def show_priority_interval_prompt(user_id: int, chat_id: int, priority: str) -> None:
    title = PRIORITY_TITLES.get(priority, "🟡 Обычно")
    show_screen(
        user_id,
        chat_id,
        f"<b>{escape_html(title)}</b>\n\n"
        "Выбери, раз в какой промежуток времени будет повторяться уведомление.\n\n"
        "Минимум: <b>5 секунд</b>\n"
        "Максимум: <b>30 минут</b>\n\n"
        "Напиши, например: <code>5 минут</code> или <code>10 секунд</code>.\n"
        "Для отмены напиши <b>Отмена</b> или нажми «Назад».",
        build_priority_time_settings_markup(user_id),
    )


def show_priority_count_prompt(user_id: int, chat_id: int, priority: str) -> None:
    title = PRIORITY_TITLES.get(priority, "🟡 Обычно")
    show_screen(
        user_id,
        chat_id,
        f"<b>{escape_html(title)}</b>\n\n"
        "Выбери, сколько раз бот будет повторять уведомление, если пользователь не нажал действие.\n\n"
        "Минимум: <b>1 сообщение</b>\n"
        "Максимум: <b>30 сообщений</b>\n\n"
        "Напиши число, например: <code>5</code> или <code>10</code>.\n"
        "Для отмены напиши <b>Отмена</b> или нажми «Назад».",
        build_priority_count_settings_markup(user_id),
    )


def show_time_words_screen(user_id:int, chat_id:int)->None:
    times=get_user_time_words(user_id)
    text=(
        "<b>🕓 Время дня</b>\n\n"
        "Настрой, какое время бот будет подставлять вместо слов «утро», «день», «вечер» и «ночь».\n\n"
        f"🌅 <b>Утро:</b> {escape_html(times['morning'])}\n"
        f"☀️ <b>День:</b> {escape_html(times['day'])}\n"
        f"🌆 <b>Вечер:</b> {escape_html(times['evening'])}\n"
        f"🌙 <b>Ночь:</b> {escape_html(times['night'])}\n\n"
        "Нажми на нужную кнопку и отправь новое время текстом."
    )
    show_screen(user_id, chat_id, text, build_time_words_markup(user_id))


def show_breaks_days_screen(user_id:int, chat_id:int)->None:
    configured=count_configured_break_days(user_id)
    text=(
        "<b>🔔 Перемены</b>\n\n"
        "Выбери дни недели, для которых нужно настроить перемены. Можно выбрать сразу несколько дней.\n\n"
        f"Дней с настроенными переменами: <b>{configured}</b>.\n"
        "После выбора дней нажми «Настроить время перемен»."
    )
    show_screen(user_id, chat_id, text, build_break_days_markup(user_id))


def format_breaks_for_days(user_id:int, weekdays:set[int])->str:
    if not weekdays:
        return "Сначала выбери хотя бы один день."
    parts=[]
    for day in sorted(weekdays):
        parts.append(f"<b>{WEEKDAYS[day].capitalize()}</b>")
        rows=get_school_breaks(user_id, day)
        if not rows:
            parts.append("Перемены пока не настроены.")
        else:
            for r in rows:
                parts.append(f"{int(r['break_index'])}. {escape_html(r['start_time'])}-{escape_html(r['end_time'])}")
        parts.append("")
    return "\n".join(parts).strip()


def show_break_times_screen(user_id:int, chat_id:int)->None:
    chosen=selected_break_days(user_id)
    text=(
        "<b>🕘 Время перемен</b>\n\n"
        f"Выбранные дни: <b>{escape_html(', '.join(WEEKDAYS[d] for d in sorted(chosen)) if chosen else 'не выбраны')}</b>\n\n"
        f"{format_breaks_for_days(user_id, chosen)}"
    )
    show_screen(user_id, chat_id, text, build_break_times_markup(user_id))

def show_help_screen (user_id :int ,chat_id :int )->None :
    times =get_user_time_words (user_id )
    intervals =get_user_priority_intervals (user_id )
    counts =get_user_priority_max_counts (user_id )
    priority_lines =[]
    for title ,priority in PRIORITY_BUTTONS:
        priority_lines .append (f"{title}: раз в {format_priority_interval (intervals .get (priority ,PRIORITY_INTERVALS_SECONDS .get (priority ,300 )))}; сообщений: {counts .get (priority ,PRIORITY_MAX_NOTIFY_COUNT .get (priority ,10 ))}")
    text =(
    "<b>Помощь по боту</b>\n\n"
    "<b>Создание</b>\n"
    "Напиши текстом или голосом: бот покажет черновик с темой, временем, категорией и приоритетом. Если разбор не подошёл, нажми «Разбор не подходит» или измени поля вручную.\n\n"
    "<b>Что понимает бот</b>\n"
    "• обычные напоминания: <code>завтра в 18:30 позвонить</code>\n"
    "• повторы: <code>каждый понедельник в 8:00 расписание</code>\n"
    "• интервалы: <code>каждые 2 часа с 9 до 18 пить воду</code>\n"
    "• серии: <code>каждые 2 часа в течение 5 дней пить воду</code>\n"
    "• перемены и уроки: <code>завтра на 2 перемене сдать тетради</code>, <code>на 3 уроке повторить правило</code>\n"
    "• сложные фразы: бот старается разделить их на несколько черновиков.\n\n"
    "<b>Интервалы</b>\n"
    "Интервал — это «каждые N секунд/минут/часов/дней». Для коротких интервалов можно указать период: <code>с 9 до 18</code>, <code>до вечера</code>, <code>в течение 6 часов</code>. Для серии можно указать длительность: <code>в течение 5 дней</code>.\n\n"
    "<b>Перемены и уроки</b>\n"
    "Перемены настраиваются в кастомизации. Уроки считаются автоматически: 1 урок начинается в 08:30, дальше начало и конец уроков берутся по расписанию перемен.\n\n"
    "<b>Кастомизация</b>\n"
    f"Время дня: утро {escape_html (times ['morning'])}, день {escape_html (times ['day'])}, вечер {escape_html (times ['evening'])}, ночь {escape_html (times ['night'])}.\n"
    "Приоритеты сейчас:\n"
    +"\n".join (escape_html (line) for line in priority_lines)
    +"\n\n<b>Уведомления</b>\n"
    "Если напоминание пришло на перемене или уроке, бот повторяет его только до конца этой перемены или урока, потом ждёт твоего ответа."
    )
    show_screen (user_id ,chat_id ,text ,build_main_nav_markup ())


def show_timezone_screen (user_id :int ,chat_id :int )->None :
    show_screen (user_id ,chat_id ,"Выбери часовой пояс.",build_timezone_markup ())


def show_stats_screen (user_id :int ,chat_id :int )->None :
    rows =get_all_active_reminders (user_id )
    category_counts =Counter (r ["category"]for r in rows )
    history_rows =get_recent_history (user_id ,7 )
    result_counts =Counter (r ["result_status"]for r in history_rows if r ["result_status"] in {"done","not_done","snoozed","deleted"})

    parts =["<b>Статистика</b>"]
    active_intervals =sum (1 for r in rows if reminder_kind_from_row (r)==REMINDER_KIND_INTERVAL)
    active_interval_duration =sum (1 for r in rows if reminder_kind_from_row (r)==REMINDER_KIND_INTERVAL and duration_from_window_days(r["window_days"] if "window_days" in r.keys() else "")>0)
    active_breaks =sum (1 for r in rows if reminder_kind_from_row (r) in {REMINDER_KIND_BREAK_SINGLE,REMINDER_KIND_BREAK_EACH})
    active_lessons =sum (1 for r in rows if reminder_kind_from_row (r) in {REMINDER_KIND_LESSON_SINGLE,REMINDER_KIND_LESSON_EACH})
    parts .append (f"Активных напоминаний: {len (rows )}")
    parts .append (f"Интервальных: {active_intervals }")
    parts .append (f"Интервальных с длительностью серии: {active_interval_duration }")
    parts .append (f"По переменам: {active_breaks }\n")
    parts .append ("<b>Активные по категориям:</b>")
    for key ,title in CATEGORY_TITLES .items ():
        parts .append (f"{title }: {category_counts .get (key ,0 )}")

    total =result_counts .get ("done",0 )+result_counts .get ("not_done",0 )
    parts .append ("\n<b>Итоги за последние 7 дней:</b>")
    if total ==0 and result_counts .get ("snoozed",0 )==0:
        parts .append ("Пока нет завершённых срабатываний.")
    else :
        for key in ["done","not_done","snoozed","deleted"]:
            value =result_counts .get (key ,0 )
            if value >0 :
                percent =round ((value /max (total ,1 ))*100 ) if key in {"done","not_done"} else "—"
                suffix =f" ({percent}%)" if isinstance (percent ,int ) else ""
                parts .append (f"{RESULT_TITLES [key ]}: {value }{suffix}")

    parts .append ("\n<b>Последние события:</b>")
    filtered_history =[row for row in history_rows if row ["result_status"] in {"done","not_done","snoozed","deleted"}]
    if not filtered_history :
        parts .append ("Пока нет записей.")
    else :
        for i ,row in enumerate (filtered_history [:10 ],start =1 ):
            title =RESULT_TITLES .get (row ["result_status"],row ["result_status"])
            parts .append (f"{i }. {escape_html (row ['topic'])} — {escape_html (title )} ({escape_html (row ['trigger_local_at'][5 :16 ])})")

    markup =types .InlineKeyboardMarkup ()
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:main"))
    show_screen (user_id ,chat_id ,"\n".join (parts ),markup )



def show_list_screen (user_id :int ,chat_id :int ,today_only :bool =False )->None :
    timezone_name ,timezone_title =get_user_timezone (user_id )
    rows =get_all_active_reminders (user_id )
    if today_only :
        today =datetime .now (ZoneInfo (timezone_name )).date ()
        rows =[r for r in rows if datetime .strptime (r ["next_local_at"],"%Y-%m-%d %H:%M").date ()==today ]

    if not rows :
        markup =types .InlineKeyboardMarkup ()
        markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:main"))
        show_screen (user_id ,chat_id ,"Напоминаний нет.",markup )
        return 

    groups =defaultdict (list )
    for row in rows :
        groups [format_group_title (row ["next_local_at"],row ["timezone_name"])].append (row )

    title ="<b>Напоминания на сегодня</b>"if today_only else "<b>Все напоминания</b>"
    parts =[title ,f"Часовой пояс: {escape_html (timezone_title )}\n"]
    for group_title ,group_rows in groups .items ():
        parts .append (f"<b>{escape_html (group_title )}</b>")
        for row in group_rows [:20 ]:
            timer_line =""
            if should_show_time_until (row ['priority']):
                timer_line =f"\n  До события: {escape_html (format_time_until (row ['next_local_at'],row ['timezone_name']))}"
            kind =reminder_kind_from_row (row )
            if kind ==REMINDER_KIND_INTERVAL:
                if is_long_interval_minutes(int(row ['interval_minutes']or 0)):
                    detail =f"{row ['next_local_at'][11 :16 ]} • {interval_title_from_minutes (int (row ['interval_minutes']or 0 ))}"
                else:
                    detail =f"{row ['next_local_at'][11 :16 ]} • {interval_title_from_minutes (int (row ['interval_minutes']or 0 ))} • до {row ['window_end_time'] or 'вечера'}"
                if row ['repeat_type']!='none':
                    detail +=f" • {repeat_title (row ['repeat_type'],row ['repeat_value'])}"
            elif kind in {REMINDER_KIND_BREAK_SINGLE,REMINDER_KIND_BREAK_EACH}:
                detail =f"{row ['next_local_at'][11 :16 ]} • {reminder_kind_title (row )}"
            elif row ['repeat_type']!='none':
                detail =f"{row ['next_local_at'][11 :16 ]} • {repeat_title (row ['repeat_type'],row ['repeat_value'])}"
            else:
                detail =f"{row ['next_local_at'][11 :16 ]}"
            parts .append (
            f"• <b>{escape_html (row ['topic'])}</b>\n"
            f"  {escape_html (detail)}"
            f"{timer_line}"
            )
        parts .append ("")

    list_type ="today"if today_only else "list"
    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (types .InlineKeyboardButton ("👁 Посмотреть",callback_data =f"choose_action:view:{list_type }"))
    markup .add (
    types .InlineKeyboardButton ("✏️ Изменить",callback_data =f"choose_action:edit:{list_type }"),
    types .InlineKeyboardButton ("🗑 Удалить",callback_data =f"choose_action:delete:{list_type }"),
    )
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:main"))
    show_screen (user_id ,chat_id ,"\n".join (parts ).strip (),markup )


    # =========================================================


EXCEL_EVENT_TITLES = {
    "created": "Создано напоминание",
    "done": "Выполнено",
    "not_done": "Не выполнено",
    "snoozed": "Перенесено",
    "deleted": "Удалено",
}

EXCEL_STATUS_TITLES = {
    "pending": "Активно",
    "done": "Выполнено",
    "not_done": "Не выполнено",
    "deleted": "Удалено",
    "ok": "Выполнено",
    "skipped": "Старый статус",
    "no_response": "Старый статус",
}



def excel_value_title(mapping: dict, value: object) -> str:
    if value is None:
        return ""
    text = str(value)
    return mapping.get(text, text)


def excel_category_title(value: object) -> str:
    return excel_value_title(CATEGORY_TITLES, value).replace("📚 ", "").replace("📝 ", "").replace("👥 ", "").replace("⏰ ", "").replace("🏠 ", "").replace("📌 ", "")


def excel_priority_title(value: object) -> str:
    return excel_value_title(PRIORITY_TITLES, value).replace("⚡ ", "").replace("🔥 ", "").replace("🔴 ", "").replace("🟡 ", "").replace("🟢 ", "")


def excel_event_title(value: object) -> str:
    return excel_value_title(EXCEL_EVENT_TITLES, value)


def excel_status_title(value: object) -> str:
    return excel_value_title(EXCEL_STATUS_TITLES, value)


def setup_excel_sheet(sheet) -> None:
    try:
        from openpyxl.styles import Font, Alignment, PatternFill
        header_fill = PatternFill("solid", fgColor="D9EAF7")
        for cell in sheet[1]:
            cell.font = Font(bold=True)
            cell.fill = header_fill
            cell.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)
        for row in sheet.iter_rows(min_row=2):
            for cell in row:
                cell.alignment = Alignment(vertical="top", wrap_text=True)
        sheet.freeze_panes = "A2"
        sheet.auto_filter.ref = sheet.dimensions
    except Exception:
        pass


def append_excel_row(sheet, values: list) -> None:
    sheet.append(["" if value is None else value for value in values])


def reminder_excel_status (row :sqlite3 .Row )->str :
    status =str (row ["status"]or "pending")
    if status =="pending":
        try :
            if int (row ["snooze_count"]or 0)>0 :
                return "Перенесено"
        except Exception :
            pass
        return "Активно"
    return excel_status_title (status)


def excel_utc_to_local (utc_value :object ,timezone_name :str )->str :
    text =str (utc_value or "").strip ()
    if not text :
        return ""
    tz_name =str (timezone_name or DEFAULT_TIMEZONE_NAME ).strip ()or DEFAULT_TIMEZONE_NAME
    try :
        dt =datetime .strptime (text ,"%Y-%m-%d %H:%M:%S").replace (tzinfo =timezone .utc )
        return dt .astimezone (ZoneInfo (tz_name )).strftime ("%Y-%m-%d %H:%M")
    except Exception :
        return text


def excel_short_text (value :object ,limit :int =120 )->str :
    text =normalize_spaces (str (value or ""))
    if len (text )<=limit :
        return text
    return text [:limit -1 ].rstrip ()+"…"


def send_normal_greeting_message (user_id :int ,chat_id :int ):
    _ ,current_timezone_title =get_user_timezone (user_id )
    if user_timezone_is_selected (user_id ):
        text =(
        "<b>Привет! Я бот-напоминалка.</b>\n\n"
        "Создаю напоминания из текста и голосовых, понимаю повторы, приоритеты "
        "и могу сделать несколько напоминаний из одной фразы.\n\n"
        f"Часовой пояс: <b>{escape_html (current_timezone_title )}</b>."
        )
    else :
        text =(
        "<b>Привет! Я бот-напоминалка.</b>\n\n"
        "Создаю напоминания из текста и голосовых, понимаю повторы, приоритеты "
        "и могу сделать несколько напоминаний из одной фразы.\n\n"
        "Сначала выбери часовой пояс в сообщении ниже."
        )
    msg =bot .send_message (chat_id ,text ,reply_markup =build_main_menu_reply (user_id ))
    remember_bot_service_message (user_id ,chat_id ,msg .message_id ,"greeting")
    GREETING_MESSAGES [user_id ]={"chat_id":chat_id ,"message_id":msg .message_id ,"kind":"normal"}
    return msg


    # =========================================================
    # Сессии и редактирование
    # =========================================================

def new_session_id ()->str :
    return uuid .uuid4 ().hex [:10 ]


def get_session (session_id :str ,user_id :int )->Optional [dict ]:
    s =SESSIONS .get (session_id )
    if not s or s ["user_id"]!=user_id :
        return None 
    return s 


def destroy_session (session_id :str )->None :
    s =SESSIONS .pop (session_id ,None )
    if s :
        INPUT_STATES .pop (s ["user_id"],None )


def create_draft_session (user_id :int ,chat_id :int ,parsed :ParsedReminder ,source_text :Optional [str ]=None )->str :
    sid =new_session_id ()
    timezone_name ,timezone_title =get_user_timezone (user_id )
    data ={
    "topic":parsed .topic ,
    "reminder_text":parsed .reminder_text ,
    "category":parsed .category ,
    "priority":parsed .priority ,
    "repeat_type":parsed .repeat_type or "none",
    "repeat_value":parsed .repeat_value or "",
    "next_local_at":parsed .next_local_at ,
    "next_utc_at":parsed .next_utc_at ,
    "timezone_name":timezone_name ,
    "timezone_title":timezone_title ,
    "parse_method":parsed .parse_method or "yandex",
    "yandex_reparse_used":1 if parsed .parse_method =="yandex_reparse" else 0,
    "reminder_kind":parsed .reminder_kind or "normal",
    "interval_minutes":int (parsed .interval_minutes or 0),
    "window_start_time":parsed .window_start_time or "",
    "window_end_time":parsed .window_end_time or "",
    "window_days":parsed .window_days or "",
    "break_number":int (parsed .break_number or 0),
    "break_mode":parsed .break_mode or "",
    }
    SESSIONS [sid ]={"mode":"draft","user_id":user_id ,"chat_id":chat_id ,"source":"main","source_text":source_text or parsed .reminder_text,"data":dict (data ),"original":dict (data )}
    return sid 



def create_bulk_draft_session (user_id :int ,chat_id :int ,parsed_items :list [ParsedReminder ])->str :
    sid =new_session_id ()
    timezone_name ,timezone_title =get_user_timezone (user_id )
    data_items =[]
    for parsed in parsed_items :
        data_items .append ({
        "topic":parsed .topic ,
        "reminder_text":parsed .reminder_text ,
        "category":parsed .category ,
        "priority":parsed .priority ,
        "repeat_type":parsed .repeat_type or "none",
        "repeat_value":parsed .repeat_value or "",
        "next_local_at":parsed .next_local_at ,
        "next_utc_at":parsed .next_utc_at ,
        "timezone_name":timezone_name ,
        "timezone_title":timezone_title ,
        "parse_method":parsed .parse_method or "yandex",
        "yandex_reparse_used":1 if parsed .parse_method =="yandex_reparse" else 0,
        })
    SESSIONS [sid ]={
    "mode":"bulk_draft",
    "user_id":user_id ,
    "chat_id":chat_id ,
    "source":"main",
    "items":data_items ,
    "original_items":[dict (x )for x in data_items ],
    }
    return sid 


def render_bulk_session_text (session :dict )->str :
    items =session .get ("items",[])
    parts =[
    f"<b>Проверь несколько напоминаний</b>\n",
    f"Найдено: {len (items )}",
    "⚠️ Проверь список: если какого-то дела не хватает, отправь его отдельным сообщением.",
    ]
    for i ,item in enumerate (items ,start =1 ):
        timer_line =""
        if should_show_time_until (item ['priority']):
            timer_line =f"До события: {escape_html (format_time_until (item ['next_local_at'],item ['timezone_name']))}\n"
        parts .append (
        f"\n<b>{i }. {escape_html (item ['topic'])}</b>\n"
        f"{escape_html (format_human_datetime (item ['next_local_at'],item ['timezone_name']))}\n"
        f"{timer_line}"
        f"{escape_html (repeat_title (item ['repeat_type'],item ['repeat_value']))} • "
        f"{escape_html (PRIORITY_TITLES .get (item ['priority'],'🟡 Обычно'))}"
        )
    return "\n".join (parts )


def build_bulk_draft_preview_markup (session_id :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("✅ Подтвердить все",callback_data =f"bulk_confirm:{session_id }"))
    markup .add (types .InlineKeyboardButton ("✏️ Изменить одно",callback_data =f"bulk_edit:{session_id }"))
    markup .add (types .InlineKeyboardButton ("🗑 Удалить одно из черновика",callback_data =f"bulk_delete:{session_id }"))
    markup .add (types .InlineKeyboardButton ("↩️ Отмена",callback_data =f"bulk_cancel:{session_id }"))
    return markup 


def build_bulk_select_edit_markup (session_id :str )->types .InlineKeyboardMarkup :
    s =SESSIONS .get (session_id )
    markup =types .InlineKeyboardMarkup (row_width =1 )
    if not s :
        markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:main"))
        return markup 
    for i ,item in enumerate (s .get ("items",[])):
        label =f"{i +1 }. {item ['topic']} — {item ['next_local_at'][5 :16 ]}"
        if len (label )>60 :
            label =label [:57 ]+"..."
        markup .add (types .InlineKeyboardButton (label ,callback_data =f"bulk_select:{session_id }:{i }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"bulk_back:{session_id }"))
    return markup 


def build_bulk_select_delete_markup (session_id :str )->types .InlineKeyboardMarkup :
    s =SESSIONS .get (session_id )
    markup =types .InlineKeyboardMarkup (row_width =1 )
    if not s :
        markup .add (types .InlineKeyboardButton ("↩️ На главную",callback_data ="nav:main"))
        return markup 
    for i ,item in enumerate (s .get ("items",[])):
        label =f"🗑 {i +1 }. {item ['topic']} — {item ['next_local_at'][5 :16 ]}"
        if len (label )>60 :
            label =label [:57 ]+"..."
        markup .add (types .InlineKeyboardButton (label ,callback_data =f"bulk_delete_select:{session_id }:{i }"))
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"bulk_back:{session_id }"))
    return markup 


def create_draft_session_from_data (user_id :int ,chat_id :int ,data :dict )->str :
    sid =new_session_id ()
    SESSIONS [sid ]={
    "mode":"draft",
    "user_id":user_id ,
    "chat_id":chat_id ,
    "source":"main",
    "source_text":data .get ("source_text",data .get ("reminder_text","")),
    "data":dict (data ),
    "original":dict (data ),
    }
    return sid 


def convert_remaining_bulk_item_to_single_draft (user_id :int ,chat_id :int ,bulk_session_id :str )->Optional [str ]:
    parent =get_session (bulk_session_id ,user_id )
    if not parent or parent .get ("mode")!="bulk_draft":
        return None 
    items =parent .get ("items",[])
    if len (items )!=1 :
        return None 
    data =dict (items [0 ])
    destroy_session (bulk_session_id )
    return create_draft_session_from_data (user_id ,chat_id ,data )

def show_bulk_draft_preview (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        show_main_screen (user_id ,chat_id )
        return 
    show_screen (user_id ,chat_id ,render_bulk_session_text (s ),build_bulk_draft_preview_markup (session_id ))


def create_bulk_item_session (user_id :int ,chat_id :int ,parent_session_id :str ,index :int )->Optional [str ]:
    parent =get_session (parent_session_id ,user_id )
    if not parent or parent .get ("mode")!="bulk_draft":
        return None 
    items =parent .get ("items",[])
    if index <0 or index >=len (items ):
        return None 
    sid =new_session_id ()
    data =dict (items [index ])
    SESSIONS [sid ]={
    "mode":"bulk_item",
    "user_id":user_id ,
    "chat_id":chat_id ,
    "source":"bulk",
    "parent_session_id":parent_session_id ,
    "parent_index":index ,
    "source_text":data .get ("source_text",data .get ("reminder_text","")),
    "data":dict (data ),
    "original":dict (data ),
    }
    return sid 

def create_saved_session (user_id :int ,chat_id :int ,reminder_id :int ,source :str )->Optional [str ]:
    row =get_reminder_by_id (reminder_id ,user_id )
    if not row :
        return None 
    sid =new_session_id ()
    data ={
    "topic":row ["topic"],
    "reminder_text":row ["reminder_text"],
    "category":row ["category"],
    "priority":row ["priority"],
    "repeat_type":row ["repeat_type"],
    "repeat_value":row ["repeat_value"],
    "next_local_at":row ["next_local_at"],
    "next_utc_at":row ["next_utc_at"],
    "timezone_name":row ["timezone_name"],
    "timezone_title":row ["timezone_title"],
    "parse_method":row ["parse_method"] if "parse_method" in row .keys () else "",
    "yandex_reparse_used":row ["yandex_reparse_used"] if "yandex_reparse_used" in row .keys () else 0,
    "reminder_kind":row ["reminder_kind"] if "reminder_kind" in row .keys () else "normal",
    "interval_minutes":row ["interval_minutes"] if "interval_minutes" in row .keys () else 0,
    "window_start_time":row ["window_start_time"] if "window_start_time" in row .keys () else "",
    "window_end_time":row ["window_end_time"] if "window_end_time" in row .keys () else "",
    "window_days":row ["window_days"] if "window_days" in row .keys () else "",
    "break_number":row ["break_number"] if "break_number" in row .keys () else 0,
    "break_mode":row ["break_mode"] if "break_mode" in row .keys () else "",
    }
    SESSIONS [sid ]={"mode":"saved","user_id":user_id ,"chat_id":chat_id ,"source":source ,"reminder_id":reminder_id ,"source_text":data .get ("reminder_text",""),"data":dict (data ),"original":dict (data )}
    return sid 


def show_draft_preview (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        show_main_screen (user_id ,chat_id )
        return 
    show_screen (user_id ,chat_id ,render_session_text (s ["data"],"Проверь данные"),build_draft_preview_markup (session_id ))


def show_independent_draft_preview (user_id :int ,chat_id :int ,session_id :str ,number :int ,total :int )->None :
    """
    Для нескольких одноразовых напоминаний показываем отдельные независимые карточки.
    Важно: такие карточки НЕ являются главным служебным сообщением, поэтому их нужно
    отдельно удалить после подтверждения/отмены/перехода в редактирование.
    """
    s =get_session (session_id ,user_id )
    if not s :
        return 

    title =f"Проверь напоминание {number } из {total }"
    s ["independent_title"]=title
    sent =bot .send_message (
    chat_id ,
    render_session_text (s ["data"],title),
    reply_markup =build_draft_preview_markup (session_id ),
    )
    s ["independent_message_id"]=sent .message_id 
    s ["independent_chat_id"]=chat_id 


def refresh_draft_preview_after_reparse (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        show_main_screen (user_id ,chat_id )
        return
    if s .get ("independent_message_id"):
        title =s .get ("independent_title","Проверь данные")
        try :
            bot .edit_message_text (
            render_session_text (s ["data"],title),
            chat_id =int (s .get ("independent_chat_id",chat_id )),
            message_id =int (s ["independent_message_id"]),
            reply_markup =build_draft_preview_markup (session_id ),
            parse_mode ="HTML",
            )
            return
        except Exception :
            pass
    show_draft_preview (user_id ,chat_id ,session_id )


def show_reparse_processing (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        return
    if s .get ("independent_message_id"):
        try :
            bot .edit_message_text (
            "⏳ Отправляю текст в YandexGPT и пересобираю черновик...",
            chat_id =int (s .get ("independent_chat_id",chat_id )),
            message_id =int (s ["independent_message_id"]),
            reply_markup =None ,
            parse_mode ="HTML",
            )
            return
        except Exception :
            pass
    show_screen (user_id ,chat_id ,"⏳ Отправляю текст в YandexGPT и пересобираю черновик...",None )


def process_yandex_reparse_for_draft (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s or s .get ("mode") not in {"draft","bulk_item"}:
        show_main_screen (user_id ,chat_id )
        return
    source_text =str (s .get ("source_text") or s .get ("data",{}).get ("reminder_text","")).strip ()
    if not source_text :
        source_text =str (s .get ("data",{}).get ("topic","")).strip ()
    timezone_name ,timezone_title =get_user_timezone (user_id )
    custom_times =get_user_time_words (user_id )
    parsed_many ,err =force_yandex_parse_many (source_text ,timezone_name ,timezone_title ,custom_times ,"yandex_reparse")
    if not parsed_many :
        show_screen (user_id ,chat_id ,debug_text ("Не удалось пересобрать черновик",err or "YandexGPT не вернул корректные данные."),build_main_nav_markup ())
        return
    parsed =parsed_many [0 ]
    data =s ["data"]
    data .update ({
    "topic":parsed .topic ,
    "reminder_text":parsed .reminder_text ,
    "category":parsed .category ,
    "priority":parsed .priority ,
    "repeat_type":parsed .repeat_type or "none",
    "repeat_value":parsed .repeat_value or "",
    "next_local_at":parsed .next_local_at ,
    "next_utc_at":parsed .next_utc_at ,
    "timezone_name":timezone_name ,
    "timezone_title":timezone_title ,
    "parse_method":"yandex_reparse",
    "yandex_reparse_used":1 ,
    })
    s ["original"]=dict (data )
    s ["changed_fields"]=set ()
    record_parse_usage (user_id ,"yandex_reparse")
    refresh_draft_preview_after_reparse (user_id ,chat_id ,session_id )



LOCKED_USER_FIELDS ={
"topic",
"reminder_text",
"category",
"priority",
"repeat_type",
"repeat_value",
"next_local_at",
"next_utc_at",
}


def mark_session_field_changed (session :dict ,*fields :str )->None :
    """
    Фиксирует, что пользователь сам изменил конкретные поля.
    Все остальные поля считаются заблокированными от скрытых изменений.
    """
    changed =session .setdefault ("changed_fields",set ())
    for field in fields :
        changed .add (field )


def apply_locked_fields (session :dict )->None :
    """
    Блокировка скрытых изменений.

    Смысл:
    если пользователь менял только время — тема, текст, категория, приоритет и повтор
    не должны измениться сами;
    если менял только приоритет — время/повтор/текст не должны измениться сами;
    если ничего не менял — сохраняется исходный черновик без скрытой пересборки параметров.
    """
    original =session .get ("original")
    data =session .get ("data")
    if not isinstance (original ,dict )or not isinstance (data ,dict ):
        return 

    changed =session .get ("changed_fields",set ())
    if not isinstance (changed ,set ):
        changed =set (changed )

    for field in LOCKED_USER_FIELDS :
        if field in original and field not in changed :
            data [field ]=original [field ]


def apply_locked_fields_to_bulk_item (session :dict )->None :
    """
    То же самое для редактирования одного элемента внутри комбинированного черновика.
    """
    apply_locked_fields (session )



def reset_session_changes (user_id :int ,session_id :str )->bool :
    """
    Полный сброс правок внутри сессии.
    Очищает data, временный выбор дней недели, флаг ручного изменения времени и состояние ввода.
    """
    s =get_session (session_id ,user_id )
    if not s :
        INPUT_STATES .pop (user_id ,None )
        return False 

    original =s .get ("original")
    if isinstance (original ,dict ):
        s ["data"]=dict (original )

    s .pop ("temp_weekdays",None )
    s .pop ("time_manually_changed",None )
    s .pop ("changed_fields",None )
    INPUT_STATES .pop (user_id ,None )
    return True 


def edit_text_has_date_hint(current_data: dict, user_text: str) -> bool:
    """
    Проверяет, есть ли в ручной правке именно дата, а не только часы и минуты.
    Это нужно, чтобы при вводе "10 мая в 23:00" менялась дата,
    а при вводе "23:00" оставалась старая дата.
    """
    try:
        timezone_name = current_data["timezone_name"]
        tz = ZoneInfo(timezone_name)
        now_local = datetime.now(tz)
        current_base = datetime.strptime(current_data["next_local_at"], "%Y-%m-%d %H:%M").replace(tzinfo=tz)
        return extract_date_base_from_edit_text(user_text, now_local, current_base) is not None
    except Exception:
        t = (user_text or "").lower().replace("ё", "е")
        if re.search(r"\b(сегодня|завтра|послезавтра)\b", t):
            return True
        if re.search(r"(?<!\d)\d{1,2}[.\-/]\d{1,2}(?:[.\-/]\d{2,4})?(?!\d)", t):
            return True
        if any(month in t for month in MONTH_WORD_TO_NUMBER):
            return True
        return bool(re.search(r"\b(понедельник|вторник|среда|среду|четверг|пятница|суббота|воскресенье|пн|вт|ср|чт|пт|сб|вс)\b", t))

def apply_edited_time_preserving_repeat(data: dict, local_at: str, date_was_changed: bool = False) -> tuple[str, str]:
    """
    Меняет дату/время и не ломает повтор.

    Если пользователь написал только время, например "23:00", дата остаётся старой,
    а повтор пересчитывается как раньше.

    Если пользователь написал дату, например "10 мая в 23:00" или "в среду в 8:30",
    меняется и дата. Для повторов по конкретным дням недели бот также меняет день повтора.
    Например, было "каждый понедельник", пользователь ввёл "в среду в 8:30" — станет среда.
    """
    repeat_type = data.get("repeat_type", "none")
    repeat_value = data.get("repeat_value", "")
    timezone_name = data["timezone_name"]
    tz = ZoneInfo(timezone_name)
    local_dt = datetime.strptime(local_at, "%Y-%m-%d %H:%M").replace(tzinfo=tz)
    now_local = datetime.now(tz)

    if repeat_type != "none":
        if date_was_changed:
            weekday = local_dt.weekday()

            if repeat_type == "custom_weekdays":
                data["repeat_value"] = str(weekday)
                repeat_value = str(weekday)
            elif repeat_type == "weekdays" and weekday >= 5:
                data["repeat_type"] = "custom_weekdays"
                data["repeat_value"] = str(weekday)
                repeat_type = "custom_weekdays"
                repeat_value = str(weekday)
            elif repeat_type == "weekends" and weekday < 5:
                data["repeat_type"] = "custom_weekdays"
                data["repeat_value"] = str(weekday)
                repeat_type = "custom_weekdays"
                repeat_value = str(weekday)

            if local_dt <= now_local:
                return recalc_next_after_repeat_change(
                    local_dt.strftime("%Y-%m-%d %H:%M"),
                    timezone_name,
                    data.get("repeat_type", repeat_type),
                    data.get("repeat_value", repeat_value),
                )
            return local_dt.strftime("%Y-%m-%d %H:%M"), local_dt.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")

        return recalc_next_after_repeat_change(local_at, timezone_name, repeat_type, repeat_value)

    if local_dt <= now_local and local_dt.date() == now_local.date():
        local_dt += timedelta(days=1)

    return local_dt.strftime("%Y-%m-%d %H:%M"), local_dt.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")

def show_edit_session_screen (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        show_main_screen (user_id ,chat_id )
        return 
    show_screen (user_id ,chat_id ,render_session_text (s ["data"],"Редактирование напоминания"),build_edit_menu_markup (session_id ,s ["mode"]))


def process_session_confirm (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        show_main_screen (user_id ,chat_id )
        return 

    if s ["mode"]=="bulk_draft":
        try :
            for data in s .get ("items",[]):
                if data .get ("repeat_type")!="none":
                    data ["next_local_at"],data ["next_utc_at"]=recalc_next_after_repeat_change (
                    data ["next_local_at"],
                    data ["timezone_name"],
                    data ["repeat_type"],
                    data .get ("repeat_value",""),
                    )
                data ["next_local_at"],data ["next_utc_at"]=ensure_future_for_repeat (
                data ["next_local_at"],
                data ["timezone_name"],
                data ["repeat_type"],
                data ["repeat_value"],
                )
                insert_reminder ({"user_id":user_id ,**data })
        except ValueError as e :
            show_screen (user_id ,chat_id ,str (e ),build_bulk_draft_preview_markup (session_id ))
            return 

        saved_items =list (s .get ("items",[]))
        count =len (saved_items )
        destroy_session (session_id )
        markup =types .InlineKeyboardMarkup ()
        markup .add (types .InlineKeyboardButton ("📋 К списку",callback_data ="nav:list"))
        markup .add (types .InlineKeyboardButton ("↩️ На главную",callback_data ="nav:main"))
        lines =[f"✅ Сохранено напоминаний: {count }"]
        for i ,item in enumerate (saved_items ,start =1 ):
            lines .append (f"{i }. {escape_html (item ['topic'])} — {escape_html (format_human_datetime (item ['next_local_at'],item ['timezone_name']))}")
        show_screen (user_id ,chat_id ,"\n".join (lines ),markup )
        return 

    if s ["mode"]=="bulk_item":
        apply_locked_fields_to_bulk_item (s )
        parent_id =s .get ("parent_session_id")
        parent_index =s .get ("parent_index")
        parent =get_session (parent_id ,user_id )if parent_id else None 
        if parent and parent .get ("mode")=="bulk_draft":
            parent ["items"][parent_index ]=dict (s ["data"])
            destroy_session (session_id )
            show_bulk_draft_preview (user_id ,chat_id ,parent_id )
            return 
        destroy_session (session_id )
        show_main_screen (user_id ,chat_id )
        return 

    apply_locked_fields (s )
    data =s ["data"]
    try :
        changed_fields =s .get ("changed_fields",set ())
        if (
        data .get ("repeat_type")!="none"
        and not s .get ("time_manually_changed")
        and bool ({"repeat_type","repeat_value","next_local_at","next_utc_at"}&set (changed_fields ))
        ):
            data ["next_local_at"],data ["next_utc_at"]=recalc_next_after_repeat_change (
            data ["next_local_at"],
            data ["timezone_name"],
            data ["repeat_type"],
            data .get ("repeat_value",""),
            )
        data ["next_local_at"],data ["next_utc_at"]=ensure_future_for_repeat (
        data ["next_local_at"],
        data ["timezone_name"],
        data ["repeat_type"],
        data ["repeat_value"],
        )
    except ValueError as e :
        markup =types .InlineKeyboardMarkup ()
        markup .add (types .InlineKeyboardButton ("✏️ Исправить",callback_data =f"edit_field:time:{session_id }"))
        markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data =f"edit_menu_back:{session_id }"))
        show_screen (user_id ,chat_id ,str (e ),markup )
        return 

    if s ["mode"]=="draft":
        insert_reminder ({"user_id":user_id ,**data })

        independent_message_id =s .get ("independent_message_id")
        independent_chat_id =s .get ("independent_chat_id",chat_id )

        destroy_session (session_id )

        if independent_message_id :
            safe_delete_message (independent_chat_id ,independent_message_id )
            # Для независимых дублей не оставляем сообщение "сохранено" сверху.
            # Остаётся приветствие с клавиатурой и главное служебное меню.
            show_main_screen (user_id ,chat_id )
            return 

        markup =types .InlineKeyboardMarkup ()
        markup .add (types .InlineKeyboardButton ("📋 К списку",callback_data ="nav:list"))
        markup .add (types .InlineKeyboardButton ("↩️ На главную",callback_data ="nav:main"))
        show_screen (user_id ,chat_id ,"✅ Напоминание сохранено.",markup )
        return 

    ok =update_reminder (s ["reminder_id"],user_id ,data )
    source =s ["source"]
    destroy_session (session_id )
    if not ok :
        show_screen (user_id ,chat_id ,"Не удалось сохранить изменения.",build_main_nav_markup ())
        return 
    show_list_screen (user_id ,chat_id ,source =="today")


def back_from_saved_session (user_id :int ,chat_id :int ,session_id :str )->None :
    s =get_session (session_id ,user_id )
    if not s :
        show_main_screen (user_id ,chat_id )
        return 
    source =s ["source"]
    destroy_session (session_id )
    show_list_screen (user_id ,chat_id ,source =="today")


def parse_custom_time_value (text_value :str )->Optional [str ]:
    t =normalize_spaces ((text_value or "").lower ().replace ("ё","е"))
    if not t :
        return None 

    explicit =extract_explicit_time_from_text (t )
    if explicit :
        return format_hhmm (*explicit )

    match =re .fullmatch (r"(\d{1,2})[:.](\d{1,2})",t )
    if match :
        hour =int (match .group (1 ))
        minute =int (match .group (2 ))
        if 0 <=hour <=23 and 0 <=minute <=59 :
            return format_hhmm (hour ,minute )

    match =re .fullmatch (r"(\d{1,2})\s+(\d{1,2})",t )
    if match :
        hour =int (match .group (1 ))
        minute =int (match .group (2 ))
        if 0 <=hour <=23 and 0 <=minute <=59 :
            return format_hhmm (hour ,minute )

    match =re .fullmatch (r"(\d{3,4})",t )
    if match :
        digits =match .group (1 )
        if len (digits )==3 :
            hour =int (digits [0 ])
            minute =int (digits [1 :])
        else :
            hour =int (digits [:2 ])
            minute =int (digits [2 :])
        if 0 <=hour <=23 and 0 <=minute <=59 :
            return format_hhmm (hour ,minute )

    match =re .fullmatch (r"(\d{1,2})\s*(утра|дня|вечера|ночи)?",t )
    if match :
        hour =int (match .group (1 ))
        period =match .group (2 )or ""
        if period in {"дня","вечера"}and 1 <=hour <=11 :
            hour +=12 
        if period =="ночи"and hour ==12 :
            hour =0 
        if 0 <=hour <=23 :
            return format_hhmm (hour ,0 )

    return None 



SNOOZE_NUMBER_WORDS ={
    "один":1,"одну":1,"одно":1,"одного":1,
    "два":2,"две":2,"трех":3,"три":3,"четыре":4,"пять":5,"шесть":6,"семь":7,"восемь":8,"девять":9,"десять":10,
}


def _snooze_number_to_int (value :str )->Optional [int ]:
    value =normalize_spaces ((value or "").lower ().replace ("ё","е"))
    if value .isdigit ():
        return int (value )
    return SNOOZE_NUMBER_WORDS .get (value )


def _next_weekday_datetime (now_local :datetime ,weekday :int ,hour :int ,minute :int )->datetime :
    days_ahead =(weekday -now_local .weekday ())%7
    candidate =(now_local +timedelta (days =days_ahead )).replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )
    if candidate <=now_local :
        candidate +=timedelta (days =7 )
    return candidate


def parse_snooze_request_local (row :sqlite3 .Row ,text_value :str ,custom_times :Optional [dict [str ,str ]]=None )->Optional [tuple [str ,str ,str ]]:
    """
    Локальный разбор переноса. Возвращает (local_at, utc_at, details).
    Поддерживает длительность: 30 минут, на 2 часа, 1 день, на час, на полчаса.
    Поддерживает даты: завтра, завтра в 9, завтра утром, в понедельник в 8:30.
    """
    raw =text_value or ""
    t =normalize_spaces (raw .lower ().replace ("ё","е"))
    if not t :
        return None

    tz =ZoneInfo (row ["timezone_name"])
    now_local =datetime .now (tz ).replace (second =0 ,microsecond =0 )
    original_dt =datetime .strptime (row ["next_local_at"],"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    original_hour =original_dt .hour
    original_minute =original_dt .minute

    relative_datetime =parse_relative_datetime_from_now (t ,row ["timezone_name"], custom_times )
    if relative_datetime :
        local_at ,utc_at ,details =relative_datetime
        return local_at ,utc_at ,details

    if re .search (r"\b(пол\s*часа|полчаса)\b",t ):
        candidate =now_local +timedelta (minutes =30 )
        return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),"на 30 минут"

    if re .search (r"\b(час|один\s+час|на\s+час)\b",t )and not re .search (r"\d",t ):
        candidate =now_local +timedelta (hours =1 )
        return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),"на 1 час"

    duration_match =re .search (
    r"(?:\bна\s+|\bчерез\s+)?(\d{1,3}|один|одну|одно|два|две|три|четыре|пять|шесть|семь|восемь|девять|десять)\s*"
    r"(минут(?:у|ы)?|мин|час(?:а|ов)?|ч|день|дня|дней|сутки|суток)\b",
    t ,
    )
    if duration_match :
        n =_snooze_number_to_int (duration_match .group (1 ))
        unit =duration_match .group (2 )
        if n and n >0 :
            if unit .startswith ("мин"):
                delta =timedelta (minutes =n )
                details =f"на {n} мин."
            elif unit in {"ч"}or unit .startswith ("час"):
                delta =timedelta (hours =n )
                details =f"на {n} ч."
            else:
                delta =timedelta (days =n )
                details =f"на {n} дн."
            candidate =now_local +delta
            return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),details

    explicit =extract_explicit_time_from_text (t )
    default_words =None if explicit else extract_default_time_from_words (t ,custom_times )
    if explicit :
        hour ,minute =explicit
    elif default_words :
        hour ,minute =default_words
    else:
        hour ,minute =original_hour ,original_minute

    if "послезавтра"in t :
        candidate =(now_local +timedelta (days =2 )).replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )
        return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),"на послезавтра"

    if "завтра"in t :
        candidate =(now_local +timedelta (days =1 )).replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )
        return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),"на завтра"

    if "сегодня"in t :
        candidate =now_local .replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )
        if candidate <=now_local :
            candidate +=timedelta (days =1 )
        return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),"на сегодня"

    weekday_patterns ={
    0 :[r"\bпонедельник[а-я]*\b",r"\bпн\b"],
    1 :[r"\bвторник[а-я]*\b",r"\bвт\b"],
    2 :[r"\bсред[а-я]*\b",r"\bср\b"],
    3 :[r"\bчетверг[а-я]*\b",r"\bчт\b"],
    4 :[r"\bпятниц[а-я]*\b",r"\bпт\b"],
    5 :[r"\bсуббот[а-я]*\b",r"\bсб\b"],
    6 :[r"\bвоскресень[а-я]*\b",r"\bвс\b"],
    }
    for day_num ,patterns in weekday_patterns .items ():
        if any (re .search (pattern ,t )for pattern in patterns ):
            candidate =_next_weekday_datetime (now_local ,day_num ,hour ,minute )
            return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),f"на {WEEKDAYS [day_num]}"

    # Если пользователь написал только конкретное время, переносим на ближайшее будущее это время.
    if explicit or default_words :
        candidate =now_local .replace (hour =hour ,minute =minute ,second =0 ,microsecond =0 )
        if candidate <=now_local :
            candidate +=timedelta (days =1 )
        return candidate .strftime ("%Y-%m-%d %H:%M"),candidate .astimezone (timezone .utc ).strftime ("%Y-%m-%d %H:%M:%S"),"на указанное время"

    return None


def parse_snooze_request (row :sqlite3 .Row ,text_value :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [Optional [str ],Optional [str ],str ,Optional [str ]]:
    local_result =parse_snooze_request_local (row ,text_value ,custom_times )
    if local_result :
        local_at ,utc_at ,details =local_result
        return local_at ,utc_at ,details ,None

    current_data ={
    "topic":row ["topic"],
    "reminder_text":row ["reminder_text"],
    "category":row ["category"],
    "priority":row ["priority"],
    "repeat_type":row ["repeat_type"],
    "repeat_value":row ["repeat_value"],
    "next_local_at":row ["next_local_at"],
    "next_utc_at":row ["next_utc_at"],
    "timezone_name":row ["timezone_name"],
    "timezone_title":row ["timezone_title"],
    }
    yandex_local ,err =ask_yandex_edit_time (current_data ,text_value ,custom_times )
    if not yandex_local :
        return None ,None ,"",err or "Не удалось понять перенос."
    local_at ,utc_at =parse_exact_local_datetime (yandex_local ,row ["timezone_name"])
    if not local_at or not utc_at :
        return None ,None ,"", "Не удалось проверить новое время."
    return local_at ,utc_at ,"по уточнённой фразе",None


def apply_snooze_to_reminder (reminder_id :int ,user_id :int ,new_local_at :str ,new_utc_at :str ,details :str )->bool :
    row =get_reminder_by_id (reminder_id ,user_id )
    if not row :
        return False
    old_snooze_count =0
    try :
        old_snooze_count =int (row ["snooze_count"]or 0)
    except Exception :
        old_snooze_count =0

    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        UPDATE denis_v4_reminders
        SET next_local_at=?, next_utc_at=?, next_notify_utc=?,
            notify_count=0, max_notify_count=?,
            active_message_chat_id=0, active_message_id=0,
            snooze_count=COALESCE(snooze_count,0)+1,
            interval_snoozed_count=COALESCE(interval_snoozed_count,0)+CASE WHEN reminder_kind IN ('interval','break_each','lesson_each') THEN 1 ELSE 0 END,
            last_snooze_text=?, last_snooze_at_utc=?
        WHERE id=? AND user_id=? AND status='pending'
    """,(
        new_local_at ,new_utc_at ,new_utc_at ,
        max_notify_count_for_priority (row ["priority"],user_id),
        details or "перенос",now_utc_str (),
        reminder_id ,user_id
    ))
    conn .commit ()
    conn .close ()

    # В статистике перенос считается по напоминанию, а не по числу переносов.
    if old_snooze_count ==0 :
        record_analytics_event (
        user_id,
        "snoozed",
        reminder_id,
        row ["topic"],
        row ["reminder_text"],
        new_local_at,
        new_utc_at,
        row ["category"],
        row ["priority"],
        row ["repeat_type"],
        details,
        )
    return True


def handle_edit_input (message :telebot .types .Message )->bool :
    state =INPUT_STATES .get (message .from_user .id )
    if not state :
        return False 

    user_id =message .from_user .id 
    chat_id =message .chat .id 

    if state.get("mode") == "breaks_add":
        safe_delete_user_message(message)
        if message.text.strip().lower() == "отмена":
            INPUT_STATES.pop(user_id, None)
            show_break_times_screen(user_id, chat_id)
            return True
        ranges, err = parse_break_ranges_text(message.text)
        if err:
            show_screen(
                user_id,
                chat_id,
                f"<b>➕ Добавление перемен</b>\n\n"
                f"{escape_html(err)}\n\n"
                "Попробуй ещё раз:\n"
                "<code>09:40-09:50\n10:30-10:45</code>",
                build_break_times_markup(user_id),
            )
            return True
        added, duplicates = add_school_breaks_for_days(user_id, selected_break_days(user_id), ranges)
        INPUT_STATES.pop(user_id, None)
        text = f"✅ Добавлено перемен: <b>{added}</b>."
        if duplicates:
            text += f"\n⚠️ Дублей пропущено: <b>{duplicates}</b>."
        show_screen(user_id, chat_id, text, build_break_times_markup(user_id))
        return True

    if state.get("mode") == "custom_priority_interval":
        safe_delete_user_message(message)
        if message.text.strip().lower().replace("ё", "е") == "отмена":
            INPUT_STATES.pop(user_id, None)
            show_priority_time_settings_screen(user_id, chat_id)
            return True
        priority = str(state.get("priority") or "medium")
        seconds, err = parse_priority_interval_value(message.text.strip())
        if err or seconds is None:
            show_screen(
                user_id,
                chat_id,
                f"<b>{escape_html(PRIORITY_TITLES.get(priority, '🟡 Обычно'))}</b>\n\n"
                f"{escape_html(err or 'Не удалось понять интервал.')}\n\n"
                "Напиши ещё раз. Примеры:\n"
                "<code>5 минут</code>\n"
                "<code>10 секунд</code>\n"
                "<code>раз в 2 минуты</code>",
                build_priority_settings_markup(user_id),
            )
            return True
        update_user_priority_interval(user_id, priority, seconds)
        INPUT_STATES.pop(user_id, None)
        show_priority_time_settings_screen(user_id, chat_id)
        return True

    if state.get("mode") == "custom_priority_count":
        safe_delete_user_message(message)
        if message.text.strip().lower().replace("ё", "е") == "отмена":
            INPUT_STATES.pop(user_id, None)
            show_priority_count_settings_screen(user_id, chat_id)
            return True
        priority = str(state.get("priority") or "medium")
        count, err = parse_priority_max_count_value(message.text.strip())
        if err or count is None:
            show_screen(
                user_id,
                chat_id,
                f"<b>{escape_html(PRIORITY_TITLES.get(priority, '🟡 Обычно'))}</b>\n\n"
                f"{escape_html(err or 'Не удалось понять количество.')}\n\n"
                "Напиши число от 1 до 30 или напиши <b>Отмена</b>.",
                build_priority_count_settings_markup(user_id),
            )
            return True
        update_user_priority_max_count(user_id, priority, count)
        INPUT_STATES.pop(user_id, None)
        show_priority_count_settings_screen(user_id, chat_id)
        return True

    if state.get("mode") == "custom_time":
        safe_delete_user_message(message)

        if message.text.strip().lower() == "отмена":
            INPUT_STATES.pop(user_id, None)
            show_time_words_screen(user_id, chat_id)
            return True

        word_key = state.get("word_key", "")
        title = TIME_WORD_TITLES.get(word_key, "Настройка")
        parsed_time = parse_custom_time_value(message.text.strip())

        if word_key not in TIME_WORD_COLUMNS or not parsed_time:
            show_screen(
                user_id,
                chat_id,
                f"<b>{escape_html(title)}</b>\n\n"
                "Не удалось понять время. Напиши ещё раз.\n\n"
                "Подходят форматы:\n"
                "• 08:30\n"
                "• 8 30\n"
                "• 830\n"
                "• 8 утра\n\n"
                "Для отмены напиши: <b>Отмена</b>",
                build_time_words_markup(user_id),
            )
            return True

        update_user_time_word(user_id, word_key, parsed_time)
        INPUT_STATES.pop(user_id, None)
        show_time_words_screen(user_id, chat_id)
        return True

    if state .get ("mode")=="snooze_reminder":
        safe_delete_user_message (message )
        text_value =message .text .strip ()

        reminder_id =int (state .get ("reminder_id",0 ))
        row =get_reminder_by_id (reminder_id ,user_id )

        if text_value .lower ().replace ("ё","е")=="отмена":
            INPUT_STATES .pop (user_id ,None )
            if row :
                try :
                    bot .edit_message_text (
                    render_due_notification_text (row),
                    chat_id =int (state .get ("source_chat_id",chat_id )or chat_id ),
                    message_id =int (state .get ("source_message_id",0 )or 0 ),
                    reply_markup =build_due_actions_markup (reminder_id,row),
                    parse_mode ="HTML",
                    )
                except Exception :
                    show_screen (user_id ,chat_id ,render_due_notification_text (row),build_due_actions_markup (reminder_id,row))
            else:
                show_screen (user_id ,chat_id ,"Напоминание уже недоступно.",build_main_nav_markup ())
            return True

        if time .time ()>float (state .get ("expires_at",0 )):
            INPUT_STATES .pop (user_id ,None )
            if row :
                try :
                    bot .edit_message_text (
                    render_due_notification_text (row),
                    chat_id =int (state .get ("source_chat_id",chat_id )or chat_id ),
                    message_id =int (state .get ("source_message_id",0 )or 0 ),
                    reply_markup =build_due_actions_markup (reminder_id,row),
                    parse_mode ="HTML",
                    )
                except Exception :
                    show_screen (user_id ,chat_id ,render_due_notification_text (row),build_due_actions_markup (reminder_id,row))
            return True

        if not row :
            INPUT_STATES .pop (user_id ,None )
            show_screen (user_id ,chat_id ,"Напоминание уже недоступно.",build_main_nav_markup ())
            return True

        custom_times =get_user_time_words (user_id )
        new_local ,new_utc ,details ,err =parse_snooze_request (row ,text_value ,custom_times )
        if not new_local or not new_utc :
            error_text =(
            "<b>⏰ Перенос напоминания</b>\n\n"
            "Не удалось понять, на сколько перенести. Напиши ещё раз.\n\n"
            "Примеры:\n"
            "• <code>30 минут</code>\n"
            "• <code>на 2 часа</code>\n"
            "• <code>на полчаса</code>\n"
            "• <code>завтра в 9</code>\n"
            "• <code>в понедельник в 8:30</code>\n\n"
            "Для отмены напиши: <b>Отмена</b>"
            + (f"\n\n<code>{escape_html (err)}</code>" if DEBUG and err else "")
            )
            try :
                bot .edit_message_text (
                error_text,
                chat_id =int (state .get ("source_chat_id",chat_id )or chat_id ),
                message_id =int (state .get ("source_message_id",0 )or 0 ),
                reply_markup =build_snooze_prompt_markup (reminder_id),
                parse_mode ="HTML",
                )
            except Exception :
                show_screen (user_id ,chat_id ,error_text ,build_snooze_prompt_markup (reminder_id))
            return True

        clear_active_message_for_reminder (
        reminder_id,
        user_id,
        current_chat_id =int (state .get ("source_chat_id",0 )or 0 ),
        current_message_id =int (state .get ("source_message_id",0 )or 0 ),
        fallback_text ="⏰ Напоминание перенесено.",
        )
        apply_snooze_to_reminder (reminder_id ,user_id ,new_local ,new_utc ,details )
        INPUT_STATES .pop (user_id ,None )
        show_screen (
        user_id ,chat_id ,
        "✅ <b>Напоминание перенесено</b>\n\n"
        f"<b>Тема:</b> {escape_html (row ['topic'])}\n"
        f"<b>Новое время:</b> {escape_html (format_human_datetime (new_local ,row ['timezone_name']))}\n"
        f"<b>Как перенесено:</b> {escape_html (details or text_value)}",
        build_main_nav_markup (),
        )
        return True

    session_id =state ["session_id"]
    field =state ["field"]

    if message .text .strip ().lower ()=="отмена":
        INPUT_STATES .pop (user_id ,None )
        show_edit_session_screen (user_id ,chat_id ,session_id )
        return True 

    s =get_session (session_id ,user_id )
    if not s :
        INPUT_STATES .pop (user_id ,None )
        show_main_screen (user_id ,chat_id )
        return True 

    data =s ["data"]

    if field =="topic":
        data ["topic"]=message .text .strip ()[:120 ]
        mark_session_field_changed (s ,"topic")
        INPUT_STATES .pop (user_id ,None )
        show_edit_session_screen (user_id ,chat_id ,session_id )
        return True 

    if field =="text":
        data ["reminder_text"]=message .text .strip ()
        mark_session_field_changed (s ,"reminder_text")
        INPUT_STATES .pop (user_id ,None )
        show_edit_session_screen (user_id ,chat_id ,session_id )
        return True 

    if field == "time":
        show_screen(user_id, chat_id, "⏳ Уточняю новую дату и время...", None)
        time_text, err = ask_yandex_edit_time(data, message.text.strip(), get_user_time_words(user_id))
        if not time_text:
            markup = types.InlineKeyboardMarkup()
            markup.add(types.InlineKeyboardButton("↩️ Назад", callback_data=f"edit_menu_back:{session_id}"))
            show_screen(user_id, chat_id, debug_text("Ошибка изменения даты и времени", (err or "Не удалось изменить дату и время.") + "\n\nПопробуй так:\n• 23:00\n• 10 мая в 23:00\n• завтра утром\n• в понедельник в 8:30"), markup)
            return True

        local_at, utc_at = parse_exact_local_datetime(time_text, data["timezone_name"])
        if not local_at or not utc_at:
            markup = types.InlineKeyboardMarkup()
            markup.add(types.InlineKeyboardButton("↩️ Назад", callback_data=f"edit_menu_back:{session_id}"))
            show_screen(user_id, chat_id, "Не удалось понять новую дату и время. Попробуй написать точнее.", markup)
            return True

        old_repeat_type = data.get("repeat_type", "none")
        old_repeat_value = data.get("repeat_value", "")
        date_was_changed = edit_text_has_date_hint(data, message.text.strip())

        local_at, utc_at = apply_edited_time_preserving_repeat(data, local_at, date_was_changed=date_was_changed)

        # Если пользователь менял только время, повтор не меняем.
        # Если он ввёл дату или день недели, повтор по конкретному дню можно обновить.
        if not date_was_changed:
            data["repeat_type"] = old_repeat_type
            data["repeat_value"] = old_repeat_value
        data["next_local_at"] = local_at
        data["next_utc_at"] = utc_at
        s["time_manually_changed"] = True
        if date_was_changed:
            mark_session_field_changed(s, "next_local_at", "next_utc_at", "repeat_type", "repeat_value")
        else:
            mark_session_field_changed(s, "next_local_at", "next_utc_at")

        INPUT_STATES.pop(user_id, None)
        show_edit_session_screen(user_id, chat_id, session_id)
        return True

    if field == "interval":
        minutes = parse_interval_minutes_from_text(message.text.strip())
        if not minutes:
            show_screen(user_id, chat_id, "Не понял интервал. Напиши, например: <code>30 минут</code>, <code>2 часа</code>, <code>3 дня</code>, <code>полчаса</code>.", None)
            return True
        data["interval_minutes"] = minutes
        mark_session_field_changed(s, "interval_minutes")
        INPUT_STATES.pop(user_id, None)
        show_edit_session_screen(user_id, chat_id, session_id)
        return True

    if field == "period":
        base_dt = None
        try:
            base_dt = datetime.strptime(data.get("next_local_at", ""), "%Y-%m-%d %H:%M").replace(tzinfo=ZoneInfo(data.get("timezone_name") or DEFAULT_TIMEZONE_NAME))
        except Exception:
            base_dt = None
        start_time, end_time, _explicit, duration_minutes = parse_interval_window_from_text(message.text.strip(), get_user_time_words(user_id), data.get("timezone_name") or DEFAULT_TIMEZONE_NAME, base_dt)
        data["window_start_time"] = start_time
        data["window_end_time"] = end_time
        if duration_minutes:
            try:
                start_dt = set_time_on_date(base_dt.date() if base_dt else datetime.now(ZoneInfo(data.get("timezone_name") or DEFAULT_TIMEZONE_NAME)).date(), start_time, ZoneInfo(data.get("timezone_name") or DEFAULT_TIMEZONE_NAME))
            except Exception:
                start_dt = None
            data["window_days"] = build_interval_window_days(duration_minutes, start_dt)
        else:
            data["window_days"] = ""
        mark_session_field_changed(s, "window_start_time", "window_end_time", "window_days")
        INPUT_STATES.pop(user_id, None)
        show_edit_session_screen(user_id, chat_id, session_id)
        return True

    if field == "break":
        txt = message.text.strip().lower().replace("ё","е")
        period_type = school_period_kind_from_text(txt)
        if "кажд" in txt and period_type == "lesson":
            data["reminder_kind"] = REMINDER_KIND_LESSON_EACH
            data["break_mode"] = "each"
            data["break_number"] = 0
        elif "кажд" in txt and period_type == "break":
            data["reminder_kind"] = REMINDER_KIND_BREAK_EACH
            data["break_mode"] = "each"
            data["break_number"] = 0
        else:
            n = extract_lesson_number(txt) if period_type == "lesson" else extract_break_number(txt)
            if not n:
                show_screen(user_id, chat_id, "Не понял номер перемены или урока. Напиши, например: <code>2 перемена</code>, <code>3 урок</code>, <code>каждая перемена</code> или <code>каждый урок</code>.", build_edit_input_cancel_markup(session_id))
                return True
            data["reminder_kind"] = REMINDER_KIND_LESSON_SINGLE if period_type == "lesson" else REMINDER_KIND_BREAK_SINGLE
            data["break_mode"] = "single"
            data["break_number"] = n
        mark_session_field_changed(s, "reminder_kind", "break_mode", "break_number")
        INPUT_STATES.pop(user_id, None)
        show_edit_session_screen(user_id, chat_id, session_id)
        return True

    if field =="every_n_days":
        txt =message .text .strip ()
        if not txt .isdigit ():
            show_screen (user_id ,chat_id ,"Нужно ввести число от 1 до 365.",None )
            return True 
        n =int (txt )
        if not (1 <=n <=365 ):
            show_screen (user_id ,chat_id ,"Число должно быть от 1 до 365.",None )
            return True 
        apply_repeat_to_session_data (data ,"every_n_days",str (n ))
        mark_session_field_changed (s ,"repeat_type","repeat_value","next_local_at","next_utc_at")
        INPUT_STATES .pop (user_id ,None )
        show_edit_session_screen (user_id ,chat_id ,session_id )
        return True 

    return False 


    # =========================================================
    # Создание напоминаний
    # =========================================================


def process_user_new_request (user_id :int ,chat_id :int ,source_text :str )->None :
    if not source_text .strip ():
        show_screen (user_id ,chat_id ,"Сообщение пустое.",build_main_nav_markup ())
        return 

    timezone_name ,timezone_title =get_user_timezone (user_id )
    custom_times =get_user_time_words (user_id )
    if is_complex_reminder_text(source_text):
        show_screen (
        user_id ,
        chat_id ,
        "🤖 Фраза похожа на сложную. Подключаю нейросеть для точного разбора...",
        None ,
        )
    else:
        show_screen (user_id ,chat_id ,"⏳ Обрабатываю...",None )

    mixed_break_items, mixed_break_err = parse_mixed_break_segments(user_id, source_text, timezone_name, timezone_title, custom_times)
    if mixed_break_items:
        parsed_many, err = mixed_break_items, None
    elif mixed_break_err:
        parsed_many, err = [], mixed_break_err
    else:
        break_parsed, break_err = local_parse_break_reminder(user_id, source_text, timezone_name, timezone_title)
        if break_parsed:
            parsed_many, err = [break_parsed], None
        elif break_err:
            parsed_many, err = [], break_err
        else:
            parsed_many ,err =local_or_yandex_parse_many (source_text ,timezone_name ,timezone_title ,custom_times )
    if not parsed_many :
        error_message =debug_text (
        "Ошибка обработки текста",
        (err or "Не удалось обработать сообщение.")
        +"\n\nПопробуйте написать проще.\n"
        "Примеры:\n• сегодня и завтра в 18:30 позвонить клиенту\n"
        "• каждую субботу и среду в 10:00 тренировка\n"
        "• каждый понедельник в 8:00 проверять расписание",
        )
        show_screen (user_id ,chat_id ,error_message ,build_main_nav_markup ())

        if err and "Ошибка распознавания"in err :
            threading .Timer (8.0 ,lambda :show_main_screen (user_id ,chat_id )).start ()
        return 

    parsed_many =dedupe_parsed_reminders (parsed_many )
    if parsed_many :
        record_parse_usage (user_id ,parsed_many [0 ].parse_method )

    if len (parsed_many )==1 :
        session_id =create_draft_session (user_id ,chat_id ,parsed_many [0 ],source_text )
        show_draft_preview (user_id ,chat_id ,session_id )
        return 

    show_main_screen (user_id ,chat_id )
    total =len (parsed_many )
    for number ,parsed in enumerate (parsed_many ,start =1 ):
        session_id =create_draft_session (user_id ,chat_id ,parsed ,parsed .reminder_text)
        show_independent_draft_preview (user_id ,chat_id ,session_id ,number ,total )
    return 


        # =========================================================
        # Голос
        # =========================================================

def voice_to_text (voice_bytes :bytes )->tuple [Optional [str ],Optional [str ]]:
    ogg_path =None 
    wav_path =None 
    try :
        temp_dir =tempfile .gettempdir ()
        unique =uuid .uuid4 ().hex 
        ogg_path =os .path .join (temp_dir ,f"{unique }.ogg")
        wav_path =os .path .join (temp_dir ,f"{unique }.wav")

        with open (ogg_path ,"wb")as f :
            f .write (voice_bytes )

        audio =AudioSegment .from_file (ogg_path ,format ="ogg")
        audio .export (wav_path ,format ="wav")

        with sr .AudioFile (wav_path )as source :
            audio_data =recognizer .record (source )
        text =recognizer .recognize_google (audio_data ,language ="ru-RU")
        return text .strip (),None 

    except sr .UnknownValueError :
        return None ,"Не удалось распознать речь."
    except sr .RequestError as e :
        return None ,f"Сервис распознавания недоступен: {e }"
    except Exception as e :
        return None ,f"Ошибка распознавания: {e }"
    finally :
        for p in (ogg_path ,wav_path ):
            try :
                if p and os .path .exists (p ):
                    os .remove (p )
            except Exception :
                pass 


                # =========================================================
                # Цикл напоминаний
                # =========================================================



def schedule_after_send (reminder_id :int ,user_id :int ,priority :str ,current_count :int ,max_count :int ,row :sqlite3 .Row )->None :
    """Обновляет счётчик отправок после уведомления."""
    conn =get_db ()
    cur =conn .cursor ()
    new_count =int(current_count or 0)+1
    if should_stop_due_repeats_by_school_period(row):
        cur.execute("""
            UPDATE denis_v4_reminders
            SET notify_count=?, max_notify_count=?, next_notify_utc='9999-12-31 23:59:59'
            WHERE id=? AND user_id=? AND status='pending'
        """, (new_count, max_count, reminder_id, user_id))
        conn.commit(); conn.close(); return

    if is_interval_kind_value(reminder_kind_from_row(row)):
        max_count = INTERVAL_NOTIFY_ATTEMPTS
        if new_count >= max_count:
            next_local, next_utc = compute_next_periodic_occurrence(row)
            if next_local and next_utc:
                cur.execute("""
                    UPDATE denis_v4_reminders
                    SET notify_count=0, max_notify_count=?, next_local_at=?, next_utc_at=?, next_notify_utc=?
                    WHERE id=? AND user_id=? AND status='pending'
                """, (max_count, next_local, next_utc, next_utc, reminder_id, user_id))
            else:
                cur.execute("""
                    UPDATE denis_v4_reminders
                    SET notify_count=?, max_notify_count=?, next_notify_utc='9999-12-31 23:59:59'
                    WHERE id=? AND user_id=? AND status='pending'
                """, (new_count, max_count, reminder_id, user_id))
        else:
            next_dt=datetime.now(timezone.utc)+timedelta(seconds=INTERVAL_NOTIFY_INTERVAL_SECONDS)
            cur.execute("""
                UPDATE denis_v4_reminders
                SET notify_count=?, max_notify_count=?, next_notify_utc=?
                WHERE id=? AND user_id=? AND status='pending'
            """, (new_count, max_count, next_dt.strftime("%Y-%m-%d %H:%M:%S"), reminder_id, user_id))
        conn.commit(); conn.close(); return

    max_count =max_notify_count_for_priority (priority ,user_id )
    if new_count >=max_count :
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET notify_count=?, max_notify_count=?, next_notify_utc='9999-12-31 23:59:59'
            WHERE id=? AND user_id=? AND status='pending'
        """,(new_count ,max_count ,reminder_id ,user_id ))
    else :
        next_dt =datetime .now (timezone .utc )+timedelta (seconds =notify_interval_seconds_for_priority (priority ,user_id ))
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET notify_count=?, max_notify_count=?, next_notify_utc=?
            WHERE id=? AND user_id=? AND status='pending'
        """,(new_count ,max_count ,next_dt .strftime ("%Y-%m-%d %H:%M:%S"),reminder_id ,user_id ))
    conn .commit ()
    conn .close ()

def close_one_time (reminder_id :int ,user_id :int ,final_status :str ="done")->None :
    clear_active_message_for_reminder (reminder_id ,user_id ,fallback_text ="Напоминание закрыто.")

    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        UPDATE denis_v4_reminders
        SET status=?, completed_at_utc=?, active_trigger_local_at='', active_trigger_utc_at='',
            active_message_chat_id=0, active_message_id=0
        WHERE id=? AND user_id=? AND status='pending'
    """,(final_status ,now_utc_str (),reminder_id ,user_id ))
    conn .commit ()
    conn .close ()



def save_recurring_next_cycle (reminder_id :int ,user_id :int ,next_local_at :str ,next_utc_at :str )->None :
    clear_active_message_for_reminder (reminder_id ,user_id ,fallback_text ="Напоминание перенесено на следующий цикл.")

    conn =get_db ()
    cur =conn .cursor ()
    cur .execute ("""
        UPDATE denis_v4_reminders
        SET next_local_at=?, next_utc_at=?, next_notify_utc=?, active_trigger_local_at='',
            active_trigger_utc_at='', active_message_chat_id=0, active_message_id=0, notify_count=0
        WHERE id=? AND user_id=? AND status='pending'
    """,(next_local_at ,next_utc_at ,next_utc_at ,reminder_id ,user_id ))
    conn .commit ()
    conn .close ()


def mark_current_cycle_closed (reminder_id :int ,user_id :int ,result_status :str )->tuple [bool ,Optional [sqlite3 .Row ]]:
    row =get_reminder_by_id (reminder_id ,user_id )
    if not row :
        return False ,None 
    if row ["active_trigger_utc_at"]:
        # Для одноразового напоминания после переноса итог фиксируем по актуальному перенесённому времени.
        # Для повторяющегося напоминания исходное active_trigger_* сохраняется, чтобы следующий повтор
        # считался от старого расписания, а не от времени переноса.
        if row ["repeat_type"]=="none":
            trigger_local =row ["next_local_at"]
            trigger_utc =row ["next_utc_at"]
        else:
            trigger_local =row ["active_trigger_local_at"]
            trigger_utc =row ["active_trigger_utc_at"]
        add_history (reminder_id ,user_id ,row ["topic"],trigger_local ,trigger_utc ,result_status )
    return True ,row 


def reminder_loop ()->None :
    while True :
        try :
            cleanup_old_history ()
            rows =get_due_reminders (now_utc_str ())
            for row in rows :
                try :
                    if (not row ["active_trigger_utc_at"]) or (is_interval_kind_value(reminder_kind_from_row(row)) and row ["active_trigger_utc_at"] != row ["next_utc_at"]):
                        conn =get_db ()
                        cur =conn .cursor ()
                        cur .execute ("""
                            UPDATE denis_v4_reminders
                            SET active_trigger_local_at=?, active_trigger_utc_at=?, interval_occurrence_count=COALESCE(interval_occurrence_count,0)+?
                            WHERE id=?
                        """,(row ["next_local_at"],row ["next_utc_at"],1 if is_interval_kind_value(reminder_kind_from_row(row)) else 0,row ["id"]))
                        conn .commit ()
                        conn .close ()
                        if is_interval_kind_value(reminder_kind_from_row(row)):
                            increment_summary_counters(int(row["user_id"]), "interval_triggers", 1)

                        # Перед повторной отправкой одного и того же напоминания удаляем его старое активное сообщение.
                        # Другие напоминания не затрагиваются, потому что у них другой reminder_id.
                    clear_active_message_for_reminder (row ["id"],row ["user_id"],fallback_text ="Напоминание заменено новым сообщением.")

                    max_count =interval_max_count_for_row (row)
                    attempt_number =int (row ["notify_count"]or 0 )+1 
                    is_final_attempt =attempt_number >=max_count 

                    due_markup =build_due_actions_markup (row ["id"],row)

                    sent =bot .send_message (
                    row ["user_id"],
                    render_due_notification_text (row,attempt_number),
                    reply_markup =due_markup ,
                    )
                    set_active_message_for_reminder (row ["id"],row ["user_id"],row ["user_id"],sent .message_id )

                    schedule_after_send (row ["id"],row ["user_id"],row ["priority"],row ["notify_count"],row ["max_notify_count"],row )
                except Exception as e :
                    print ("Send reminder error:",e )

            time .sleep (5 )

        except Exception as e :
            print ("Reminder loop error:",e )
            time .sleep (5 )


            # =========================================================
            # Хэндлеры
            # =========================================================

def ensure_user_ready (message :telebot .types .Message )->bool :
    register_user_from_message (message ,False )
    if not user_timezone_is_selected (message .from_user .id ):
        show_timezone_screen (message .from_user .id ,message .chat .id )
        return False 
    return True 



def greet_text (user_id :int )->str :
    _ ,current_timezone_title =get_user_timezone (user_id )
    text =(
    "<b>Привет! Я умный бот-напоминалка.</b>\n\n"
    "Я умею создавать одноразовые и повторяющиеся напоминания, понимать текст и голосовые сообщения, "
    "редактировать черновики и напоминать до подтверждения.\n\n"
    "<b>Как работать:</b>\n"
    "• отправь текст или голосовое сообщение\n"
    "• проверь черновик\n"
    "• подтверди или измени его\n"
    "• когда напоминание сработает — нажми Выполнено, Не выполнено или Перенести\n\n"
    )
    if user_timezone_is_selected (user_id ):
        text +=(
        f"Текущий часовой пояс: <b>{escape_html (current_timezone_title )}</b>.\n\n"
        "Можешь сразу отправить, например:\n"
        "• завтра в 18:30 позвонить клиенту\n"
        "• через 2 часа проверить задачу\n"
        "• каждый понедельник в 8:00 проверить расписание"
        )
    else :
        text +="Сначала выбери часовой пояс. Это нужно, чтобы напоминания приходили вовремя."
    return text 


def send_reply_keyboard (chat_id :int ,user_id :int )->None :
    """
    Нижняя reply-клавиатура привязана к приветственному сообщению.
    Это сообщение остаётся в чате, чтобы клавиатура не пропадала.
    """
    try :
        old =GREETING_MESSAGES .get (user_id )
        _ ,current_timezone_title =get_user_timezone (user_id )
        if user_timezone_is_selected (user_id ):
            text =(
            "<b>Привет! Я бот-напоминалка.</b>\n\n"
            "Создаю напоминания из текста и голосовых, понимаю повторы, приоритеты "
            "и могу сделать несколько напоминаний из одной фразы.\n\n"
            f"Часовой пояс: <b>{escape_html (current_timezone_title )}</b>."
            )
        else :
            text =(
            "<b>Привет! Я бот-напоминалка.</b>\n\n"
            "Создаю напоминания из текста и голосовых, понимаю повторы, приоритеты "
            "и могу сделать несколько напоминаний из одной фразы.\n\n"
            "Сначала выбери часовой пояс в сообщении ниже."
            )

        msg =bot .send_message (chat_id ,text ,reply_markup =build_main_menu_reply (user_id ))
        GREETING_MESSAGES [user_id ]={"chat_id":chat_id ,"message_id":msg .message_id }
    except Exception :
        pass 


@bot .message_handler (commands =["start"])



def start_handler (message :telebot .types .Message )->None :
    # /start всегда пересобирает экран с нуля.
    # Это чинит случай, когда пользователь очистил чат, а бот ещё помнит старые message_id.
    register_user_from_message (message ,True  )
    safe_delete_user_message (message )
    force_rebuild_start_screen (message .from_user .id ,message .chat .id )


@bot .message_handler (commands =["help"])
def help_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    show_help_screen (message .from_user .id ,message .chat .id )


@bot .message_handler (commands =["timezone","tz"])
def timezone_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    show_timezone_screen (message .from_user .id ,message .chat .id )


@bot .message_handler (commands =["list"])
def list_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    if ensure_user_ready (message ):
        show_list_screen (message .from_user .id ,message .chat .id ,False )


@bot .message_handler (commands =["today"])
def today_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    if ensure_user_ready (message ):
        show_list_screen (message .from_user .id ,message .chat .id ,True )


@bot .message_handler (commands =["stats"])
def stats_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    if ensure_user_ready (message ):
        show_stats_screen (message .from_user .id ,message .chat .id )


@bot .message_handler (commands =["clear"])
def clear_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    if ensure_user_ready (message ):
        show_screen (message .from_user .id ,message .chat .id ,"Удалить все активные напоминания?",build_clear_confirm_markup ())


@bot .message_handler (commands =["customization","customize"])
def customization_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    if ensure_user_ready (message ):
        show_customization_screen (message .from_user .id ,message .chat .id )


@bot .message_handler (func =lambda m :getattr (m ,"text",None )in ["📋 Список","📅 На сегодня","📊 Статистика","🎨 Кастомизация","ℹ️ Помощь"])
def menu_text_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )
    text =message .text or ""
    user_id =message .from_user .id
    chat_id =message .chat .id

    if text =="📋 Список":
        if ensure_user_ready (message ):
            show_list_screen (user_id ,chat_id ,False )
        return

    if text =="📅 На сегодня":
        if ensure_user_ready (message ):
            show_list_screen (user_id ,chat_id ,True )
        return

    if text =="📊 Статистика":
        if ensure_user_ready (message ):
            show_stats_screen (user_id ,chat_id )
        return

    if text =="🎨 Кастомизация":
        if ensure_user_ready (message ):
            show_customization_screen (user_id ,chat_id )
        return

    if text =="ℹ️ Помощь":
        show_help_screen (user_id ,chat_id )
        return



@bot .message_handler (content_types =["voice"])
def voice_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    if not ensure_user_ready (message ):
        return 
    if message .from_user .id in INPUT_STATES :
        safe_delete_user_message (message )
        show_screen (message .from_user .id ,message .chat .id ,"Во время ручного редактирования лучше отправить обычный текст.\n\nДля отмены напиши: Отмена",build_main_nav_markup ())
        return 

    safe_delete_user_message (message )
    try :
        file_info =bot .get_file (message .voice .file_id )
        voice_bytes =bot .download_file (file_info .file_path )
        show_screen (message .from_user .id ,message .chat .id ,"🎙 Обрабатываю голосовое...",None )

        text ,err =voice_to_text (voice_bytes )
        if not text :
            show_screen (
            message .from_user .id ,
            message .chat .id ,
            debug_text ("Ошибка распознавания голосового сообщения",err or "Неизвестная ошибка."),
            build_main_nav_markup (),
            )
            return 

        process_user_new_request (message .from_user .id ,message .chat .id ,text )

    except Exception as e :
        show_screen (
        message .from_user .id ,
        message .chat .id ,
        debug_text ("Ошибка голосового сообщения",str (e )),
        build_main_nav_markup (),
        )


@bot .message_handler (content_types =["photo"])
def photo_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    safe_delete_user_message (message )


@bot .message_handler (content_types =["text"])
def text_handler (message :telebot .types .Message )->None :
    register_user_from_message (message ,True )
    if not message .text :
        return 
    if message .text .startswith ("/"):
        return 
    if message .text in ["📋 Список","📅 На сегодня","📊 Статистика","🎨 Кастомизация","ℹ️ Помощь"]:
        return 
    if not ensure_user_ready (message ):
        safe_delete_user_message (message )
        return 
    if handle_edit_input (message ):
        safe_delete_user_message (message )
        return 

    safe_delete_user_message (message )
    process_user_new_request (message .from_user .id ,message .chat .id ,message .text )


    # =========================================================
    # Callback
    # =========================================================

@bot .callback_query_handler (func =lambda c :True )
def callback_handler (call :telebot .types .CallbackQuery )->None :
    register_user_from_telegram_user (call .from_user ,False )
    user_id =call .from_user .id 
    chat_id =call .message .chat .id 
    data =call .data 

    try :
        if data =="nav:main":
            bot .answer_callback_query (call .id )
            clear_help_document_message (user_id )
            show_main_screen (user_id ,chat_id )
            return 
        if data =="nav:list":
            bot .answer_callback_query (call .id )
            show_list_screen (user_id ,chat_id ,False )
            return 
        if data =="nav:today":
            bot .answer_callback_query (call .id )
            show_list_screen (user_id ,chat_id ,True )
            return 
        if data =="nav:stats":
            bot .answer_callback_query (call .id )
            show_stats_screen (user_id ,chat_id )
            return 
        if data =="nav:timezone":
            bot .answer_callback_query (call .id )
            show_timezone_screen (user_id ,chat_id )
            return 
        if data =="nav:customization":
            bot .answer_callback_query (call .id )
            show_customization_screen (user_id ,chat_id )
            return 
        if data =="nav:help":
            bot .answer_callback_query (call .id )
            show_help_screen (user_id ,chat_id )
            return 

        if data == "custom_nav:time":
            bot.answer_callback_query(call.id)
            show_time_words_screen(user_id, chat_id)
            return
        if data == "custom_nav:breaks":
            bot.answer_callback_query(call.id)
            show_breaks_days_screen(user_id, chat_id)
            return
        if data == "custom_nav:priorities":
            bot.answer_callback_query(call.id)
            show_priority_settings_screen(user_id, chat_id)
            return
        if data == "custom_priority:time_menu":
            bot.answer_callback_query(call.id)
            show_priority_time_settings_screen(user_id, chat_id)
            return
        if data == "custom_priority:count_menu":
            bot.answer_callback_query(call.id)
            show_priority_count_settings_screen(user_id, chat_id)
            return
        if data.startswith("custom_priority_time:set:"):
            priority = data.split(":", 2)[2]
            if priority not in PRIORITY_INTERVALS_SECONDS:
                bot.answer_callback_query(call.id, "Неизвестный приоритет")
                show_priority_settings_screen(user_id, chat_id)
                return
            INPUT_STATES[user_id] = {"mode":"custom_priority_interval", "priority":priority}
            bot.answer_callback_query(call.id)
            show_priority_interval_prompt(user_id, chat_id, priority)
            return
        if data.startswith("custom_priority_count:set:"):
            priority = data.split(":", 2)[2]
            if priority not in PRIORITY_MAX_NOTIFY_COUNT:
                bot.answer_callback_query(call.id, "Неизвестный приоритет")
                show_priority_settings_screen(user_id, chat_id)
                return
            INPUT_STATES[user_id] = {"mode":"custom_priority_count", "priority":priority}
            bot.answer_callback_query(call.id)
            show_priority_count_prompt(user_id, chat_id, priority)
            return
        if data.startswith("breaks:toggle:"):
            day=int(data.split(":")[-1])
            days=selected_break_days(user_id)
            if day in days:
                days.remove(day)
            else:
                days.add(day)
            bot.answer_callback_query(call.id)
            show_breaks_days_screen(user_id, chat_id)
            return
        if data == "breaks:configure":
            bot.answer_callback_query(call.id)
            show_break_times_screen(user_id, chat_id)
            return
        if data == "breaks:add":
            if not selected_break_days(user_id):
                bot.answer_callback_query(call.id,"Выбери дни")
                show_breaks_days_screen(user_id, chat_id)
                return
            INPUT_STATES[user_id]={"mode":"breaks_add"}
            bot.answer_callback_query(call.id)
            show_screen(
                user_id,
                chat_id,
                "<b>➕ Добавление перемен</b>\n\n"
                "Напиши время начала и конца каждой перемены с новой строки:\n"
                "<code>09:40-09:50\n10:30-10:45</code>\n\n"
                "Для отмены напиши: <b>Отмена</b>",
                build_break_times_markup(user_id),
            )
            return
        if data == "breaks:delete":
            if not selected_break_days(user_id):
                bot.answer_callback_query(call.id,"Выбери дни")
                show_breaks_days_screen(user_id, chat_id)
                return
            rows=[]
            for d in selected_break_days(user_id):
                rows.extend(get_school_breaks(user_id,d))
            markup=types.InlineKeyboardMarkup(row_width=2)
            seen=set()
            delete_buttons=[]
            for r in sorted(rows, key=lambda x:(int(x['break_index']), x['start_time'])):
                idx=int(r['break_index'])
                if idx in seen: continue
                seen.add(idx)
                delete_buttons.append(types.InlineKeyboardButton(f"{idx}. {r['start_time']}-{r['end_time']}", callback_data=f"breaks_delete:{idx}"))
            if delete_buttons:
                markup.add(*delete_buttons)
            markup.add(types.InlineKeyboardButton("↩️ Назад", callback_data="breaks:configure"))
            bot.answer_callback_query(call.id)
            show_screen(
                user_id,
                chat_id,
                "<b>🗑 Удаление перемены</b>\n\n"
                "Выбери номер перемены. Она удалится для всех выбранных дней.",
                markup,
            )
            return
        if data.startswith("breaks_delete:"):
            idx=int(data.split(":")[-1])
            deleted=delete_school_break_for_days(user_id, selected_break_days(user_id), idx)
            bot.answer_callback_query(call.id, "Удалено" if deleted else "Не найдено")
            show_break_times_screen(user_id, chat_id)
            return

        if data .startswith ("custom_time:set:"):
            word_key =data .split (":",2 )[2 ]
            if word_key not in TIME_WORD_COLUMNS :
                bot .answer_callback_query (call .id ,"Неизвестная настройка")
                show_customization_screen (user_id ,chat_id )
                return 
            INPUT_STATES [user_id ]={"mode":"custom_time","word_key":word_key }
            bot .answer_callback_query (call .id )
            show_screen (
            user_id ,
            chat_id ,
            f"<b>{escape_html(TIME_WORD_TITLES[word_key])}</b>\n\nНапиши новое время одним сообщением.\n\nПодходят форматы:\n• 08:30\n• 8 30\n• 830\n• 8 утра\n\nДля отмены напиши: <b>Отмена</b>",
            build_customization_markup (user_id ),
            )
            return 

        if data == "custom_time:reset":
            INPUT_STATES.pop(user_id, None)
            bot.answer_callback_query(call.id)
            show_screen(
                user_id,
                chat_id,
                "<b>🔄 Сброс настроек времени</b>\n\n"
                "Точно вернуть стандартные значения?\n\n"
                "🌅 Утро — 08:00\n"
                "☀️ День — 13:00\n"
                "🌆 Вечер — 18:00\n"
                "🌙 Ночь — 22:00",
                build_custom_reset_confirm_markup(),
            )
            return

        if data == "custom_time:reset:yes":
            reset_user_time_words(user_id)
            INPUT_STATES.pop(user_id, None)
            bot.answer_callback_query(call.id, "Сброшено")
            show_customization_screen(user_id, chat_id)
            return

        if data == "custom_time:reset:no":
            INPUT_STATES.pop(user_id, None)
            bot.answer_callback_query(call.id)
            show_customization_screen(user_id, chat_id)
            return

        if data .startswith ("tz:"):
            timezone_title ,timezone_name =TIMEZONE_OPTIONS [data ]
            upsert_user_timezone (user_id ,timezone_name ,timezone_title )

            if user_id not in GREETING_MESSAGES :
                send_reply_keyboard (chat_id ,user_id )

            bot .answer_callback_query (call .id ,"Часовой пояс сохранён")
            show_screen (
            user_id ,
            chat_id ,
            f"✅ Часовой пояс сохранён: <b>{escape_html (timezone_title )}</b>\n\n"
            "Теперь можно пользоваться нижними кнопками или просто отправить текст/голосовое напоминание.",
            build_main_nav_markup (),
            )
            return 

        if data =="clear:no":
            bot .answer_callback_query (call .id ,"Отменено")
            show_main_screen (user_id ,chat_id )
            return 

        if data =="clear:yes":
            count =clear_all_pending (user_id )
            bot .answer_callback_query (call .id ,"Готово")
            markup =types .InlineKeyboardMarkup ()
            markup .add (types .InlineKeyboardButton ("📋 К списку",callback_data ="nav:list"))
            markup .add (types .InlineKeyboardButton ("↩️ На главную",callback_data ="nav:main"))
            show_screen (user_id ,chat_id ,f"🗑 Удалено активных напоминаний: {count }",markup )
            return 

        if data .startswith ("draft_yandex_reparse:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id ,"Переразбираю")
            show_reparse_processing (user_id ,chat_id ,sid )
            process_yandex_reparse_for_draft (user_id ,chat_id ,sid )
            return 

        if data .startswith ("draft_confirm:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id ,"Сохраняю")
            process_session_confirm (user_id ,chat_id ,sid )
            return 

        if data .startswith ("bulk_confirm:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id ,"Сохраняю")
            process_session_confirm (user_id ,chat_id ,sid )
            return 

        if data .startswith ("bulk_edit:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id )
            show_screen (user_id ,chat_id ,"Выбери напоминание для изменения:",build_bulk_select_edit_markup (sid ))
            return 

        if data .startswith ("bulk_delete:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id )
            show_screen (user_id ,chat_id ,"Выбери напоминание, которое нужно удалить из черновика:",build_bulk_select_delete_markup (sid ))
            return 

        if data .startswith ("bulk_delete_select:"):
            _ ,parent_sid ,index_str =data .split (":")
            parent =get_session (parent_sid ,user_id )
            bot .answer_callback_query (call .id ,"Удалено из черновика")
            if not parent or parent .get ("mode")!="bulk_draft":
                show_main_screen (user_id ,chat_id )
                return 
            try :
                index =int (index_str )
            except Exception :
                show_bulk_draft_preview (user_id ,chat_id ,parent_sid )
                return 
            items =parent .get ("items",[])
            if 0 <=index <len (items ):
                items .pop (index )
            if not items :
                destroy_session (parent_sid )
                show_main_screen (user_id ,chat_id )
                return 
            if len (items )==1 :
                single_sid =convert_remaining_bulk_item_to_single_draft (user_id ,chat_id ,parent_sid )
                if single_sid :
                    show_draft_preview (user_id ,chat_id ,single_sid )
                else :
                    show_bulk_draft_preview (user_id ,chat_id ,parent_sid )
                return 
            show_bulk_draft_preview (user_id ,chat_id ,parent_sid )
            return 

        if data .startswith ("bulk_select:"):
            _ ,parent_sid ,index_str =data .split (":")
            item_sid =create_bulk_item_session (user_id ,chat_id ,parent_sid ,int (index_str ))
            bot .answer_callback_query (call .id )
            if not item_sid :
                show_bulk_draft_preview (user_id ,chat_id ,parent_sid )
                return 
            show_edit_session_screen (user_id ,chat_id ,item_sid )
            return 

        if data .startswith ("bulk_back:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id )
            show_bulk_draft_preview (user_id ,chat_id ,sid )
            return 

        if data .startswith ("bulk_cancel:"):
            sid =data .split (":",1 )[1 ]
            destroy_session (sid )
            bot .answer_callback_query (call .id )
            show_main_screen (user_id ,chat_id )
            return 

        if data .startswith ("bulk_item_confirm:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id )
            process_session_confirm (user_id ,chat_id ,sid )
            return 

        if data .startswith ("bulk_item_reset:"):
            sid =data .split (":",1 )[1 ]
            reset_session_changes (user_id ,sid )
            bot .answer_callback_query (call .id ,"Изменения сброшены")
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("bulk_item_back:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            parent_sid =s .get ("parent_session_id")if s else None 
            destroy_session (sid )
            bot .answer_callback_query (call .id )
            if parent_sid :
                show_bulk_draft_preview (user_id ,chat_id ,parent_sid )
            else :
                show_main_screen (user_id ,chat_id )
            return 

        if data .startswith ("draft_edit:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            if s and s .get ("independent_message_id"):
                safe_delete_message (s .get ("independent_chat_id",chat_id ),s ["independent_message_id"])
                s .pop ("independent_message_id",None )
                s .pop ("independent_chat_id",None )
            bot .answer_callback_query (call .id )
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("draft_reject:"):
            sid =data .split (":",1 )[1 ]
            destroy_session (sid )
            bot .answer_callback_query (call .id ,"Черновик удалён")
            show_main_screen (user_id ,chat_id )
            return 

        if data .startswith ("draft_reset:"):
            sid =data .split (":",1 )[1 ]
            if reset_session_changes (user_id ,sid ):
                bot .answer_callback_query (call .id ,"Изменения сброшены")
                show_edit_session_screen (user_id ,chat_id ,sid )
            else :
                bot .answer_callback_query (call .id )
                show_main_screen (user_id ,chat_id )
            return 

        if data .startswith ("draft_back_cancel:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            if s and s .get ("independent_message_id"):
                safe_delete_message (s .get ("independent_chat_id",chat_id ),s ["independent_message_id"])
            destroy_session (sid )
            bot .answer_callback_query (call .id ,"Черновик удалён")
            show_main_screen (user_id ,chat_id )
            return 

        if data .startswith ("draft_back:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            if s :
                s .pop ("temp_weekdays",None )
            INPUT_STATES .pop (user_id ,None )
            bot .answer_callback_query (call .id )
            show_draft_preview (user_id ,chat_id ,sid )
            return 

        if data .startswith ("saved_confirm:"):
            sid =data .split (":",1 )[1 ]
            bot .answer_callback_query (call .id )
            process_session_confirm (user_id ,chat_id ,sid )
            return 

        if data .startswith ("saved_reset:"):
            sid =data .split (":",1 )[1 ]
            if not reset_session_changes (user_id ,sid ):
                bot .answer_callback_query (call .id )
                show_main_screen (user_id ,chat_id )
                return 
            bot .answer_callback_query (call .id ,"Изменения сброшены")
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("saved_back:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            if s :
                s .pop ("temp_weekdays",None )
            INPUT_STATES .pop (user_id ,None )
            bot .answer_callback_query (call .id )
            back_from_saved_session (user_id ,chat_id ,sid )
            return 

        if data .startswith ("edit_menu_back:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            if s :
                s .pop ("temp_weekdays",None )
            bot .answer_callback_query (call .id )
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("edit_field:"):
            _ ,field ,sid =data .split (":")
            s =get_session (sid ,user_id )
            if not s :
                show_main_screen (user_id ,chat_id )
                return 

            if field =="interval":
                INPUT_STATES [user_id ]={"session_id":sid ,"field":"interval"}
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"<b>🔁 Интервал</b>\n\nНапиши новый интервал. Например: <code>30 минут</code>, <code>2 часа</code>, <code>3 дня</code>.\n\nДля отмены напиши <b>Отмена</b> или нажми «Назад».",build_edit_input_cancel_markup (sid) )
                return
            if field =="period":
                INPUT_STATES [user_id ]={"session_id":sid ,"field":"period"}
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"<b>⏱ Период</b>\n\nНапиши новый период. Например: <code>с 9 до 18</code>, <code>до вечера</code>, <code>в течение 5 дней</code>.\n\nДля отмены напиши <b>Отмена</b> или нажми «Назад».",build_edit_input_cancel_markup (sid) )
                return
            if field =="break":
                INPUT_STATES [user_id ]={"session_id":sid ,"field":"break"}
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"<b>🔔 Перемена или урок</b>\n\nНапиши, например: <code>2 перемена</code>, <code>каждая перемена</code>, <code>3 урок</code> или <code>каждый урок</code>.\n\nДля отмены напиши <b>Отмена</b> или нажми «Назад».",build_edit_input_cancel_markup (sid) )
                return

            if field =="priority":
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"Выбери новый приоритет:",build_priority_markup (sid ))
                return 
            if field =="category":
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"Выбери новую категорию:",build_category_markup (sid ))
                return 
            if field =="repeat":
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"Выбери тип повтора:",build_repeat_markup (sid ))
                return 

            INPUT_STATES [user_id ]={"session_id":sid ,"field":field }
            bot .answer_callback_query (call .id )

            if field =="topic":
                show_screen (user_id ,chat_id ,"Отправь новую тему одним сообщением.\n\nДля отмены напиши: Отмена",None )
            elif field =="text":
                show_screen (user_id ,chat_id ,"Отправь новый полный текст одним сообщением.\n\nДля отмены напиши: Отмена",None )
            elif field =="time":
                show_screen (
                user_id ,
                chat_id ,
                "Отправь новое время обычным языком.\n\nПримеры:\n• завтра в 19:30\n• 25 апреля в 18:00\n• на час позже\n• через 2 часа\n\nДля отмены напиши: Отмена",
                None ,
                )
            return 

        if data .startswith ("set_priority:"):
            _ ,value ,sid =data .split (":")
            s =get_session (sid ,user_id )
            if not s :
                show_main_screen (user_id ,chat_id )
                return 
            s ["data"]["priority"]=value 
            mark_session_field_changed (s ,"priority")
            bot .answer_callback_query (call .id ,"Приоритет обновлён")
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("set_category:"):
            _ ,value ,sid =data .split (":")
            s =get_session (sid ,user_id )
            if not s :
                show_main_screen (user_id ,chat_id )
                return 
            s ["data"]["category"]=value 
            mark_session_field_changed (s ,"category")
            bot .answer_callback_query (call .id ,"Категория обновлена")
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("set_repeat:"):
            _ ,value ,sid =data .split (":")
            s =get_session (sid ,user_id )
            if not s :
                show_main_screen (user_id ,chat_id )
                return 

            if value =="custom_weekdays":
                if s ["data"].get ("repeat_type")=="custom_weekdays":
                    current =s ["data"].get ("repeat_value","")
                else :
                    try :
                        current =str (datetime .strptime (s ["data"]["next_local_at"],"%Y-%m-%d %H:%M").weekday ())
                    except Exception :
                        current =""
                s ["temp_weekdays"]=current 
                bot .answer_callback_query (call .id )
                show_screen (
                user_id ,
                chat_id ,
                "Выбери дни недели.\n\nИзменения применятся только после кнопки «Готово». Если нажать «Назад», выбор отменится.",
                build_custom_weekdays_markup (sid ,current ),
                )
                return 

            if value =="every_n_days":
                INPUT_STATES [user_id ]={"session_id":sid ,"field":"every_n_days"}
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,"Введи число от 1 до 365.\n\nПример: 3",None )
                return 

            apply_repeat_to_session_data (s ["data"],value ,"")
            mark_session_field_changed (s ,"repeat_type","repeat_value","next_local_at","next_utc_at")
            bot .answer_callback_query (call .id ,"Повтор обновлён")
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("toggle_weekday:"):
            _ ,day_str ,sid =data .split (":")
            s =get_session (sid ,user_id )
            if not s :
                show_main_screen (user_id ,chat_id )
                return 

            if "temp_weekdays"not in s :
                s ["temp_weekdays"]=s ["data"].get ("repeat_value","")if s ["data"].get ("repeat_type")=="custom_weekdays"else ""

            chosen =set (parse_weekday_value (s .get ("temp_weekdays","")))
            day =int (day_str )
            if day in chosen :
                chosen .remove (day )
            else :
                chosen .add (day )

            s ["temp_weekdays"]=",".join (str (x )for x in sorted (chosen ))
            bot .answer_callback_query (call .id )
            show_screen (
            user_id ,
            chat_id ,
            "Выбери дни недели.\n\nИзменения применятся только после кнопки «Готово». Если нажать «Назад», выбор отменится.",
            build_custom_weekdays_markup (sid ,s ["temp_weekdays"]),
            )
            return 

        if data .startswith ("finish_weekdays:"):
            sid =data .split (":",1 )[1 ]
            s =get_session (sid ,user_id )
            if not s :
                show_main_screen (user_id ,chat_id )
                return 

            selected_value =s .get ("temp_weekdays","")
            if not selected_value :
                bot .answer_callback_query (call .id ,"Выбери хотя бы один день")
                show_screen (
                user_id ,
                chat_id ,
                "Нужно выбрать хотя бы один день недели.",
                build_custom_weekdays_markup (sid ,selected_value ),
                )
                return 

            apply_repeat_to_session_data (s ["data"],"custom_weekdays",selected_value )
            mark_session_field_changed (s ,"repeat_type","repeat_value","next_local_at","next_utc_at")
            s .pop ("temp_weekdays",None )
            bot .answer_callback_query (call .id ,"Повтор обновлён")
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("choose_action:"):
            _ ,mode ,list_type =data .split (":")
            bot .answer_callback_query (call .id )
            if mode =="edit":
                title ="Выбери напоминание для изменения:"
            elif mode =="view":
                title ="Выбери напоминание для просмотра:"
            else :
                title ="Выбери напоминание для удаления:"
            show_screen (user_id ,chat_id ,title ,build_select_reminder_markup (user_id ,mode ,list_type ))
            return 

        if data .startswith ("select_reminder:"):
            _ ,mode ,rid ,list_type =data .split (":")
            rid_i =int (rid )

            if mode =="edit":
                sid =create_saved_session (user_id ,chat_id ,rid_i ,"today"if list_type =="today"else "list")
                if not sid :
                    show_main_screen (user_id ,chat_id )
                    return 
                bot .answer_callback_query (call .id )
                show_edit_session_screen (user_id ,chat_id ,sid )
                return 

            row =get_reminder_by_id (rid_i ,user_id )
            if not row :
                show_main_screen (user_id ,chat_id )
                return 

            if mode =="view":
                bot .answer_callback_query (call .id )
                show_screen (user_id ,chat_id ,render_reminder_full_card (row ),build_view_reminder_markup (rid_i ,list_type,row ))
                return 

            bot .answer_callback_query (call .id )
            show_screen (
            user_id ,
            chat_id ,
            f"Удалить напоминание?\n\n<b>{escape_html (row ['topic'])}</b>\n{escape_html (row ['next_local_at'][5 :16 ])}",
            build_delete_confirm_markup (rid_i ,list_type ),
            )
            return 

        if data.startswith("interval_finish:"):
            _p, rid, list_type = data.split(":")
            row = get_reminder_by_id(int(rid), user_id)
            bot.answer_callback_query(call.id, "Серия завершена")
            if row and is_interval_kind_value(reminder_kind_from_row(row)) and row["repeat_type"] != "none":
                # Завершаем текущую серию и переносим на следующий подходящий день.
                end_local = (row["next_local_at"][:10] + " " + (row["window_end_time"] or "23:59")) if reminder_kind_from_row(row)==REMINDER_KIND_INTERVAL else row["next_local_at"]
                fake = dict(row)
                next_local, next_utc = compute_next_periodic_occurrence(row)
                if next_local and next_utc:
                    save_recurring_next_cycle(int(rid), user_id, next_local, next_utc)
                else:
                    close_one_time(int(rid), user_id, "done")
            elif row:
                close_one_time(int(rid), user_id, "done")
            show_list_screen(user_id, chat_id, list_type=="today")
            return

        if data .startswith ("view_edit:"):
            _ ,rid ,list_type =data .split (":")
            sid =create_saved_session (user_id ,chat_id ,int (rid ),"today"if list_type =="today"else "list")
            bot .answer_callback_query (call .id )
            if not sid :
                show_main_screen (user_id ,chat_id )
                return 
            show_edit_session_screen (user_id ,chat_id ,sid )
            return 

        if data .startswith ("view_delete:"):
            _ ,rid ,list_type =data .split (":")
            row =get_reminder_by_id (int (rid ),user_id )
            bot .answer_callback_query (call .id )
            if not row :
                show_main_screen (user_id ,chat_id )
                return 
            show_screen (
            user_id ,
            chat_id ,
            f"Удалить напоминание?\n\n<b>{escape_html (row ['topic'])}</b>\n{escape_html (row ['next_local_at'][5 :16 ])}",
            build_delete_confirm_markup (int (rid ),list_type ),
            )
            return 

        if data .startswith ("delete_confirm:"):
            _ ,rid ,list_type =data .split (":")
            ok =delete_pending_reminder (int (rid ),user_id )
            bot .answer_callback_query (call .id ,"Удалено"if ok else "Не найдено")
            show_list_screen (user_id ,chat_id ,list_type =="today")
            return 

        if data .startswith ("close_no_response:"):
            _ ,rid =data .split (":")
            reminder_id =int (rid )
            row =get_reminder_by_id (reminder_id ,user_id )

            clear_active_message_for_reminder (
            reminder_id ,
            user_id ,
            current_chat_id =chat_id ,
            current_message_id =call .message .message_id ,
            fallback_text ="Напоминание закрыто.",
            )

            if not row :
                bot .answer_callback_query (call .id ,"Закрыто")
                return 

            conn =get_db ()
            cur =conn .cursor ()

            if row ["repeat_type"]=="none":
                cur .execute ("""
                    UPDATE denis_v4_reminders
                    SET status='not_done', completed_at_utc=?,
                        active_trigger_local_at='', active_trigger_utc_at='',
                        active_message_chat_id=0, active_message_id=0
                    WHERE id=? AND user_id=? AND status='pending'
                """,(now_utc_str (),reminder_id ,user_id ))
            else :
                next_local ,next_utc =compute_next_occurrence (
                row ["repeat_type"],
                row ["repeat_value"],
                row ["next_local_at"],
                row ["timezone_name"],
                )
                cur .execute ("""
                    UPDATE denis_v4_reminders
                    SET notify_count=0, next_local_at=?, next_utc_at=?, next_notify_utc=?,
                        active_trigger_local_at='', active_trigger_utc_at='',
                        active_message_chat_id=0, active_message_id=0
                    WHERE id=? AND user_id=? AND status='pending'
                """,(next_local ,next_utc ,next_utc ,reminder_id ,user_id ))

            conn .commit ()
            conn .close ()

            bot .answer_callback_query (call .id ,"Закрыто")
            return 

        if data.startswith("interval_finish_due:"):
            _p, rid = data.split(":")
            reminder_id = int(rid)
            row = get_reminder_by_id(reminder_id, user_id)
            if not row or not is_interval_kind_value(reminder_kind_from_row(row)):
                bot.answer_callback_query(call.id, "Серия уже недоступна")
                safe_delete_message(chat_id, call.message.message_id)
                return
            bot.answer_callback_query(call.id, "Серия завершена")
            if row["repeat_type"] != "none":
                next_local, next_utc = compute_next_periodic_occurrence(row)
                if next_local and next_utc:
                    save_recurring_next_cycle(reminder_id, user_id, next_local, next_utc)
                else:
                    close_one_time(reminder_id, user_id, "done")
            else:
                close_one_time(reminder_id, user_id, "done")
            safe_delete_message(chat_id, call.message.message_id)
            return

        if data .startswith ("result:"):
            _ ,result_status ,rid =data .split (":")
            reminder_id =int (rid )
            ok ,row =mark_current_cycle_closed (reminder_id ,user_id ,result_status )
            if not ok or not row :
                bot .answer_callback_query (call .id ,"Напоминание уже недоступно")
                if not safe_delete_message (chat_id ,call .message .message_id ):
                    try :
                        bot .edit_message_text ("Закрыто.",chat_id =chat_id ,message_id =call .message .message_id )
                    except Exception :
                        pass 
                return 

            if is_interval_kind_value(reminder_kind_from_row(row)):
                conn=get_db(); cur=conn.cursor()
                if result_status=="done":
                    cur.execute("UPDATE denis_v4_reminders SET interval_done_count=COALESCE(interval_done_count,0)+1 WHERE id=?", (reminder_id,))
                elif result_status=="not_done":
                    cur.execute("UPDATE denis_v4_reminders SET interval_not_done_count=COALESCE(interval_not_done_count,0)+1 WHERE id=?", (reminder_id,))
                conn.commit(); conn.close()
                next_local,next_utc=compute_next_periodic_occurrence(row)
                if next_local and next_utc:
                    save_recurring_next_cycle(reminder_id,user_id,next_local,next_utc)
                elif row["repeat_type"]=="none":
                    close_one_time(reminder_id,user_id,result_status)
                else:
                    save_recurring_next_cycle(reminder_id,user_id,row["next_local_at"],row["next_utc_at"])
            elif row ["repeat_type"]=="none":
                close_one_time (reminder_id ,user_id ,result_status )
            else :
                repeat_base_local =row ["active_trigger_local_at"] if row ["active_trigger_local_at"] else row ["next_local_at"]
                next_local ,next_utc =compute_next_occurrence (row ["repeat_type"],row ["repeat_value"],repeat_base_local ,row ["timezone_name"])
                save_recurring_next_cycle (reminder_id ,user_id ,next_local ,next_utc )

            bot .answer_callback_query (call .id ,RESULT_TITLES .get (result_status ,"Готово"))
            clear_active_message_for_reminder (
            reminder_id ,
            user_id ,
            current_chat_id =chat_id ,
            current_message_id =call .message .message_id ,
            fallback_text ="✅ Напоминание закрыто.",
            )
            return 

        if data .startswith ("snooze_cancel:"):
            _ ,rid =data .split (":")
            reminder_id =int (rid )
            state =INPUT_STATES .get (user_id )or {}
            if state .get ("mode")=="snooze_reminder"and int (state .get ("reminder_id",0 )or 0 )==reminder_id:
                INPUT_STATES .pop (user_id ,None )
            row =get_reminder_by_id (reminder_id ,user_id )
            if not row :
                bot .answer_callback_query (call .id ,"Недоступно")
                safe_delete_message (chat_id ,call .message .message_id )
                return
            bot .answer_callback_query (call .id ,"Перенос отменён")
            try :
                bot .edit_message_text (
                render_due_notification_text (row),
                chat_id =chat_id,
                message_id =call .message .message_id,
                reply_markup =build_due_actions_markup (reminder_id,row),
                parse_mode ="HTML",
                )
            except Exception :
                show_screen (user_id ,chat_id ,render_due_notification_text (row),build_due_actions_markup (reminder_id,row))
            return

        if data .startswith ("snooze_custom:"):
            _ ,rid =data .split (":")
            reminder_id =int (rid )
            row =get_reminder_by_id (reminder_id ,user_id )
            if not row :
                bot .answer_callback_query (call .id ,"Недоступно")
                safe_delete_message (chat_id ,call .message .message_id )
                return 

            INPUT_STATES [user_id ]={
            "mode":"snooze_reminder",
            "reminder_id":reminder_id,
            "source_chat_id":chat_id,
            "source_message_id":call .message .message_id,
            "expires_at":time .time ()+600,
            }
            bot .answer_callback_query (call .id ,"Напиши, на сколько перенести")
            try :
                bot .edit_message_text (
                render_snooze_prompt_text (row),
                chat_id =chat_id,
                message_id =call .message .message_id,
                reply_markup =build_snooze_prompt_markup (reminder_id),
                parse_mode ="HTML",
                )
            except Exception :
                show_screen (user_id ,chat_id ,render_snooze_prompt_text (row),build_snooze_prompt_markup (reminder_id))
            return 

        bot .answer_callback_query (call .id ,"Неизвестное действие")

    except Exception as e :
        try :
            bot .answer_callback_query (call .id ,"Ошибка")
        except Exception :
            pass 
        show_screen (user_id ,chat_id ,debug_text ("Ошибка обработки кнопки",str (e )),build_main_nav_markup ())


        # =========================================================
        # Запуск
        # =========================================================

def main ()->None :
    init_db ()
    print ("✅ ЗАПУЩЕНА НОВАЯ ВЕРСИЯ С ЧИСТЫМИ ТАБЛИЦАМИ V4")
    print (f"✅ SQLite база V4: {DB_PATH}")
    threading .Thread (target =reminder_loop ,daemon =True ).start ()
    while True :
        try :
            bot .remove_webhook ()
            time .sleep (1 )
            print ("Бот запущен...")
            bot .infinity_polling (skip_pending =True ,timeout =60 ,long_polling_timeout =30 )
        except Exception as e :
            print ("Polling error:",e )
            time .sleep (5 )


if __name__ =="__main__":
    main ()
