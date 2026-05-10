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

TELEGRAM_BOT_TOKEN =""
YANDEX_API_KEY =""
YANDEX_FOLDER_ID =""
YANDEX_MODEL_URI =os .getenv ("YANDEX_MODEL_URI","").strip ()or (
f"gpt://{YANDEX_FOLDER_ID }/yandexgpt-lite/latest"if YANDEX_FOLDER_ID else ""
)

APP_DIR =os .path .dirname (os .path .abspath (__file__ ))if "__file__"in globals ()else os .getcwd ()
DB_PATH =os .path .join (APP_DIR ,"denis_school_ip_clean_v4.sqlite3")
YANDEX_ENDPOINT =os .getenv ("YANDEX_ENDPOINT","").strip ()or "https://llm.api.cloud.yandex.net/foundationModels/v1/completion"

# История завершённых напоминаний хранится ограниченное время.
HISTORY_RETENTION_DAYS = 62

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

PRIORITY_TITLES ={"very_high":"🔥 Очень важно","high":"🔴 Важно","medium":"🟡 Обычно","low":"🟢 Не важно"}
PRIORITY_BUTTONS =[("🔥 Очень важно","very_high"),("🔴 Важно","high"),("🟡 Обычно","medium"),("🟢 Не важно","low")]
PRIORITY_INTERVALS_SECONDS ={"very_high":40 ,"high":60 ,"medium":300 ,"low":600 }
PRIORITY_MAX_NOTIFY_COUNT ={"very_high":15 ,"high":10 ,"medium":10 ,"low":10 }

TIME_WORD_DEFAULTS ={"morning":"08:00","day":"13:00","evening":"18:00","night":"22:00"}
TIME_WORD_TITLES ={"morning":"🌅 Утро","day":"☀️ День","evening":"🌆 Вечер","night":"🌙 Ночь"}
TIME_WORD_COLUMNS ={"morning":"morning_time","day":"day_time","evening":"evening_time","night":"night_time"}


def max_notify_count_for_priority (priority :str )->int :
    return PRIORITY_MAX_NOTIFY_COUNT .get (priority ,10 )


def notify_interval_seconds_for_priority (priority :str )->int :
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
            completed_at_utc TEXT NOT NULL DEFAULT ''
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
    ensure_column ("denis_v4_user_settings","updated_at_utc","updated_at_utc TEXT NOT NULL DEFAULT ''")

    cur .execute ("UPDATE denis_v4_user_settings SET morning_time='08:00' WHERE morning_time IS NULL OR morning_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET day_time='13:00' WHERE day_time IS NULL OR day_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET evening_time='18:00' WHERE evening_time IS NULL OR evening_time=''")
    cur .execute ("UPDATE denis_v4_user_settings SET night_time='22:00' WHERE night_time IS NULL OR night_time=''")

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
    ("snooze_count","snooze_count INTEGER NOT NULL DEFAULT 0"),
    ("last_snooze_text","last_snooze_text TEXT NOT NULL DEFAULT ''"),
    ("last_snooze_at_utc","last_snooze_at_utc TEXT NOT NULL DEFAULT ''"),
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

    conn .commit ()
    conn .close ()


init_db ()


def register_user_from_telegram_user (tg_user ,count_message :bool =False )->None :
    return


def register_user_from_message (message :telebot .types .Message ,count_message :bool =True )->None :
    return


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
    "max_notify_count":max_notify_count_for_priority (data ["priority"]),
    "active_trigger_local_at":"",
    "active_trigger_utc_at":"",
    "active_message_chat_id":0 ,
    "active_message_id":0 ,
    "next_notify_utc":data ["next_utc_at"],
    "created_at_utc":now_utc_str (),
    "completed_at_utc":"",
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
    "max_notify_count":max_notify_count_for_priority (data ["priority"]),
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
    boundary =(datetime .now (timezone .utc )-timedelta (days =HISTORY_RETENTION_DAYS )).strftime ("%Y-%m-%d %H:%M:%S")
    conn =get_db ()
    cur =conn .cursor ()

    cur .execute ("DELETE FROM denis_v4_reminder_history WHERE created_at_utc < ?",(boundary ,))

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
            return 
        except Exception :
            pass 

    sent =bot .send_message (chat_id ,text ,reply_markup =markup )
    SCREEN_MESSAGES [user_id ]={
    "chat_id":chat_id ,
    "message_id":sent .message_id ,
    "text":text ,
    "markup":markup ,
    }
    if prev and prev .get ("chat_id")==chat_id and prev .get ("message_id")!=sent .message_id :
        safe_delete_message (chat_id ,prev ["message_id"])


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
    t =text .lower ()
    if any (word in t for word in ["экзам","зачет","контрольн","олимпиад","тест","егэ","огэ"]):
        return "exam"
    if any (word in t for word in ["урок","пара","лекц","семинар","дз","домаш","реферат","доклад","лаба","лаборат","курсов","проект","учеб"]):
        return "study"
    if any (word in t for word in ["созвон","встреч","собран","совещан","команд","репетитор"]):
        return "meeting"
    if any (word in t for word in ["дедлайн","сдать","срок"]):
        return "deadline"
    if any (word in t for word in ["день рождения","поесть","спорт","трениров","врач","магазин","позвонить","личн","витамин"]):
        return "personal"
    return "other"


def classify_priority (text :str ,category :str )->str :
    t =text .lower ().replace ("ё","е")
    if any (word in t for word in ["очень важно","крайне важно","максимально важно","сверхважно","супер важно","критически важно"]):
        return "very_high"
    if category in {"exam","deadline"}:
        return "high"
    if any (word in t for word in ["срочно","обязательно","важно","не забыть","дедлайн"]):
        return "high"
    if any (word in t for word in ["потом","не срочно","если успею","необязательно"]):
        return "low"
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



def ask_yandex (messages :list [dict ],temperature :float =0.05 ,max_tokens :int =170 )->tuple [Optional [str ],Optional [str ]]:
    payload ={
    "modelUri":YANDEX_MODEL_URI ,
    "completionOptions":{"stream":False ,"temperature":temperature ,"maxTokens":max_tokens },
    "messages":messages ,
    }
    headers ={"Authorization":f"Api-Key {YANDEX_API_KEY }","Content-Type":"application/json"}

    try :
        response =requests .post (YANDEX_ENDPOINT ,headers =headers ,json =payload ,timeout =(5 ,60 ))
    except requests .Timeout :
        return None ,"Ошибка распознавания: нейросеть отвечает дольше минуты. Попробуйте сделать запрос проще."
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
        f"- 'ночь', 'ночью' без точного времени = {times['night']}.\n"
        "Если рядом есть точное время, например 'в 8 утра', используй точное время 08:00, а не настройку слова 'утро'."
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
6. Если пользователь указал дату без времени, поставь 10:00.
7. Если пользователь написал одно из слов времени без точного времени, используй настройки пользователя из блока выше.
8. "после обеда" используй как настройку слова "день".
9. "к вечеру" используй как настройку слова "вечер".
10. "завтра" — дата завтра из контекста.
11. "послезавтра" — дата послезавтра из контекста.
12. "через 2 часа", "через 30 минут", "через 3 дня" считай от текущего времени из контекста.
13. Если указан день недели без даты, выбери ближайшую будущую дату этого дня недели.
14. Если указан день и месяц без года, выбери ближайшую будущую такую дату.
15. reminder_text должен быть частью исходного текста, которая относится именно к этому напоминанию. Если напоминание одно — можно вернуть весь текст пользователя.
16. topic — короткая понятная тема без даты, времени и лишних слов.
17. Если фраза сложная или непонятная, не думай долго: верни JSON так, как понял. Если не понял дату/время — поставь datetime_local = "", но остальные поля заполни по смыслу.

КОМБИНИРОВАННЫЕ ФРАЗЫ:
1. Если пользователь говорит "каждую субботу и среду", "каждый понедельник и пятницу", "по вторникам и четвергам" — это ОДНО повторяющееся напоминание custom_weekdays, а не несколько напоминаний.
2. Массив reminders из нескольких объектов используй только для одноразовых разных дат: "сегодня и завтра", "сегодня и в субботу", "в понедельник и среду" без слов повтора.
3. Если пользователь перечисляет несколько одноразовых дат или разных дел, создай несколько объектов в reminders.
3.1. Разделяй разные одноразовые события по словам "а", "потом", "ещё", "еще", "также", а также по запятым и точкам с запятой, если рядом разные даты/дни недели/дела.
3.2. Фраза "в субботу мне в школу а в понедельник на работу" => два одноразовых напоминания: первое про школу в ближайшую субботу, второе про работу в ближайший понедельник.
3.3. Если общее время указано один раз, например "в субботу и понедельник в 9:00", примени 9:00 к каждому одноразовому напоминанию. Это НЕ повтор, если нет слов "каждый", "по", "еженедельно".
3.4. Если у каждого события своё время, например "в субботу в 9 школа, а в понедельник в 12 работа", создай два напоминания с разным временем.
4. "сегодня и завтра в 18:00 позвонить клиенту" => два одноразовых напоминания: сегодня 18:00 и завтра 18:00.
5. "сегодня, завтра и послезавтра в 9:00 пить витамины" => три одноразовых напоминания.
6. "сегодня и в субботу в 18:00 позвонить клиенту" => два одноразовых напоминания: сегодня 18:00 и ближайшая будущая суббота 18:00.
7. "в понедельник и среду в 8:00" без слов "каждый/по/еженедельно" => два одноразовых напоминания на ближайшие понедельник и среду.
8. Если есть слова "каждый", "каждую", "каждое", "по понедельникам", "еженедельно", тогда это повтор, а не несколько одноразовых дат.
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
19. "каждые 3 дня", "раз в 3 дня", "через каждые 3 дня" => every_n_days, repeat_value = "3".
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
4. Если указана дата без времени, ставь 10:00.
5. Если есть слова "утро", "день", "вечер", "ночь", "после обеда" или "к вечеру" без точного времени, используй настройки пользователя из блока выше.
6. "завтра", "послезавтра", "через 2 часа", "через 3 дня" нужно пересчитать в точную дату и время.
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



def extract_explicit_time_from_text(text: str) -> Optional[tuple[int, int]]:
    """
    Локальный приоритетный разбор времени.

    Если время удалось понять локально, используем его.
    Нейросеть берём только если локально время не найдено.
    """
    t = text.lower().replace("ё", "е").strip()
    t = re.sub(r"\s+", " ", t)

    if re.search(r"\b(в\s+)?полдень\b", t):
        return 12, 0
    if re.search(r"\b(в\s+)?полночь\b", t):
        return 0, 0

    patterns = [
        r"(?<!\d)([01]?\d|2[0-3])\s*[:.]\s*([0-5]\d)(?!\d)",
        r"(?<!\d)([01]?\d|2[0-3])\s*[-]\s*([0-5]\d)(?!\d)",
        r"(?<!\d)([01]?\d|2[0-3])\s*[чh]\s*([0-5]\d)(?!\d)",
        r"(?<!\d)([01]?\d|2[0-3])\s+([0-5]\d)(?!\d)",
    ]
    for pattern in patterns:
        m = re.search(pattern, t)
        if m:
            return int(m.group(1)), int(m.group(2))

    m = re.search(r"(?<!\d)([01]\d|2[0-3])([0-5]\d)(?!\d)", t)
    if m:
        return int(m.group(1)), int(m.group(2))

    m = re.search(r"\b(?:в|к|на)\s+([01]?\d|2[0-3])\s*(?:час(?:а|ов)?|утра|вечера|дня|ночи)?\b", t)
    if m:
        hour = int(m.group(1))
        tail = t[m.start():m.end()]
        if hour <= 11 and re.search(r"\b(вечера|ночи)\b", tail):
            hour += 12
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
    """
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


def detect_repeat_from_text (user_text :str )->Optional [tuple [str ,str ]]:
    """
    Локальная страховка после YandexGPT.
    Исправляет очевидные фразы с повторами:
    каждый/каждую/каждое/каждые, дни недели, будни, выходные, каждые N дней.
    """
    text =user_text .lower ().replace ("ё","е")
    text =re .sub (r"[^а-яa-z0-9\s,.-]"," ",text )
    text =re .sub (r"\s+"," ",text ).strip ()

    if re .search (r"\b(по\s+будням|в\s+будни|будние\s+дни|каждый\s+будний\s+день|каждые\s+будни)\b",text ):
        return "weekdays",""

    if re .search (r"\b(по\s+выходным|каждые\s+выходные|каждый\s+выходной|в\s+выходные|на\s+выходных)\b",text ):
        return "weekends",""

    if (
    re .search (r"\bсуббот[а-я]*\s*(и|,)\s*воскресень[а-я]*\b",text )
    or re .search (r"\bвоскресень[а-я]*\s*(и|,)\s*суббот[а-я]*\b",text )
    or re .search (r"\bсб\s*(и|,)\s*вс\b",text )
    or re .search (r"\bвс\s*(и|,)\s*сб\b",text )
    ):
        if re .search (r"\b(кажд|каждый|каждую|каждое|каждые|по|еженедельно|раз\s+в\s+неделю)\b",text ):
            return "weekends",""

    if re .search (r"\b(каждый\s+день|каждое\s+утро|каждый\s+вечер|каждую\s+ночь|ежедневно|каждые\s+сутки)\b",text ):
        return "daily",""

    n_match =re .search (r"\b(?:каждые|каждый|раз\s+в|через\s+каждые)\s+(\d{1,3})\s+(?:день|дня|дней|сутки|суток)\b",text )
    if n_match :
        n =int (n_match .group (1 ))
        if 1 <=n <=365 :
            return "every_n_days",str (n )

    weekday_patterns ={
    0 :[r"\bпонедельник[а-я]*\b",r"\bпн\b"],
    1 :[r"\bвторник[а-я]*\b",r"\bвт\b"],
    2 :[r"\bсред[а-я]*\b",r"\bср\b"],
    3 :[r"\bчетверг[а-я]*\b",r"\bчт\b"],
    4 :[r"\bпятниц[а-я]*\b",r"\bпт\b"],
    5 :[r"\bсуббот[а-я]*\b",r"\bсб\b"],
    6 :[r"\bвоскресень[а-я]*\b",r"\bвс\b"],
    }

    has_repeat_marker =bool (re .search (
    r"\b(кажд|каждый|каждую|каждое|каждые|по|еженедельно|раз\s+в\s+неделю|еженедельн)\b",
    text ,
    ))

    found_days =[]
    if has_repeat_marker :
        for day_num ,patterns in weekday_patterns .items ():
            if any (re .search (pattern ,text )for pattern in patterns ):
                found_days .append (day_num )

    found_days =sorted (set (found_days ))
    if found_days ==[5 ,6 ]:
        return "weekends",""
    if found_days :
        return "custom_weekdays",",".join (str (day )for day in found_days )

    if re .search (r"\b(каждый\s+месяц|каждого\s+месяца|раз\s+в\s+месяц|ежемесячно)\b",text ):
        return "monthly",""

    if re .search (r"\b(каждый\s+год|каждого\s+года|раз\s+в\s+год|ежегодно)\b",text ):
        return "yearly",""

    if re .search (r"\b(каждую\s+неделю|каждая\s+неделя|раз\s+в\s+неделю|еженедельно)\b",text ):
        return "weekly",""

    return None 



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

    return replace_time_in_local_at (local_at ,timezone_name ,10 ,0 )


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


def normalize_parsed (raw :dict ,user_text :str ,timezone_name :str ,custom_times :Optional [dict [str ,str ]]=None )->tuple [Optional [ParsedReminder ],Optional [str ]]:
    topic =str (raw .get ("topic","")).strip ()or "Напоминание"
    reminder_text =str (raw .get ("reminder_text","")).strip ()or normalize_spaces (user_text )
    category =str (raw .get ("category","")).strip ()or classify_category (user_text )
    priority =str (raw .get ("priority","")).strip ()or classify_priority (user_text ,category )
    repeat_type =str (raw .get ("repeat_type","")).strip ()or "none"
    repeat_value =str (raw .get ("repeat_value","")).strip ()
    datetime_local =str (raw .get ("datetime_local","")).strip ()

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
    if detected_repeat :
        repeat_type ,repeat_value =detected_repeat 

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

    local_at ,utc_at =apply_default_time_from_text (local_at ,user_text ,timezone_name ,custom_times )
    local_at ,utc_at =apply_month_day_if_needed (local_at ,user_text ,timezone_name ,repeat_type )

    tz =ZoneInfo (timezone_name )
    local_dt =datetime .strptime (local_at ,"%Y-%m-%d %H:%M").replace (tzinfo =tz )
    now_local =datetime .now (tz )

    # Важное исправление:
    # если нейросеть поставила сегодняшнее время, которое уже прошло,
    # считаем, что пользователь имел в виду ближайшее будущее — завтра в это же время.
    if repeat_type =="none"and local_dt <=now_local and local_dt .date ()==now_local .date ():
        local_dt =local_dt +timedelta (days =1 )
        local_at =local_dt .strftime ("%Y-%m-%d %H:%M")
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

    for item in raw_items:
        parsed ,err =normalize_parsed (item ,user_text ,timezone_name ,custom_times )
        if parsed :
            parsed_items .append (parsed )
        elif err :
            errors .append (err )

    if not parsed_items :
        return [],errors [0 ]if errors else "Нейросеть не вернула ни одного корректного напоминания."

    detected_repeat =detect_repeat_from_text (user_text )
    if detected_repeat :
        first =parsed_items [0 ]
        repeat_type ,repeat_value =detected_repeat 
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
    Может вернуть одно напоминание или несколько, если пользователь написал:
    "сегодня и завтра", "сегодня и в субботу", "понедельник и среда" и т.д.
    """
    result_text ,error =ask_yandex (
    [
    {"role":"system","text":"Ты извлекаешь одно или несколько напоминаний. Ответ строго JSON."},
    {"role":"user","text":build_prompt (user_text ,timezone_name ,timezone_title ,custom_times )},
    ],
    temperature =0.05 ,
    max_tokens =1000 ,
    )
    if error :
        return [],error 

    raw =extract_json (result_text or "")
    if raw :
        parsed_many ,err =normalize_many_reminders (raw ,user_text ,timezone_name ,custom_times )
        if parsed_many :
            return parsed_many ,None 

            # Запасной простой разбор. Он возвращает одиночное напоминание,
            # но normalize_many_reminders всё равно умеет принять его.
    result_text ,error =ask_yandex (
    [
    {"role":"system","text":"Минимально выдели напоминание. Ответ строго JSON."},
    {"role":"user","text":build_fallback_prompt (user_text ,timezone_name ,timezone_title ,custom_times )},
    ],
    temperature =0.05 ,
    max_tokens =120 ,
    )
    if error :
        return [],error 

    raw =extract_json (result_text or "")
    if not raw :
        return [],"Нейросеть не вернула корректный JSON."

    if "category"not in raw :
        raw ["category"]=classify_category (user_text )
    if "repeat_type"not in raw :
        raw ["repeat_type"]="none"
    if "repeat_value"not in raw :
        raw ["repeat_value"]=""

    return normalize_many_reminders (raw ,user_text ,timezone_name ,custom_times )


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


def build_customization_markup (user_id :int )->types .InlineKeyboardMarkup :
    times =get_user_time_words (user_id )
    markup =types .InlineKeyboardMarkup (row_width =1 )
    for key in ["morning","day","evening","night"]:
        markup .add (types .InlineKeyboardButton (
        f"{TIME_WORD_TITLES [key ]} — {times [key ]}",
        callback_data =f"custom_time:set:{key }",
        ))
    markup .add (types .InlineKeyboardButton ("🔄 Сбросить настройки времени",callback_data ="custom_time:reset"))
    markup .add (types .InlineKeyboardButton ("↩️ На главную",callback_data ="nav:main"))
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


def build_due_actions_markup (reminder_id :int )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("✅ Выполнено",callback_data =f"result:done:{reminder_id }"))
    markup .add (types .InlineKeyboardButton ("❌ Не выполнено",callback_data =f"result:not_done:{reminder_id }"))
    markup .add (types .InlineKeyboardButton ("⏰ Перенести",callback_data =f"snooze_custom:{reminder_id }"))
    return markup 




def build_draft_preview_markup (session_id :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =1 )
    markup .add (types .InlineKeyboardButton ("✅ Подтвердить",callback_data =f"draft_confirm:{session_id }"))
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
    markup .add (
    types .InlineKeyboardButton ("↩️ Сбросить изменения",callback_data =reset_callback ),
    types .InlineKeyboardButton ("⬅️ Назад",callback_data =back_callback ),
    )
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
    timer_line =render_time_until_line (row ['next_local_at'],row ['timezone_name'],row ['priority'])
    timer_text =f"{timer_line}\n"if timer_line else ""
    return (
    f"<b>{escape_html (row ['topic'])}</b>\n\n"
    f"<b>Текст:</b> {escape_html (row ['reminder_text'])}\n"
    f"<b>Когда:</b> {escape_html (format_human_datetime (row ['next_local_at'],row ['timezone_name']))}\n"
    f"{timer_text}"
    f"<b>Повтор:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}\n"
    f"<b>Приоритет:</b> {escape_html (PRIORITY_TITLES .get (row ['priority'],'🟡 Обычно'))}\n"
    f"<b>Категория:</b> {escape_html (CATEGORY_TITLES .get (row ['category'],'📌 Другое'))}"
    )


def build_view_reminder_markup (reminder_id :int ,list_type :str )->types .InlineKeyboardMarkup :
    markup =types .InlineKeyboardMarkup (row_width =2 )
    markup .add (
    types .InlineKeyboardButton ("✏️ Изменить",callback_data =f"view_edit:{reminder_id }:{list_type }"),
    types .InlineKeyboardButton ("🗑 Удалить",callback_data =f"view_delete:{reminder_id }:{list_type }"),
    )
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

def render_session_text (data :dict ,title :str )->str :
    timer_line =render_time_until_line (data ['next_local_at'],data ['timezone_name'],data ['priority'])
    timer_text =f"{timer_line}\n"if timer_line else ""
    return (
    f"<b>{escape_html (title )}</b>\n\n"
    f"<b>Тема:</b> {escape_html (data ['topic'])}\n"
    f"<b>Время:</b> {escape_html (format_human_datetime (data ['next_local_at'],data ['timezone_name']))}\n"
    f"{timer_text}"
    f"<b>Часовой пояс:</b> {escape_html (data ['timezone_title'])}\n"
    f"<b>Приоритет:</b> {escape_html (PRIORITY_TITLES [data ['priority']])}\n"
    f"<b>Категория:</b> {escape_html (CATEGORY_TITLES [data ['category']])}\n"
    f"<b>Повтор:</b> {escape_html (repeat_title (data ['repeat_type'],data ['repeat_value']))}\n"
    f"<b>Текст:</b> {escape_html (data ['reminder_text'])}"
    )


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
    times = get_user_time_words(user_id)
    text = (
        "<b>🎨 Кастомизация времени</b>\n\n"
        "Настрой, какое время бот будет подставлять вместо слов <b>утро</b>, <b>день</b>, <b>вечер</b> и <b>ночь</b>.\n\n"
        "Например: если <b>Утро — 09:30</b>, то фраза «завтра утром сделать дз» будет понята как завтра в 09:30.\n\n"
        f"🌅 <b>Утро:</b> {escape_html(times['morning'])}\n"
        f"☀️ <b>День:</b> {escape_html(times['day'])}\n"
        f"🌆 <b>Вечер:</b> {escape_html(times['evening'])}\n"
        f"🌙 <b>Ночь:</b> {escape_html(times['night'])}\n\n"
        "Нажми на нужную кнопку и отправь новое время текстом.\n"
        "Можно писать: <code>08:30</code>, <code>8 30</code>, <code>830</code>, <code>8 утра</code>."
    )
    show_screen(user_id, chat_id, text, build_customization_markup(user_id))


def show_help_screen (user_id :int ,chat_id :int )->None :
    times =get_user_time_words (user_id )
    text =(
    "<b>Помощь по боту</b>\n\n"
    "<b>Создание</b>\n"
    "Отправь текст или голосовое сообщение. Бот соберёт черновик: тему, время, приоритет, категорию, повтор и полный текст.\n\n"
    "<b>Понимаемые фразы</b>\n"
    "• завтра в 18:30\n"
    "• послезавтра утром\n"
    "• завтра вечером очень важно подготовиться\n"
    "• сегодня и завтра в 18:30\n"
    "• сегодня и в субботу в 18:00\n"
    "• через 2 часа\n"
    "• каждый понедельник в 8:00\n"
    "• каждую субботу и среду в 10:00\n"
    "• по будням в 7:30\n"
    "• каждые 3 дня в 20:00\n\n"
    "<b>Если время неполное</b>\n"
    "• дата без времени → 10:00\n"
    f"• утром → {escape_html (times ['morning'])}\n"
    f"• днём / после обеда → {escape_html (times ['day'])}\n"
    f"• вечером / к вечеру → {escape_html (times ['evening'])}\n"
    f"• ночью → {escape_html (times ['night'])}\n"
    "• только время → сегодня, если время ещё впереди, иначе завтра\n\n"
    "<b>Кастомизация</b>\n"
    "В разделе 🎨 Кастомизация можно настроить, какое время бот будет понимать под словами «утро», «день», «вечер» и «ночь».\n\n"
    "<b>Редактирование</b>\n"
    "Можно изменить тему, время, приоритет, категорию, полный текст и повтор.\n\n"
    "<b>Приоритет</b>\n"
    "🔥 Очень важно — повтор каждые 40 секунд, максимум 15 уведомлений\n"
    "🔴 Важно — повтор каждые 1 минуту\n"
    "🟡 Обычно — каждые 5 минут\n"
    "🟢 Не важно — каждые 10 минут\n"
    "Для обычных приоритетов максимум 10 уведомлений.\n\n"
    "<b>Команды</b>\n"
    "/start — запуск\n"
    "/timezone или /tz — изменить часовой пояс\n"
    "/list — все напоминания\n"
    "/today — на сегодня\n"
    "/stats — статистика\n"
    "/clear — очистить активные\n"
    "/help — помощь\n\n"
    "<b>Подробная инструкция</b>\n"
    "Ниже прикреплён Word-файл <b>«инструкция к боту»</b>, где подробно и понятно описано, как работает бот, как им пользоваться и какие технологии используются.\n\n"
    "<b>Нашли ошибку или есть предложение?</b>\n"
    "Напишите мне лично: @TOlllHOTA"
    )
    markup =types .InlineKeyboardMarkup ()
    markup .add (types .InlineKeyboardButton ("↩️ Назад",callback_data ="nav:main"))
    show_screen (user_id ,chat_id ,text ,markup )

    doc_path =os .path .join (APP_DIR ,"инструкция к боту.docx")
    if not os .path .exists (doc_path ):
        warning =(
        text +
        "\n\n❌ Файл инструкции пока не найден рядом с ботом. "
        "Положи файл <code>инструкция к боту.docx</code> в папку с <code>bottt.py</code>."
        )
        show_screen (user_id ,chat_id ,warning ,markup ,push_history =False )
        return

    try :
        with open (doc_path ,"rb")as doc_file :
            sent_doc =bot .send_document (
            chat_id ,
            doc_file ,
            caption ="📎 Полная инструкция к боту в формате Word.",
            parse_mode ="HTML",
            )
        HELP_DOCUMENT_MESSAGES [user_id ]={"chat_id":chat_id ,"message_id":sent_doc .message_id }
    except Exception as e :
        warning =text +"\n\n"+debug_text ("Не удалось отправить файл инструкции",str (e ))
        show_screen (user_id ,chat_id ,warning ,markup ,push_history =False )


def show_timezone_screen (user_id :int ,chat_id :int )->None :
    show_screen (user_id ,chat_id ,"Выбери часовой пояс.",build_timezone_markup ())


def show_stats_screen (user_id :int ,chat_id :int )->None :
    rows =get_all_active_reminders (user_id )
    category_counts =Counter (r ["category"]for r in rows )
    history_rows =get_recent_history (user_id ,7 )
    result_counts =Counter (r ["result_status"]for r in history_rows if r ["result_status"] in {"done","not_done","snoozed","deleted"})

    parts =["<b>Статистика</b>"]
    parts .append (f"Активных напоминаний: {len (rows )}\n")
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
            parts .append (
            f"• <b>{escape_html (row ['topic'])}</b>\n"
            f"  {escape_html (row ['next_local_at'][11 :16 ])} • {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}"
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


def create_draft_session (user_id :int ,chat_id :int ,parsed :ParsedReminder )->str :
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
    }
    SESSIONS [sid ]={"mode":"draft","user_id":user_id ,"chat_id":chat_id ,"source":"main","data":dict (data ),"original":dict (data )}
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
    }
    SESSIONS [sid ]={"mode":"saved","user_id":user_id ,"chat_id":chat_id ,"source":source ,"reminder_id":reminder_id ,"data":dict (data ),"original":dict (data )}
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

    sent =bot .send_message (
    chat_id ,
    render_session_text (s ["data"],f"Проверь напоминание {number } из {total }"),
    reply_markup =build_draft_preview_markup (session_id ),
    )
    s ["independent_message_id"]=sent .message_id 
    s ["independent_chat_id"]=chat_id 




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
            last_snooze_text=?, last_snooze_at_utc=?
        WHERE id=? AND user_id=? AND status='pending'
    """,(
        new_local_at ,new_utc_at ,new_utc_at ,
        max_notify_count_for_priority (row ["priority"]),
        details or "перенос",now_utc_str (),
        reminder_id ,user_id
    ))
    conn .commit ()
    conn .close ()

    return True


def handle_edit_input (message :telebot .types .Message )->bool :
    state =INPUT_STATES .get (message .from_user .id )
    if not state :
        return False 

    user_id =message .from_user .id 
    chat_id =message .chat .id 

    if state.get("mode") == "custom_time":
        safe_delete_user_message(message)

        if message.text.strip().lower() == "отмена":
            INPUT_STATES.pop(user_id, None)
            show_customization_screen(user_id, chat_id)
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
                build_customization_markup(user_id),
            )
            return True

        update_user_time_word(user_id, word_key, parsed_time)
        INPUT_STATES.pop(user_id, None)
        show_customization_screen(user_id, chat_id)
        return True

    if state .get ("mode")=="snooze_reminder":
        safe_delete_user_message (message )
        text_value =message .text .strip ()

        if text_value .lower ().replace ("ё","е")=="отмена":
            INPUT_STATES .pop (user_id ,None )
            show_screen (user_id ,chat_id ,"Перенос отменён. Уведомление осталось активным.",build_main_nav_markup ())
            return True

        if time .time ()>float (state .get ("expires_at",0 )):
            INPUT_STATES .pop (user_id ,None )
            show_screen (user_id ,chat_id ,"Время ожидания ввода переноса истекло. Нажми «Перенести» ещё раз.",build_main_nav_markup ())
            return True

        reminder_id =int (state .get ("reminder_id",0 ))
        row =get_reminder_by_id (reminder_id ,user_id )
        if not row :
            INPUT_STATES .pop (user_id ,None )
            show_screen (user_id ,chat_id ,"Напоминание уже недоступно.",build_main_nav_markup ())
            return True

        custom_times =get_user_time_words (user_id )
        new_local ,new_utc ,details ,err =parse_snooze_request (row ,text_value ,custom_times )
        if not new_local or not new_utc :
            show_screen (
            user_id ,chat_id ,
            "<b>⏰ Перенос напоминания</b>\n\n"
            "Не удалось понять, на сколько перенести. Напиши ещё раз.\n\n"
            "Примеры:\n"
            "• <code>30 минут</code>\n"
            "• <code>на 2 часа</code>\n"
            "• <code>на полчаса</code>\n"
            "• <code>завтра в 9</code>\n"
            "• <code>в понедельник в 8:30</code>\n\n"
            "Для отмены напиши: <b>Отмена</b>"
            + (f"\n\n<code>{escape_html (err)}</code>" if DEBUG and err else ""),
            build_main_nav_markup (),
            )
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
    show_screen (user_id ,chat_id ,"⏳ Обрабатываю...",None )

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

    if len (parsed_many )==1 :
        session_id =create_draft_session (user_id ,chat_id ,parsed_many [0 ])
        show_draft_preview (user_id ,chat_id ,session_id )
        return 

    show_main_screen (user_id ,chat_id )
    total =len (parsed_many )
    for number ,parsed in enumerate (parsed_many ,start =1 ):
        session_id =create_draft_session (user_id ,chat_id ,parsed )
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
    """
    После отправки уведомления обновляет счётчик.

    Новая логика:
    - обычные и важные напоминания отправляются до 10 раз;
    - очень важные отправляются до 15 раз;
    - перед каждой новой попыткой старое активное сообщение этого же напоминания удаляется;
    - последнее сообщение остаётся в чате с кнопками и ждёт действия пользователя;
    - статус «пропущено» больше автоматически не ставится.
    """
    conn =get_db ()
    cur =conn .cursor ()
    new_count =current_count +1 
    max_count =max_notify_count_for_priority (priority )

    if new_count >=max_count :
        cur .execute ("""
            UPDATE denis_v4_reminders
            SET notify_count=?, max_notify_count=?, next_notify_utc='9999-12-31 23:59:59'
            WHERE id=? AND user_id=? AND status='pending'
        """,(new_count ,max_count ,reminder_id ,user_id ))
    else :
        next_dt =datetime .now (timezone .utc )+timedelta (seconds =notify_interval_seconds_for_priority (priority ))
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
                    if not row ["active_trigger_utc_at"]:
                        conn =get_db ()
                        cur =conn .cursor ()
                        cur .execute ("""
                            UPDATE denis_v4_reminders
                            SET active_trigger_local_at=?, active_trigger_utc_at=?
                            WHERE id=?
                        """,(row ["next_local_at"],row ["next_utc_at"],row ["id"]))
                        conn .commit ()
                        conn .close ()

                        # Перед повторной отправкой одного и того же напоминания удаляем его старое активное сообщение.
                        # Другие напоминания не затрагиваются, потому что у них другой reminder_id.
                    clear_active_message_for_reminder (row ["id"],row ["user_id"],fallback_text ="Напоминание заменено новым сообщением.")

                    max_count =max_notify_count_for_priority (row ["priority"])
                    attempt_number =int (row ["notify_count"]or 0 )+1 
                    is_final_attempt =attempt_number >=max_count 

                    if is_final_attempt :
                        message_title ="🔔 <b>Напоминание ждёт подтверждения</b>"
                        message_footer =(
                        f"Сообщение {attempt_number } из {max_count }\n"
                        "Автоматические повторы завершены. Выбери действие ниже, когда увидишь напоминание."
                        )
                    else :
                        message_title ="🔔 <b>Напоминание ждёт подтверждения</b>"
                        message_footer =f"Сообщение {attempt_number } из {max_count }"
                    due_markup =build_due_actions_markup (row ["id"])

                    timer_line =render_time_until_line (row ['next_local_at'],row ['timezone_name'],row ['priority'])
                    timer_text =f"{timer_line}\n"if timer_line else ""
                    sent =bot .send_message (
                    row ["user_id"],
                    f"{message_title }\n\n"
                    f"<b>Тема:</b> {escape_html (row ['topic'])}\n"
                    f"<b>Время:</b> {escape_html (format_human_datetime (row ['next_local_at'],row ['timezone_name']))}\n"
                    f"{timer_text}"
                    f"<b>Часовой пояс:</b> {escape_html (row ['timezone_title'])}\n"
                    f"<b>Приоритет:</b> {escape_html (PRIORITY_TITLES .get (row ['priority'],'🟡 Обычно'))}\n"
                    f"<b>Категория:</b> {escape_html (CATEGORY_TITLES .get (row ['category'],'📌 Другое'))}\n"
                    f"<b>Повтор:</b> {escape_html (repeat_title (row ['repeat_type'],row ['repeat_value']))}\n"
                    f"<b>Текст:</b> {escape_html (row ['reminder_text'])}\n\n"
                    f"{message_footer }",
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
        if old and old .get ("chat_id")==chat_id :
            safe_delete_message (chat_id ,old ["message_id"])

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
    register_user_from_message (message ,True )
    safe_delete_user_message (message )

    send_reply_keyboard (message .chat .id ,message .from_user .id )

    if user_timezone_is_selected (message .from_user .id ):
        show_screen (
        message .from_user .id ,
        message .chat .id ,
        "Готово. Можно отправить текст или голосовое напоминание.\n\n"
        "Пример: <b>завтра в 18:30 позвонить клиенту</b>",
        build_main_nav_markup (),
        )
    else :
        show_screen (
        message .from_user .id ,
        message .chat .id ,
        "Выбери часовой пояс. Это нужно, чтобы напоминания приходили вовремя.",
        build_timezone_markup (),
        )


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
            destroy_session (sid )
            bot .answer_callback_query (call .id )
            if not show_previous_screen (user_id ,chat_id ):
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
                show_screen (user_id ,chat_id ,render_reminder_full_card (row ),build_view_reminder_markup (rid_i ,list_type ))
                return 

            bot .answer_callback_query (call .id )
            show_screen (
            user_id ,
            chat_id ,
            f"Удалить напоминание?\n\n<b>{escape_html (row ['topic'])}</b>\n{escape_html (row ['next_local_at'][5 :16 ])}",
            build_delete_confirm_markup (rid_i ,list_type ),
            )
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

            if row ["repeat_type"]=="none":
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
            show_screen (
            user_id ,
            chat_id ,
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
            "Для отмены напиши: <b>Отмена</b>",
            build_main_nav_markup (),
            )
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
