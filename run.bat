@echo off
rem 작업 스케줄러가 매일 07:00에 실행. 로그는 news\last_run.log
chcp 65001 >nul
set PYTHONIOENCODING=utf-8
cd /d "%~dp0"
"C:\Users\jhrhee\AppData\Local\Programs\Python\Python312\python.exe" fetch_news.py > last_run.log 2>&1
