@echo off
setlocal ENABLEDELAYEDEXPANSION

set PROJECT=%~dp0..\project.json
set OUTDIR=%~dp0..\out
set LOGDIR=%~dp0..\logs
if not exist "%LOGDIR%" mkdir "%LOGDIR%"

set BUILD_ID=bd_%DATE:~10,4%%DATE:~4,2%%DATE:~7,2%_%TIME:~0,2%%TIME:~3,2%_%RANDOM%
set BUILD_ID=%BUILD_ID: =0%

echo Starting RTL build %BUILD_ID% > "%LOGDIR%\batch.log"
python3 "%~dp0..\axi4gen.py" -c "%PROJECT%" -o "%OUTDIR%" --log-format json --log-file "%LOGDIR%\build.jsonl" gen-rtl
set ERR=%ERRORLEVEL%
echo Exit: %ERR% (build_id=%BUILD_ID%)>> "%LOGDIR%\batch.log"
exit /b %ERR%