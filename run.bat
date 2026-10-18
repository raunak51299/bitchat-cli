@echo off
rem bitchat-cli launcher: (re)builds the venv if missing or stale
rem (e.g. the python it was built against was upgraded/removed), then starts chat.
cd /d "%~dp0"

rem prefer the py launcher so a fresh python install keeps working
set "PY=python"
py -3 --version >nul 2>&1
if not errorlevel 1 set "PY=py -3"

rem fast path: venv exists and its packages still import
if exist .venv\Scripts\python.exe (
    .venv\Scripts\python -c "import websockets, cryptography" >nul 2>&1
    if not errorlevel 1 goto run
)

rem missing or broken venv: rebuild with the current python
echo setting up python environment ^(first run, or after a python update^)...
if exist .venv rmdir /s /q .venv
%PY% -m venv .venv
.venv\Scripts\python -m pip install --disable-pip-version-check -r requirements.txt

:run
.venv\Scripts\python bitchat.py %*
