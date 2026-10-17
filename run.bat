@echo off
rem bitchat-cli launcher: bootstraps the venv on first run, then starts chat.
cd /d "%~dp0"
if not exist .venv (
    echo setting up python environment ^(first run^)...
    python -m venv .venv
    .venv\Scripts\python -m pip install --disable-pip-version-check -r requirements.txt
)
.venv\Scripts\python bitchat.py %*
