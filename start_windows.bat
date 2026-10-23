@echo off
setlocal
cd /d "%~dp0"
title PADDOCK SCOUT
set "PYEXE="
rem 1) bundled portable Python (no install needed)
if exist "%~dp0runtime\python\python.exe" set "PYEXE="%~dp0runtime\python\python.exe""
rem 2) fallback: Python installed on this PC
if not defined PYEXE (
  where py >nul 2>nul && set "PYEXE=py -3"
)
if not defined PYEXE (
  python -c "import sys" >nul 2>nul && set "PYEXE=python"
)
if not defined PYEXE (
  echo.
  echo  [PADDOCK SCOUT] runtime\python was not found.
  echo  Please extract the whole ZIP file first, then run this file again.
  echo.
  pause
  exit /b 1
)
%PYEXE% "%~dp0sw_nas_watch.py" %*
if errorlevel 1 pause
