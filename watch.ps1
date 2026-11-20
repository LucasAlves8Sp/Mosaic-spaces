# watch.ps1 -- build watcher for the MosaicSpaces Lean project.
#
# READ THIS BEFORE RUNNING. This script runs on your computer and executes a
# FIXED list of commands, all inside this folder, when a request file appears
# in ci\requests. It never runs a command taken from a request file: a request
# only selects one of the actions below and, for `build` and `lean`, names a
# Lake target or a .lean file inside this folder.
#
#   toolchain        elan show / lean --version / lake --version
#   update           lake update            (fetches Mathlib, writes lake-manifest.json)
#   cache            lake exe cache get     (downloads prebuilt Mathlib)
#   build <target>   lake build <target>
#   lean <file>      lake env lean <file>   (checks one file, writes nothing)
#   stop             ends the watcher
#
# Note that `lake build` and `lean` elaborate the Lean files in this folder,
# and Lean files can run code while they are checked. Only the files of this
# project are involved.
#
# Start:  powershell -ExecutionPolicy Bypass -File .\watch.ps1
# Stop:   Ctrl+C
$ErrorActionPreference = 'Continue'
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $root
$req  = Join-Path $root 'ci\requests'
$logs = Join-Path $root 'ci\logs'
New-Item -ItemType Directory -Force -Path $req, $logs | Out-Null
Write-Host "MosaicSpaces watcher: waiting for requests in $req  (Ctrl+C to stop)"
$running = $true
while ($running) {
  $files = Get-ChildItem -Path $req -Filter *.req -ErrorAction SilentlyContinue | Sort-Object Name
  foreach ($f in $files) {
    $name = $f.BaseName
    $done = Join-Path $logs "$name.done"
    if (Test-Path $done) { continue }
    $log  = Join-Path $logs "$name.log"
    $line = ''
    try { $line = ((Get-Content $f.FullName -TotalCount 1) -as [string]).Trim() } catch { $line = '' }
    $parts  = $line -split '\s+'
    $action = $parts[0]
    $arg    = ''
    if ($parts.Count -gt 1) { $arg = $parts[1] }
    $cmd = $null
    $argOk = ($arg -eq '') -or (($arg -match '^[A-Za-z0-9_][A-Za-z0-9_./+:-]*$') -and ($arg -notmatch '\.\.') -and ($arg -notmatch '^[A-Za-z]:'))
    if ($argOk) {
      switch ($action) {
        'toolchain' { $cmd = 'ver & elan show & lean --version & lake --version & git --version' }
        'update'    { $cmd = 'lake update' }
        'cache'     { $cmd = 'lake exe cache get' }
        'build'     { if ($arg -ne '') { $cmd = "lake build $arg" } }
        'lean'      { if ($arg -match '\.lean$') { $cmd = "lake env lean $arg" } }
        'stop'      { $running = $false; $cmd = 'echo watcher stopped' }
      }
    }
    $start = Get-Date
    if ($null -eq $cmd) {
      "rejected request: '$line'" | Set-Content -Encoding ascii $log
      $code = 97
    } else {
      Write-Host ("[{0}] {1}: {2}" -f (Get-Date -Format 'HH:mm:ss'), $name, $cmd)
      cmd /c "$cmd > `"$log`" 2>&1"
      $code = $LASTEXITCODE
    }
    $secs = [int]((Get-Date) - $start).TotalSeconds
    "exit=$code seconds=$secs command=$cmd" | Set-Content -Encoding ascii $done
    Write-Host ("            exit {0} after {1}s" -f $code, $secs)
  }
  Start-Sleep -Seconds 2
}
