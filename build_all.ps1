param(
  [string[]]$Modules = @(
    'HPDE_common',
    'HPDE_01_caccioppoli',
    'LHF_01_commutator',
    'LHF_02_scaling',
    'LHF_03_gaussian',
    'LHF_04_gronwall',
    'LHF_05_GN'
  ),
  [string]$LogDir = (Join-Path $PSScriptRoot 'build_logs')
)

$ErrorActionPreference = 'Stop'

if (!(Test-Path $LogDir)) {
  New-Item -ItemType Directory -Path $LogDir | Out-Null
}

$results = @()

foreach ($m in $Modules) {
  $path = Join-Path $PSScriptRoot $m
  if (!(Test-Path $path)) {
    $results += [pscustomobject]@{ module = $m; status = 'SKIP'; log = ''; note = 'not found' }
    continue
  }

  Write-Host "=== $m ===" -ForegroundColor Cyan
  $log = Join-Path $LogDir ("{0}.log" -f $m)

  Push-Location $path
  try {
    lake build 2>&1 | Tee-Object -FilePath $log
    if ($LASTEXITCODE -eq 0) {
      $results += [pscustomobject]@{ module = $m; status = 'OK'; log = $log; note = '' }
    } else {
      $results += [pscustomobject]@{ module = $m; status = 'FAIL'; log = $log; note = "exit=$LASTEXITCODE" }
    }
  } catch {
    $results += [pscustomobject]@{ module = $m; status = 'FAIL'; log = $log; note = $_.Exception.Message }
    throw
  } finally {
    Pop-Location
  }
}

$summaryPath = Join-Path $LogDir 'build_summary.txt'
$results | Format-Table -AutoSize | Out-String | Set-Content -Encoding utf8 $summaryPath
Write-Host "\nSummary written to $summaryPath" -ForegroundColor Green

# fail script if any FAIL
if (($results | Where-Object { $_.status -eq 'FAIL' }).Count -gt 0) {
  exit 1
}