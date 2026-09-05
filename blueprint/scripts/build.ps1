$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
Set-Location -LiteralPath $projectRoot
$taskLogRoot = $env:VBP_LOG_DIR
if (-not $taskLogRoot) {
    $taskLogRoot = Join-Path ([IO.Path]::GetTempPath()) ('verso-blueprint-' + [guid]::NewGuid())
}
New-Item -ItemType Directory -Force -Path $taskLogRoot | Out-Null
Write-Output "Build logs: $taskLogRoot"

function Invoke-Logged {
    param([string]$Label, [string]$Executable, [string[]]$Arguments)
    if ($Executable -eq 'lake') {
        $active = @(Get-Process lean,lake -ErrorAction SilentlyContinue)
        if ($active.Count -gt 0) {
            throw "Lean/Lake slot occupied by process ids: $($active.Id -join ', ')"
        }
    }
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & $Executable @Arguments 2>&1 | Tee-Object -FilePath (Join-Path $taskLogRoot "$Label.log")
    $code = $LASTEXITCODE
    $timer.Stop()
    [ordered]@{
        command = "$Executable $($Arguments -join ' ')"
        exit_code = $code
        wall_time_seconds = $timer.Elapsed.TotalSeconds
    } | ConvertTo-Json -Compress | Add-Content -LiteralPath (Join-Path $taskLogRoot 'commands.jsonl')
    if ($code -ne 0) { exit $code }
}

# At this Verso pin the bundled search assets retain Windows separators.
# Prepare their escaped destination, then copy them to the HTML's layout.
$escapedSearch = Join-Path $projectRoot '_out\static-web\search'
$siteSearch = Join-Path $projectRoot '_out\site\html-multi\-verso-search'
New-Item -ItemType Directory -Force -Path $escapedSearch | Out-Null

Invoke-Logged 'vbp-build' 'lake' @('exe', 'vbp', 'build')

New-Item -ItemType Directory -Force -Path $siteSearch | Out-Null
Get-ChildItem -LiteralPath $escapedSearch -File | Copy-Item -Destination $siteSearch -Force

Invoke-Logged 'public-sources' 'python' @('-B', (Join-Path $projectRoot 'scripts\public_sources.py'))
Invoke-Logged 'vbp-check' 'lake' @('exe', 'vbp', 'check')
Invoke-Logged 'check-tiers' 'python' @('-B', (Join-Path $projectRoot 'scripts\check_tiers.py'))

$required = @(
    (Join-Path $projectRoot '_out\site\html-multi\index.html'),
    (Join-Path $projectRoot '_out\site\html-multi\-verso-data\blueprint-manifest.json'),
    (Join-Path $projectRoot '_out\site\html-multi\-verso-data\blueprint-html-cache.json'),
    (Join-Path $siteSearch 'search-page.js')
)
foreach ($path in $required) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        throw "Verso Blueprint build did not produce required file: $path"
    }
}
