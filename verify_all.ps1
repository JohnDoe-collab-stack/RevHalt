$root = $PWD.Path
$allFilesPath = Join-Path $root "all_files.txt"

if (Test-Path $allFilesPath) {
    $files = Get-Content $allFilesPath
} else {
    $files = Get-ChildItem -Recurse -Filter *.lean -File |
        Where-Object { $_.FullName -notmatch "\\\\.lake\\\\" -and $_.FullName -notmatch "\\\\build\\\\" } |
        ForEach-Object { $_.FullName }
}

foreach ($f in $files) {
    if ([string]::IsNullOrWhiteSpace($f)) { continue }
    # relative path
    $rel = $f.Replace($root + "\", "")
    # module conversion: RevHalt\Base.lean -> RevHalt.Base
    $mod = $rel.Replace(".lean", "").Replace("\", ".")
    
    Write-Host "Verifying module: $mod"
    lake build $mod
    if ($LASTEXITCODE -ne 0) {
        Write-Host "❌ FAILED: $mod" -ForegroundColor Red
        # Continue or exit? User asked to verify individually. I will continue to list all failures.
    } else {
        Write-Host "✅ PASS: $mod" -ForegroundColor Green
    }
}
