$files = Get-Content all_files.txt
$root = $PWD.Path
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
