param([Parameter(Mandatory=$true)][string]$Module)
$ErrorActionPreference = 'Stop'
$taskRoot = 'C:/Users/17815/Documents/Codex/2026-11-11/w'
$mathRoot = 'C:/Users/17815/Desktop/论文/lean_deps/mathlib4-4.33.1'
$paths = @((Join-Path $mathRoot '.lake/build/lib/lean'))
Get-ChildItem -LiteralPath (Join-Path $mathRoot '.lake/packages') -Directory | ForEach-Object {
  $lib = Join-Path $_.FullName '.lake/build/lib/lean'
  if (Test-Path -LiteralPath $lib) { $paths += $lib }
}
$sourceRoot = Join-Path $taskRoot 'work/rotating_formal'
$buildRoot = Join-Path $sourceRoot 'build'
$output = Join-Path $buildRoot ($Module + '.olean')
New-Item -ItemType Directory -Force -Path (Split-Path -Parent $output) | Out-Null
$env:LEAN_PATH = (@($buildRoot) + $paths) -join ';'
Push-Location -LiteralPath $sourceRoot
try {
  & 'C:/Users/17815/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe' -o $output ($Module + '.lean')
  exit $LASTEXITCODE
} finally { Pop-Location }
