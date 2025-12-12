# Lean-Navier-Stokes (Lean 4)

Lean 4 formalization artifacts supporting the analytic components of the \(\Lambda_L\) / spectral-lock Navier--Stokes paper series.

## What this repo contains
This repository is organized as a **collection of small Lake projects**, one per module. Each module directory contains its own:
- `lean-toolchain`
- `lakefile.lean`
- `lake-manifest.json`

### Suites
- **LHF\_\***: â€œlow-hanging fruitâ€ geometric/analytic chassis components
- **HPDE\_\***: â€œheavy PDEâ€ infrastructure components
- **HPDE\_common**: shared definitions used across modules

## Build prerequisites
- Install `elan` (Lean toolchain manager) and ensure `lake` is available.

## Build a single module
Each module is a standalone Lake project. Example:

```powershell
cd HPDE_01_caccioppoli
lake build
```

## Build all key modules (PowerShell)
From the repo root:

```powershell
$mods = @(
  'HPDE_01_caccioppoli','HPDE_02_weighted','HPDE_03_logsob','HPDE_04_campanato',
  'HPDE_common',
  'LHF_01_commutator','LHF_02_scaling','LHF_03_gaussian','LHF_04_gronwall','LHF_05_GN','LHF_06_LSI','LHF_07_campanato'
)
foreach ($m in $mods) {
  Write-Host "=== $m ==="
  Push-Location $m
  lake build
  Pop-Location
}
```

## Status (high level)
Some modules are **sorry-free**, while certain deep analytic facts are isolated as **explicit axioms** (e.g. Gaussian analytic infrastructure, Campanato embeddings, A\(_2\) power-weight fact). See the accompanying formal-verification summary documents in this repo and the LaTeX â€œFormal Verification Supplementâ€ distributed with the papers.

## License
See `LICENSE`.