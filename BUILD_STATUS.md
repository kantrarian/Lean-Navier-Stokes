# Build Status (baseline)

Root: `C:\v2_files\lean_proofs`  
Build style: **per-module Lake packages** (each module has its own `lakefile.lean`; there is no root `lakefile.lean`).

## Baseline builds (Phase 1)

Build logs are saved under `build_logs/`:
- Full logs: `build_logs/<module>.log`
- Summary JSON: `build_logs/build_summary.json`

### Summary table

| Module | Status | Notes |
|---|---:|---|
| `HPDE_common` | ✅ PASS | Baseline `lake build` succeeded. |
| `HPDE_01_caccioppoli` | ✅ PASS | Baseline `lake build` succeeded. |
| `LHF_01_commutator` | ❌ FAIL | Missing package entry file `LHF_01_commutator.lean` (Lake expects this file). See `build_logs/LHF_01_commutator.log`. |
| `LHF_02_scaling` | ❌ FAIL | Parse/syntax issues in `LHF_02_scaling/LHF_02_manual.lean` (notably use of `λ` as an identifier, plus cascading parse errors). See `build_logs/LHF_02_scaling.log`. |
| `LHF_03_gaussian` | ❌ FAIL | Missing package entry file `LHF_03_gaussian.lean` (Lake expects this file). See `build_logs/LHF_03_gaussian.log`. |
| `LHF_04_gronwall` | ✅ PASS | Baseline `lake build` succeeded. |
| `LHF_05_GN` | ✅ PASS | Baseline `lake build` succeeded. |

## Immediate next fixes (from baseline failures)
- **Create missing entry files**:
  - `LHF_01_commutator/LHF_01_commutator.lean` importing `LHF_01_commutator.LHF_01` (or `LHF_01_commutator.LHF_01_manual` depending on intended main file).
  - `LHF_03_gaussian/LHF_03_gaussian.lean` importing `LHF_03_gaussian.LHF_03` (or `LHF_03_gaussian.LHF_03_manual` depending on intended main file).
- **Fix `LHF_02_scaling/LHF_02_manual.lean` parsing**:
  - Replace binder name `λ` with `lam` (Lean treats `λ` as syntax, not an identifier).
  - Re-run `lake build` to see if remaining errors are real or cascaded from the parsing failure.


