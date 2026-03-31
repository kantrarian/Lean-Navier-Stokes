# PSD6CrossTerms.lean Fix — Session Progress

## Objective
Fix 4 pre-existing errors in `KissingNumber/PSD6CrossTerms.lean` (the `sum_AC`, `sum_AD`, `sum_BD`, `sum_CD` lemmas) so the full file builds and `phi6_kernel` can assemble.

## Status Summary

| Lemma | Target | Status | Approach |
|-------|--------|--------|----------|
| `sum_AD` | `= 15` | **FIXED** | r1-r15 + `factor3, hxn; simp only [mul_one]; norm_num` |
| `sum_AC` | `= 45 * s²` | **FIXED** (verified via TestAC.lean) | 45 r-rules (r1-r45) + `factor4` permutation variants + `hxn, ← hs; simp only [mul_one, one_mul]; ring` |
| `sum_BD` | `= 540` | **IN PROGRESS** (build running) | r1-r5 + `← Finset.mul_sum, factor2, hxn; norm_num` |
| `sum_CD` | `= 5400` | **IN PROGRESS** (build running) | `simp_rw [hxn]; simp only [mul_one]; norm_num` |

## Lemmas That Already Work (no changes needed)
- `sum_AA`, `sum_AB`, `sum_BA`, `sum_CA`, `sum_DA`
- `sum_BB` (via TestBBSplit decomposition)
- `sum_BC`, `sum_CB` (via TestBCSplit decomposition)
- `sum_CC` (via TestCCSplit decomposition)
- `sum_DB`, `sum_DC` (by symmetry from `sum_BD`, `sum_CD`)
- `sum_DD`
- `phi6_kernel` (assembles all 16 cross-terms)

## Detailed Fix Descriptions

### sum_AD (FIXED — lines 277-321)
- **Problem**: `norm_num` couldn't close the goal because intermediate sums `∑ x_a * x_a` remained.
- **Fix**: Added `simp only [mul_one]` before `norm_num` to clean up `(∑ x_a * x_a) * 1` → `∑ x_a * x_a` after `hxn` substitution.
- **Key tactics**: `simp_rw [r1, ..., r15, factor3, hxn]; simp only [mul_one]; norm_num`

### sum_AC (FIXED — lines 197-269)
- **Problem**: The original `hS1-hS6` block approach (manually grouping sums into 6 blocks) left unsolvable goals.
- **Fix**: Replaced with 45 r-rules normalizing all product orderings to `(x_i*y_i)*(x_j*y_j)*(x_a*x_a)*(x_b*x_b)`, then `factor4` + permutation variants (`factor4_acbd`, `factor4_adbc`, `factor4_bcad`, `factor4_bdac`, `factor4_cdab`) collapse the 4-fold sums.
- **Verified**: TestAC.lean builds with empty trace (success).
- **Key tactics**: `simp_rw [r1,...,r45, factor4, factor4_acbd,..., hxn, ← hs]; simp only [mul_one, one_mul]; ring`

### sum_BD (IN PROGRESS — lines 383-407)
- **Problem**: Two previous approaches failed:
  1. `simp_rw [r1,r2,r3, factor2, hxn]; simp only [mul_one]; norm_num` — `factor2` can't match swapped variable order or constant coefficients.
  2. `simp_rw [r1,r2,r3,r4]; simp only [← Finset.mul_sum, ← Finset.sum_mul, hxn, mul_one, one_mul]; norm_num` — `simp only` rearranges products into `x₁*(8*x₁)` and leaves inner sums `∑ᵢ x₁*xᵢ*xᵢ`.
- **Current approach being tested**: Single `simp_rw` call with all rules together:
  ```lean
  have r5 : ∀ a b, x.ofLp a * x.ofLp a * (x.ofLp b * x.ofLp b) = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, r4, r5, ← Finset.mul_sum, factor2, hxn]
  norm_num
  ```
  Key insight: putting `← Finset.mul_sum`, `factor2`, and `hxn` ALL in `simp_rw` (not `simp only`) prevents the product rearrangement issue.
- **Build**: Running as background task (ID: b79b680), ~10+ min expected.

### sum_CD (IN PROGRESS — lines 437-457)
- **Problem**: Not yet tested; the approach `simp_rw [hxn]; simp only [mul_one]; norm_num` is simpler because C6*D6 products, after if-collapse, leave only degree-2 x-terms where `hxn` directly substitutes `∑ x_a² = 1`.
- **Build**: Running as background task (ID: bab7419), ~10+ min expected.

## Infrastructure Created

### PSD6Defs.lean additions (built successfully)
- `factor4_acbd`, `factor4_adbc`, `factor4_bcad`, `factor4_bdac`, `factor4_cdab` — 5 permutation variants of `factor4` for all 6 orderings of 4 factors in quadruple sums.

### Test Files
- `TestAC.lean` — **VERIFIED** (builds clean). Standalone test of the sum_AC approach.
- `TestBD.lean` — **TESTING** (build running). Tests the sum_BD factor2 approach.
- `TestCD.lean` — **TESTING** (build running). Tests the sum_CD simp_rw[hxn] approach.

## MCP Encoding Fix
- **Problem**: All local MCP lean-lsp tools fail with `'charmap' codec can't decode byte 0x9d` on Windows (cp1252 vs UTF-8).
- **Fix applied**: Added `"PYTHONUTF8": "1"` and `"PYTHONIOENCODING": "utf-8"` to `.mcp.json` env section.
- **Status**: Fix NOT yet active — requires MCP server restart. Confirmed still failing this session.
- **Workaround**: Using `lake env lean` builds + trace files for error analysis.

## Where to Restart Next Session

### Immediate TODO
1. **Check TestBD and TestCD build results** (background tasks b79b680, bab7419):
   - If success (empty trace): approaches are verified, ensure PSD6CrossTerms.lean matches.
   - If failure: read trace files (`trace_bd4.txt`, `trace_cd2.txt`) for the unsolved goal, then craft new r-rules or different approach.

2. **If sum_BD fails again**, consider:
   - Adding more r-rules for patterns with constant coefficients (e.g., `8 * x_a * x_a * x_b * x_b`)
   - Using `Finset.sum_mul_distrib` to handle coefficient extraction differently
   - Splitting into sub-sums analogous to TestBBSplit/TestBCSplit approach

3. **If sum_CD fails**, consider:
   - Adding product normalization r-rules similar to sum_BD
   - Using `← Finset.mul_sum, factor2, hxn` approach (same as BD)

4. **Full build of PSD6CrossTerms.lean** once all 4 lemmas are verified individually.

5. **Restart MCP server** to pick up the `.mcp.json` encoding fix, then use `lean_goal` and `lean_diagnostic_messages` for faster iteration.

### Build Commands
```bash
# Test individual lemmas
lake env lean KissingNumber/TestBD.lean 2>&1 | tee trace_bd4.txt
lake env lean KissingNumber/TestCD.lean 2>&1 | tee trace_cd2.txt

# Full build of PSD6CrossTerms (only after all 4 fixes verified)
lake env lean KissingNumber/PSD6CrossTerms.lean 2>&1 | tee trace_psd6.txt

# Build everything
lake build KissingNumber.Summary
```

### Key Files
| File | Purpose |
|------|---------|
| `KissingNumber/PSD6CrossTerms.lean` | Main file with all 16 cross-term lemmas + phi6_kernel |
| `KissingNumber/PSD6Defs.lean` | Shared definitions (A6-D6, factor2-6, factor4 variants) |
| `KissingNumber/TestAC.lean` | Verified test for sum_AC approach |
| `KissingNumber/TestBD.lean` | Test for sum_BD approach (pending result) |
| `KissingNumber/TestCD.lean` | Test for sum_CD approach (pending result) |
| `.mcp.json` | MCP config with encoding fix (needs server restart) |
| `trace_bd3.txt` | Last TestBD failure trace (for reference) |

### Architecture Notes
- **D6** is independent of its first argument (constant — purely index-based ifs). This means BD and CD products only have x-variables (no y-variables beyond what's already collapsed).
- **factor2** lemma: `∑ₐ ∑_b f(a)*g(b) = (∑ f)*(∑ g)` — works ONLY when the body is a product where factor 1 depends only on variable 1 and factor 2 depends only on variable 2.
- **simp_rw vs simp only**: `simp_rw` applies rules left-to-right without rearranging existing terms. `simp only` can normalize/rearrange the expression, which sometimes creates patterns that no longer match expected lemmas. For product normalization, always prefer `simp_rw`.
