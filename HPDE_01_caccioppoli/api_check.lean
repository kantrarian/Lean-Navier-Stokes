import Mathlib

-- Verify these lemma names exist before proceeding
#check Finset.sum_sq_le_sq_sum_of_nonneg    -- May not exist with this name
#check Finset.inner_mul_le_norm_mul_norm    -- Alternative for C-S
#check Finset.sum_le_card_nsmul             -- Alternative
#check ContinuousLinearMap.opNorm_le_bound
#check ContinuousLinearMap.le_opNorm
#check pi_norm_le_iff_of_nonneg
#check norm_le_pi_norm
#check Convex.antitoneOn_of_deriv_nonpos
#check Real.exp_le_exp