import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring

namespace Lax637351Proofs.PowerBounds

open Filter
open scoped Topology

noncomputable section

lemma nat_rpow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop

lemma power_absorb (C a b : ℝ) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  filter_upwards [(nat_rpow_tendsto (sub_pos.mpr hab)).eventually (eventually_ge_atTop C),
    eventually_ge_atTop (1 : ℕ)] with n h h1
  have hn : (0 : ℝ) < n := by exact_mod_cast h1
  have ht := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hn.le a)
  rwa [← Real.rpow_add hn, sub_add_cancel] at ht

lemma exponential_domination (C a b c eps : ℝ) (hb : 0 < b) (hc : 0 < c) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a * Real.exp (-b * (n : ℝ) ^ c) ≤ eps := by
  have hT := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / c) b hb).comp (nat_rpow_tendsto hc)
  have h' := tendsto_const_nhds (x := C) |>.mul hT
  rw [mul_zero] at h'
  have h := (tendsto_order.mp h').2 eps heps
  filter_upwards [h] with n hn
  change C * (((n : ℝ) ^ c) ^ (a / c) * Real.exp (-b * (n : ℝ) ^ c)) < eps at hn
  have ht : c * (a / c) = a := by field_simp
  rw [← Real.rpow_mul (by positivity), ht] at hn
  simpa only [← mul_assoc] using hn.le

lemma rpow_pow (x a : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (x ^ a) ^ m = x ^ (a * (m : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

lemma floor_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

lemma log_rpow_upper (x a : ℝ) (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ x ^ a / a := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx a)
  rw [Real.log_rpow hx] at h
  apply (le_div_iff₀ ha).mpr
  linarith only [h]

end
end Lax637351Proofs.PowerBounds
