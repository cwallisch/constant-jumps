import Lax637351Proofs.ColumnNormBounds
import Lax637351Proofs.ResponseContinuity

namespace Lax637351Proofs.ColumnAverages

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ResponseContinuity
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def fractionScale (s : ℝ) : ℝ := if s = 0 then 1 else s⁻¹

lemma fraction_abs_of_weighted (i : Fin n) (s : ℝ) (hs : 0 ≤ s)
    (w : PredictionMeasure.Weights (Genotype n k)) :
    |fraction i w| ≤ fractionScale s * weighted (mutants i) s w := by
  by_cases h : s = 0
  · subst s
    simp [fractionScale, weighted, fraction]
    exact (abs_mass_le _).trans (variation_project _ _)
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm h)
    rw [fractionScale, if_neg h, ← div_eq_inv_mul, le_div_iff₀ hpos]
    have hh := mul_le_mul_of_nonneg_right (abs_mass_le (project (mutants i) w)) hs
    have hn := variation_nonneg w
    dsimp [weighted, fraction] at *
    nlinarith only [hh, hn]

lemma finite_average_abs (f : ℕ → ℝ) (H : ℕ) (hH : 0 < H) (B : ℝ)
    (h : ∀ t < H, |f t| ≤ B) : |(∑ t ∈ Finset.range H, f t) / (H : ℝ)| ≤ B := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  rw [abs_div, abs_of_nonneg hHR.le, div_le_iff₀ hHR]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have he := Finset.sum_le_sum (s := Finset.range H) (fun t ht ↦ h t (Finset.mem_range.mp ht))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (H : ℝ)] using he

lemma meanResponse_bound (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T) (c : ℝ) (hc : 0 ≤ c)
    (w h : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hwc : c * fraction i w ≤ 1) :
    |meanResponse i e H w h| ≤ fractionScale c * responseLimit T * weighted (mutants i) c h := by
  unfold meanResponse
  apply finite_average_abs _ H hH
  intro t ht
  have ht' : e * (t : ℝ) ≤ T := (mul_le_mul_of_nonneg_left (by exact_mod_cast ht.le) he.1).trans hT
  have h' := (uniform_norm_bounds i e he t T ht' c hc w w h hw hw hwc hwc).1
  apply (fraction_abs_of_weighted i c hc _).trans
  have hc' : 0 ≤ fractionScale c := by unfold fractionScale; split_ifs <;> positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h' hc'

lemma meanPotential_remainder (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T) (c : ℝ) (hc : 0 ≤ c)
    (w z : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hz : probability z)
    (hwc : c * fraction i w ≤ 1) (hzc : c * fraction i z ≤ 1) :
    |meanPotential i e H z - meanPotential i e H w - meanResponse i e H w (z - w)| ≤
      fractionScale c * remainderLimit T * weighted (mutants i) c (z - w) ^ 2 := by
  unfold meanPotential meanResponse
  rw [← sub_div, ← sub_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply finite_average_abs _ H hH
  intro t ht
  have ht' : e * (t : ℝ) ≤ T := (mul_le_mul_of_nonneg_left (by exact_mod_cast ht.le) he.1).trans hT
  have h' := (uniform_norm_bounds i e he t T ht' c hc w z (z - w) hw hz hwc hzc).2
  rw [← fraction_sub, ← fraction_sub]
  apply (fraction_abs_of_weighted i c hc _).trans
  have hc' : 0 ≤ fractionScale c := by unfold fractionScale; split_ifs <;> positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h' hc'

lemma meanResponse_continuity (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w z h : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hz : probability z) :
    |meanResponse i e H z h - meanResponse i e H w h| ≤
      6 * T * Real.exp (6 * T) * variation (z - w) * variation h := by
  unfold meanResponse
  rw [← sub_div, ← Finset.sum_sub_distrib]
  apply finite_average_abs _ H hH
  intro t ht
  rw [← fraction_sub]
  apply ((abs_mass_le _).trans (variation_project (mutants i) _)).trans
  have ht' : e * (t : ℝ) ≤ T := (mul_le_mul_of_nonneg_left (by exact_mod_cast ht.le) he.1).trans hT
  have hp := (one_le_exp_bound (3 * e) (2 * t) (by linarith only [he.1])).trans
    (Real.exp_le_exp.mpr (show (3 * e) * ((2 * t : ℕ) : ℝ) ≤ 6 * T by push_cast; nlinarith only [ht']))
  have hresp := response_continuity (replaceKernel i) e he w z h hw hz t
  apply hresp.trans
  have ha : 0 ≤ (1 + 3 * e) ^ (2 * t) := by have := he.1; positivity
  have hT0 : 0 ≤ T := (mul_nonneg he.1 (Nat.cast_nonneg t)).trans ht'
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left ht' (by norm_num : (0 : ℝ) ≤ 6)) hp ha
    (by positivity : 0 ≤ 6 * T)
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (variation_nonneg (z - w))) (variation_nonneg h)
  nlinarith only [hc]

lemma meanPotential_lipschitz (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w z : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hz : probability z) :
    |meanPotential i e H z - meanPotential i e H w| ≤ Real.exp (3 * T) * variation (z - w) := by
  unfold meanPotential
  rw [← sub_div, ← Finset.sum_sub_distrib]
  apply finite_average_abs _ H hH
  intro t ht
  rw [← fraction_sub]
  apply ((abs_mass_le _).trans (variation_project (mutants i) _)).trans
  have h' (v : PredictionMeasure.Weights (Genotype n k)) (hv : probability v) (s : ℕ) :
      weighted (mutants i) 0 (predict (replaceKernel i) e s v) ≤ 1 := by
    simp [weighted, variation_probability (predict_probability _ e he v hv s)]
  have h := (iterate_bounds (replaceKernel i) (mutants (k := k) i) (replace_resident i k)
    (c := 0) (by norm_num) he w z (z - w) 1 t (fun s _ ↦ h' w hw s) (fun s _ ↦ h' z hz s)).1
  simp only [weighted, zero_mul, add_zero, one_pow, mul_one] at h
  apply h.trans
  have ht' : e * (t : ℝ) ≤ T := (mul_le_mul_of_nonneg_left (by exact_mod_cast ht.le) he.1).trans hT
  have hp := (one_le_exp_bound (3 * e) t (by linarith only [he.1])).trans
    (Real.exp_le_exp.mpr (show (3 * e) * t ≤ 3 * T by nlinarith only [ht']))
  exact mul_le_mul_of_nonneg_right hp (variation_nonneg _)

end
end Lax637351Proofs.ColumnAverages
