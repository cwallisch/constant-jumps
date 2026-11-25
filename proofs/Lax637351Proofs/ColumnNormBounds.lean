import Lax637351Proofs.ColumnPrediction

namespace Lax637351Proofs.ColumnNormBounds

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def normLimit (T : ℝ) : ℝ := 1 + Real.exp (2 * T)

def responseLimit (T : ℝ) : ℝ := Real.exp (3 * normLimit T ^ 2 * T)

def remainderLimit (T : ℝ) : ℝ := 3 * normLimit T * T * (responseLimit T) ^ 2

lemma one_le_exp_bound (a : ℝ) (t : ℕ) (ha : 0 ≤ a) : (1 + a) ^ t ≤ Real.exp (a * t) := by
  have hh := pow_le_pow_left₀ (show 0 ≤ 1 + a by positivity)
    (by simpa only [add_comm] using Real.add_one_le_exp a) t
  simpa only [← Real.exp_nat_mul, mul_comm] using hh

lemma one_sub_pow_lower (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1 / 2) (t : ℕ) :
    Real.exp (-2 * e * t) ≤ (1 - e) ^ t := by
  have h : 0 < 1 - e := by linarith [he.2]
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
  rw [Real.log_inv] at hh
  have hq : (1 - e)⁻¹ ≤ 1 + 2 * e := by
    rw [← one_div, div_le_iff₀ h]
    nlinarith only [he.1, he.2, mul_nonneg he.1 (show 0 ≤ 1 - 2 * e by linarith only [he.2])]
  have he' : Real.exp (-2 * e) ≤ 1 - e := by
    rw [← Real.exp_log h]
    exact Real.exp_le_exp.mpr (by linarith only [hh, hq])
  have ht := pow_le_pow_left₀ (Real.exp_pos _).le he' t
  simpa only [← Real.exp_nat_mul, mul_comm (t : ℝ)] using ht

lemma meanPotential_bounds (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1 / 2)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    Real.exp (-2 * T) * fraction i w ≤ meanPotential i e H w ∧
      meanPotential i e H w ≤ Real.exp (2 * T) * fraction i w := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hf := (fraction_bounds i w hw).1
  have h (t : ℕ) (ht : t ∈ Finset.range H) :
      Real.exp (-2 * T) * fraction i w ≤ fraction i (predict (replaceKernel i) e t w) ∧
        fraction i (predict (replaceKernel i) e t w) ≤ Real.exp (2 * T) * fraction i w := by
    have ht' : (t : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp ht).le
    have hscale := mul_le_mul_of_nonneg_left ht' he.1
    have hm := fraction_predict i e ⟨he.1, by linarith [he.2]⟩ w hw t
    constructor
    · have hp := (Real.exp_le_exp.mpr (show -2 * T ≤ -2 * e * t by linarith only [hscale, hT])).trans
        (one_sub_pow_lower e he t)
      exact (mul_le_mul_of_nonneg_right hp hf).trans hm.1
    · have hp := (one_le_exp_bound (2 * e) t (by linarith only [he.1])).trans
        (Real.exp_le_exp.mpr (show (2 * e) * t ≤ 2 * T by linarith only [hscale, hT]))
      exact hm.2.trans (mul_le_mul_of_nonneg_right hp hf)
  constructor
  · apply (le_div_iff₀ hHR).mpr
    have hs := Finset.sum_le_sum (fun t ht ↦ (h t ht).1)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (H : ℝ)] using hs
  · apply (div_le_iff₀ hHR).mpr
    have hs := Finset.sum_le_sum (fun t ht ↦ (h t ht).2)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (H : ℝ)] using hs

lemma prediction_norm_bound (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (T : ℝ) (t : ℕ) (hT : e * t ≤ T) (c : ℝ) (hc : 0 ≤ c)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hf : c * fraction i w ≤ 1) :
    weighted (mutants i) c (predict (replaceKernel i) e t w) ≤ normLimit T := by
  let P := predict (replaceKernel i) e t w
  have hP := predict_probability (replaceKernel i) e he w hw t
  have h := (fraction_predict i e he w hw t).2
  have hpow := (one_le_exp_bound (2 * e) t (by linarith only [he.1])).trans
    (Real.exp_le_exp.mpr (show (2 * e) * t ≤ 2 * T by linarith only [hT]))
  have ho := h.trans (mul_le_mul_of_nonneg_right hpow (fraction_bounds i w hw).1)
  unfold weighted normLimit
  rw [variation_probability hP, mass_pos_eq (project_positive (mutants i) hP.1)]
  change 1 + c * fraction i P ≤ 1 + Real.exp (2 * T)
  have hh := mul_le_mul_of_nonneg_left ho hc
  have hd := mul_le_mul_of_nonneg_left hf (Real.exp_pos (2 * T)).le
  nlinarith only [hh, hd]

lemma uniform_norm_bounds (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (t : ℕ) (T : ℝ) (hT : e * t ≤ T) (c : ℝ) (hc : 0 ≤ c)
    (w z j : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hz : probability z)
    (hwc : c * fraction i w ≤ 1) (hzc : c * fraction i z ≤ 1) :
    let N := weighted (mutants (k := k) i) c
    N (response (replaceKernel i) e t w j) ≤ responseLimit T * N j ∧
    N (predict (replaceKernel i) e t z - predict (replaceKernel i) e t w -
      response (replaceKernel i) e t w (z - w)) ≤ remainderLimit T * (N (z - w)) ^ 2 := by
  let N : PredictionMeasure.Weights (Genotype n k) → ℝ := weighted (mutants i) c
  let B := normLimit T
  let a := 3 * e * B ^ 2
  have h₁ (s : ℕ) (hs : s < t) : e * (s : ℝ) ≤ T :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hs.le) he.1).trans hT
  have hB : 0 ≤ B := by unfold B normLimit; positivity
  have h := iterate_bounds (replaceKernel i) (mutants (k := k) i) (replace_resident i k) hc he w z j B t
    (fun s hs ↦ prediction_norm_bound i e he T s (h₁ s hs) c hc w hw hwc)
    (fun s hs ↦ prediction_norm_bound i e he T s (h₁ s hs) c hc z hz hzc)
  have hp : (1 + a) ^ t ≤ responseLimit T := by
    apply (one_le_exp_bound a t (by unfold a; exact mul_nonneg (mul_nonneg (by norm_num) he.1) (sq_nonneg _))).trans
    unfold responseLimit
    apply Real.exp_le_exp.mpr
    dsimp [a, B]
    nlinarith only [mul_le_mul_of_nonneg_left hT (show 0 ≤ 3 * normLimit T ^ 2 by positivity)]
  change N (response (replaceKernel i) e t w j) ≤ responseLimit T * N j ∧ _
  constructor
  · exact h.2.1.trans (mul_le_mul_of_nonneg_right hp (weighted_nonneg _ hc _))
  · apply h.2.2.trans
    unfold remainderLimit
    have ha : 0 ≤ 1 + a := add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num) he.1) (sq_nonneg B))
    have hP : (1 + a) ^ (2 * t) ≤ responseLimit T ^ 2 := by
      rw [mul_comm 2 t, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg ha t) hp _
    have hB' := mul_le_mul_of_nonneg_left hT (show 0 ≤ 3 * B from mul_nonneg (by norm_num) hB)
    have hscale : 0 ≤ 3 * B * e * t := by unfold B normLimit; have := he.1; positivity
    have hd := mul_le_mul hB' hP (pow_nonneg ha _) (by have := (mul_nonneg he.1 (Nat.cast_nonneg t)).trans hT; unfold B normLimit; positivity)
    have hh := mul_le_mul_of_nonneg_right hd (sq_nonneg (N (z - w)))
    convert hh using 1; dsimp [a, B]; ring

end
end Lax637351Proofs.ColumnNormBounds
