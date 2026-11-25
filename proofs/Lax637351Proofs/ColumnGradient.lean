import Lax637351Proofs.ColumnEmpirical
import Lax637351Proofs.ColumnMixture

namespace Lax637351Proofs.ColumnGradient

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ColumnMixture Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnClasses
open Lax637351Proofs.ResponseContinuity (variation_zero)
open Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma vanishing_scale (f U b : ℝ) (hf : 0 ≤ f) (hU : 0 ≤ U)
    (h : ∀ c > 0, c * f ≤ 1 → b ≤ U / c) : b ≤ f * U := by
  by_cases hz : f = 0
  · rw [hz, zero_mul]
    by_contra! hb
    let c := (U + 1) / b
    have hc : 0 < c := div_pos (by linarith only [hU]) hb
    have hd := h c hc (by simp [hz])
    have ht := (le_div_iff₀ hc).mp hd
    have he : b * c = U + 1 := by dsimp [c]; field_simp
    linarith only [ht, he]
  · have hf' : 0 < f := lt_of_le_of_ne hf (Ne.symm hz)
    have hp := h f⁻¹ (inv_pos.mpr hf') (by rw [inv_mul_cancel₀ hz])
    simpa only [div_inv_eq_mul, mul_comm U f] using hp

lemma project_resident_atom (i : Fin n) (x : Genotype n k) (hx : x ∉ mutants i) :
    project (mutants i) (atom x) = 0 := by
  funext y
  by_cases hy : y ∈ mutants i
  · have he : x ≠ y := fun h ↦ hx (h.symm ▸ hy)
    simp [project, atom, hy, he]
  · simp [project, hy]

lemma projection_resident_replacement (i : Fin n) (x y : Genotype n k) (hx : x ∉ mutants i) (hy : y ∉ mutants i) :
    project (mutants i) (atom x - atom y) = 0 := by
  rw [project_sub, project_resident_atom i x hx, project_resident_atom i y hy, sub_self]

lemma meanResponse_resident (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w d : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hd : project (mutants i) d = 0) :
    |meanResponse i e H w d| ≤ fraction i w * (responseLimit T * variation d) := by
  apply vanishing_scale (fraction i w) (responseLimit T * variation d) _ (fraction_bounds i w hw).1
    (mul_nonneg (Real.exp_pos _).le (variation_nonneg _))
  intro c hc hcf
  have h := meanResponse_bound i e he H hH T hT c hc.le w d hw hcf
  rw [fractionScale, if_neg hc.ne', weighted, hd, variation_zero, mul_zero, add_zero] at h
  exact h.trans_eq (by ring)

lemma remainder_resident (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w z : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (hz : probability z)
    (hd : project (mutants i) (z - w) = 0) :
    |meanPotential i e H z - meanPotential i e H w - meanResponse i e H w (z - w)| ≤
      fraction i w * (remainderLimit T * variation (z - w) ^ 2) := by
  have hf : fraction i z = fraction i w := by
    have h := congrArg mass hd
    rw [show mass (project (mutants i) (z - w)) = fraction i (z - w) from rfl, fraction_sub] at h
    have h0 : mass (0 : PredictionMeasure.Weights (Genotype n k)) = 0 := by simp [mass]
    rwa [h0, sub_eq_zero] at h
  have hT0 := (mul_nonneg he.1 (Nat.cast_nonneg H)).trans hT
  have hR : 0 ≤ remainderLimit T := by unfold remainderLimit normLimit; positivity
  apply vanishing_scale _ _ _ (fraction_bounds i w hw).1 (mul_nonneg hR (sq_nonneg _))
  intro c hc hcf
  have h := meanPotential_remainder i e he H hH T hT c hc.le w z hw hz hcf (by rwa [hf])
  rw [fractionScale, if_neg hc.ne', weighted, hd, variation_zero, mul_zero, add_zero] at h
  simpa only [← mul_assoc, mul_comm (c⁻¹), div_eq_mul_inv, mul_assoc] using h

lemma meanResponse_seed_lower (hn : 2 ≤ n) (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1 / 2)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (x y : Genotype n k)
    (hx : x ∈ mutants i) (hy : y ∉ mutants i) :
    Real.exp (-2 * T) ≤ meanResponse i e H w (atom x - atom y) := by
  let d := atom x - atom y
  have hmass : mass d = 0 := by unfold d; rw [mass_sub, mass_atom, mass_atom, sub_self]
  have hd : positive (view i 1 d) := by
    intro z
    have hz : fromClass z ∈ mutants i := by
      change Genotypes.toString (fromClass z) i = 1
      rw [string_fromClass]
      exact z.property.2
    have hzy : y ≠ fromClass z := by intro h; exact hy (h.symm ▸ hz)
    change 0 ≤ atom x (fromClass z) - atom y (fromClass z)
    simp only [atom, if_neg hzy, sub_zero]
    split_ifs <;> norm_num
  have hfrac : fraction i d = 1 := by
    dsimp [d]
    simp [fraction_sub, atom_fraction, indicator, hx, hy]
  have he' : 0 ≤ e ∧ e ≤ 1 := ⟨he.1, by linarith [he.2]⟩
  have ht (t : ℕ) (ht : t ∈ Finset.range H) :
      Real.exp (-2 * T) ≤ fraction i (response (replaceKernel i) e t w d) := by
    have htR : (t : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp ht).le
    have hsm := mul_le_mul_of_nonneg_left htR he.1
    have hs := (response_seed hn i e he' w d hw hR hmass hd t).2
    rw [hfrac, mul_one] at hs
    exact (Real.exp_le_exp.mpr (by linarith only [hsm, hT])).trans ((one_sub_pow_lower e he t).trans hs)
  unfold meanResponse
  apply (le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)).mpr
  have hsum := Finset.sum_le_sum ht
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (H : ℝ)] using hsum

lemma meanResponse_immigrant (hn : 2 ≤ n) (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1 / 2)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hf : fraction i w < 1) (hf' : 24 * T * Real.exp (6 * T) * fraction i w ≤ Real.exp (-2 * T) / 2)
    (x y : Genotype n k) (hx : x ∈ mutants i) (hy : y ∉ mutants i) :
    Real.exp (-2 * T) / 2 ≤ meanResponse i e H w (atom x - atom y) := by
  let a := residents i w
  let d := atom x - atom y
  have ha := residents_probability i w hw hf
  have hr := meanResponse_seed_lower hn i e he H hH T hT a ha (residents_zero i w) x y hx hy
  have h := meanResponse_continuity i e ⟨he.1, by linarith [he.2]⟩ H hH T hT a w d ha hw
  have hT0 := (mul_nonneg he.1 (Nat.cast_nonneg H)).trans hT
  have ht : 0 ≤ 6 * T * Real.exp (6 * T) := by positivity
  have hu := mul_le_mul (mul_le_mul_of_nonneg_left (residents_delta i w hw hf) ht)
    (variation_atom_diff x y) (variation_nonneg _) (mul_nonneg ht (mul_nonneg (by norm_num) (fraction_bounds i w hw).1))
  change Real.exp (-2 * T) ≤ meanResponse i e H a d at hr
  have hl := (abs_le.mp h).1
  change Real.exp (-2 * T) / 2 ≤ meanResponse i e H w d
  nlinarith only [hr, hl, hu, hf']

end
end Lax637351Proofs.ColumnGradient
