import Lax637351Proofs.ColumnAverages

namespace Lax637351Proofs.ColumnMixture

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ResponseContinuity (variation_zero)
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def residents (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k)) :
    PredictionMeasure.Weights (Genotype n k) :=
  (1 - fraction i w)⁻¹ • project (mutants i)ᶜ w

def rare (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k)) :
    PredictionMeasure.Weights (Genotype n k) :=
  (fraction i w)⁻¹ • project (mutants i) w

lemma residents_probability (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k))
    (hw : probability w) (hf : fraction i w < 1) : probability (residents i w) := by
  have hd : 0 < 1 - fraction i w := sub_pos.mpr hf
  have hm := congrArg mass (conserve_split (mutants i) w)
  rw [mass_add, hw.2, ← fraction] at hm
  refine ⟨fun x ↦ mul_nonneg (inv_nonneg.mpr hd.le) (project_positive _ hw.1 x), ?_⟩
  unfold residents
  rw [mass_smul, show mass (project (mutants i)ᶜ w) = 1 - fraction i w by linarith only [hm],
    inv_mul_cancel₀ hd.ne']

lemma rare_probability (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k))
    (hw : probability w) (hf : 0 < fraction i w) : probability (rare i w) := by
  refine ⟨fun x ↦ mul_nonneg (inv_nonneg.mpr hf.le) (project_positive _ hw.1 x), ?_⟩
  unfold rare
  rw [mass_smul, ← fraction, inv_mul_cancel₀ hf.ne']

lemma residents_zero (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k))
    (x : Genotype n k) (hx : x ∈ mutants i) : residents i w x = 0 := by
  simp [residents, project, hx]

lemma rare_zero (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k))
    (x : Genotype n k) (hx : x ∉ mutants i) : rare i w x = 0 := by
  simp [rare, project, hx]

lemma residents_delta (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k))
    (hw : probability w) (hf : fraction i w < 1) :
    variation (w - residents i w) ≤ 2 * fraction i w := by
  have hf₀ := (fraction_bounds i w hw).1
  have hq : 0 < 1 - fraction i w := sub_pos.mpr hf
  let π := residents i w
  have hEq : w - π = project (mutants i) w + (-(fraction i w)) • π := by
    funext x
    have hb := congrFun (conserve_split (mutants i) w) x
    change project (mutants i) w x + project (mutants i)ᶜ w x = w x at hb
    simp only [π, residents, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hb]
    field_simp
    ring
  rw [hEq]
  apply (variation_add _ _).trans
  rw [variation_smul, abs_neg, abs_of_nonneg hf₀, variation_probability (residents_probability i w hw hf),
    mass_pos_eq (project_positive (mutants i) hw.1), ← fraction]
  ring_nf
  exact le_rfl

lemma mixture_eq (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k))
    (h0 : 0 < fraction i w) (h1 : fraction i w < 1) :
    w - residents i w = fraction i w • (rare i w - residents i w) := by
  have hq : 0 < 1 - fraction i w := sub_pos.mpr h1
  funext x
  have hb := congrFun (conserve_split (mutants i) w) x
  change project (mutants i) w x + project (mutants i)ᶜ w x = w x at hb
  simp only [residents, rare, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hb]
  field_simp
  ring

lemma nonlinear_from_response (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) (H : ℕ)
    (T : ℝ) (hT : e * H ≤ T) (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hf : fraction i w < 1) (hfsmall : 4 * remainderLimit T * fraction i w ≤ 1)
    (hlinear : 0 < fraction i w → 4 ≤ fraction i (response (replaceKernel i) e H
      (residents i w) (rare i w - residents i w))) :
    3 * fraction i w ≤ fraction i (predict (replaceKernel i) e H w) := by
  by_cases hzero : fraction i w = 0
  · rw [hzero, mul_zero]
    exact (fraction_bounds i _ (predict_probability _ _ he w hw H)).1
  have hpos : 0 < fraction i w := lt_of_le_of_ne (fraction_bounds i w hw).1 (Ne.symm hzero)
  let a := residents i w
  have ha := residents_probability i w hw hf
  have hbound := (uniform_norm_bounds i e he H T hT 0 (by norm_num) a w (w - a) ha hw
    (by simp) (by simp)).2
  have h₀ : fraction i (predict (replaceKernel i) e H a) = 0 := by
    unfold fraction mass
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ mutants i
    · simp [project, hx, ColumnEvolution.resident_preserved i e he a ha (residents_zero i w) H x hx]
    · simp [project, hx]
  have hr := (fraction_abs_of_weighted i 0 (by norm_num) _).trans (by
    simpa only [fractionScale, if_true, one_mul] using hbound)
  rw [fraction_sub, fraction_sub, h₀, sub_zero] at hr
  have heq : fraction i (response (replaceKernel i) e H a (w - a)) = fraction i w *
      fraction i (response (replaceKernel i) e H a (rare i w - a)) := by
    rw [show w - a = fraction i w • (rare i w - a) from mixture_eq i w hpos hf, response_smul, fraction_smul]
  rw [heq] at hr
  simp only [weighted, zero_mul, add_zero] at hr
  have hR : 0 ≤ remainderLimit T := by
    have hT₀ := (mul_nonneg he.1 (Nat.cast_nonneg H)).trans hT
    unfold remainderLimit normLimit
    positivity
  have hn := (abs_le.mp hr).1
  have hsq := pow_le_pow_left₀ (variation_nonneg (w - a)) (residents_delta i w hw hf) 2
  have hscale := mul_le_mul_of_nonneg_left hsq hR
  have hscale' := mul_le_mul_of_nonneg_right hfsmall hpos.le
  have hg := mul_le_mul_of_nonneg_left (hlinear hpos) hpos.le
  nlinarith only [hn, hscale, hscale', hg]

end
end Lax637351Proofs.ColumnMixture
