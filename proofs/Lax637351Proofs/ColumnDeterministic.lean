import Lax637351Proofs.ColumnGradient

namespace Lax637351Proofs.ColumnDeterministic

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ColumnGradient Lax637351Proofs.ColumnEmpirical
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma variation_sub (α : Type*) [Fintype α] (x y : PredictionMeasure.Weights α) :
    variation (x - y) ≤ variation x + variation y := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ y]
  apply (variation_add _ _).trans
  rw [variation_smul, abs_neg, abs_one, one_mul]

lemma step_project_variation (i : Fin n) (e : ℝ) (he : 0 ≤ e)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    variation (project (mutants i) (update (replaceKernel i) e w - w)) ≤ 4 * e * fraction i w := by
  let T := replaceKernel (k := k) i
  let E := mutants (k := k) i
  have heq : update T e w - w = e • (transform T w w w - w) := by
    funext x
    simp only [update, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change variation (project E (update T e w - w)) ≤ _
  rw [heq, project_smul, project_sub, variation_smul, abs_of_nonneg he]
  have h := variation_project_transform T E (replace_resident i k) w w w
  rw [variation_probability hw, mass_pos_eq (project_positive E hw.1)] at h
  have hu := variation_sub _ (project E (transform T w w w)) (project E w)
  rw [mass_pos_eq (project_positive E hw.1)] at hu
  change variation (project E (transform T w w w)) ≤ fraction i w * 1 * 1 + 1 * fraction i w * 1 +
    1 * 1 * fraction i w at h
  change variation (project E (transform T w w w) - project E w) ≤
    variation (project E (transform T w w w)) + fraction i w at hu
  have hb := mul_le_mul_of_nonneg_left (show variation (project E (transform T w w w) - project E w) ≤
    4 * fraction i w by linarith only [h, hu]) he
  exact hb.trans_eq (by ring)

lemma deterministic_remainder (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H ≤ T)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    let v := update (replaceKernel i) e w
    |meanPotential i e H v - meanPotential i e H w - meanResponse i e H w (v - w)| ≤
      48 * remainderLimit T * e ^ 2 * fraction i w := by
  let v := update (replaceKernel i) e w
  let f := fraction i w
  let R := remainderLimit T
  have hf : 0 ≤ f := (fraction_bounds i w hw).1
  have hv := update_probability (replaceKernel i) e he w hw
  have hT0 := (mul_nonneg he.1 (Nat.cast_nonneg H)).trans hT
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  change |meanPotential i e H v - meanPotential i e H w - meanResponse i e H w (v - w)| ≤ _
  have heq : (3 * f) * (R * (4 * e) ^ 2) = 48 * R * e ^ 2 * f := by ring
  rw [← heq]
  apply vanishing_scale _ _ _ (by positivity) (mul_nonneg hR (sq_nonneg _))
  intro c hc hcf
  have hcw : c * f ≤ 1 := by nlinarith only [hcf, mul_nonneg hc.le hf]
  have hcv : c * fraction i v ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (fraction_step i e he w hw).2 hc.le
    have hp := mul_le_mul_of_nonneg_right (show 1 + 2 * e ≤ 3 by linarith [he.2]) (mul_nonneg hc.le hf)
    nlinarith only [hh, hp, hcf]
  have hm := meanPotential_remainder i e he H hH T hT c hc.le w v hw hv hcw hcv
  have hN : weighted (mutants i) c (v - w) ≤ 4 * e := by
    unfold weighted
    have hh := ResidentCap.step_variation i e he.1 w hw
    have ht := mul_le_mul_of_nonneg_left (step_project_variation i e he.1 w hw) hc.le
    have hn := mul_le_mul_of_nonneg_right hcf (show 0 ≤ 2 * e from mul_nonneg (by norm_num) he.1)
    have hv := mul_nonneg he.1 (mul_nonneg hc.le hf)
    change variation (v - w) ≤ 2 * e at hh
    nlinarith only [hh, ht, hn, hv]
  have hN' := pow_le_pow_left₀ (weighted_nonneg (mutants i) hc.le (v - w)) hN 2
  rw [fractionScale, if_neg hc.ne'] at hm
  have hmul := mul_le_mul_of_nonneg_left hN' (mul_nonneg (inv_nonneg.mpr hc.le) hR)
  exact hm.trans (hmul.trans_eq (by unfold R; ring))

lemma deterministic_response_lower (i : Fin n) (e : ℝ) (he : 0 < e ∧ e ≤ 1)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : e * H = T) (hsmall : 48 * remainderLimit T * e * T ≤ 1)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hg : 3 * fraction i w ≤ fraction i (predict (replaceKernel i) e H w)) :
    e * fraction i w / T ≤ meanResponse i e H w (update (replaceKernel i) e w - w) := by
  have h := deterministic_remainder i e ⟨he.1.le, he.2⟩ H hH T hT.le w hw
  dsimp only at h
  rw [one_step_mean_potential] at h
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hT' : 0 < T := hT ▸ mul_pos he.1 hH'
  have hf := (fraction_bounds i w hw).1
  have hh : 48 * remainderLimit T * e ^ 2 ≤ 1 / (H : ℝ) := by
    rw [le_div_iff₀ hH']
    rw [show 48 * remainderLimit T * e ^ 2 * (H : ℝ) = 48 * remainderLimit T * e * (e * (H : ℝ)) by ring, hT]
    exact hsmall
  have h₁ := mul_le_mul_of_nonneg_right hh hf
  have h₂ := div_le_div_of_nonneg_right hg hH'.le
  have hR := (abs_le.mp h).2
  rw [sub_div] at hR
  rw [show (1 / (H : ℝ)) * fraction i w = fraction i w / H by ring] at h₁
  have heq : e * fraction i w / T = fraction i w / H := by rw [← hT]; field_simp [he.1.ne']
  rw [heq]
  linarith only [h₁, h₂, hR, show (3 * fraction i w) / (H : ℝ) = 3 * (fraction i w / H) by ring]

end
end Lax637351Proofs.ColumnDeterministic
