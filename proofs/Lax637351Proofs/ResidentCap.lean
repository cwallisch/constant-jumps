import Lax637351Proofs.ResidentBirth

namespace Lax637351Proofs.ResidentCap

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnClasses
open Lax637351Proofs.ColumnEvolution Lax637351Proofs.SpeciesCap
open Lax637351Proofs.ResidentScore Lax637351Proofs.ResidentBirth
open OffspringEstimates.ActualBirthKernels
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def dimensionError (n k : ℕ) : ℝ :=
  (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k + 5 / (4 * (n : ℝ))

def bandGain (k : ℕ) (l : ℝ) : ℝ := Real.exp (-1) * floorWeight k * (2 / 5 * l) ^ 2 / 200

lemma step_variation (i : Fin n) (e : ℝ) (he : 0 ≤ e) (w : PredictionMeasure.Weights (Genotype n k))
    (hw : probability w) : variation (update (replaceKernel i) e w - w) ≤ 2 * e := by
  let T := replaceKernel (k := k) i
  have hP : probability (transform T w w w) := ⟨transform_positive _ hw.1 hw.1 hw.1, by rw [transform_mass, hw.2]; norm_num⟩
  have heq : update T e w - w = e • (transform T w w w - w) := by
    funext x
    simp only [update, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change variation (update T e w - w) ≤ _
  rw [heq, variation_smul, abs_of_nonneg he]
  have h := variation_add (transform T w w w) (-w)
  rw [← neg_one_smul ℝ w, variation_smul, variation_probability hP, variation_probability hw] at h
  norm_num only [abs_neg, abs_one, one_mul] at h
  rw [neg_one_smul, ← sub_eq_add_neg] at h
  linarith only [mul_le_mul_of_nonneg_left h he]

lemma band_contrast (hn : 4 * k ≤ n) (h₂ : 2 ≤ n) (l : ℝ) (hl : 0 ≤ l)
    (herror : dimensionError n k ≤ bandGain k l) (i : Fin n) (B : Genotype n k)
    (hB : B ∉ mutants i) (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (hwB : 1 / 2 ≤ w B)
    (hupper : weightedMass B w / w B ≤ 1 / 25) (hlower : l ≤ lawScore B w) :
    0 ≤ weightedMass B (births i w w) - weightedMass B w / w B * births i w w B := by
  let ν := asPMF w hw
  let q := weightedMass B w / w B
  have hq : 0 ≤ q := div_nonneg
    (Finset.sum_nonneg (fun x _ ↦ mul_nonneg (hw.1 x) (W_bounds B x).1)) (hw.1 B)
  have hv (x : Genotype n k) : (ν x).toReal = w x := congrFun (asPMF_density w hw) x
  have hR' : Species.cloud B (fun x ↦ (ν x).toReal) / (ν B).toReal = q := by
    simp_rw [hv]
    rw [← weightedMass_cloud]
  have hV := SpeciesEnvelope.ideal_quadratic_drift B ν (1 / 2) (by norm_num) (by norm_num)
    (by rw [hv]; linarith) (by rwa [hv]) (by rwa [hR'])
  rw [hR', hv B] at hV
  have hcross := crossed_ratio_lower h₂ hn B ν q hq
  have hprod := mul_le_mul_of_nonneg_left hV (Real.exp_pos (-1)).le
  have hl' := hlower.trans (lawScore_bounds B w hw).2
  have hpow : (2 / 5 * l) ^ 2 ≤ (1 - w B) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (sub_nonneg.mpr (atom_upper w hw B))).mpr (by linarith only [hl'])
  have hcoef : 0 ≤ Real.exp (-1) * floorWeight k / 200 := by unfold floorWeight; positivity
  have hbound := mul_le_mul_of_nonneg_left hpow hcoef
  have he := mul_le_mul_of_nonneg_right (show (5 / 4 : ℝ) + q ≤ 129 / 100 by linarith only [hupper])
    (show 0 ≤ PlateauKernelApproximation.approximationError n k by unfold PlateauKernelApproximation.approximationError; positivity)
  have hscore := weighted_birth_law h₂ (by omega : k ≤ n) i B w hw hR
  have hc := clone_birth_law i B hB w hw
  rw [hc]
  change 0 ≤ _ - q * _
  unfold dimensionError bandGain at herror
  change Real.exp (-1) * ((1 / 2 * floorWeight k / 100) * (1 - w B) ^ 2) ≤ _ at hprod
  nlinarith only [hprod, hcross, hbound, he, hscore, herror]

lemma one_step_cap (hn : 4 * k ≤ n) (h₂ : 2 ≤ n) (l : ℝ) (hl : 0 < l)
    (hl₀ : l ≤ floorWeight k / 16) (hl₁ : l ≤ 1 / 100)
    (herror : dimensionError n k ≤ bandGain k l) (i : Fin n) (B : Genotype n k)
    (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1 / 8) (hes : 16 * e ≤ l)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (hB : B ∉ mutants i) (h : l ≤ lawScore B w) :
    l ≤ lawScore B (update (replaceKernel i) e w) := by
  let z := update (replaceKernel i) e w
  have hz : probability z := update_probability _ _ ⟨he.1, by linarith [he.2]⟩ w hw
  have hΔ := step_variation i e he.1 w hw
  have hΔ' := lawScore_change B w z hw hz
  have hΔscore := (abs_le.mp (hΔ'.trans (mul_le_mul_of_nonneg_left hΔ (by norm_num)))).1
  by_cases hlarge : 2 * l ≤ lawScore B w
  · change l ≤ lawScore B z
    linarith only [hΔscore, hlarge, hes]
  have hsmall : lawScore B w ≤ 2 * l := (not_le.mp hlarge).le
  have hW : 0 < floorWeight k := by unfold floorWeight; positivity
  have hcount : (7 / 8 : ℝ) ≤ w B := by
    have h' := (lawScore_bounds B w hw).1.trans (hsmall.trans (mul_le_mul_of_nonneg_left hl₀ (by norm_num)))
    have heq : (2 : ℝ) * (floorWeight k / 16) = floorWeight k * (1 / 8) := by ring
    rw [heq] at h'
    have h'' := (mul_le_mul_iff_of_pos_left hW).mp h'
    linarith only [h'']
  have hcz : (1 / 2 : ℝ) ≤ z B := by
    have h' := (abs_le.mp ((point_change z w B).trans hΔ)).1
    linarith only [h', hcount, he.2]
  let q := weightedMass B w / w B
  have hq : lawScore B w = q := by
    unfold lawScore q
    rw [max_eq_left (show (1 / 2 : ℝ) ≤ w B by linarith only [hcount])]
  have hq' : q ≤ 1 / 25 := by
    rw [← hq]
    linarith only [hsmall, hl₁]
  have hs := band_contrast hn h₂ l hl.le herror i B hB w hw hR (by linarith only [hcount]) hq' h
  have hw₀ : 0 < w B := by linarith only [hcount]
  have hz₀ : 0 < z B := by linarith only [hcz]
  have heq : weightedMass B z - q * z B = e *
      (weightedMass B (births i w w) - q * births i w w B) := by
    dsimp [z]
    rw [resident_step i e w hw, weightedMass_add, weightedMass_smul, weightedMass_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, q]
    field_simp
    ring
  have hh : q ≤ lawScore B z := by
    unfold lawScore
    rw [max_eq_left hcz, le_div_iff₀ hz₀]
    linarith only [heq, mul_nonneg he.1 hs]
  exact h.trans (hq.symm ▸ hh)

lemma resident_cap (hn : 4 * k ≤ n) (h₂ : 2 ≤ n) (l : ℝ) (hl : 0 < l)
    (hl₀ : l ≤ floorWeight k / 16) (hl₁ : l ≤ 1 / 100) (herror : dimensionError n k ≤ bandGain k l)
    (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1 / 8) (hes : 16 * e ≤ l)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (h : ∀ x ∉ mutants i, l ≤ lawScore x w)
    (t : ℕ) (x : Genotype n k) : predict (replaceKernel i) e t w x ≤ 1 - 2 / 5 * l := by
  have hvalid : 0 ≤ e ∧ e ≤ 1 := ⟨he.1, by linarith [he.2]⟩
  have hS : ∀ t x, x ∉ mutants i → l ≤ lawScore x (predict (replaceKernel i) e t w) := by
    intro t
    induction t with
    | zero => exact h
    | succ t ih =>
      intro x hx
      exact one_step_cap hn h₂ l hl hl₀ hl₁ herror i x e he hes _ (predict_probability _ _ hvalid w hw t)
        (resident_preserved i e hvalid w hw hR t) hx (ih x hx)
  by_cases hx : x ∈ mutants i
  · rw [resident_preserved i e hvalid w hw hR t x hx]
    linarith only [hl₁]
  · have h' := (hS t x hx).trans (lawScore_bounds x _ (predict_probability _ _ hvalid w hw t)).2
    linarith only [h']

end
end Lax637351Proofs.ResidentCap
