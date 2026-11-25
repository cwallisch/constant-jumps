import Lax637351Proofs.ColumnGain
import Lax637351Proofs.ResidentCap

namespace Lax637351Proofs.ColumnPrediction

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnClasses
open Lax637351Proofs.ColumnEvolution Lax637351Proofs.LinearInvasion Lax637351Proofs.ColumnGain
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma fraction_add (i : Fin n) (w z : PredictionMeasure.Weights (Genotype n k)) :
    fraction i (w + z) = fraction i w + fraction i z := by rw [fraction, project_add, mass_add]; rfl

lemma fraction_sub (i : Fin n) (w z : PredictionMeasure.Weights (Genotype n k)) :
    fraction i (w - z) = fraction i w - fraction i z := by rw [fraction, project_sub, mass_sub]; rfl

lemma fraction_smul (i : Fin n) (a : ℝ) (w : PredictionMeasure.Weights (Genotype n k)) :
    fraction i (a • w) = a * fraction i w := by rw [fraction, project_smul, mass_smul]; rfl

lemma fraction_bounds (i : Fin n) (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    0 ≤ fraction i w ∧ fraction i w ≤ 1 := by
  have hn := project_positive (mutants (k := k) i) hw.1
  have he := mass_pos_eq hn
  rw [fraction, ← he]
  exact ⟨variation_nonneg _, (variation_project _ _).trans_eq (variation_probability hw)⟩

lemma fraction_step (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    (1 - e) * fraction i w ≤ fraction i (update (replaceKernel i) e w) ∧
      fraction i (update (replaceKernel i) e w) ≤ (1 + 2 * e) * fraction i w := by
  let t := transform (replaceKernel i) w w w
  have ht : positive t := transform_positive _ hw.1 hw.1 hw.1
  have hn : 0 ≤ fraction i t := by unfold fraction mass; exact Finset.sum_nonneg (fun x _ ↦ project_positive (mutants i) ht x)
  have hu : fraction i t ≤ 3 * fraction i w := by
    have h := variation_project_transform (replaceKernel i) (mutants (k := k) i) (replace_resident i k) w w w
    rw [mass_pos_eq (project_positive (mutants i) ht), mass_pos_eq (project_positive (mutants i) hw.1), variation_probability hw] at h
    change fraction i t ≤ fraction i w * 1 * 1 + 1 * fraction i w * 1 + 1 * 1 * fraction i w at h
    linarith only [h]
  rw [update, fraction_add, fraction_smul, fraction_smul]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg he.1 hn)
  · linarith only [mul_le_mul_of_nonneg_left hu he.1]

lemma fraction_predict (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (t : ℕ) :
    (1 - e) ^ t * fraction i w ≤ fraction i (predict (replaceKernel i) e t w) ∧
      fraction i (predict (replaceKernel i) e t w) ≤ (1 + 2 * e) ^ t * fraction i w := by
  induction t with
  | zero => simp [predict]
  | succ t ih =>
    have h := fraction_step i e he _ (predict_probability (replaceKernel i) e he w hw t)
    rw [predict, pow_succ', pow_succ']
    constructor
    · rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih.1 (sub_nonneg.mpr he.2)).trans h.1
    · refine h.2.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ih.2 (by have := he.1; positivity)

lemma response_seed (hn : 2 ≤ n) (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w h : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (hh : mass h = 0)
    (hh' : positive (view i 1 h)) (t : ℕ) :
    positive (view i 1 (response (replaceKernel i) e t w h)) ∧
      (1 - e) ^ t * fraction i h ≤ fraction i (response (replaceKernel i) e t w h) := by
  induction t with
  | zero => exact ⟨hh', by simp [response]⟩
  | succ t ih =>
    let u := predict (replaceKernel i) e t w
    let v := response (replaceKernel i) e t w h
    let p := predict_probability (replaceKernel i) e he w hw t
    let A := mixedKernel (b := 1) (i := i) (k := k) (partners u p)
    let c := 1 - e * mass (births i u u)
    have ht := view_mutant_step hn i e u v p (response_mass_zero _ e w h hh t)
      (resident_preserved i e he w hw hR t)
    have hV : 1 - e ≤ c := by
      have ht := mul_le_mul_of_nonneg_left (total_birth_mass i u p).2 he.1
      dsimp [c] at *
      linarith only [ht]
    have hc : 0 ≤ c := (sub_nonneg.mpr he.2).trans hV
    have hF : positive (forward A (view i 1 v)) := fun x ↦
      Finset.sum_nonneg (fun y _ ↦ mul_nonneg (ih.1 y) (A.nonneg _ _))
    rw [response]
    change positive (view i 1 (tangent (replaceKernel i) e u v)) ∧ _
    constructor
    · rw [ht]
      exact fun x ↦ add_nonneg (mul_nonneg hc (ih.1 x)) (mul_nonneg he.1 (hF x))
    · change _ ≤ mass (project (mutants i) (tangent (replaceKernel i) e u v))
      rw [← mutant_view_mass, ht, mass_add, mass_smul, mass_smul, mutant_view_mass]
      have hm : 0 ≤ fraction i v := by
        rw [fraction, ← mutant_view_mass]
        exact Finset.sum_nonneg (fun x _ ↦ ih.1 x)
      have hnew : 0 ≤ mass (forward A (view i 1 v)) := Finset.sum_nonneg (fun x _ ↦ hF x)
      have hbase := mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr he.2)
      rw [pow_succ']
      change (1 - e) * (1 - e) ^ t * fraction i h ≤ c * fraction i v + _
      linarith only [hbase, mul_le_mul_of_nonneg_right hV hm, mul_nonneg he.1 hnew]

def meanPotential (i : Fin n) (e : ℝ) (H : ℕ) (w : PredictionMeasure.Weights (Genotype n k)) : ℝ :=
  (∑ t ∈ Finset.range H, fraction i (predict (replaceKernel i) e t w)) / (H : ℝ)

def meanResponse (i : Fin n) (e : ℝ) (H : ℕ) (w h : PredictionMeasure.Weights (Genotype n k)) : ℝ :=
  (∑ t ∈ Finset.range H, fraction i (response (replaceKernel i) e t w h)) / (H : ℝ)

lemma meanResponse_add (i : Fin n) (e : ℝ) (H : ℕ) (w x y : PredictionMeasure.Weights (Genotype n k)) :
    meanResponse i e H w (x + y) = meanResponse i e H w x + meanResponse i e H w y := by
  simp_rw [meanResponse, response_add, fraction_add, Finset.sum_add_distrib, add_div]

lemma meanResponse_smul (i : Fin n) (e : ℝ) (H : ℕ) (w x : PredictionMeasure.Weights (Genotype n k)) (c : ℝ) :
    meanResponse i e H w (c • x) = c * meanResponse i e H w x := by
  simp_rw [meanResponse, response_smul, fraction_smul, ← Finset.mul_sum, mul_div_assoc]

lemma predict_shift (i : Fin n) (e : ℝ) (w : PredictionMeasure.Weights (Genotype n k)) (t : ℕ) :
    predict (replaceKernel i) e t (update (replaceKernel i) e w) =
      predict (replaceKernel i) e (t + 1) w := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [predict, ih]

lemma one_step_mean_potential (i : Fin n) (e : ℝ) (H : ℕ) (w : PredictionMeasure.Weights (Genotype n k)) :
    meanPotential i e H (update (replaceKernel i) e w) - meanPotential i e H w =
      (fraction i (predict (replaceKernel i) e H w) - fraction i w) / H := by
  unfold meanPotential
  rw [← sub_div]
  simp_rw [predict_shift]
  induction H with
  | zero => simp [predict]
  | succ H ih =>
    apply congrArg (fun x : ℝ ↦ x / ((H + 1 : ℕ) : ℝ))
    have he (H : ℕ) :
        (∑ t ∈ Finset.range H, fraction i (predict (replaceKernel i) e (t + 1) w)) -
          (∑ t ∈ Finset.range H, fraction i (predict (replaceKernel i) e t w)) =
          fraction i (predict (replaceKernel i) e H w) - fraction i w := by
      induction H with
      | zero => simp [predict]
      | succ H ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linarith only [ih]
    exact he (H + 1)

end
end Lax637351Proofs.ColumnPrediction
