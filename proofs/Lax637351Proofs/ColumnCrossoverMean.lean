import Lax637351Proofs.ColumnContrast
import Lax637351Proofs.ColumnDeterministic

namespace Lax637351Proofs.ColumnCrossoverMean

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.OffspringProduct Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear
open Lax637351Proofs.ColumnGain Lax637351Proofs.ColumnPrediction
open Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnSlot
open Lax637351Proofs.PlateauKernel Lax637351Proofs.ColumnEvents Lax637351Proofs.ColumnReplacement
open Lax637351Proofs.SpeciesDrift (genotypeList)
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def mateMean (P : Population n μ) (hP : plateau (k := k) P)
    (f : Genotype n k → Genotype n k → BitString n → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin μ)) fun x ↦
    mean (PMF.uniformOfFintype (Fin μ)) fun y ↦
      mean (pairMutation (P x) (P y) (1 / (n : ℝ))) (f (genotypeList P hP x) (genotypeList P hP y))

lemma sum_atom_decomp {α : Type*} [Fintype α] (w : PredictionMeasure.Weights α) :
    (∑ x, w x • atom x) = w := by
  funext y
  rw [Finset.sum_apply, Finset.sum_eq_single y]
  · simp [atom]
  · intro x _ hx
    simp [atom, hx]
  · simp

lemma linear_atom_decomp {α : Type*} [Fintype α] (L : PredictionMeasure.Weights α →ₗ[ℝ] ℝ)
    (w : PredictionMeasure.Weights α) : L w = ∑ x, w x * L (atom x) := by
  conv_lhs => rw [← sum_atom_decomp w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

lemma birth_weight (i : Fin n) (x y : Genotype n k) (f : Genotype n k → ℝ) :
    (∑ z, birthMass i x y z * f z) =
      mean (pairMutation (toString x) (toString y) (1 / (n : ℝ))) (fun u ↦ ((proposal i x y u).map f).getD 0) := by
  let q := pairMutation (toString x) (toString y) (1 / (n : ℝ))
  let g (o : Option (Genotype n k)) : ℝ := (o.map f).getD 0
  change _ = mean q (fun u ↦ g (proposal i x y u))
  rw [← mean_map q (proposal i x y) g]
  unfold mean g
  rw [Fintype.sum_option]
  simp only [Option.map_none, Option.getD_none, mul_zero, zero_add, Option.map_some, Option.getD_some]
  rfl

lemma mateMean_weights (P : Population n μ) (hP : plateau (k := k) P)
    (f : Genotype n k → Genotype n k → BitString n → ℝ) :
    mateMean P hP f = ∑ x, ∑ y, empiricalWeights P hP x * empiricalWeights P hP y *
      mean (pairMutation (toString x) (toString y) (1 / (n : ℝ))) (f x y) := by
  let G := genotypeList P hP
  let q := EmpiricalKernels.empirical G
  let F (x y : Genotype n k) := mean (pairMutation (toString x) (toString y) (1 / (n : ℝ))) (f x y)
  have h (u : Fin μ) : toString (G u) = P u := toString_ofString _ _
  have he : mateMean P hP f = mean q (fun x ↦ mean q (F x)) := by
    unfold mateMean q EmpiricalKernels.empirical
    simp only [mean_map, F, h]
    rfl
  rw [he]
  change (∑ x, (q x).toReal * ∑ y, (q y).toReal * F x y) =
    ∑ x, ∑ y, (q x).toReal * (q y).toReal * F x y
  simp only [Finset.mul_sum, mul_assoc]

def predictedContrast (i : Fin n) (H : ℕ) (P : Population n μ) (hP : plateau (k := k) P) : ℝ :=
  mateMean P hP (fun x y raw ↦
    if (proposal i x y raw).isSome then rawContrast k i H P hP raw else 0)

lemma predictedContrast_eq (i : Fin n) (H : ℕ) (P : Population n μ) (hP : plateau (k := k) P) :
    meanResponse i (eps μ) H (empiricalWeights P hP)
      (update (replaceKernel i) (eps μ) (empiricalWeights P hP) - empiricalWeights P hP) =
      eps μ * predictedContrast i H P hP := by
  let w := empiricalWeights P hP
  let L := responseMap i (eps μ) H w
  let b := births i w w
  let e := eps μ
  let f (z : Genotype n k) := L (atom z) - L w
  have he : L (update (replaceKernel i) e w - w) = e * (L b - mass b * L w) := by
    rw [resident_step i e w (empirical_probability P hP), map_sub, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  change L (update (replaceKernel i) e w - w) = _
  rw [he, predictedContrast, mateMean_weights]
  congr 1
  have hsum : L b - mass b * L w = ∑ z, b z * f z := by
    rw [linear_atom_decomp L b, mass, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    dsimp [f]
    ring
  rw [hsum]
  have hmean (x y : Genotype n k) :
      mean (pairMutation (toString x) (toString y) (1 / (n : ℝ))) (fun raw ↦
        if (proposal i x y raw).isSome then rawContrast k i H P hP raw else 0) =
      ∑ z, birthMass i x y z * f z := by
    rw [birth_weight i x y f]
    congr 1
    funext raw
    by_cases hz : (zeros raw).card = k
    · by_cases hm : x ∉ mutants i ∧ y ∉ mutants i ∧ raw i = 1
      · simp [proposal, hz, hm]
      · simp only [proposal, dif_pos hz, if_neg hm, Option.isSome_some, if_true, Option.map_some, Option.getD_some]
        change rawGradient L raw - slotMean (rawGradient L) P = L (atom (ofString raw hz)) - L w
        rw [rawGradient_of_plateau L raw hz, empirical_slot P hP L]
    · simp [proposal, hz]
  simp_rw [hmean, Finset.mul_sum]
  unfold b births
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  change w x * w y * birthMass i x y z * f z = w x * w y * (birthMass i x y z * f z)
  ring

lemma predictedContrast_lower (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ)
    (hT : eps μ * H = T) (hsmall : 48 * remainderLimit T * eps μ * T ≤ 1)
    (P : Population n μ) (hP : plateau (k := k) P)
    (hg : 3 * frequency k i P ≤ fraction i (predict (replaceKernel i) (eps μ) H (empiricalWeights P hP))) :
    frequency k i P / T ≤ predictedContrast i H P hP := by
  have he := eps_bounds μ
  have h := ColumnDeterministic.deterministic_response_lower i (eps μ) ⟨he.1, by linarith [he.2]⟩ H hH T hT hsmall
    _ (empirical_probability P hP) (by rwa [empirical_fraction i P hP])
  rw [predictedContrast_eq, empirical_fraction i P hP, mul_div_assoc] at h
  exact (mul_le_mul_iff_of_pos_left he.1).mp h

end
end Lax637351Proofs.ColumnCrossoverMean
