import Lax637351Proofs.OffspringEstimates.PopulationRatio
import Lax637351Proofs.OffspringEstimates.EntryBounds

namespace Lax637351Proofs.OffspringEstimates.SpeciesState

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Sampling Lax637351Proofs.OffspringEstimates.Genotypes
open Lax637351Proofs.OffspringEstimates.Weights Lax637351Proofs.OffspringEstimates.WeightSums Lax637351Proofs.OffspringEstimates.RegionGeometry
open Lax637351Proofs.OffspringEstimates.PlateauDynamics Lax637351Proofs.OffspringEstimates.Deletion
open Lax637351Proofs.OffspringEstimates.PopulationRatio Lax637351Proofs.OffspringEstimates.Species
open Lax637351Proofs.OffspringEstimates.FiniteDrift Lax637351Proofs.OffspringEstimates.FiniteComparison
open Lax637351Proofs.OffspringEstimates.EmpiricalKernels Lax637351Proofs.OffspringEstimates.ActualBirthKernels
open Lax637351Proofs.OffspringEstimates.MutationDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def weightFunction {n k : ℕ} (B : Genotype n k) (child : BitString n) : ℝ :=
  weight (insideCount (toString B) child)

lemma weightFunction_anchor {n k : ℕ} (B : Genotype n k) : weightFunction B (toString B) = 0 := by
  simp [weightFunction, Lax637351Proofs.OffspringEstimates.PlateauKernelApproximation.insideCount_self, weight_zero]

lemma weightFunction_bounds {n k : ℕ} (B : Genotype n k) (child : BitString n) :
    0 ≤ weightFunction B child ∧ weightFunction B child ≤ 5 / 4 :=
  ⟨weight_nonneg _, weight_upper _⟩

lemma weightFunction_toString {n k : ℕ} (B x : Genotype n k) :
    weightFunction B (toString x) = weight (distance B x) := by
  rw [weightFunction, toString_insideCount]

def realizePopulation {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) : Population n μ :=
  fun u ↦ toString (P u)

lemma count_empirical {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    count (toString B) (realizePopulation P) = (μ : ℕ) * (empirical P B).toReal := by
  have h := mean_pick (empirical P) B 1
  rw [empirical, mean_map, mean_uniform] at h
  simp only [Fintype.card_fin, mul_one] at h
  have hc : count (toString B) (realizePopulation P) =
      ∑ u : Fin (μ : ℕ), if P u = B then (1 : ℝ) else 0 := by
    unfold count total indicator realizePopulation
    simp only [toString_eq_iff]
  rw [← hc] at h
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have h' := congrArg (fun x : ℝ ↦ (μ : ℕ) * x) h
  rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul] at h'
  exact h'

lemma total_empirical {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    total (weightFunction B) (realizePopulation P) =
      (μ : ℕ) * cloud B (fun x ↦ (empirical P x).toReal) := by
  have h := mean_weight_cloud B (empirical P)
  rw [empirical, mean_map, mean_uniform] at h
  simp only [Fintype.card_fin] at h
  have hw : total (weightFunction B) (realizePopulation P) =
      ∑ u : Fin (μ : ℕ), weight (distance B (P u)) := by
    unfold total realizePopulation
    simp only [weightFunction_toString]
  rw [← hw] at h
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have h' := congrArg (fun x : ℝ ↦ (μ : ℕ) * x) h
  rw [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul] at h'
  exact h'

lemma ratio_empirical {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k) (B : Genotype n k) :
    ratio (weightFunction B) (toString B) (realizePopulation P) =
      cloud B (fun x ↦ (empirical P x).toReal) / (empirical P B).toReal := by
  unfold ratio
  rw [total_empirical, count_empirical]
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  rw [mul_div_mul_left _ _ hμ.ne']

lemma accepted_indicator {n k : ℕ} (B : Genotype n k) :
    (fun z ↦ if onPlateau k z then indicator (toString B) z else 0) = acceptedClone B := by
  funext z
  rw [Lax637351Proofs.OffspringEstimates.AnchorMutation.acceptedClone_indicator]
  by_cases hp : onPlateau k z
  · simp [hp, indicator]
  · have hz : z ≠ toString B := by
      intro hz
      rw [hz] at hp
      exact hp (toString_onPlateau B)
    simp [hp, hz]

lemma offspring_contrast {n k : ℕ} {μ : ℕ+} (P : Fin (μ : ℕ) → Genotype n k)
    (B : Genotype n k) (p_c : ℝ) (hp_c : 0 ≤ p_c ∧ p_c ≤ 1) :
    let Q := ratio (weightFunction B) (toString B) (realizePopulation P)
    mean (offspring p_c (realizePopulation P))
      (fun z ↦ if onPlateau k z then weightFunction B z else 0) -
        Q * mean (offspring p_c (realizePopulation P))
          (fun z ↦ if onPlateau k z then indicator (toString B) z else 0) =
      p_c * (pairMean (empirical P) (weightedBirth B) -
        Q * pairMean (empirical P) (cloneBirth B)) +
      (1 - p_c) * (mean (empirical P) (fun x ↦ weightedBirth B x x) -
        Q * mean (empirical P) (fun x ↦ cloneBirth B x x)) := by
  dsimp only
  rw [accepted_indicator]
  change mean (offspring p_c (fun u ↦ toString (P u))) (acceptedWeight B) -
    ratio (weightFunction B) (toString B) (realizePopulation P) *
      mean (offspring p_c (fun u ↦ toString (P u))) (acceptedClone B) = _
  rw [empirical_offspring_weight p_c hp_c P B, empirical_offspring_clone p_c hp_c P B]
  ring

end
end Lax637351Proofs.OffspringEstimates.SpeciesState
