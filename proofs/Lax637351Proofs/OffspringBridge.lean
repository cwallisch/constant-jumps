import Lax637351Proofs.PlateauChanges
import Lax637351Proofs.ArrivalProgress
import Lax637351Proofs.OffspringEstimates.SpeciesState

namespace Lax637351Proofs.OffspringBridge

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.MarkedStep Lax637351Proofs.PairStep
open Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauChanges Lax637351Proofs.PlateauPairs
open Lax637351Proofs.OffspringEstimates
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma coin_apply (p : ℝ) (b : Fin 2) :
    OffspringEstimates.Algorithm.coin p b = Lax637351.Algorithm.coin p (b = 1) := by
  by_cases hp : 0 ≤ p ∧ p ≤ 1
  · fin_cases b <;> simp [OffspringEstimates.Algorithm.coin, Lax637351.Algorithm.coin, hp]
  · fin_cases b <;> simp [OffspringEstimates.Algorithm.coin, Lax637351.Algorithm.coin, hp, PMF.pure_apply]

lemma independent_eq (n : ℕ) (p : ℝ) :
    OffspringEstimates.Algorithm.independentBits n p = Lax637351.Algorithm.independentBits n p := by
  ext x
  change (∏ j, OffspringEstimates.Algorithm.coin p (x j)) =
    ∏ j, Lax637351.Algorithm.coin p (x j = 1)
  exact Finset.prod_congr rfl (fun j _ ↦ coin_apply p (x j))

lemma mean_offspring (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (f : BitString n → ℝ) :
    mean (OffspringEstimates.Sampling.offspring p P) f = mean (draws p P) (fun d ↦ f (child d)) := by
  unfold OffspringEstimates.Sampling.offspring OffspringEstimates.Sampling.parents
  simp only [Bind.bind, Pure.pure, mean_bind, independent_eq]
  have h (g : Fin 2 → ℝ) : mean (OffspringEstimates.Algorithm.coin p) g = p * g 1 + (1 - p) * g 0 :=
    OffspringEstimates.FiniteComparison.mean_coin p hp g
  rw [h, mean_draws hp, ArrivalProgress.branch_cross]
  simp only [if_true, if_neg Fin.zero_ne_one, mean_bind, mean_pure, child]
  rw [mean_uniform_pair (fun i j : Fin μ ↦ mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
    mean (independentBits n (1 / (n : ℝ))) (fun t ↦ f (mutate (crossover (P i) (P j) m) t))))]

lemma submit_centered (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (f : BitString n → ℝ) (hf : slotMean f P = 0) :
    submitMean k p ar P f = mean (OffspringEstimates.Sampling.offspring p P)
      (fun z ↦ if (zeros z).card = k then f z else 0) := by
  have he : submitMean k p ar P f = submitMean k p false P f := by
    rw [submit_split p hp ar P hP, submit_split p hp false P hP, hf]
    simp only [mul_zero]
  rw [he, mean_offspring p hp, submitMean]
  congr 1
  funext d
  by_cases h : (zeros (child d)).card = k
  · simp [indicator, submitted, discarded, h]
  · simp [indicator, submitted, h]

lemma old_onPlateau (hkn : k ≤ n) (z : BitString n) :
    OffspringEstimates.PlateauDynamics.onPlateau k z ↔ (zeros z).card = k := by
  change ones z = n - k ↔ _
  have hh := ones_add_card_zeros z
  omega

lemma accepted_contrast (hkn : k ≤ n) (B : Genotypes.Genotype n k) (p : ℝ)
    (P : Population n μ) (q : ℝ) :
    mean (OffspringEstimates.Sampling.offspring p P) (fun z ↦ if (zeros z).card = k then
      SpeciesState.weightFunction B z - q * PopulationRatio.indicator (Genotypes.toString B) z else 0) =
      mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedWeight B) -
        q * mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedClone B) := by
  rw [← mean_mul, ← mean_sub, ← SpeciesState.accepted_indicator]
  congr 1
  funext z
  by_cases h : (zeros z).card = k
  · simp [h, (old_onPlateau hkn z).mpr h, ActualBirthKernels.acceptedWeight, SpeciesState.weightFunction]
  · simp [h, show ¬ OffspringEstimates.PlateauDynamics.onPlateau k z from fun hz ↦ h ((old_onPlateau hkn z).mp hz),
      ActualBirthKernels.acceptedWeight]

end
end Lax637351Proofs.OffspringBridge
