import Lax637351.Runtime
import Lax637351Proofs.FiniteChain
import Lax637351Proofs.Transitions

namespace Lax637351Proofs.RuntimeBridge

open Lax637351.Algorithm Lax637351.Runtime
open Lax637351Proofs.FiniteChain Lax637351Proofs.Transitions
open scoped ENNReal Classical

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma populationDistribution_eq (n k : ℕ) (μ : ℕ+) (p : ℝ) (avoid : Bool) (t : ℕ) :
    populationDistribution n k μ p avoid t =
      law (step (jump k) p avoid) (PMF.uniformOfFintype (Population n μ)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (populationDistribution n k μ p avoid t).bind (step (jump k) p avoid) = _
    rw [ih]
    rfl

lemma expectedOptimizationTime_eq (n k : ℕ) (μ : ℕ+) (p : ℝ) (avoid : Bool) :
    expectedOptimizationTime n k μ p avoid =
      ∑' t, (law (step (jump k) p avoid) (PMF.uniformOfFintype (Population n μ)) t).toOuterMeasure
        {P | missing P} := by
  unfold expectedOptimizationTime
  apply tsum_congr
  intro t
  rw [← populationDistribution_eq, PMF.toOuterMeasure_apply_fintype, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  by_cases h : ∀ i, P i ≠ optimum n
  · have hs : P ∈ ({Q | missing Q} : Set (Population n μ)) := h
    rw [Set.indicator_of_mem hs, if_pos h]
  · have hs : P ∉ ({Q | missing Q} : Set (Population n μ)) := h
    rw [Set.indicator_of_notMem hs, if_neg h]

lemma step_missing_eq_zero (hk : 0 < k) (p : ℝ) (avoid : Bool) (P : Population n μ)
    (hP : ¬ missing P) :
    (step (jump k) p avoid P).toOuterMeasure {Q | missing Q} = 0 := by
  exact event_zero_of_support _ _ (fun Q hQ ↦ step_preserves_optimum hk p avoid hP hQ)

lemma expectedOptimizationTime_le_of_block (n k : ℕ) (μ : ℕ+) (p : ℝ) (avoid : Bool)
    (hk : 0 < k) (L : ℕ) (hL : 0 < L) (r : ℝ≥0∞)
    (hblock : ∀ P : Population n μ, missing P →
      (law (step (jump k) p avoid) (PMF.pure P) L).toOuterMeasure {Q | missing Q} ≤ r) :
    expectedOptimizationTime n k μ p avoid ≤ (L : ℝ≥0∞) * (1 - r)⁻¹ := by
  rw [expectedOptimizationTime_eq]
  exact runtime_le_of_block _ _ _ (step_missing_eq_zero hk p avoid) L hL r hblock

end
end Lax637351Proofs.RuntimeBridge
