import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax637351Proofs.OffspringEstimates.FiniteChain

open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*}

def law (K : α → PMF α) (p : PMF α) : ℕ → PMF α
  | 0 => p
  | t + 1 => (law K p t).bind K

lemma event_le_one (p : PMF α) (A : Set α) : p.toOuterMeasure A ≤ 1 := by
  calc
    p.toOuterMeasure A ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ A)
    _ = 1 := by simp [PMF.toOuterMeasure_apply]

lemma event_add_compl (p : PMF α) (A : Set α) :
    p.toOuterMeasure A + p.toOuterMeasure Aᶜ = 1 := by
  classical
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  calc
    (∑' x, (A.indicator p x + Aᶜ.indicator p x)) = ∑' x, p x := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ A <;> simp [hx]
    _ = 1 := p.tsum_coe

end
end Lax637351Proofs.OffspringEstimates.FiniteChain
