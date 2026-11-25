import Lax637351Proofs.OffspringEstimates.Algorithm
import Mathlib.Tactic.NormNum

namespace Lax637351Proofs.OffspringEstimates.Dynamics

open Lax637351Proofs.OffspringEstimates.Algorithm
open scoped ENNReal Classical BigOperators

noncomputable section

lemma ones_le {n : ℕ} (x : BitString n) : ones x ≤ n := by
  calc
    ones x ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun j _ ↦ by
      have h := (x j).isLt
      omega
    _ = n := by simp

def missing {n : ℕ} {μ : ℕ+} : Set (Population n μ) := {P | ∀ i, P i ≠ optimum n}

end
end Lax637351Proofs.OffspringEstimates.Dynamics
