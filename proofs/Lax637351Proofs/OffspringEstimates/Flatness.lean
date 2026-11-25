import Lax637351Proofs.OffspringEstimates.Sampling
import Mathlib.Tactic.Linarith

namespace Lax637351Proofs.OffspringEstimates.Flatness

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Sampling
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def columnCount {n : ℕ} {μ : ℕ+} (P : Population n μ) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i ↦ P i j = 0)).card

def complementary {n : ℕ} {μ : ℕ+} (P : Population n μ) :
    Set (Fin (μ : ℕ) × Fin (μ : ℕ)) :=
  {uv | Disjoint (zeros (P uv.1)) (zeros (P uv.2))}

end
end Lax637351Proofs.OffspringEstimates.Flatness
