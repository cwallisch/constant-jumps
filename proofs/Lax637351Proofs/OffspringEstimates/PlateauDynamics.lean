import Lax637351Proofs.OffspringEstimates.Plateau
import Lax637351Proofs.OffspringEstimates.Deletion

namespace Lax637351Proofs.OffspringEstimates.PlateauDynamics

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Dynamics Lax637351Proofs.OffspringEstimates.Sampling
open Lax637351Proofs.OffspringEstimates.Deletion Lax637351Proofs.OffspringEstimates.Plateau
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def onPlateau {n : ℕ} (k : ℕ) (x : BitString n) : Prop := ones x = n - k

def plateauPopulation {n : ℕ} {μ : ℕ+} (k : ℕ) (P : Population n μ) : Prop :=
  ∀ i, onPlateau k (P i)

def auxiliaryInsert {n : ℕ} {μ : ℕ+} (k : ℕ) (P : Population n μ) (z : BitString n) :
    PMF (Population n μ) :=
  if onPlateau k z then Lax637351Proofs.OffspringEstimates.Sampling.insert (jump k) P z else PMF.pure P

def auxiliaryStep {n : ℕ} {μ : ℕ+} (k : ℕ) (p_c : ℝ) (P : Population n μ) :
    PMF (Population n μ) := (offspring p_c P).bind (auxiliaryInsert k P)

end
end Lax637351Proofs.OffspringEstimates.PlateauDynamics
