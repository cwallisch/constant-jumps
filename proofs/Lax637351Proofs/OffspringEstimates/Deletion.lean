import Lax637351Proofs.OffspringEstimates.Sampling
import Lax637351Proofs.OffspringEstimates.FiniteDrift
import Lax637351Proofs.OffspringEstimates.Species

namespace Lax637351Proofs.OffspringEstimates.Deletion

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Sampling Lax637351Proofs.OffspringEstimates.FiniteDrift
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

def replace {n : ℕ} {μ : ℕ+} (P : Population n μ) (z : BitString n)
    (d : Fin ((μ : ℕ) + 1)) : Population n μ :=
  if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P

def total {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ) : ℝ := ∑ i, ψ (P i)

lemma total_update {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ)
    (i : Fin (μ : ℕ)) (z : BitString n) :
    total ψ (Function.update P i z) - total ψ P = ψ z - ψ (P i) := by
  rw [total, total,
    Lax637351Proofs.OffspringEstimates.Species.sum_split i (fun j ↦ ψ (Function.update P i z j)),
    Lax637351Proofs.OffspringEstimates.Species.sum_split i (fun j ↦ ψ (P j)), Function.update_self]
  have heq : Lax637351Proofs.OffspringEstimates.Species.offSum i (fun j ↦ ψ (Function.update P i z j)) =
      Lax637351Proofs.OffspringEstimates.Species.offSum i (fun j ↦ ψ (P j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [heq]
  ring

lemma total_replace_castSucc {n : ℕ} {μ : ℕ+} (ψ : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) (i : Fin (μ : ℕ)) :
    total ψ (replace P z i.castSucc) - total ψ P = ψ z - ψ (P i) := by
  have hi : i.castSucc.val < (μ : ℕ) := i.isLt
  rw [replace, dif_pos hi]
  exact total_update ψ P i z

end
end Lax637351Proofs.OffspringEstimates.Deletion
