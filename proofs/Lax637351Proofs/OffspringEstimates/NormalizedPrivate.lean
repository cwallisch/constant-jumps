import Lax637351Proofs.OffspringEstimates.PrivateKernelFormula
import Lax637351Proofs.OffspringEstimates.CatalystBounds

namespace Lax637351Proofs.OffspringEstimates.NormalizedPrivate

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Sampling Lax637351Proofs.OffspringEstimates.NamedBirth
open Lax637351Proofs.OffspringEstimates.PrivatePool Lax637351Proofs.OffspringEstimates.PrivateKernelFormula
open Lax637351Proofs.OffspringEstimates.ColumnKernels Lax637351Proofs.OffspringEstimates.BirthGeometry
open Lax637351Proofs.OffspringEstimates.CurveBounds Lax637351Proofs.OffspringEstimates.FiniteDrift
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma resident_private_size {n r : ℕ} {i : Fin n} (x : ColumnClass n (r + 1) i 0) :
    ((zeros x.val).erase i).card = r := by
  rw [Finset.card_erase_of_mem (by rw [mem_zeros]; exact x.property.2), x.property.1]
  omega

lemma mutant_private_size {n r : ℕ} {i : Fin n} (x : ColumnClass n r i 1) :
    ((zeros x.val).erase i).card = r := by
  rw [Finset.erase_eq_of_notMem (by simp [mem_zeros, x.property.2]), x.property.1]

lemma liftClass_exact_support {n k : ℕ} {i : Fin n} {b : Fin 2}
    (h : ColumnClass n k i b → ℝ) (x : BitString n) (hx : (zeros x).card ≠ k) : liftClass h x = 0 := by
  unfold liftClass
  rw [dif_neg (fun h ↦ hx h.1)]

end
end Lax637351Proofs.OffspringEstimates.NormalizedPrivate
