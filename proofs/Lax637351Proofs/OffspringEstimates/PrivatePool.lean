import Lax637351Proofs.OffspringEstimates.ColumnSlotSplit
import Lax637351Proofs.OffspringEstimates.ColumnKernels

namespace Lax637351Proofs.OffspringEstimates.PrivatePool

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Sampling Lax637351Proofs.OffspringEstimates.NamedBirth
open Lax637351Proofs.OffspringEstimates.BirthGeometry Lax637351Proofs.OffspringEstimates.BirthCouplings
open Lax637351Proofs.OffspringEstimates.ColumnSlotSplit
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Pool {n : ℕ} (i : Fin n) (x y : BitString n) :=
  {j : Fin n // j ≠ i ∧ x j ≠ y j}

def label {n : ℕ} (i : Fin n) (x y : BitString n) : Pool i x y ↪ Fin n :=
  Function.Embedding.subtype _

def common {n : ℕ} (i : Fin n) (x y : BitString n) : Finset (Fin n) :=
  (zeros x ∩ zeros y).erase i

lemma different_not_fresh {n : ℕ} (R : Finset (Fin n)) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) {j : Fin n} (hj : x j ≠ y j) : j ∉ R := by
  intro hjR
  exact hj ((hR j hjR).1.trans (hR j hjR).2.symm)

def sameEquiv {n : ℕ} (R : Finset (Fin n)) (i : Fin n) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (hi : x i = y i) :
    Differing R x y ≃ Pool i x y where
  toFun a := ⟨a.val.val, by
    refine ⟨?_, a.property⟩
    intro hai
    exact a.property (by rw [hai]; exact hi)⟩
  invFun a := ⟨⟨a.val, different_not_fresh R x y hR a.property.2⟩, a.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def distinguished {n : ℕ} (R : Finset (Fin n)) (i : Fin n) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (hi : x i ≠ y i) : Differing R x y :=
  ⟨⟨i, different_not_fresh R x y hR hi⟩, hi⟩

def mixedEquiv {n : ℕ} (R : Finset (Fin n)) (i : Fin n) (x y : BitString n)
    (hR : ∀ j ∈ R, x j = 1 ∧ y j = 1) (hi : x i ≠ y i) :
    {a : Differing R x y // a ≠ distinguished R i x y hR hi} ≃ Pool i x y where
  toFun a := ⟨a.val.val.val, by
    refine ⟨?_, a.val.property⟩
    intro hai
    exact a.property (Subtype.ext (Subtype.ext hai))⟩
  invFun a := ⟨⟨⟨a.val, different_not_fresh R x y hR a.property.2⟩, a.property.2⟩, by
    intro heq
    have hval := congrArg (fun z : Differing R x y ↦ z.val.val) heq
    exact a.property.1 hval⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma column_extra {n : ℕ} (R : Finset (Fin n)) (i : Fin n) (x y : BitString n) (hiR : i ∉ R) :
    Extra (common i x y) (label i x y) R i :=
  ⟨Finset.notMem_erase _ _, hiR, fun a ↦ a.property.1⟩

def test {n : ℕ} (i : Fin n) (b : Fin 2) (f : BitString n → ℝ) (x : BitString n) : ℝ :=
  if x i = 1 then f (Function.update x i b) else 0

lemma value_test {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (k : ℕ)
    (C : Finset (Fin n)) (l : α ↪ Fin n) (R : Finset (Fin n)) (i : Fin n)
    (hi : Extra C l R i) (b : Fin 2) (f : BitString n → ℝ) :
    BirthOn.value k C l R (test i b f) =
      BirthOn.value k C l R (fun x ↦ f (Function.update x i b)) := by
  apply value_congr
  intro J F
  unfold test
  rw [if_pos (constructed_column_one C l R hi J F)]

lemma value_test_one {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (k : ℕ)
    (C : Finset (Fin n)) (l : α ↪ Fin n) (R : Finset (Fin n)) (i : Fin n)
    (hi : Extra C l R i) (f : BitString n → ℝ) :
    BirthOn.value k C l R (test i 1 f) = BirthOn.value k C l R f := by
  apply value_congr
  intro J F
  have hbit := constructed_column_one C l R hi J F
  unfold test
  rw [if_pos hbit]
  have hu : Function.update (fromZeros (C ∪ J.map l ∪ F.map (freshEmbedding R))) i 1 =
      fromZeros (C ∪ J.map l ∪ F.map (freshEmbedding R)) := by
    rw [← hbit, Function.update_eq_self]
  rw [hu]

lemma zeros_update_zero {n : ℕ} (x : BitString n) (i : Fin n) :
    zeros (Function.update x i 0) = insert i (zeros x) := by
  have hu : Function.update x i 0 = fromZeros (insert i (zeros x)) := by
    rw [fromZeros_insert, fromZeros_zeros]
  rw [hu, zeros_fromZeros]

lemma test_resident_support {n r : ℕ} (i : Fin n) (f : BitString n → ℝ)
    (hf : ∀ x, (zeros x).card ≠ r + 1 → f x = 0) (x : BitString n) (hx : (zeros x).card ≠ r) :
    test i 0 f x = 0 := by
  unfold test
  split_ifs with hxi
  · apply hf
    rw [zeros_update_zero, Finset.card_insert_of_notMem (by simp [mem_zeros, hxi])]
    omega
  · rfl

lemma test_mutant_support {n r : ℕ} (i : Fin n) (f : BitString n → ℝ)
    (hf : ∀ x, (zeros x).card ≠ r → f x = 0) (x : BitString n) (hx : (zeros x).card ≠ r) :
    test i 1 f x = 0 := by
  unfold test
  split_ifs with hxi
  · have hu : Function.update x i 1 = x := by rw [← hxi, Function.update_eq_self]
    rw [hu]
    exact hf x hx
  · rfl

lemma common_eq_inter {n : ℕ} (i : Fin n) (x y : BitString n) :
    common i x y = (zeros x).erase i ∩ (zeros y).erase i := by
  ext j
  simp only [common, Finset.mem_erase, Finset.mem_inter]
  tauto

end
end Lax637351Proofs.OffspringEstimates.PrivatePool
