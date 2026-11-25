import Lax637351Proofs.Ordinary
import Lax637351Proofs.CopyingStage

namespace Lax637351Proofs.CopyingModel

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.MarkedStep Lax637351Proofs.Ordinary
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def copies (A : BitString n) (P : Population n μ) : Finset (Fin μ) :=
  Finset.univ.filter fun i ↦ P i = A

def copyCount (A : BitString n) (P : Population n μ) : ℕ := (copies A P).card

@[simp] lemma mem_copies (A : BitString n) (P : Population n μ) (i : Fin μ) :
    i ∈ copies A P ↔ P i = A := by simp [copies]

lemma copyCount_update (A : BitString n) (P : Population n μ) (i : Fin μ) (hi : P i ≠ A) :
    copyCount A (Function.update P i A) = copyCount A P + 1 := by
  have heq : copies A (Function.update P i A) = {i} ∪ copies A P := by
    ext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  rw [copyCount, heq, Finset.singleton_union, Finset.card_insert_of_notMem (by simpa using hi)]
  rfl

lemma copyCount_update_other (A z : BitString n) (P : Population n μ) (i : Fin μ)
    (hi : P i ≠ A) (hz : z ≠ A) : copyCount A (Function.update P i z) = copyCount A P := by
  have heq : copies A (Function.update P i z) = copies A P := by
    ext j
    by_cases h : j = i <;> simp [h, hi, hz, Function.update_of_ne]
  simp only [copyCount, heq]

lemma copyCount_le (A : BitString n) (P : Population n μ) : copyCount A P ≤ (μ : ℕ) :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

lemma copyCount_full_iff (A : BitString n) (P : Population n μ) :
    copyCount A P = (μ : ℕ) ↔ ∀ i, P i = A := by
  unfold copyCount copies
  have h := Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin μ))) (p := fun i ↦ P i = A)
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ, forall_const] using h

lemma uniform_copyRate (A : BitString n) (P : Population n μ) :
    mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ indicator (P i = A)) =
      (copyCount A P : ℝ) / (μ : ℕ) := by
  rw [mean_uniform]
  simp only [Fintype.card_fin, indicator, copyCount, copies, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : P j = A <;> simp [h]

lemma invariant_next (hk : 0 < k) (hkn : k ≤ n) {P Q : Population n μ} (hp : ordinary k P)
    (cross : Bool) (x z : BitString n) (hz : z ≠ optimum n)
    (hQ : Q ∈ (select (jump k) true cross P x z).support) : ordinary k Q := by
  have hmiss (i : Fin μ) : Q i ≠ optimum n := by
    have hP := ordinary_missing hk hp
    unfold select at hQ
    split_ifs at hQ
    · rw [(PMF.mem_support_pure_iff _ _).mp hQ]
      exact hP i
    · rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨d, _, rfl⟩
      refine Fin.lastCases ?_ (fun j ↦ ?_) d
      · simpa [replace] using hP i
      · by_cases hi : i = j
        · simpa [replace, hi] using hz
        · simpa [replace, Function.update_of_ne hi] using hP i
  intro i
  apply large_fitness_ordinary hkn _ (hmiss i)
  have hh := select_fitness_mono (jump k) true cross P x z hQ i
  rw [jump_of_many_zeros hkn _ (hp i)] at hh
  exact le_trans (by exact_mod_cast Nat.le_add_right k (n - (zeros (P i)).card)) hh

lemma copyCount_wait (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ) (A : BitString n)
    (hA : (zeros A).card = k) (i : Fin μ) (m : BitString n)
    (hm : ¬ dangerous k (P i) m) (Q : Population n μ)
    (hQ : Q ∈ (select (jump k) true false P (P i) (mutate (P i) m)).support) :
    copyCount A Q = copyCount A P := by
  let z := mutate (P i) m
  by_cases he : z = P i
  · have hq : Q = P := by
      apply (PMF.mem_support_pure_iff _ _).mp
      simpa [select, z, he] using hQ
    rw [hq]
  · have hz : k < (zeros z).card := by
      exact lt_of_not_ge (fun h ↦ hm ⟨he, h⟩)
    have hnopt : z ≠ optimum n := by
      intro h
      rw [h, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hz
      omega
    have hzfit : jump k z < jump k A := by
      rw [jump_plateau hkn _ hA]
      exact jump_lt_plateau hk hkn z hnopt (Nat.ne_of_gt hz)
    have hq' : Q ∈ (Transitions.insert (jump k) P z).support := by
      unfold select at hQ
      simpa only [true_and, Bool.false_eq_true, not_false_eq_true, z, he,
        and_false, if_false] using hQ
    rcases (PMF.mem_support_map_iff _ _ _).mp hq' with ⟨d, hd, rfl⟩
    revert hd
    refine Fin.lastCases ?_ (fun u ↦ ?_) d
    · simp [replace]
    · intro hd
      simp only [replace, Fin.lastCases_castSucc]
      apply copyCount_update_other
      · intro hu
        have hh := deletion_min_lastCases (jump k) P z u.castSucc hd (Fin.last (μ : ℕ))
        rw [Fin.lastCases_castSucc, Fin.lastCases_last, hu] at hh
        exact (not_lt_of_ge hh) hzfit
      · intro hzA
        rw [hzA] at hzfit
        exact (lt_irrefl _) hzfit

end
end Lax637351Proofs.CopyingModel
