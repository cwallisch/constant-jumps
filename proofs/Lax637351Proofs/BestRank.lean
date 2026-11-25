import Lax637351Proofs.CopyingModel
import Lax637351Proofs.PairAveraging

namespace Lax637351Proofs.BestRank

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.CopyingModel Lax637351Proofs.Ordinary
open Lax637351Proofs.PairAveraging Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def bestZeros (P : Population n μ) : ℕ :=
  (Finset.univ.image (fun i ↦ (zeros (P i)).card)).min'
    ⟨(zeros (P 0)).card, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

lemma bestZeros_le (P : Population n μ) (i : Fin μ) : bestZeros P ≤ (zeros (P i)).card := by
  unfold bestZeros
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

lemma bestZeros_attains (P : Population n μ) : ∃ i : Fin μ, (zeros (P i)).card = bestZeros P := by
  have h := Finset.min'_mem (Finset.univ.image (fun i ↦ (zeros (P i)).card))
    (show (Finset.univ.image (fun i ↦ (zeros (P i)).card)).Nonempty from
      ⟨(zeros (P 0)).card, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact ⟨i, hi⟩

lemma ordinary_iff_bestZeros (P : Population n μ) : ordinary k P ↔ k ≤ bestZeros P := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := bestZeros_attains P
    exact hi ▸ h i
  · exact fun h i ↦ h.trans (bestZeros_le P i)

def bestCount (P : Population n μ) : ℕ :=
  Finset.univ.sup (fun i ↦ if (zeros (P i)).card = bestZeros P then copyCount (P i) P else 0)

lemma bestCount_ge (P : Population n μ) (i : Fin μ) (hi : (zeros (P i)).card = bestZeros P) :
    copyCount (P i) P ≤ bestCount P := by
  unfold bestCount
  have h := Finset.le_sup (f := fun j : Fin μ ↦ if (zeros (P j)).card = bestZeros P then copyCount (P j) P else 0)
    (Finset.mem_univ i)
  simpa only [if_pos hi] using h

lemma bestCount_pos (P : Population n μ) : 0 < bestCount P := by
  obtain ⟨i, hi⟩ := bestZeros_attains P
  have h := Finset.card_pos.mpr (show (copies (P i) P).Nonempty from
    ⟨i, (mem_copies _ _ _).mpr rfl⟩)
  exact h.trans_le (bestCount_ge P i hi)

lemma bestCount_exists (P : Population n μ) :
    ∃ i : Fin μ, (zeros (P i)).card = bestZeros P ∧ copyCount (P i) P = bestCount P := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    (⟨(0 : Fin μ), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin μ)).Nonempty)
    (fun j ↦ if (zeros (P j)).card = bestZeros P then copyCount (P j) P else 0)
  change bestCount P = _ at hi
  by_cases hh : (zeros (P i)).card = bestZeros P
  · exact ⟨i, hh, (hi.trans (if_pos hh)).symm⟩
  · have hc : bestCount P = 0 := hi.trans (if_neg hh)
    exact (Nat.ne_of_gt (bestCount_pos P) hc).elim

lemma bestCount_le (P : Population n μ) : bestCount P ≤ (μ : ℕ) := by
  obtain ⟨i, _, hi⟩ := bestCount_exists P
  rw [← hi]
  exact copyCount_le _ _

lemma bestCount_full (P : Population n μ) : bestCount P = (μ : ℕ) ↔ homogeneous P := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := bestCount_exists P
    have hall := (copyCount_full_iff (P i) P).mp (hi.trans h)
    exact fun j ↦ (hall j).trans (hall 0).symm
  · intro h
    obtain ⟨i, _, hi⟩ := bestCount_exists P
    rw [← hi]
    exact (copyCount_full_iff _ _).mpr (fun j ↦ (h j).trans (h i).symm)

lemma count_cast_sum (A : BitString n) (P : Population n μ) :
    (copyCount A P : ℝ) = ∑ i, indicator (P i = A) := by
  simp only [copyCount, copies, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, indicator]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P i = A <;> simp [h]

lemma replace_counts (A z : BitString n) (P : Population n μ) (d : Fin ((μ : ℕ) + 1)) :
    copyCount A (replace P z d) ≤ copyCount A P + 1 ∧
      copyCount A P ≤ copyCount A (replace P z d) + 1 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [replace]
  · have h := PairAveraging.sum_update P i z (fun x ↦ indicator (x = A))
    simp only [replace, Fin.lastCases_castSucc]
    rw [← count_cast_sum, ← count_cast_sum] at h
    have h₁ : (copyCount A (Function.update P i z) : ℝ) ≤ (copyCount A P : ℝ) + 1 := by
      linarith [indic_nonneg (P i = A), indic_le_one (z = A)]
    have h₂ : (copyCount A P : ℝ) ≤ (copyCount A (Function.update P i z) : ℝ) + 1 := by
      linarith [indic_le_one (P i = A), indic_nonneg (z = A)]
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

lemma lower_best_notlost (hkn : k ≤ n) (P Q : Population n μ) (hP : ordinary k P)
    (hQ : ordinary k Q) (hfit : ∀ i, jump k (P i) ≤ jump k (Q i)) :
    bestZeros Q ≤ bestZeros P := by
  obtain ⟨i, hi⟩ := bestZeros_attains P
  have hs := hfit i
  rw [jump_of_many_zeros hkn _ (hP i), jump_of_many_zeros hkn _ (hQ i)] at hs
  have he : k + (n - (zeros (P i)).card) ≤ k + (n - (zeros (Q i)).card) := by exact_mod_cast hs
  have hp := Finset.card_le_univ (zeros (P i))
  have hq := Finset.card_le_univ (zeros (Q i))
  simp only [Fintype.card_fin] at hp hq
  rw [← hi]
  exact (bestZeros_le Q i).trans (by omega)

lemma copyCount_le_of_best (P : Population n μ) (A : BitString n) (hA : (zeros A).card = bestZeros P) :
    copyCount A P ≤ bestCount P := by
  by_cases h : (copies A P).Nonempty
  · obtain ⟨i, hi⟩ := h
    have he := (mem_copies A P i).mp hi
    rw [← he] at hA ⊢
    exact bestCount_ge P i hA
  · have he : copyCount A P = 0 := Finset.card_eq_zero.mpr (by simpa using h)
    rw [he]
    exact Nat.zero_le _

lemma bestCount_adjacent (P : Population n μ) (z : BitString n) (d : Fin ((μ : ℕ) + 1))
    (he : bestZeros (replace P z d) = bestZeros P) :
    bestCount P ≤ bestCount (replace P z d) + 1 := by
  obtain ⟨i, hi, hcnt⟩ := bestCount_exists P
  have hscore : copyCount (P i) (replace P z d) ≤ bestCount (replace P z d) :=
    copyCount_le_of_best _ _ (hi.trans he.symm)
  rw [← hcnt]
  exact (replace_counts (P i) z P d).2.trans (Nat.add_le_add_right hscore _)

end
end Lax637351Proofs.BestRank
