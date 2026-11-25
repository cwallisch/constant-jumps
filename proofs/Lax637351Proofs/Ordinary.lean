import Lax637351Proofs.OffspringProduct
import Lax637351Proofs.ArrivalMutation

namespace Lax637351Proofs.Ordinary

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.MarkedStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def ordinary (k : ℕ) (P : Population n μ) : Prop := ∀ i, k ≤ (zeros (P i)).card

def hasPlateau (k : ℕ) (P : Population n μ) : Prop := ∃ i, (zeros (P i)).card = k

def homogeneous (P : Population n μ) : Prop := ∀ i, P i = P 0

def homogeneousPlateau (k : ℕ) (P : Population n μ) : Prop :=
  plateau (k := k) P ∧ homogeneous P

lemma ordinary_missing (hk : 0 < k) {P : Population n μ} (hp : ordinary k P) : missing P := by
  intro i hi
  have hc := hp i
  rw [hi, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hc
  omega

lemma large_fitness_ordinary (hk : k ≤ n) (x : BitString n) (hx : x ≠ optimum n)
    (hf : (k : ℝ) ≤ jump k x) : k ≤ (zeros x).card := by
  by_contra! h
  have hpos : 0 < (zeros x).card := by
    by_contra! hn
    exact hx ((zeros_eq_empty_iff x).mp (Finset.card_eq_zero.mp (by omega)))
  rw [jump_of_few_zeros hk x hpos h] at hf
  have hle : k ≤ (zeros x).card := by exact_mod_cast hf
  omega

lemma ordinary_preserved (hk : k ≤ n) (p : ℝ) (ar : Bool) {P Q : Population n μ}
    (hp : ordinary k P) (hq : Q ∈ (step (jump k) p ar P).support) (hmiss : missing Q) :
    ordinary k Q := by
  intro i
  apply large_fitness_ordinary hk _ (hmiss i)
  have hf := step_fitness_mono (jump k) p ar P hq i
  rw [jump_of_many_zeros hk _ (hp i)] at hf
  exact le_trans (by exact_mod_cast Nat.le_add_right k (n - (zeros (P i)).card)) hf

lemma zero_persists_no_flip (x m : BitString n) (j : Fin n) (hx : j ∈ zeros x)
    (hm : m j ≠ 1) : j ∈ zeros (mutate x m) := by
  simp [mutate, hm, (mem_zeros x j).mp hx]

def dangerous (k : ℕ) (x m : BitString n) : Prop :=
  mutate x m ≠ x ∧ (zeros (mutate x m)).card ≤ k

lemma danger_bound (hn : 2 ≤ n) (x : BitString n) (hx : k ≤ (zeros x).card) :
    mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (dangerous k x m)) ≤ (k + 1 : ℝ) / n := by
  have hS (S : Finset (Fin n)) (hs : S.card ≤ k + 1)
      (h : ∀ m, dangerous k x m → ∃ j ∈ S, m j = 1) :
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (dangerous k x m)) ≤ (k + 1 : ℝ) / n := by
    apply le_trans _ (le_trans (mask_hit_upper hn S) (div_le_div_of_nonneg_right
      (by exact_mod_cast hs) (by positivity)))
    apply mean_mono
    intro m
    by_cases hm : dangerous k x m
    · simp only [indicator, if_pos hm, if_pos (h m hm), le_refl]
    · simp only [indicator, if_neg hm]
      split_ifs <;> norm_num
  by_cases he : (zeros x).card = k
  · apply hS (zeros x) (by omega)
    intro m hm
    by_contra h
    have hsub : zeros x ⊆ zeros (mutate x m) := by
      intro j hj
      exact zero_persists_no_flip x m j hj (fun hh ↦ h ⟨j, hj, hh⟩)
    have hcard : (zeros (mutate x m)).card = (zeros x).card := by
      have hlo := Finset.card_le_card hsub
      have hhi := hm.2
      omega
    exact hm.1 (equal_card_no_hit x m h hcard)
  · obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq (show k + 1 ≤ (zeros x).card by omega)
    apply hS S hcard.le
    intro m hm
    by_contra h
    have hsub' : S ⊆ zeros (mutate x m) := by
      intro j hj
      exact zero_persists_no_flip x m j (hsub hj) (fun hh ↦ h ⟨j, hj, hh⟩)
    have hl := Finset.card_le_card hsub'
    have hh := hm.2
    omega

end
end Lax637351Proofs.Ordinary
