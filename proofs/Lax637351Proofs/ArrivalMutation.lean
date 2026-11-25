import Lax637351Proofs.PlateauPairs

namespace Lax637351Proofs.ArrivalMutation

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs (swap_card)
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def fitnessLevel {n : ℕ} (k : ℕ) (x : BitString n) : ℕ :=
  if x = optimum n then n + k
  else if k ≤ (zeros x).card then k + (n - (zeros x).card)
  else (zeros x).card

lemma fitnessLevel_eq (hkn : k ≤ n) (x : BitString n) :
    (fitnessLevel k x : ℝ) = jump k x := by
  unfold fitnessLevel
  split_ifs with hx h
  · rw [hx, jump_optimum, Nat.add_comm]
  · exact (jump_of_many_zeros hkn x h).symm
  · have hpos : 0 < (zeros x).card := by
      by_contra! hz
      exact hx ((zeros_eq_empty_iff x).mp (Finset.card_eq_zero.mp (by omega)))
    exact (jump_of_few_zeros hkn x hpos (by omega)).symm

lemma fitnessLevel_le_of_nonopt (_hkn : k ≤ n) {x : BitString n} (hx : x ≠ optimum n) :
    fitnessLevel k x ≤ n := by
  have hcard := Finset.card_le_univ (zeros x)
  rw [Fintype.card_fin] at hcard
  unfold fitnessLevel
  rw [if_neg hx]
  split_ifs <;> omega

lemma fitnessLevel_eq_plateau (_hkn : k ≤ n) {x : BitString n} (hx : x ≠ optimum n) :
    fitnessLevel k x = n ↔ (zeros x).card = k := by
  have hcard := Finset.card_le_univ (zeros x)
  rw [Fintype.card_fin] at hcard
  unfold fitnessLevel
  rw [if_neg hx]
  split_ifs <;> omega

def favorable (v : ℕ) (x m : BitString n) : Prop :=
  let z := mutate x m
  z ≠ x ∧ v < fitnessLevel k z

lemma mutation_progress (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (v : ℕ) (hv : v < n)
    (x : BitString n) (hx : x ≠ optimum n) (hxlevel : v ≤ fitnessLevel k x) :
    ((n - v : ℕ) : ℝ) / (32 * n) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ if favorable (k := k) v x m then 1 else 0) := by
  have hn : 2 ≤ n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let Z := (zeros x).card
  have hZle : Z ≤ n := by
    simpa [Z] using Finset.card_le_univ (zeros x)
  have hZpos : 0 < Z := by
    by_contra! h
    exact hx ((zeros_eq_empty_iff x).mp (Finset.card_eq_zero.mp (by dsimp [Z] at h; omega)))
  have hlevel : fitnessLevel k x = if k ≤ Z then k + (n - Z) else Z := by simp [fitnessLevel, hx, Z]
  let G := favorable (k := k) v x
  have hsingle (S : Finset (Fin n)) (hS : n - v ≤ 4 * S.card)
      (hm : ∀ j ∈ S, v < fitnessLevel k (mutate x (mask {j}))) :
      ((n - v : ℕ) : ℝ) / (32 * n) ≤
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦ if G m then 1 else 0) := by
    apply le_trans _ (single_mask_event hn S G (fun j hj ↦ ⟨mutate_mask_ne x (by simp), hm j hj⟩))
    have hS' : ((n - v : ℕ) : ℝ) ≤ 4 * (S.card : ℝ) := by exact_mod_cast hS
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hnew (m : BitString n) (h : k ≤ (zeros (mutate x m)).card) :
      fitnessLevel k (mutate x m) = k + (n - (zeros (mutate x m)).card) := by
    unfold fitnessLevel
    have hnopt : mutate x m ≠ optimum n := by
      intro heq
      rw [heq, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at h
      omega
    simp [hnopt, h]
  have hone (j : Fin n) (hj : j ∈ (zeros x)ᶜ) :
      (zeros (mutate x (mask {j}))).card = Z + 1 :=
    flip_one_card x (Finset.mem_compl.mp hj)
  have hzero (j : Fin n) (hj : j ∈ zeros x) :
      (zeros (mutate x (mask {j}))).card = Z - 1 := flip_zero_card x hj
  by_cases hval : v < k
  · by_cases hsmall : Z ≤ k
    · apply hsingle (zeros x)ᶜ
      · rw [Finset.card_compl, Fintype.card_fin]
        change n - v ≤ 4 * (n - Z)
        omega
      · intro j hj
        have heq := hone j hj
        have hnopt : mutate x (mask {j}) ≠ optimum n := by
          intro h
          rw [h, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at heq
          omega
        unfold fitnessLevel
        rw [if_neg hnopt, heq]
        rw [hlevel] at hxlevel
        split_ifs at hxlevel ⊢ <;> omega
    · apply hsingle Finset.univ
      · simp
        omega
      · intro j _
        by_cases hz : j ∈ zeros x
        · rw [hnew _ (by rw [hzero j hz]; omega), hzero j hz]
          omega
        · have hz' := hone j (Finset.mem_compl.mpr hz)
          rw [hnew _ (by omega), hz']
          omega
  · have hmany : k ≤ Z := by
      by_contra! h
      rw [hlevel, if_neg (by omega)] at hxlevel
      omega
    rw [hlevel, if_pos hmany] at hxlevel
    by_cases hstrict : k < Z
    · by_cases hlarge : n - v ≤ 4 * Z
      · apply hsingle (zeros x) hlarge
        intro j hj
        have hz := hzero j hj
        rw [hnew _ (by omega), hz]
        omega
      · apply hsingle (zeros x)ᶜ
        · rw [Finset.card_compl, Fintype.card_fin]
          change n - v ≤ 4 * (n - Z)
          omega
        · intro j hj
          have hz := hone j hj
          rw [hnew _ (by omega), hz]
          omega
    · have hZ : Z = k := by omega
      by_cases hfar : v + 1 < n
      · apply hsingle (zeros x)ᶜ
        · rw [Finset.card_compl, Fintype.card_fin]
          change n - v ≤ 4 * (n - Z)
          omega
        · intro j hj
          have hz := hone j hj
          rw [hnew _ (by omega), hz]
          omega
      · have hne : (zeros x).Nonempty := Finset.card_pos.mp hZpos
        obtain ⟨a, ha⟩ := hne
        apply le_trans _ (swap_mask_event hn a (zeros x)ᶜ (by simp [ha]) G ?_)
        · rw [Finset.card_compl, Fintype.card_fin]
          change ((n - v : ℕ) : ℝ) / (32 * n) ≤ ((n - Z : ℕ) : ℝ) / (8 * (n : ℝ) ^ 2)
          have hnv : n - v = 1 := by omega
          have hmore : n ≤ 2 * (n - Z) := by omega
          have hmore' : (n : ℝ) ≤ 2 * ((n - Z : ℕ) : ℝ) := by exact_mod_cast hmore
          rw [hnv]
          push_cast
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith
        · intro j hj
          have hj' := Finset.mem_compl.mp hj
          have hz := swap_card x ha hj'
          refine ⟨mutate_mask_ne x (by simp), ?_⟩
          rw [hnew _ (by omega), hz]
          omega

end
end Lax637351Proofs.ArrivalMutation
