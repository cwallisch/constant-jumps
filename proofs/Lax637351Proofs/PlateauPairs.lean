import Lax637351Proofs.Mutation

namespace Lax637351Proofs.PlateauPairs

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def distance (x y : BitString n) : ℕ := (zeros x \ zeros y).card

def pairGood (i j : Fin μ) (r : ℕ) (P : Population n μ) : Prop :=
  ¬ missing P ∨ r ≤ distance (P i) (P j)

def plateau (P : Population n μ) : Prop := ∀ u, (zeros (P u)).card = k

lemma pairGood_zero (i j : Fin μ) (P : Population n μ) : pairGood i j 0 P :=
  Or.inr (Nat.zero_le _)

lemma distance_le_card (x y : BitString n) : distance x y ≤ (zeros x).card :=
  Finset.card_le_card Finset.sdiff_subset

lemma distance_eq_card_iff (x y : BitString n) :
    distance x y = (zeros x).card ↔ Disjoint (zeros x) (zeros y) := by
  have h := Finset.card_sdiff_add_card_inter (zeros x) (zeros y)
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
  unfold distance
  omega

lemma disjoint_from_swap (x y : BitString n) {a b : Fin n}
    (ha : a ∈ zeros x) (hb : b ∉ zeros x ∪ zeros y) :
    distance (mutate x (mask {a, b})) y =
      (if a ∈ zeros y then distance x y + 1 else distance x y) := by
  have hbx : b ∉ zeros x := fun h ↦ hb (Finset.mem_union_left _ h)
  have hby : b ∉ zeros y := fun h ↦ hb (Finset.mem_union_right _ h)
  rw [distance, swap_zero_set x ha hbx]
  have heq : ({b} ∪ (zeros x).erase a) \ zeros y = {b} ∪ (zeros x \ zeros y).erase a := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
    by_cases hu : u = b
    · simp [hu, hby]
    · simp [hu, and_assoc]
  rw [heq, Finset.singleton_union, Finset.card_insert_of_notMem]
  · by_cases hay : a ∈ zeros y
    · have hna : a ∉ zeros x \ zeros y := by simp [hay]
      simp [hay, distance]
    · have haa : a ∈ zeros x \ zeros y := Finset.mem_sdiff.mpr ⟨ha, hay⟩
      have hpos := Finset.card_pos.mpr ⟨a, haa⟩
      rw [if_neg hay, distance, Finset.card_erase_of_mem haa]
      omega
  · intro hm
    exact hbx (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hm)).1

lemma swap_card (x : BitString n) {a b : Fin n}
    (ha : a ∈ zeros x) (hb : b ∉ zeros x) :
    (zeros (mutate x (mask {a, b}))).card = (zeros x).card := by
  rw [swap_zero_set x ha hb, Finset.singleton_union, Finset.card_insert_of_notMem,
    Finset.card_erase_of_mem ha]
  · have hpos := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  · exact fun h ↦ hb (Finset.mem_of_mem_erase h)

lemma choose_remove {x y : BitString n} {r : ℕ}
    (hr : r < (zeros x).card) (hdist : r ≤ distance x y) :
    ∃ a ∈ zeros x, ∀ b ∉ zeros x ∪ zeros y,
      r + 1 ≤ distance (mutate x (mask {a, b})) y := by
  by_cases hfull : r < distance x y
  · have hne : (zeros x).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hne
    refine ⟨a, ha, fun b hb ↦ ?_⟩
    rw [disjoint_from_swap x y ha hb]
    split_ifs <;> omega
  · have hlt : distance x y < (zeros x).card := by omega
    have hi := Finset.card_sdiff_add_card_inter (zeros x) (zeros y)
    have hne : (zeros x ∩ zeros y).Nonempty :=
      Finset.card_pos.mp (by unfold distance at hlt; omega)
    obtain ⟨a, ha⟩ := hne
    obtain ⟨hax, hay⟩ := Finset.mem_inter.mp ha
    refine ⟨a, hax, fun b hb ↦ ?_⟩
    rw [disjoint_from_swap x y hax hb, if_pos hay]
    omega

lemma mean_supported_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ x ∈ p.support, f x = c) : mean p f = c := by
  apply le_antisymm
  · exact (mean_mono_on_support p (fun x hx ↦ (h x hx).le)).trans_eq (mean_const p c)
  · exact (mean_const p c).symm.le.trans (mean_mono_on_support p (fun x hx ↦ (h x hx).ge))

abbrev mark (P : Population n μ) (z : BitString n) (d : Fin ((μ : ℕ) + 1)) :
    Population n μ := replace P z d

def plateauResult (k : ℕ) (cross : Bool) (P : Population n μ) (y z : BitString n)
    (d : Fin ((μ : ℕ) + 1)) : Population n μ :=
  if z = optimum n then Function.update P 0 z
  else if (zeros z).card = k ∧ (cross = true ∨ z ≠ y) then mark P z d
  else P

lemma plateauResult_optimum (cross : Bool) (P : Population n μ) (y : BitString n) (d) :
    ¬ missing (plateauResult k cross P y (optimum n) d) := by
  intro h
  exact h 0 (by simp [plateauResult])

lemma plateau_result_mean (hk : 0 < k) (hkn : k ≤ n) (cross : Bool) (P : Population n μ)
    (hp : plateau (k := k) P) (y z : BitString n) (hy : cross = false → y ≠ optimum n)
    (f : Population n μ → ℝ) (hf : ∀ Q, ¬ missing Q → f Q = 1) :
    mean (select (jump k) true cross P y z) f =
      mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
        (fun d ↦ f (plateauResult k cross P y z d)) := by
  by_cases hopt : z = optimum n
  · subst z
    have hdiscard : ¬ (true = true ∧ ¬ cross = true ∧ optimum n = y) := by
      rintro ⟨_, hc, hy'⟩
      exact hy (Bool.eq_false_of_not_eq_true hc) hy'.symm
    rw [select, if_neg hdiscard]
    have hmiss (i : Fin μ) : P i ≠ optimum n := by
      intro h
      have hi := hp i
      rw [h, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hi
      omega
    rw [mean_supported_const _ _ 1, mean_supported_const _ _ 1]
    · intro d _
      exact hf _ (plateauResult_optimum cross P y d)
    · intro Q hQ
      obtain ⟨d, rfl, _⟩ := insert_strict_improvement (jump k) P _
        (0 : Fin μ) (jump_lt_optimum hk _ (hmiss 0)) hQ
      exact hf _ (fun hm ↦ hm d (Function.update_self d (optimum n) P))
  · by_cases hplat : (zeros z).card = k
    · cases cross
      · by_cases hzy : z = y
        · subst y
          simp [select, plateauResult, hopt, mean_const, mean_pure]
        · simp only [select, Bool.false_eq_true, not_false_eq_true, hzy, and_false,
            if_false]
          rw [insert_eq_uniform (jump k) P z (fun i ↦
            (jump_plateau hkn _ (hp i)).trans (jump_plateau hkn z hplat).symm), mean_map]
          congr 1
          funext d
          simp [plateauResult, hopt, hplat, hzy]
      · simp only [select, not_true_eq_false, false_and, and_false, if_false]
        rw [insert_eq_uniform (jump k) P z (fun i ↦
          (jump_plateau hkn _ (hp i)).trans (jump_plateau hkn z hplat).symm), mean_map]
        congr 1
        funext d
        simp [plateauResult, hopt, hplat]
    · have hz (i : Fin μ) : jump k z < jump k (P i) :=
        (jump_plateau hkn _ (hp i)).symm ▸ jump_lt_plateau hk hkn z hopt hplat
      simp only [plateauResult, hopt, hplat, false_and, if_false, mean_const]
      unfold select
      split_ifs
      · exact mean_pure _ _
      · apply mean_supported_const
        intro Q hQ
        rw [insert_support_of_worse (jump k) P z hz hQ]

end
end Lax637351Proofs.PlateauPairs
