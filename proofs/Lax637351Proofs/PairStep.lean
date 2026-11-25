import Lax637351Proofs.PlateauPairs

namespace Lax637351Proofs.PairStep

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def indicator (G : Prop) : ℝ := if G then 1 else 0

lemma indic_nonneg (G : Prop) : 0 ≤ indicator G := by unfold indicator; split_ifs <;> norm_num

lemma indic_le_one (G : Prop) : indicator G ≤ 1 := by unfold indicator; split_ifs <;> norm_num

lemma pair_off (P : Population n μ) (z : BitString n) (i j : Fin μ)
    (d : Fin ((μ : ℕ) + 1)) (hi : d ≠ i.castSucc) (hj : d ≠ j.castSucc) :
    distance (replace P z d i) (replace P z d j) = distance (P i) (P j) := by
  revert hi hj
  refine Fin.lastCases ?_ (fun u ↦ ?_) d
  · simp [replace]
  · intro hi hj
    have hui : i ≠ u := fun h ↦ hi (by rw [h])
    have huj : j ≠ u := fun h ↦ hj (by rw [h])
    simp [replace, Function.update_of_ne hui, Function.update_of_ne huj]

lemma pair_mark (P : Population n μ) (z : BitString n) (i j : Fin μ) (hij : i ≠ j) :
    distance (replace P z i.castSucc i) (replace P z i.castSucc j) = distance z (P j) := by
  simp [replace, Function.update_of_ne hij.symm]

lemma uniform_pair_target (P : Population n μ) (z : BitString n) (i j : Fin μ)
    (hij : i ≠ j) (r : ℕ) (hP : missing P) :
    (1 - 2 / ((μ : ℕ) + 1 : ℝ)) * indicator (pairGood i j r P) +
      indicator (r ≤ distance z (P j)) / ((μ : ℕ) + 1 : ℝ) ≤
      mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
        (fun d ↦ indicator (pairGood i j r (replace P z d))) := by
  have hn : i.castSucc ≠ j.castSucc := fun h ↦ hij (Fin.castSucc_injective _ h)
  have heq := uniform_avoid_two i.castSucc j.castSucc hn (indicator (pairGood i j r P))
    (indicator (r ≤ distance z (P j)))
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at heq
  rw [← heq]
  apply mean_mono
  intro d
  by_cases hi : d = i.castSucc
  · subst d
    rw [if_pos rfl]
    by_cases h : r ≤ distance z (P j)
    · have hgood : pairGood i j r (replace P z i.castSucc) :=
        Or.inr (by simpa only [pair_mark P z i j hij] using h)
      simp [indicator, h, hgood]
    · simpa [indicator, h] using indic_nonneg (pairGood i j r (replace P z i.castSucc))
  · rw [if_neg hi]
    by_cases hj : d = j.castSucc
    · rw [if_pos hj]
      exact indic_nonneg _
    · rw [if_neg hj]
      by_cases h : pairGood i j r P
      · have hgood : pairGood i j r (replace P z d) := by
          rcases h with hn | hr
          · exact (hn hP).elim
          · exact Or.inr (by simpa only [pair_off P z i j d hi hj] using hr)
        simp [indicator, h, hgood]
      · rw [indicator, if_neg h]
        exact indic_nonneg _

lemma select_pair_lower (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ)
    (hP : missing P) (hpl : plateau (k := k) P) (i j : Fin μ) (hij : i ≠ j)
    (r : ℕ) (cross : Bool) (x z : BitString n) (hx : cross = false → x ≠ optimum n)
    (e g : Prop)
    (he : (zeros z).card = k → cross = true ∨ z ≠ x → e)
    (hg : g → (zeros z).card = k ∧ (cross = true ∨ z ≠ x) ∧ r ≤ distance z (P j)) :
    (1 - 2 / ((μ : ℕ) + 1 : ℝ) * indicator e) * indicator (pairGood i j r P) +
      indicator g / ((μ : ℕ) + 1 : ℝ) ≤
      mean (select (jump k) true cross P x z) (fun Q ↦ indicator (pairGood i j r Q)) := by
  have hμ : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hpos : (0 : ℝ) < (μ : ℕ) + 1 := by linarith
  have hnonneg : 0 ≤ 2 / ((μ : ℕ) + 1 : ℝ) := by positivity
  have hdiv : (2 : ℝ) ≤ (μ : ℕ) + 1 := by linarith
  rw [plateau_result_mean hk hkn cross P hpl x z hx
    (fun Q ↦ indicator (pairGood i j r Q))]
  · by_cases hz : z = optimum n
    · have hnplat : (zeros z).card ≠ k := by
        simpa [hz, (zeros_eq_empty_iff (optimum n)).mpr rfl] using hk.ne'.symm
      have hng : ¬ g := fun h ↦ hnplat (hg h).1
      have hmean : mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
          (fun d ↦ indicator (pairGood i j r (plateauResult k cross P x z d))) = 1 := by
        subst z
        simp only [fun d ↦ show pairGood i j r (plateauResult k cross P x (optimum n) d) from
          Or.inl (plateauResult_optimum cross P x d), indicator, if_true, mean_const]
      rw [hmean, show indicator g = 0 by simp [indicator, hng], zero_div, add_zero]
      exact (mul_le_mul_of_nonneg_right
        (sub_le_self _ (mul_nonneg hnonneg (indic_nonneg e))) (indic_nonneg _)).trans
        (by simpa only [one_mul] using indic_le_one (pairGood i j r P))
    · by_cases hb : (zeros z).card = k ∧ (cross = true ∨ z ≠ x)
      · have hE := he hb.1 hb.2
        simp only [plateauResult, if_neg hz, if_pos hb]
        have hh := uniform_pair_target P z i j hij r hP
        apply le_trans _ hh
        have hg' : indicator g ≤ indicator (r ≤ distance z (P j)) := by
          by_cases hG : g
          · simp [indicator, hG, (hg hG).2.2]
          · simpa [indicator, hG] using indic_nonneg (r ≤ distance z (P j))
        simpa only [indicator, if_pos hE, mul_one] using
          add_le_add_right (div_le_div_of_nonneg_right hg' hpos.le)
            ((1 - 2 / ((μ : ℕ) + 1 : ℝ)) * indicator (pairGood i j r P))
      · have hng : ¬ g := fun h ↦ hb ⟨(hg h).1, (hg h).2.1⟩
        simp only [plateauResult, if_neg hz, if_neg hb, mean_const]
        rw [show indicator g = 0 by simp [indicator, hng], zero_div, add_zero]
        exact (mul_le_mul_of_nonneg_right
          (sub_le_self _ (mul_nonneg hnonneg (indic_nonneg e))) (indic_nonneg _)).trans_eq
          (one_mul _)
  · intro Q hQ
    simp [indicator, show pairGood i j r Q from Or.inl hQ]

def useful (k : ℕ) (r : ℕ) (x y m : BitString n) : Prop :=
  let z := mutate x m
  (zeros z).card = k ∧ z ≠ x ∧ r + 1 ≤ distance z y

lemma useful_lower (hk : 0 < k) (hn : 4 * k ≤ n)
    (r : ℕ) (hr : r < k) (x y : BitString n)
    (hx : (zeros x).card = k) (hy : (zeros y).card = k) :
    indicator (r ≤ distance x y) / (16 * n) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (useful k r x y m)) := by
  have hn2 : 2 ≤ n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases h : r ≤ distance x y
  · obtain ⟨a, ha, hgood⟩ := choose_remove (hx ▸ hr) h
    let S := (zeros x ∪ zeros y)ᶜ
    have hna : a ∉ S := by simp [S, ha]
    have hs : n ≤ 2 * S.card := by
      have hU := Finset.card_union_le (zeros x) (zeros y)
      rw [hx, hy] at hU
      simp only [S, Finset.card_compl, Fintype.card_fin]
      omega
    apply le_trans _ (swap_mask_event hn2 a S hna _ ?_)
    · have hsr : (n : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hs
      rw [indicator, if_pos h]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    · intro j hj
      have hnj : j ∉ zeros x ∪ zeros y := Finset.mem_compl.mp hj
      have hnx : j ∉ zeros x := fun h' ↦ hnj (Finset.mem_union_left _ h')
      exact ⟨(swap_card x ha hnx).trans hx, mutate_mask_ne x (by simp), hgood j hnj⟩
  · rw [indicator, if_neg h, zero_div]
    exact mean_nonneg _ (fun _ ↦ indic_nonneg _)

lemma mutation_pair_lower (hk : 0 < k) (hn : 4 * k ≤ n) (P : Population n μ)
    (hP : missing P) (hpl : plateau (k := k) P) (i j u : Fin μ) (hij : i ≠ j)
    (r : ℕ) (hr : r < k) :
    (1 - (2 / ((μ : ℕ) + 1 : ℝ)) * ((k : ℝ) / n)) *
        indicator (pairGood i j (r + 1) P) +
      (if u ≠ j then indicator (pairGood u j r P) else 0) /
        (16 * n * ((μ : ℕ) + 1) : ℝ) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦
        mean (select (jump k) true false P (P u) (mutate (P u) m))
          (fun Q ↦ indicator (pairGood i j (r + 1) Q))) := by
  let A := indicator (pairGood i j (r + 1) P)
  let D : ℝ := (μ : ℕ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hn' : 2 ≤ n := by omega
  let hit (m : BitString n) : Prop := ∃ l ∈ zeros (P u), m l = 1
  let good (m : BitString n) : Prop := u ≠ j ∧ useful k r (P u) (P j) m
  have hstep (m : BitString n) :
      A - ((2 / D) * A) * indicator (hit m) + D⁻¹ * indicator (good m) ≤
        mean (select (jump k) true false P (P u) (mutate (P u) m))
          (fun Q ↦ indicator (pairGood i j (r + 1) Q)) := by
    have hh := select_pair_lower hk (by omega : k ≤ n) P hP hpl i j hij (r + 1)
      false (P u) (mutate (P u) m) (fun _ ↦ hP u) (hit m) (good m)
      (fun hcard hchanged ↦ by
        by_contra hn
        have heq := equal_card_no_hit (P u) m hn (hcard.trans (hpl u).symm)
        simp [heq] at hchanged)
      (fun h ↦ ⟨h.2.1, Or.inr h.2.2.1, h.2.2.2⟩)
    calc
      _ = (1 - 2 / D * indicator (hit m)) * A + indicator (good m) / D := by ring
      _ ≤ _ := hh
  have hmean := mean_mono (independentBits n (1 / (n : ℝ))) hstep
  rw [mean_add, mean_sub, mean_const, mean_mul, mean_mul] at hmean
  have hhit : mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (hit m)) ≤
      (k : ℝ) / n := by
    have hh := mask_hit_upper hn' (zeros (P u))
    rw [hpl u] at hh
    convert hh using 2
    funext m
    simp [indicator, hit]
  have hgood : (if u ≠ j then indicator (pairGood u j r P) else 0) / (16 * n : ℝ) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (good m)) := by
    by_cases hu : u ≠ j
    · simpa [good, hu, pairGood, hP] using
        useful_lower hk hn r hr (P u) (P j) (hpl u) (hpl j)
    · simp [good, hu, indicator, mean_const]
  have ha' : 0 ≤ (2 / D) * A := mul_nonneg (by positivity) (indic_nonneg _)
  have hb := add_le_add
    (sub_le_sub_left (mul_le_mul_of_nonneg_left hhit ha') A)
    (mul_le_mul_of_nonneg_left hgood (inv_nonneg.mpr hD.le))
  apply le_trans _ (hb.trans hmean)
  change (1 - 2 / D * ((k : ℝ) / n)) * A +
    (if u ≠ j then indicator (pairGood u j r P) else 0) / (16 * n * D) ≤ _
  simp only [div_eq_mul_inv, mul_inv]
  ring_nf
  exact le_rfl

lemma crossover_pair_lower (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ)
    (hP : missing P) (hpl : plateau (k := k) P) (i j : Fin μ) (hij : i ≠ j) (r : ℕ)
    (y m : BitString n) :
    (1 - 2 / ((μ : ℕ) + 1 : ℝ)) * indicator (pairGood i j r P) ≤
      mean (select (jump k) true true P y (mutate y m))
        (fun Q ↦ indicator (pairGood i j r Q)) := by
  simpa [indicator] using select_pair_lower hk hkn P hP hpl i j hij r true y (mutate y m)
    (by simp) True False (by simp) (by simp)

end
end Lax637351Proofs.PairStep
