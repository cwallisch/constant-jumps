import Lax637351Proofs.CoordinateExtension
import Lax637351Proofs.ArrivalMutation

namespace Lax637351Proofs.CrossBand

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.FairCrossover Lax637351Proofs.CoordinateExtension
open Lax637351Proofs.Mutation Lax637351Proofs.ArrivalMutation
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ}

def maskDual : BitString n ≃ BitString n :=
  Equiv.piCongrRight fun _ ↦ (Equiv.swap (0 : Fin 2) 1)

lemma maskDual_apply (m : BitString n) (i : Fin n) :
    maskDual m i = if m i = 1 then 0 else 1 := by
  change Equiv.swap (0 : Fin 2) 1 (m i) = _
  obtain h | h := (show m i = 0 ∨ m i = 1 by by_cases he : m i = 0; exact Or.inl he; exact Or.inr (bit_eq_one_of_ne_zero _ he)) <;> simp [h]

lemma cross_dual_count (x y m : BitString n) :
    (zeros (crossover x y m)).card + (zeros (crossover x y (maskDual m))).card =
      (zeros x).card + (zeros y).card := by
  simp only [zeros, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain h | h := (show m i = 0 ∨ m i = 1 by by_cases he : m i = 0; exact Or.inl he; exact Or.inr (bit_eq_one_of_ne_zero _ he)) <;> simp [maskDual_apply, crossover, h, add_comm]

lemma symmetric_mean (f : BitString n → ℝ) :
    mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ f (maskDual m)) =
      mean (PMF.uniformOfFintype (BitString n)) f := by
  rw [← mean_map, uniform_map_equiv]

lemma mask_copies_first (x y : BitString n) :
    (1 / 2 : ℝ) ^ (mismatch x y).card ≤
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ indicator (crossover x y m = x)) := by
  let S := mismatch x y
  rw [← mask_pattern_weight S (fun _ ↦ 1)]
  apply mean_mono
  intro m
  by_cases hm : (fun j : S ↦ m j) = fun _ ↦ 1
  · have he : crossover x y m = x := by
      funext j
      by_cases hj : j ∈ S
      · have hs := congrFun hm ⟨j, hj⟩
        change m j = 1 at hs
        simp [crossover, hs]
      · have hs : x j = y j := by simpa [S, mismatch] using hj
        simp [crossover, hs]
    simp [indicator, hm, he]
  · simpa only [indicator, if_neg hm] using indic_nonneg (crossover x y m = x)

lemma cross_lower_half (x y : BitString n) (v : ℕ)
    (hx : v ≤ (zeros x).card) (hy : v ≤ (zeros y).card) :
    (1 / 2 : ℝ) ≤ mean (PMF.uniformOfFintype (BitString n))
       (fun m ↦ indicator (v ≤ (zeros (crossover x y m)).card)) := by
  let f (m : BitString n) := indicator (v ≤ (zeros (crossover x y m)).card)
  have h (m : BitString n) : 1 ≤ f m + f (maskDual m) := by
    have he := cross_dual_count x y m
    dsimp [f, indicator]
    split_ifs <;> (try norm_num); omega
  have hm := mean_mono (PMF.uniformOfFintype (BitString n)) h
  rw [mean_const, mean_add, symmetric_mean] at hm
  change _ ≤ mean _ f
  linarith

lemma available_band (x y : BitString n) (z : ℕ)
    (hx : k ≤ (zeros x).card ∧ (zeros x).card ≤ z)
    (_hy : k ≤ (zeros y).card) (hsum : (zeros x).card + (zeros y).card ≤ 2 * z + 1) :
    (1 / 2 : ℝ) ^ (2 * k + 1) ≤ mean (PMF.uniformOfFintype (BitString n))
      (fun m ↦ indicator (k ≤ (zeros (crossover x y m)).card ∧ (zeros (crossover x y m)).card ≤ z)) := by
  let f (m : BitString n) :=
    indicator (k ≤ (zeros (crossover x y m)).card ∧ (zeros (crossover x y m)).card ≤ z)
  change _ ≤ mean _ f
  by_cases h : (mismatch x y).card < 2 * k
  · apply (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show (mismatch x y).card ≤ 2 * k + 1 by omega)).trans
    apply (mask_copies_first x y).trans
    apply mean_mono
    intro m
    by_cases hm : crossover x y m = x
    · simp [f, indicator, hm, hx]
    · rw [indicator, if_neg hm]
      exact indic_nonneg _
  · obtain ⟨U, hU, hUk⟩ := Finset.exists_subset_card_eq (s := mismatch x y) (n := 2 * k) (by omega)
    obtain ⟨A, hA, hAk⟩ := Finset.exists_subset_card_eq (s := U) (n := k) (by omega)
    let B := U \ A
    have hBk : B.card = k := by
      dsimp [B]
      rw [Finset.card_sdiff_of_subset hA]
      omega
    let m0 (j : U) : Fin 2 := if (x j = 0) = (j.val ∈ A) then 1 else 0
    let g (m : BitString n) := indicator ((fun j : U ↦ m j) = m0)
    have hinv (m : BitString n) (hm : (fun j : U ↦ m j) = m0) (i : Fin n) (hi : i ∈ U) :
        (crossover x y m) i = 0 ↔ i ∈ A := by
      have hd := (Finset.mem_filter.mp (hU hi)).2
      have hc := congrFun hm ⟨i, hi⟩
      change m i = if (x i = 0) = (i ∈ A) then 1 else 0 at hc
      by_cases ha : i ∈ A <;> by_cases hz : x i = 0
      · simp [ha, hz] at hc
        simp [crossover, hc, ha, hz]
      · have hyz : y i = 0 := by
          by_contra he
          exact hd ((bit_eq_one_of_ne_zero _ hz).trans (bit_eq_one_of_ne_zero _ he).symm)
        simp [ha, hz] at hc
        simp [crossover, hc, ha, hyz]
      · have hyz : y i ≠ 0 := fun he ↦ hd (hz.trans he.symm)
        simp [ha, hz] at hc
        simp [crossover, hc, ha, hyz]
      · simp [ha, hz] at hc
        simp [crossover, hc, ha, hz]
    have h1 (m : BitString n) (hm : (fun j : U ↦ m j) = m0) : k ≤ (zeros (crossover x y m)).card := by
      rw [← hAk]
      apply Finset.card_le_card
      intro i hi
      exact (mem_zeros _ _).mpr ((hinv m hm i (hA hi)).mpr hi)
    have h2 (m : BitString n) (hm : (fun j : U ↦ m j) = m0) :
        k ≤ (zeros (crossover x y (maskDual m))).card := by
      rw [← hBk]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨hiU, hiA⟩ := Finset.mem_sdiff.mp hi
      have hd := (Finset.mem_filter.mp (hU hiU)).2
      have hz := fun he ↦ hiA ((hinv m hm i hiU).mp he)
      apply (mem_zeros _ _).mpr
      obtain he | he := (show m i = 0 ∨ m i = 1 by by_cases he : m i = 0; exact Or.inl he; exact Or.inr (bit_eq_one_of_ne_zero _ he))
      · simp only [crossover, he, Fin.zero_ne_one, if_false] at hz
        have hx' : x i = 0 := by
          by_contra hn
          exact hd ((bit_eq_one_of_ne_zero _ hn).trans (bit_eq_one_of_ne_zero _ hz).symm)
        simp [maskDual_apply, crossover, he, hx']
      · simp only [crossover, he, if_true] at hz
        have hy' : y i = 0 := by
          by_contra hn
          exact hd ((bit_eq_one_of_ne_zero _ hz).trans (bit_eq_one_of_ne_zero _ hn).symm)
        simp [maskDual_apply, crossover, he, hy']
    have hd (m : BitString n) : g m ≤ f m + f (maskDual m) := by
      by_cases hm : (fun j : U ↦ m j) = m0
      · have ha := h1 m hm
        have hb := h2 m hm
        have hs := cross_dual_count x y m
        have hh : (zeros (crossover x y m)).card ≤ z ∨
            (zeros (crossover x y (maskDual m))).card ≤ z := by omega
        rcases hh with hu | hu
        · simp [g, f, indicator, hm, ha, hu]
          exact indic_nonneg _
        · simp [g, f, indicator, hm, hb, hu]
          exact indic_nonneg _
      · rw [show g m = 0 from if_neg hm]
        exact add_nonneg (indic_nonneg _) (indic_nonneg _)
    have hh := mean_mono (PMF.uniformOfFintype (BitString n)) hd
    rw [mean_add, symmetric_mean] at hh
    rw [show mean (PMF.uniformOfFintype (BitString n)) g = (1 / 2 : ℝ) ^ (2 * k) by
      rw [show g = _ from rfl, mask_pattern_weight, hUk]] at hh
    rw [pow_succ]
    linarith

end
end Lax637351Proofs.CrossBand
