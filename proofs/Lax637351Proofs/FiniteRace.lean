import Lax637351Proofs.FiniteHitting

namespace Lax637351Proofs.FiniteRace

open Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

lemma visit_lower_through (K : α → PMF α) (G H : Set α) (r : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hq' : q ≤ 1) (h : ∀ x ∈ G, q ≤ visit K H r x) (t : ℕ) (x : α) :
    q * visit K G t x ≤ visit K H (t + r) x := by
  induction t generalizing x with
  | zero =>
    by_cases hx : x ∈ G
    · simpa [visit, hx] using h x hx
    · simpa [visit, hx] using visit_nonneg K H r x
  | succ t ih =>
    by_cases hx : x ∈ G
    · rw [visit_in K G _ x hx, mul_one]
      exact (h x hx).trans (visit_monotone K H x (Nat.le_add_left _ _))
    · by_cases hh : x ∈ H
      · rw [visit_in K H _ x hh]
        exact (mul_le_mul_of_nonneg_left (visit_le_one K G _ x) hq).trans (by simpa using hq')
      · rw [show t + 1 + r = t + r + 1 by omega, visit, if_neg hx, visit, if_neg hh, ← mean_mul]
        exact mean_mono _ ih

def raceBound (δ : ℝ) (t : ℕ) : ℝ := (1 - (1 - δ) ^ t) / 2

lemma raceBound_mem {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (t : ℕ) :
    0 ≤ raceBound δ t ∧ raceBound δ t ≤ 1 / 2 := by
  have hpow := pow_le_one₀ (sub_nonneg.mpr hδ') (sub_le_self 1 hδ) (n := t)
  have hpos := pow_nonneg (sub_nonneg.mpr hδ') t
  unfold raceBound
  constructor <;> linarith

lemma visit_race (K : α → PMF α) (G B I : Set α)
    (hGB : Disjoint G B) (hGI : Disjoint G I) (hBI : Disjoint B I)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hsupp : ∀ x ∈ I, ∀ y ∈ (K x).support, y ∈ G ∪ B ∪ I)
    (hcomp : ∀ x ∈ I, mean (K x) (fun y ↦ if y ∈ B then 1 else 0) ≤
      mean (K x) (fun y ↦ if y ∈ G then 1 else 0))
    (hbad : ∀ x ∈ I, δ ≤ mean (K x) (fun y ↦ if y ∈ B then 1 else 0))
    (t : ℕ) (x : α) (hx : x ∈ I) : raceBound δ t ≤ visit K G t x := by
  induction t generalizing x with
  | zero => simpa [raceBound] using visit_nonneg K G 0 x
  | succ t ih =>
    let q := raceBound δ t
    let g := mean (K x) (fun y ↦ if y ∈ G then 1 else 0)
    let b := mean (K x) (fun y ↦ if y ∈ B then 1 else 0)
    have ⟨hq, hq'⟩ := raceBound_mem hδ hδ' t
    have hp (y : α) (hy : y ∈ (K x).support) :
        (if y ∈ G then 1 else 0) +
            q * (1 - (if y ∈ G then 1 else 0) - (if y ∈ B then 1 else 0)) ≤
          visit K G t y := by
      rcases hsupp x hx y hy with (hG | hB) | hI
      · rw [visit_in K G t y hG, if_pos hG, if_neg (Set.disjoint_left.mp hGB hG)]
        ring_nf
        exact le_rfl
      · rw [if_pos hB, if_neg (Set.disjoint_left.mp hGB.symm hB)]
        simpa only [sub_zero, sub_self, mul_zero, zero_add] using visit_nonneg K G t y
      · rw [if_neg (Set.disjoint_left.mp hGI.symm hI), if_neg (Set.disjoint_left.mp hBI.symm hI)]
        simpa only [sub_zero, mul_one, zero_add] using ih y hI
    have ht := mean_mono_on_support (K x) hp
    rw [mean_add, mean_mul, mean_sub, mean_sub, mean_const] at ht
    change g + q * (1 - g - b) ≤ _ at ht
    have hq0 : 0 ≤ q := hq
    have hq1 : 0 ≤ 1 - 2 * q := by linarith
    have hbg : b ≤ g := hcomp x hx
    have hg : δ ≤ g := (hbad x hx).trans hbg
    have hm := mul_le_mul_of_nonneg_left hg hq1
    have hb := mul_le_mul_of_nonneg_left hbg hq0
    have hd : raceBound δ (t + 1) = q + (1 - 2 * q) * (δ / 2) := by
      dsimp [raceBound, q]
      rw [pow_succ]
      ring
    rw [visit, if_neg (Set.disjoint_left.mp hGI.symm hx), hd]
    have hδg : 0 ≤ δ * (1 - 2 * q) := mul_nonneg hδ hq1
    nlinarith only [hm, ht, hb, hδg]

end
end Lax637351Proofs.FiniteRace
