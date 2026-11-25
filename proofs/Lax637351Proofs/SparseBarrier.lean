import Lax637351Proofs.Barrier
import Lax637351Proofs.FiniteWindows

namespace Lax637351Proofs.SparseBarrier

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.Barrier Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {α ι : Type*} [Fintype α] [Fintype ι]

lemma visit_stopped_le (K : α → PMF α) (A G : Set α) (t : ℕ) (x : α) :
    visit (stopped K A) G t x ≤ visit K G t x := by
  induction t generalizing x with
  | zero => simp [visit]
  | succ t ih =>
    by_cases hg : x ∈ G
    · rw [visit_in _ _ _ _ hg, visit_in _ _ _ _ hg]
    · rw [visit, if_neg hg]
      by_cases hx : x ∈ A
      · rw [stopped, if_pos hx, visit, if_neg hg]
        exact mean_mono _ ih
      · rw [stopped, if_neg hx, mean_pure]
        exact (ih x).trans (visit_monotone K G x (by omega))

lemma visit_iUnion_le (K : α → PMF α) (G : ι → Set α) (t : ℕ) (x : α) :
    visit K (⋃ i, G i) t x ≤ ∑ i, visit K (G i) t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x ∈ ⋃ i, G i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      rw [visit_in _ _ _ _ h, ← visit_in K (G i) 0 x hi]
      exact Finset.single_le_sum (fun j _ ↦ visit_nonneg K (G j) 0 x) (Finset.mem_univ i)
    · simpa only [visit, if_neg h] using Finset.sum_nonneg (fun i _ ↦ visit_nonneg K (G i) 0 x)
  | succ t ih =>
    by_cases h : x ∈ ⋃ i, G i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      rw [visit_in _ _ _ _ h, ← visit_in K (G i) (t + 1) x hi]
      exact Finset.single_le_sum (fun j _ ↦ visit_nonneg K (G j) (t + 1) x) (Finset.mem_univ i)
    · have h' (i : ι) : x ∉ G i := fun hi ↦ h (Set.mem_iUnion.mpr ⟨i, hi⟩)
      rw [visit, if_neg h]
      have he (i : ι) : visit K (G i) (t + 1) x = mean (K x) (visit K (G i) t) := by
        rw [visit, if_neg (h' i)]
      simp_rw [he, ← mean_sum]
      exact mean_mono _ ih

lemma sum_charge (K : α → PMF α) (G R : ι → Set α) (C : Set α)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C)
    (a : ℝ) (_ha : 0 ≤ a)
    (hcost : ∀ x ∈ C, ∀ t, mean (K x) (fun y ↦
      ∑ i, if x ∈ R i then visit (stopped K (R i)ᶜ) (G i) t y else 0) ≤ a)
    (t : ℕ) (x : α) (hx : x ∈ C) :
    (∑ i, visit K (G i) t x) ≤ (t : ℝ) * a + ∑ i, visit (stopped K (R i)ᶜ) (G i) t x := by
  let D (t : ℕ) (x : α) (i : ι) :=
    visit K (G i) t x - visit (stopped K (R i)ᶜ) (G i) t x
  have hpos (t : ℕ) (x : α) (i : ι) : 0 ≤ D t x i :=
    sub_nonneg.mpr (visit_stopped_le K _ _ t x)
  have h'D (t : ℕ) (x : α) (i : ι) :
      D (t + 1) x i ≤ mean (K x) (fun y ↦ D t y i +
        if x ∈ R i then visit (stopped K (R i)ᶜ) (G i) t y else 0) := by
    by_cases hG : x ∈ G i
    · dsimp [D]
      rw [visit_in _ _ _ _ hG, visit_in _ _ _ _ hG, sub_self]
      exact mean_nonneg _ (fun y ↦ add_nonneg (hpos t y i) (by split_ifs; exact visit_nonneg _ _ _ _; exact le_rfl))
    · dsimp only [D]
      rw [visit, if_neg hG, visit, if_neg hG]
      by_cases hR : x ∈ R i
      · simp only [if_pos hR, sub_add_cancel]
        have hh := mean_nonneg (stopped K (R i)ᶜ x) (visit_nonneg (stopped K (R i)ᶜ) (G i) t)
        linarith only [hh]
      · rw [stopped, if_pos (show x ∈ (R i)ᶜ from hR)]
        simp only [if_neg hR, add_zero, mean_sub, le_refl]
  have hsum (t : ℕ) (x : α) (hx : x ∈ C) : ∑ i, D t x i ≤ (t : ℝ) * a := by
    induction t generalizing x with
    | zero => simp [D, visit]
    | succ t ih =>
      calc
        _ ≤ ∑ i, mean (K x) (fun y ↦ D t y i +
            if x ∈ R i then visit (stopped K (R i)ᶜ) (G i) t y else 0) :=
          Finset.sum_le_sum (fun i _ ↦ h'D t x i)
        _ = mean (K x) (fun y ↦ ∑ i, D t y i) + mean (K x) (fun y ↦
            ∑ i, if x ∈ R i then visit (stopped K (R i)ᶜ) (G i) t y else 0) := by
          rw [← mean_sum]
          simp only [Finset.sum_add_distrib, mean_add]
        _ ≤ _ := by
          have ht := mean_mono_on_support (K x) (fun y hy ↦ ih y (hC x hx y hy))
          rw [mean_const] at ht
          push_cast
          linarith only [ht, hcost x hx t]
  have hh := hsum t x hx
  dsimp [D] at hh
  rw [Finset.sum_sub_distrib] at hh
  linarith only [hh]

lemma unchanged_second_moment (K : α → PMF α) (f : α → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (x : α) (hjump : ∀ y ∈ (K x).support, |f y - f x| ≤ b) :
    mean (K x) (fun y ↦ (f y - f x) ^ 2) ≤ b ^ 2 * mean (K x) (fun y ↦ indicator (y ≠ x)) := by
  rw [← mean_mul]
  apply mean_mono_on_support
  intro y hy
  by_cases h : y = x
  · simp [h, indicator]
  · simp only [indicator, if_pos h, mul_one]
    exact (sq_le_sq).mpr (by rw [abs_of_nonneg hb]; exact hjump y hy)

lemma excursion_barrier (K : α → PMF α) (X : α → ℝ) (l u b θ lam : ℝ)
    (_hlu : l ≤ u) (_hb : 0 ≤ b) (hlam : 0 ≤ lam) (hlamθ : lam ≤ θ)
    (hsmall : ∀ x, l ≤ X x → X x ≤ u → ∀ y ∈ (K x).support, |lam * (X y - X x)| ≤ 1)
    (hdrift : ∀ x, l ≤ X x → X x ≤ u → θ * mean (K x) (fun y ↦ (X y - X x) ^ 2) ≤
      mean (K x) (fun y ↦ X y - X x))
    (t : ℕ) (x : α) (hx : u - b ≤ X x) :
    visit (stopped K {y | u < X y}ᶜ) {y | X y < l} t x ≤ Real.exp (-lam * (u - b - l)) := by
  let G : Set α := {y | X y < l}
  let R : Set α := {y | u < X y}
  let A : Set α := {y | l ≤ X y ∧ X y ≤ u}
  let J := stopped K Rᶜ
  have hE : stopped J Gᶜ = stopped K A := by
    funext y
    by_cases hl : X y < l <;> by_cases hu : u < X y <;>
      simp [stopped, J, G, R, A, hl, hu, le_of_not_gt]
  rw [visit_eq_mean_stopped, hE, mean_indicator]
  have hh := stopped_lower_barrier K A X θ lam hlam hlamθ
    (fun y hy ↦ hsmall y hy.1 hy.2) (fun y hy ↦ hdrift y hy.1 hy.2) x l t
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hx hlam])

lemma sparse_visit (K : α → PMF α) (X : ι → α → ℝ) (C : Set α)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C)
    (l u b θ lam m r : ℝ)
    (hlu : l ≤ u) (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hlamθ : lam ≤ θ)
    (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hsmall : ∀ i x, l ≤ X i x → X i x ≤ u → ∀ y ∈ (K x).support, |lam * (X i y - X i x)| ≤ 1)
    (hdrift : ∀ i x, l ≤ X i x → X i x ≤ u → θ * mean (K x) (fun y ↦ (X i y - X i x) ^ 2) ≤
      mean (K x) (fun y ↦ X i y - X i x))
    (hcount : ∀ x ∈ C, ((Finset.univ.filter (fun i ↦ X i x ≤ u)).card : ℝ) ≤ m)
    (hjump : ∀ x ∈ C, ∀ y ∈ (K x).support, ∀ i, u < X i x → u - b ≤ X i y)
    (hchange : ∀ x ∈ C, mean (K x) (fun y ↦ indicator (y ≠ x)) ≤ r)
    (t : ℕ) (x : α) (hx : x ∈ C) (hx' : ∀ i, u - b ≤ X i x) :
    visit K (⋃ i, {y | X i y < l}) t x ≤
      ((t : ℝ) * r + 1) * m * Real.exp (-lam * (u - b - l)) := by
  let G (i : ι) : Set α := {y | X i y < l}
  let R (i : ι) : Set α := {y | u < X i y}
  let β := Real.exp (-lam * (u - b - l))
  let F (i : ι) (t : ℕ) := visit (stopped K (R i)ᶜ) (G i) t
  have hβ : 0 ≤ β := (Real.exp_pos _).le
  have hz (i : ι) (y : α) (hy : u < X i y) (t : ℕ) : F i t y = 0 := by
    induction t with
    | zero => simp [F, visit, G, not_lt.mpr (hlu.trans hy.le)]
    | succ t ih =>
      unfold F
      rw [visit, if_neg (show y ∉ G i from not_lt.mpr (hlu.trans hy.le))]
      rw [stopped, if_neg (show y ∉ (R i)ᶜ from fun h ↦ h hy), mean_pure]
      exact ih
  have hbar (i : ι) (y : α) (hy : u - b ≤ X i y) (t : ℕ) : F i t y ≤ β :=
    excursion_barrier K (X i) l u b θ lam hlu hb hlam hlamθ (hsmall i) (hdrift i) t y hy
  have hsum (y : α) (hy : y ∈ C) :
      (∑ i, if X i y ≤ u then β else 0) ≤ m * β := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcount y hy) hβ
  have hcost (y : α) (hy : y ∈ C) (s : ℕ) :
      mean (K y) (fun z ↦ ∑ i, if y ∈ R i then F i s z else 0) ≤ m * β * r := by
    have h (z : α) (hz' : z ∈ (K y).support) :
        (∑ i, if y ∈ R i then F i s z else 0) ≤ m * β * indicator (z ≠ y) := by
      by_cases he : z = y
      · subst z
        simp only [indicator, if_neg (not_not.mpr rfl), mul_zero]
        apply Finset.sum_nonpos
        intro i _
        by_cases hx' : y ∈ R i
        · rw [if_pos hx', hz i y hx' s]
        · simp [hx']
      · rw [indicator, if_pos he, mul_one]
        apply le_trans _ (hsum z (hC y hy z hz'))
        apply Finset.sum_le_sum
        intro i _
        by_cases hx' : y ∈ R i
        · rw [if_pos hx']
          by_cases ht : X i z ≤ u
          · rw [if_pos ht]
            exact hbar i z (hjump y hy z hz' i hx') s
          · rw [if_neg ht, hz i z (lt_of_not_ge ht) s]
        · rw [if_neg hx']
          split_ifs <;> first | exact hβ | exact le_rfl
    have h' := mean_mono_on_support (K y) h
    rw [mean_mul] at h'
    exact h'.trans (mul_le_mul_of_nonneg_left (hchange y hy) (mul_nonneg hm hβ))
  have hfirst : (∑ i, F i t x) ≤ m * β := by
    apply le_trans _ (hsum x hx)
    apply Finset.sum_le_sum
    intro i _
    by_cases h : X i x ≤ u
    · rw [if_pos h]
      exact hbar i x (hx' i) t
    · rw [if_neg h, hz i x (lt_of_not_ge h) t]
  have hh := sum_charge K G R C hC (m * β * r) (by positivity) hcost t x hx
  apply (visit_iUnion_le K G t x).trans (hh.trans _)
  change _ ≤ ((t : ℝ) * r + 1) * m * β
  linarith only [hfirst, show (t : ℝ) * (m * β * r) + m * β = ((t : ℝ) * r + 1) * m * β by ring]

lemma visit_terminal (K : α → PMF α) (G E : Set α) (q : ℝ) (hq : 0 ≤ q) (t : ℕ)
    (h : ∀ x ∈ G, visit K E t x ≤ q) (x : α) :
    mean (law K (PMF.pure x) t) (fun y ↦ indicator (y ∈ E)) ≤ 1 - visit K G t x + q := by
  induction t generalizing x with
  | zero =>
    rw [law_zero, mean_pure]
    by_cases hx : x ∈ G
    · rw [visit_in _ _ _ _ hx, sub_self, zero_add, indicator]
      exact h x hx
    · rw [visit, if_neg hx, sub_zero]
      linarith only [indic_le_one (x ∈ E), hq]
  | succ t ih =>
    by_cases hx : x ∈ G
    · rw [visit_in _ _ _ _ hx, sub_self, zero_add]
      have he : stopped K (Set.univ : Set α) = K := by funext z; simp [stopped]
      simpa only [he] using (terminal_mass_le_visit K Set.univ E (t + 1) x).trans (h x hx)
    · rw [law_first_step, mean_bind, visit, if_neg hx]
      have hm := mean_mono (K x) (fun y ↦ ih
        (fun z hz ↦ (visit_monotone K E z (Nat.le_succ t)).trans (h z hz)) y)
      rw [mean_add, mean_sub, mean_const, mean_const] at hm
      exact hm

end
end Lax637351Proofs.SparseBarrier
