import Lax637351Proofs.Sampling
import Mathlib.Data.Finset.Powerset

namespace Lax637351Proofs.Regeneration

open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

abbrev Kernel (α ι : Type*) := α → PMF (Finset ι × α)

/-- Probability that all the outstanding coordinates are hit by the finite
horizon. The iteration that enters the reset set still contributes its mask. -/
def capture (K : Kernel α ι) (R : Set α) : ℕ → Finset ι → α → ℝ
  | 0, D, _ => if D = ∅ then 1 else 0
  | t + 1, D, x =>
    if D = ∅ then 1 else if x ∈ R then 0 else
      mean (K x) (fun v ↦ capture K R t (D \ v.1) v.2)

/-- Expected number of iterations until the reset set or the finite horizon. -/
def span (K : Kernel α ι) (R : Set α) : ℕ → α → ℝ
  | 0, _ => 0
  | t + 1, x => if x ∈ R then 0 else 1 + mean (K x) (fun v ↦ span K R t v.2)

@[simp] lemma capture_empty (K : Kernel α ι) (R : Set α) (t : ℕ) (x : α) :
    capture K R t ∅ x = 1 := by cases t <;> simp [capture]

lemma capture_nonneg (K : Kernel α ι) (R : Set α) (t : ℕ) (D : Finset ι) (x : α) :
    0 ≤ capture K R t D x := by
  induction t generalizing D x with
  | zero => simp [capture]; split_ifs <;> norm_num
  | succ t ih =>
    simp only [capture]
    split_ifs
    · norm_num
    · exact le_rfl
    · exact mean_nonneg _ (fun v ↦ ih _ _)

omit [DecidableEq ι] in
lemma span_nonneg (K : Kernel α ι) (R : Set α) (t : ℕ) (x : α) : 0 ≤ span K R t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [span]
    split_ifs
    · exact le_rfl
    · have h := mean_nonneg (K x) (fun v ↦ ih v.2)
      linarith

def nonemptySubsets (D : Finset ι) : Finset (Finset ι) := D.powerset.erase ∅

omit [Fintype ι] in
lemma mem_nonemptySubsets {D J : Finset ι} : J ∈ nonemptySubsets D ↔ J ≠ ∅ ∧ J ⊆ D := by
  simp [nonemptySubsets]

def hitCoefficient (ρ : ℝ) (V : ℕ → ℝ) (D : Finset ι) : ℝ :=
  ∑ J ∈ nonemptySubsets D, ρ ^ J.card * V (D \ J).card

lemma mask_probability_first (K : Kernel α ι) (R : Set α) (ρ : ℝ)
    (V : ℕ → ℝ) (hV : ∀ d, 0 ≤ V d) (D : Finset ι)
    (hmask : ∀ x J, mean (K x) (fun v ↦ if J ⊆ v.1 then 1 else 0) ≤ ρ ^ J.card)
    (hfuture : ∀ J ∈ nonemptySubsets D, ∀ t x, capture K R t (D \ J) x ≤ V (D \ J).card)
    (C : ℝ) (hbound : hitCoefficient ρ V D ≤ C)
    (t : ℕ) (x : α) :
    mean (K x) (fun v ↦ if Disjoint D v.1 then 0 else capture K R t (D \ v.1) v.2) ≤ C := by
  have hsum (v : Finset ι × α) :
      (if Disjoint D v.1 then 0 else capture K R t (D \ v.1) v.2) ≤
        ∑ J ∈ nonemptySubsets D, V (D \ J).card * (if J ⊆ v.1 then 1 else 0) := by
    have hn (J : Finset ι) : 0 ≤ V (D \ J).card * (if J ⊆ v.1 then 1 else 0) :=
      mul_nonneg (hV _) (by split_ifs <;> norm_num)
    by_cases h : Disjoint D v.1
    · rw [if_pos h]
      exact Finset.sum_nonneg (fun J _ ↦ hn J)
    · rw [if_neg h]
      let J := D ∩ v.1
      have hJ : J ∈ nonemptySubsets D := mem_nonemptySubsets.mpr ⟨
        fun hJ ↦ h (Finset.disjoint_iff_inter_eq_empty.mpr hJ), Finset.inter_subset_left⟩
      have heq : D \ v.1 = D \ J := by
        ext j
        by_cases hj : j ∈ D <;> simp [J, hj]
      rw [heq]
      apply (hfuture J hJ t v.2).trans
      have ht := Finset.single_le_sum (s := nonemptySubsets D) (fun I _ ↦ hn I) hJ
      have hJsub : J ⊆ v.1 := Finset.inter_subset_right
      rw [if_pos hJsub, mul_one] at ht
      exact ht
  apply (mean_mono _ hsum).trans
  rw [mean_sum]
  apply le_trans _ hbound
  unfold hitCoefficient
  apply Finset.sum_le_sum
  intro J _
  rw [mean_mul, mul_comm (ρ ^ J.card)]
  exact mul_le_mul_of_nonneg_left (hmask x J) (hV _)

lemma capture_le_span (K : Kernel α ι) (R : Set α) (ρ : ℝ)
    (V : ℕ → ℝ) (hV : ∀ d, 0 ≤ V d) (D : Finset ι) (hD : D ≠ ∅)
    (hmask : ∀ x J, mean (K x) (fun v ↦ if J ⊆ v.1 then 1 else 0) ≤ ρ ^ J.card)
    (hfuture : ∀ J ∈ nonemptySubsets D, ∀ t x, capture K R t (D \ J) x ≤ V (D \ J).card)
    (C : ℝ) (hC : 0 ≤ C) (hbound : hitCoefficient ρ V D ≤ C) (t : ℕ) (x : α) :
    capture K R t D x ≤ C * span K R t x := by
  induction t generalizing x with
  | zero => simp [capture, span, hD]
  | succ t ih =>
    simp only [capture, span, if_neg hD]
    by_cases hR : x ∈ R
    · simp [hR]
    · rw [if_neg hR, if_neg hR]
      have hpt (v : Finset ι × α) : capture K R t (D \ v.1) v.2 ≤
          C * span K R t v.2 + (if Disjoint D v.1 then 0 else capture K R t (D \ v.1) v.2) := by
        by_cases h : Disjoint D v.1
        · rw [h.sdiff_eq_left, if_pos h, add_zero]
          exact ih _
        · rw [if_neg h]
          exact le_add_of_nonneg_left (mul_nonneg hC (span_nonneg K R t v.2))
      apply (mean_mono _ hpt).trans
      rw [mean_add, mean_mul, mul_add, mul_one]
      have hh := mask_probability_first K R ρ V hV D hmask hfuture C hbound t x
      linarith only [hh]

end
end Lax637351Proofs.Regeneration
