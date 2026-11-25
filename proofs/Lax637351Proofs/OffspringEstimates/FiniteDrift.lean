import Lax637351Proofs.OffspringEstimates.FiniteChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Lax637351Proofs.OffspringEstimates.FiniteDrift

open Lax637351Proofs.OffspringEstimates.FiniteChain
open scoped BigOperators ENNReal Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α β : Type*} [Fintype α] [Fintype β]

def mean (p : PMF α) (f : α → ℝ) : ℝ := ∑ x, (p x).toReal * f x

lemma sum_mass (p : PMF α) : ∑ x, (p x).toReal = 1 := by
  have h : (∑ x, p x) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have h := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top x)] at h
  simpa only [ENNReal.toReal_one] using h

lemma mean_const (p : PMF α) (c : ℝ) : mean p (fun _ ↦ c) = c := by
  rw [mean, ← Finset.sum_mul, sum_mass, one_mul]

lemma mean_pure (x : α) (f : α → ℝ) : mean (PMF.pure x) f = f x := by
  unfold mean
  simp [PMF.pure_apply, apply_ite, ite_mul]

lemma mean_mono (p : PMF α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : mean p f ≤ mean p g :=
  Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg

lemma mean_mono_on_support (p : PMF α) {f g : α → ℝ}
    (h : ∀ x ∈ p.support, f x ≤ g x) : mean p f ≤ mean p g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x = 0
  · simp only [hx, ENNReal.toReal_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hx) ENNReal.toReal_nonneg

lemma mean_nonneg (p : PMF α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ mean p f :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (h x)

lemma mean_add (p : PMF α) (f g : α → ℝ) :
    mean p (fun x ↦ f x + g x) = mean p f + mean p g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (p : PMF α) (f g : α → ℝ) :
    mean p (fun x ↦ f x - g x) = mean p f - mean p g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul (p : PMF α) (c : ℝ) (f : α → ℝ) :
    mean p (fun x ↦ c * f x) = c * mean p f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma mean_bind (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    mean (p.bind K) f = mean p (fun x ↦ mean (K x) f) := by
  have hmass : ∀ y, ((p.bind K) y).toReal = ∑ x, (p x).toReal * (K x y).toReal := by
    intro y
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
    · intro x _
      exact ENNReal.mul_ne_top (p.apply_ne_top x) ((K x).apply_ne_top y)
  unfold mean
  simp_rw [hmass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma mean_indicator (p : PMF α) (A : Set α) :
    mean p (fun x ↦ if x ∈ A then 1 else 0) = (p.toOuterMeasure A).toReal := by
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · unfold mean
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ A <;> simp [hx]
  · intro x _
    by_cases hx : x ∈ A <;> simp [hx, p.apply_ne_top]

def stopped (K : α → PMF α) (A : Set α) (x : α) : PMF α :=
  if x ∈ A then K x else PMF.pure x

end
end Lax637351Proofs.OffspringEstimates.FiniteDrift
