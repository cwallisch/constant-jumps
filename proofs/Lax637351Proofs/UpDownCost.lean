import Lax637351Proofs.Charge

namespace Lax637351Proofs.UpDownCost

open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.Regeneration Lax637351Proofs.Charge
open scoped Classical ENNReal

noncomputable section

def increments (u : ℕ → ℝ) (ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => (u (i + 1))⁻¹ + ρ * increments u ρ i

def rankCost (m : ℕ) (u : ℕ → ℝ) (ρ : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, if i ≤ j then increments u ρ j else 0

lemma increments_nonneg (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) (ρ : ℝ) (hρ : 0 ≤ ρ) (i : ℕ) :
    0 ≤ increments u ρ i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact add_nonneg (inv_nonneg.mpr (hu (i + 1))) (mul_nonneg hρ ih)

lemma rankCost_nonneg (m : ℕ) (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) (ρ : ℝ) (hρ : 0 ≤ ρ) (i : ℕ) :
    0 ≤ rankCost m u ρ i := by
  unfold rankCost
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact increments_nonneg u hu ρ hρ j
  · exact le_rfl

lemma rankCost_antitone (m : ℕ) (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Antitone (rankCost m u ρ) := by
  intro a b hab
  unfold rankCost
  apply Finset.sum_le_sum
  intro j _
  by_cases hbj : b ≤ j
  · simp only [if_pos hbj, if_pos (hab.trans hbj), le_refl]
  · simp only [if_neg hbj]
    split_ifs
    · exact increments_nonneg u hu ρ hρ j
    · exact le_rfl

lemma cost_difference (m : ℕ) (u : ℕ → ℝ) (ρ : ℝ) {i : ℕ} (hi : i < m) :
    rankCost m u ρ i - rankCost m u ρ (i + 1) = increments u ρ i := by
  unfold rankCost
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    by_cases h : i ≤ j
    · simp [h, show i + 1 ≤ j by omega]
    · simp [h, show ¬ i + 1 ≤ j by omega]
  · exact fun h ↦ (h (Finset.mem_range.mpr hi)).elim

lemma increments_upper (u : ℕ → ℝ) (ρ U : ℝ) (hρ : 1 ≤ ρ) (hU : 0 ≤ U)
    (i : ℕ) (hu : ∀ j, 1 ≤ j → j ≤ i → (u j)⁻¹ ≤ U) :
    increments u ρ i ≤ (i : ℝ) * U * ρ ^ i := by
  induction i with
  | zero => simp [increments]
  | succ i ih =>
    rw [increments]
    have hp : 1 ≤ ρ ^ (i + 1) := one_le_pow₀ hρ
    have hpart := mul_le_mul_of_nonneg_left (ih (fun j hj hj' ↦ hu j hj (hj'.trans (Nat.le_succ i))))
      (show 0 ≤ ρ by linarith)
    have hi := hu (i + 1) (by omega) le_rfl
    have hU' := mul_le_mul_of_nonneg_left hp hU
    push_cast
    rw [pow_succ] at hU' ⊢
    nlinarith only [hpart, hi, hU']

lemma rankCost_upper (m : ℕ) (u : ℕ → ℝ) (_hu : ∀ i, 0 ≤ u i)
    (ρ U : ℝ) (hρ : 1 ≤ ρ) (hU : 0 ≤ U)
    (hu' : ∀ j, 1 ≤ j → j < m → (u j)⁻¹ ≤ U) (i : ℕ) :
    rankCost m u ρ i ≤ (m : ℝ) ^ 2 * U * ρ ^ m := by
  have hbound (j : ℕ) (hj : j < m) : increments u ρ j ≤ (m : ℝ) * U * ρ ^ m := by
    apply (increments_upper u ρ U hρ hU j (fun l hl hl' ↦ hu' l hl (hl'.trans_lt hj))).trans
    have hmul := mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ m by exact_mod_cast hj.le) hU
    exact mul_le_mul hmul (pow_le_pow_right₀ hρ hj.le) (by positivity) (by positivity)
  unfold rankCost
  calc
    _ ≤ ∑ _j ∈ Finset.range m, (m : ℝ) * U * ρ ^ m := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · exact hbound j (Finset.mem_range.mp hj)
      · positivity
    _ = _ := by simp [nsmul_eq_mul]; ring

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma span_le_potential (J : Kernel α ι) (R : Set α) (V : α → ℝ)
    (hV : ∀ x, 0 ≤ V x) (h : ∀ x ∉ R, mean (marginal J x) V + 1 ≤ V x)
    (t : ℕ) (x : α) : span J R t x ≤ V x := by
  induction t generalizing x with
  | zero => exact hV x
  | succ t ih =>
    rw [span]
    split_ifs with hx
    · exact hV x
    · have hs := mean_mono (J x) (fun v ↦ ih v.2)
      have hh := h x hx
      rw [marginal, mean_map] at hh
      linarith

end
end Lax637351Proofs.UpDownCost
