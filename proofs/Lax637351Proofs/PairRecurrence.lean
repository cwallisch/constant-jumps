import Lax637351Proofs.FiniteDrift
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

namespace Lax637351Proofs.PairRecurrence

open scoped Classical

lemma rank_window {a b q : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (f g : ℕ → ℝ) (hf : 0 ≤ f 0) (hg : q ≤ g 0)
    (h₁ : ∀ t, a * g t ≤ g (t + 1))
    (h₂ : ∀ t, a * f t + b * g t ≤ f (t + 1)) (t : ℕ) :
    (t : ℝ) * b * a ^ t * q ≤ f t := by
  have hg' (s : ℕ) : a ^ s * q ≤ g s := by
    induction s with
    | zero => simpa using hg
    | succ s ih =>
      calc
        a ^ (s + 1) * q = a * (a ^ s * q) := by rw [pow_succ]; ring
        _ ≤ a * g s := mul_le_mul_of_nonneg_left ih ha
        _ ≤ g (s + 1) := h₁ s
  induction t with
  | zero => simpa using hf
  | succ t ih =>
    have hpow : a ^ (t + 1) ≤ a ^ t := pow_le_pow_of_le_one ha ha' (Nat.le_succ t)
    calc
      ((t + 1 : ℕ) : ℝ) * b * a ^ (t + 1) * q =
          a * ((t : ℝ) * b * a ^ t * q) + b * (a ^ (t + 1) * q) := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ a * f t + b * g t := add_le_add
        (mul_le_mul_of_nonneg_left ih ha)
        (mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right hpow hq).trans (hg' t)) hb)
      _ ≤ f (t + 1) := h₂ t

lemma uniform_inactivity {A : ℝ} (hA : 0 ≤ A) {L : ℕ} (hL : 0 < L)
    (hsize : 2 * A ≤ L) : Real.exp (-2 * A) ≤ (1 - A / (L : ℝ)) ^ L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hhalf : A / (L : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hL').mpr
    linarith
  have hpositive : 0 < 1 - A / (L : ℝ) := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpositive)
  rw [Real.log_inv] at hlog
  have hfrac : (1 - A / (L : ℝ))⁻¹ - 1 ≤ 2 * (A / (L : ℝ)) := by
    have hprod := mul_nonneg (div_nonneg hA hL'.le) (show 0 ≤ 1 - 2 * (A / (L : ℝ)) by linarith)
    rw [inv_eq_one_div, sub_le_iff_le_add]
    apply (div_le_iff₀ hpositive).mpr
    nlinarith
  have hlog' : -2 * (A / (L : ℝ)) ≤ Real.log (1 - A / (L : ℝ)) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog' hL'.le
  have heq : (L : ℝ) * (-2 * (A / (L : ℝ))) = -2 * A := by
    field_simp
  rw [heq, ← Real.log_pow] at hmul
  exact (Real.le_log_iff_exp_le (pow_pos hpositive _)).mp hmul

end Lax637351Proofs.PairRecurrence
