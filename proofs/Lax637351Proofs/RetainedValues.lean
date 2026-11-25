import Lax637351Proofs.OffspringEstimates.ReproductiveValues
import Mathlib.Analysis.Complex.Exponential

namespace Lax637351Proofs.RetainedValues

open Lax637351Proofs.OffspringEstimates.ReproductiveValues
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

def retained (A : ℕ → Kernel α) (a : ℝ) (c : ℕ → ℝ) (s : ℕ) : ℕ → α → ℝ
  | 0 => fun _ ↦ 1
  | t + 1 => fun x ↦ c s * retained A a c (s + 1) t x +
      a * action (A s) (retained A a c (s + 1) t) x

def retention (c : ℕ → ℝ) (s : ℕ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => c s * retention c (s + 1) t

lemma retention_nonneg (c : ℕ → ℝ) (hc : ∀ s, 0 ≤ c s) (s t : ℕ) :
    0 ≤ retention c s t := by
  induction t generalizing s with
  | zero => exact zero_le_one
  | succ t ih => exact mul_nonneg (hc s) (ih _)

lemma action_mul (A : Kernel α) (g : α → ℝ) (c : ℝ) (x : α) :
    action A (fun y ↦ c * g y) x = c * action A g x := by
  unfold action
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma retained_compare (A : ℕ → Kernel α) {a : ℝ} (ha : 0 ≤ a) (d : ℝ) (hd : 0 < d)
    (c : ℕ → ℝ) (hc : ∀ s, d ≤ c s ∧ c s ≤ 1) (s t : ℕ) (x : α) :
    retention c s t * value A a s t x ≤ retained A a c s t x ∧
      retained A a c s t x ≤ retention c s t * value A (a / d) s t x := by
  induction t generalizing s x with
  | zero => simp [retained, value, retention]
  | succ t ih =>
    let C := retention c (s + 1) t
    let v := value A a (s + 1) t
    let w := value A (a / d) (s + 1) t
    let f := retained A a c (s + 1) t
    have hc₀' (s : ℕ) : 0 ≤ c s := hd.le.trans (hc s).1
    have hc₀ : 0 ≤ c s := hc₀' s
    have hC : 0 ≤ C := retention_nonneg c hc₀' (s + 1) t
    have hv := action_nonneg (A s) v (value_nonneg A ha (s + 1) t) x
    have hw := action_nonneg (A s) w (value_nonneg A (div_nonneg ha hd.le) (s + 1) t) x
    have hv' := action_mono (A s) (fun y ↦ C * v y) f (fun y ↦ (ih (s + 1) y).1) x
    have hw' := action_mono (A s) f (fun y ↦ C * w y) (fun y ↦ (ih (s + 1) y).2) x
    rw [action_mul] at hv' hw'
    change c s * C * (v x + a * action (A s) v x) ≤ c s * f x + a * action (A s) f x ∧
      c s * f x + a * action (A s) f x ≤ c s * C * (w x + (a / d) * action (A s) w x)
    constructor
    · have h₁ := mul_le_mul_of_nonneg_left (ih (s + 1) x).1 hc₀
      have h₂ := mul_le_mul_of_nonneg_left hv' ha
      have h₃ := mul_le_mul_of_nonneg_right (hc s).2 (show 0 ≤ C * a * action (A s) v x by positivity)
      nlinarith only [h₁, h₂, h₃]
    · have h₁ := mul_le_mul_of_nonneg_left (ih (s + 1) x).2 hc₀
      have h₂ := mul_le_mul_of_nonneg_left hw' ha
      have h₃ : a ≤ c s * (a / d) := by
        rw [← mul_div_assoc, le_div_iff₀ hd]
        simpa only [mul_comm a d] using mul_le_mul_of_nonneg_right (hc s).1 ha
      have h₄ := mul_le_mul_of_nonneg_right h₃ (mul_nonneg hC hw)
      nlinarith only [h₁, h₂, h₄]

lemma value_bound (A : ℕ → Kernel α) {a : ℝ} (ha : 0 ≤ a) (s t : ℕ) (x : α) :
    value A a s t x ≤ (1 + a) ^ t := by
  induction t generalizing s x with
  | zero => exact le_rfl
  | succ t ih =>
    have h₁ := ih (s + 1) x
    have h₂ := action_le (A s) (value A a (s + 1) t) ((1 + a) ^ t) (by positivity) (ih (s + 1)) x
    have h₃ := mul_le_mul_of_nonneg_left h₂ ha
    rw [pow_succ, value]
    nlinarith only [h₁, h₃]

lemma action_sub (A : Kernel α) (g h : α → ℝ) (x : α) :
    action A (g - h) x = action A g x - action A h x := by
  simp only [action, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma value_perturbation (A : ℕ → Kernel α) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (s t : ℕ) (x : α) :
    value A b s t x - value A a s t x ≤ (b - a) * t * (1 + b) ^ t := by
  have hb : 0 ≤ b := ha.trans hab
  have hab' : 0 ≤ b - a := sub_nonneg.mpr hab
  induction t generalizing s x with
  | zero => simp [value]
  | succ t ih =>
    let f := value A b (s + 1) t
    let g := value A a (s + 1) t
    let U := (b - a) * (t : ℝ) * (1 + b) ^ t
    have hU : 0 ≤ U := by unfold U; positivity
    have h : f x - g x ≤ U := ih (s + 1) x
    have h' : action (A s) f x - action (A s) g x ≤ U := by
      rw [← action_sub]
      exact action_le _ _ _ hU (ih (s + 1)) x
    have h'' : action (A s) g x ≤ (1 + b) ^ t := by
      apply action_le _ _ _ (by positivity)
      intro y
      exact (value_bound A ha (s + 1) t y).trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
    have hnext : (1 + b) ^ t ≤ (1 + b) ^ (t + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.le_succ _)
    change f x + b * action (A s) f x - (g x + a * action (A s) g x) ≤ _
    push_cast
    rw [show (t + 1 : ℝ) = (t : ℝ) + 1 by ring, mul_add, add_mul]
    have hterm : (1 + b) * U = (b - a) * (t : ℝ) * (1 + b) ^ (t + 1) := by unfold U; rw [pow_succ]; ring
    nlinarith only [h, mul_le_mul_of_nonneg_left h' hb, mul_le_mul_of_nonneg_left h'' hab',
      mul_le_mul_of_nonneg_left hnext hab', hterm]

lemma retained_normalization (A : ℕ → Kernel α) {e : ℝ} (he : 0 ≤ e ∧ e < 1)
    (c : ℕ → ℝ) (hc : ∀ s, 1 - e ≤ c s ∧ c s ≤ 1) (s t : ℕ) (x : α)
    (hpert : (e / (1 - e) - e) * t * (1 + e / (1 - e)) ^ t ≤ 1) :
    retention c s t * value A e s t x ≤ retained A e c s t x ∧
      retained A e c s t x ≤ 2 * (retention c s t * value A e s t x) := by
  have hd : 0 < 1 - e := sub_pos.mpr he.2
  have hr : 0 ≤ retention c s t := retention_nonneg c (fun s ↦ hd.le.trans (hc s).1) s t
  have h := retained_compare A he.1 (1 - e) hd c hc s t x
  refine ⟨h.1, h.2.trans ?_⟩
  have hcoef : e ≤ e / (1 - e) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [sq_nonneg e]
  have hdiff := (value_perturbation A he.1 hcoef s t x).trans hpert
  have hbase := value_one_le A he.1 s t x
  have hupper : value A (e / (1 - e)) s t x ≤ 2 * value A e s t x := by linarith only [hdiff, hbase]
  nlinarith only [mul_le_mul_of_nonneg_left hupper hr]

end
end Lax637351Proofs.RetainedValues
