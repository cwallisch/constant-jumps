import Lax637351Proofs.FiniteWindows
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Exponential

namespace Lax637351Proofs.AffineWindow

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift
open scoped Classical ENNReal

noncomputable section

def width (la : ℝ) : ℕ := ⌈1 / la⌉₊

lemma width_upper {la : ℝ} (hla : 0 < la) (hla' : la ≤ 1) : (width la : ℝ) ≤ 2 / la := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 1 / la by positivity)
  have hh : 1 ≤ 1 / la := (le_div_iff₀ hla).mpr (by simpa using hla')
  change (width la : ℝ) < 1 / la + 1 at h
  linarith only [h, hh, show (2 : ℝ) / la = 1 / la + 1 / la by ring]

lemma width_half {la : ℝ} (hla : 0 < la) (hla' : la ≤ 1) : (1 - la) ^ width la ≤ 1 / 2 := by
  have h := (pow_le_pow_left₀ (sub_nonneg.mpr hla')
    (show 1 - la ≤ Real.exp (-la) by simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-la)) (width la))
  rw [← Real.exp_nat_mul] at h
  have hW : 1 / la ≤ (width la : ℝ) := Nat.le_ceil _
  have hL : (1 : ℝ) ≤ (width la : ℝ) * la := by
    have hh := mul_le_mul_of_nonneg_right hW hla.le
    rwa [one_div_mul_cancel hla.ne'] at hh
  have he : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    have hh := Real.add_one_le_exp 1
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hh])
  exact h.trans ((Real.exp_le_exp.mpr (by linarith only [hL])).trans he)

lemma window {la : ℝ} (hla : 0 < la) (hla' : la ≤ 1) (b : ℝ) (hb : 0 ≤ b)
    (f : ℕ → ℝ) (h0 : 0 ≤ f 0)
    (h : ∀ t < width la, (1 - la) * f t + la * b ≤ f (t + 1)) :
    b / 2 ≤ f (width la) := by
  have hh (t : ℕ) (ht : t ≤ width la) : (1 - (1 - la) ^ t) * b ≤ f t := by
    induction t with
    | zero => simpa using h0
    | succ t ih =>
      calc
        _ = (1 - la) * ((1 - (1 - la) ^ t) * b) + la * b := by rw [pow_succ]; ring
        _ ≤ _ := (add_le_add_left (mul_le_mul_of_nonneg_left (ih (by omega)) (sub_nonneg.mpr hla')) _).trans (h t (by omega))
  have hw := mul_le_mul_of_nonneg_right (sub_le_sub_left (width_half hla hla') 1) hb
  have he : (1 - (1 / 2 : ℝ)) * b = b / 2 := by ring
  rw [he] at hw
  exact hw.trans (hh _ le_rfl)

variable {α : Type*} [Fintype α]

lemma law_affine (K : α → PMF α) (I : Set α) (hI : ∀ x ∈ I, ∀ y ∈ (K x).support, y ∈ I)
    (x : α) (hx : x ∈ I) (f g : α → ℝ) (a b : ℝ)
    (h : ∀ y ∈ I, a * f y + b * g y ≤ mean (K y) f) (t : ℕ) :
    a * mean (law K (PMF.pure x) t) f + b * mean (law K (PMF.pure x) t) g ≤
      mean (law K (PMF.pure x) (t + 1)) f := by
  let ν := law K (PMF.pure x) t
  have hν : ∀ y ∈ ν.support, y ∈ I :=
    law_invariant K (PMF.pure x) I (fun y hy ↦ ((PMF.mem_support_pure_iff _ _).mp hy).symm ▸ hx) hI t
  rw [law_succ, mean_bind]
  have hh := mean_mono_on_support ν (fun y hy ↦ h y (hν y hy))
  rw [mean_add, mean_mul, mean_mul] at hh
  exact hh

lemma triangular_growth (k : ℕ) {la a d : ℝ} (hla : 0 < la) (hla' : la ≤ 1)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (E : ℕ → ℕ → ℝ)
    (hn : ∀ r t, 0 ≤ E r t) (hbase : ∀ t, d ≤ E 0 t)
    (hstep : ∀ r < k, ∀ t, (1 - la) * E (r + 1) t + (la * a) * E r t ≤ E (r + 1) (t + 1)) :
    ∀ r ≤ k, ∀ t ≥ r * width la, d * (a / 2) ^ r ≤ E r t := by
  intro r
  induction r with
  | zero =>
    intro _ t _
    simpa using hbase t
  | succ r ih =>
    intro hr t ht
    let L := width la
    have hL : L ≤ t := (Nat.le_add_left _ _).trans (by simpa only [Nat.succ_mul] using ht)
    let s := t - L
    have hs : r * L ≤ s := by
      simp only [Nat.succ_mul] at ht
      dsimp [s, L]
      omega
    have hj : s + L = t := Nat.sub_add_cancel hL
    let q := d * (a / 2) ^ r
    have hq : 0 ≤ q := mul_nonneg hd (pow_nonneg (div_nonneg ha (by norm_num)) _)
    have hh := window hla hla' (a * q) (mul_nonneg ha hq) (fun u ↦ E (r + 1) (s + u)) (hn _ _)
      (fun u hu ↦ by
        have h := hstep r (by omega) (s + u)
        have hi := ih (by omega) (s + u) (hs.trans (Nat.le_add_right _ _))
        have hm := mul_le_mul_of_nonneg_left hi (mul_nonneg hla.le ha)
        dsimp only [q] at *
        simpa only [← Nat.add_assoc] using (show
          (1 - la) * E (r + 1) (s + u) + la * (a * (d * (a / 2) ^ r)) ≤ E (r + 1) (s + u + 1) by
          nlinarith only [hm, h]))
    change a * q / 2 ≤ E (r + 1) (s + L) at hh
    rw [hj] at hh
    apply le_trans _ hh
    dsimp [q]
    rw [pow_succ]
    exact le_of_eq (by ring)

end
end Lax637351Proofs.AffineWindow
