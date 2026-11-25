import Lax637351Proofs.UpperWindows

namespace Lax637351Proofs.UpperTails

open Lax637351Proofs.ColumnParameters Lax637351Proofs.UpperWindows
open Lax637351Proofs.SpeciesWindow
open scoped Classical

noncomputable section

variable {k : ℕ}

lemma exp_small {b x y C : ℝ} (hb : 0 < b) (hx : 1 ≤ x) (hC : 3 / b ≤ C)
    (hy : C * Real.log x ≤ y) :
    Real.exp (-b * y) ≤ 1 / x ^ 3 := by
  have hx' : 0 < x := by linarith only [hx]
  have hl := Real.log_nonneg hx
  have h := (mul_le_mul_of_nonneg_right ((div_le_iff₀ hb).mp hC) hl).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hy hb.le] : C * b * Real.log x ≤ b * y)
  have h' : -b * y ≤ -(3 : ℕ) * Real.log x := by push_cast; linarith only [h]
  apply (Real.exp_le_exp.mpr h').trans_eq
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx', one_div]

lemma multiplied_exp_small {b y : ℝ} (hb : 0 < b) (_hy : 0 ≤ y) :
    y * Real.exp (-b * y) ≤ 1 / b := by
  have h := Real.add_one_le_exp (b * y)
  have hh : b * y ≤ Real.exp (b * y) := by linarith only [h]
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  apply (mul_le_mul_iff_of_pos_left hb).mp
  convert hh using 1 <;> first | rfl | field_simp [hb.ne']

lemma envelope_bound {A b x y C N η : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hx : 1 ≤ x) (hC : 3 / b ≤ C) (hy : C * Real.log x ≤ y) (hxN : N ≤ x)
    (hN : (A + 1) / η ≤ N) (hη : 0 < η) :
    (A * x ^ 2 + 1) * Real.exp (-b * y) ≤ η := by
  have hxp : 0 < x := by linarith only [hx]
  have hx₂ : 1 ≤ x ^ 2 := by nlinarith only [hx, sq_nonneg (x - 1)]
  have h : A * x ^ 2 + 1 ≤ (A + 1) * x ^ 2 := by linarith only [hx₂]
  have hh := mul_le_mul h (exp_small hb hx hC hy) (Real.exp_pos _).le (by positivity : 0 ≤ (A + 1) * x ^ 2)
  have he : (A + 1) * x ^ 2 * (1 / x ^ 3) = (A + 1) / x := by field_simp
  rw [he] at hh
  exact hh.trans ((div_le_iff₀ hxp).mpr (by
    have h := (div_le_iff₀ hη).mp (hN.trans hxN)
    linarith only [h]))

lemma vanilla_tail (a : Settings k) (hk : 2 ≤ k) (n : ℕ) (μ : ℕ+) (p C : ℝ)
    (hn : (1 : ℝ) ≤ n) (hm : (μ : ℕ) ≤ n)
    (hC : 3 / decay a ≤ C) (hpC : C * Real.log n ≤ ((μ : ℕ) : ℝ) * p)
    (hN : (plateauTimeConstant a + 1) / failureTolerance a ≤ (n : ℝ)) :
    let r := changeBound n k p false
    (plateauTimeConstant a * ((μ : ℕ) : ℝ) * n * r + 1) *
      Real.exp (-decay a * (μ : ℕ) * p / r) ≤ failureTolerance a := by
  let A := plateauTimeConstant a
  let b := decay a
  have hc := plateau_constants a hk
  have hm' : ((μ : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg n)) hc.2.1.le
  have hp : A * ((μ : ℕ) : ℝ) * n + 1 ≤ A * (n : ℝ) ^ 2 + 1 := by
    change A * (((μ : ℕ) : ℝ) * n) ≤ A * ((n : ℝ) * n) at h
    linarith only [h]
  simp only [changeBound, Bool.false_eq_true, if_false, mul_one, div_one]
  rw [show -b * ((μ : ℕ) : ℝ) * p = -b * (((μ : ℕ) : ℝ) * p) by ring]
  exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans
    (envelope_bound hc.2.1 hc.2.2.2.2 hn hC hpC le_rfl hN hc.2.2.2.1)

lemma avoidance_tail (a : Settings k) (hk : 2 ≤ k) (n : ℕ) (μ : ℕ+) (p C : ℝ)
    (hp : 0 < p) (hkp : (k : ℝ) / n ≤ p) (hnp : 1 ≤ (n : ℝ) * p)
    (hC : 3 / (decay a / 4) ≤ C) (hμC : C * Real.log (n * p) ≤ ((μ : ℕ) : ℝ))
    (hN : ((2 * plateauTimeConstant a / (decay a / 4) + 1) + 1) / failureTolerance a ≤ (n : ℝ) * p) :
    let r := changeBound n k p true
    (plateauTimeConstant a * ((μ : ℕ) : ℝ) * n * r + 1) *
      Real.exp (-decay a * (μ : ℕ) * p / r) ≤ failureTolerance a := by
  let A := plateauTimeConstant a
  let d := decay a
  let b := d / 4
  let m : ℝ := (μ : ℕ)
  let x : ℝ := (n : ℝ) * p
  let r := changeBound n k p true
  have hc := plateau_constants a hk
  have hA : 0 < A := hc.2.1
  have hd : 0 < d := hc.2.2.2.2
  have hb : 0 < b := by unfold b; positivity
  have hm : 0 ≤ m := by unfold m; positivity
  have hx : 0 ≤ x := by linarith only [hnp]
  have hr : r ≤ 2 * p := by
    change p + (k : ℝ) / n ≤ 2 * p
    linarith only [hkp]
  have hr' : 0 < r := by change 0 < p + (k : ℝ) / n; positivity
  have hex : Real.exp (-d * m * p / r) ≤ Real.exp (-(b * m + b * m)) := by
    apply Real.exp_le_exp.mpr
    have h' : b * m + b * m ≤ d * m * p / r := by
      apply (le_div_iff₀ hr').mpr
      calc
        _ ≤ (b * m + b * m) * (2 * p) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = _ := by unfold b; ring
    exact (show -d * m * p / r = -(d * m * p / r) by ring).le.trans (neg_le_neg h')
  have hmexp := multiplied_exp_small hb hm
  have hex1 : Real.exp (-b * m) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hb.le hm]
  have hR := mul_le_mul_of_nonneg_left hr (show 0 ≤ A * m * n by positivity)
  have hR' : A * m * n * r + 1 ≤ 2 * A * x * m + 1 := by
    unfold x
    linarith only [hR]
  have hI : (2 * A * x * m + 1) * Real.exp (-b * m) ≤ 2 * A / b * x + 1 := by
    have h := mul_le_mul_of_nonneg_left hmexp (show 0 ≤ 2 * A * x by positivity)
    calc
      _ = 2 * A * x * (m * Real.exp (-b * m)) + Real.exp (-b * m) := by ring
      _ ≤ 2 * A * x * (1 / b) + 1 := add_le_add h hex1
      _ = _ := by ring
  change (A * m * n * r + 1) * Real.exp (-d * m * p / r) ≤ _
  calc
    _ ≤ (2 * A * x * m + 1) * Real.exp (-(b * m + b * m)) :=
      mul_le_mul hR' hex (Real.exp_pos _).le (by positivity)
    _ = ((2 * A * x * m + 1) * Real.exp (-b * m)) * Real.exp (-b * m) := by
      rw [neg_add, Real.exp_add]
      simp only [neg_mul, mul_assoc]
    _ ≤ (2 * A / b * x + 1) * Real.exp (-b * m) := mul_le_mul_of_nonneg_right hI (Real.exp_pos _).le
    _ ≤ ((2 * A / b + 1) * x ^ 2 + 1) * Real.exp (-b * m) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have h := mul_le_mul_of_nonneg_left (show x ≤ x ^ 2 by nlinarith only [hnp, sq_nonneg (x - 1)])
        (show 0 ≤ 2 * A / b by positivity)
      nlinarith only [h, sq_nonneg x]
    _ ≤ _ := envelope_bound (by positivity) hb hnp hC hμC le_rfl hN hc.2.2.2.1

end
end Lax637351Proofs.UpperTails
