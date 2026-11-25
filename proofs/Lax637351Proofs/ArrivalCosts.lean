import Lax637351Proofs.ArrivalProgress
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Lax637351Proofs.ArrivalCosts

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift
open Lax637351Proofs.ArrivalMutation Lax637351Proofs.ArrivalTime
open Lax637351Proofs.ArrivalCross Lax637351Proofs.ArrivalProgress
open scoped Classical ENNReal

noncomputable section

lemma harmonic_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  have he : (∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹)) = (harmonic n : ℝ) := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact he.le.trans (harmonic_le_one_add_log n)

lemma root_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h₀ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h := Real.sqrt_pos.2 h₀
    have hu := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n + 1 : ℕ) by exact_mod_cast Nat.le_succ n)
    have hs := Real.sq_sqrt h₀.le
    have ht := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
    have hh : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) := by
      rw [← one_div, div_le_iff₀ h]
      have hp := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu)
      push_cast at hs ⊢
      nlinarith only [hp, hs, ht]
    linarith only [ih, hh]

lemma harmonic_after (m : ℕ) (hm : 0 < m) (l : ℕ) :
    (∑ j ∈ Finset.range l, (((m + j + 1 : ℕ) : ℝ)⁻¹)) ≤
      Real.log ((m + l : ℕ) : ℝ) - Real.log m := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ]
    have h : (0 : ℝ) < (m + l : ℕ) := by exact_mod_cast (show 0 < m + l by omega)
    have h' : (0 : ℝ) < (m + l + 1 : ℕ) := by positivity
    have ht := Real.log_le_sub_one_of_pos (div_pos h h')
    rw [Real.log_div h.ne' h'.ne'] at ht
    have he : (((m + l : ℕ) : ℝ) / ((m + l + 1 : ℕ) : ℝ)) - 1 =
        - (((m + l + 1 : ℕ) : ℝ)⁻¹) := by
      push_cast
      field_simp
      ring
    rw [he] at ht
    change _ ≤ Real.log ((m + l + 1 : ℕ) : ℝ) - _
    linarith only [ih, ht]

lemma reciprocal_estimate (T z j m : ℝ) (hT : 0 < T) (hz : 0 < z) (hj : 0 < j) (hm : 0 < m) :
    (z + T * j / m)⁻¹ ≤ Real.sqrt (m / T) * (Real.sqrt z)⁻¹ * (Real.sqrt j)⁻¹ := by
  let C := Real.sqrt (m / T)
  let x := Real.sqrt z
  let y := Real.sqrt j
  have hC : 0 < C := Real.sqrt_pos.2 (div_pos hm hT)
  have hx : 0 < x := Real.sqrt_pos.2 hz
  have hy : 0 < y := Real.sqrt_pos.2 hj
  have hc : C ^ 2 = m / T := Real.sq_sqrt (by positivity)
  have hx2 : x ^ 2 = z := Real.sq_sqrt hz.le
  have hy2 : y ^ 2 = j := Real.sq_sqrt hj.le
  have hD : 0 < z + T * j / m := by positivity
  change (z + T * j / m)⁻¹ ≤ C * x⁻¹ * y⁻¹
  rw [show C * x⁻¹ * y⁻¹ = C / (x * y) by ring]
  rw [← one_div, div_le_div_iff₀ hD (mul_pos hx hy), one_mul]
  have hcoeff : T / m * C ^ 2 = 1 := by rw [hc]; field_simp
  have hscale : C ^ 2 * (T * j / m) = j := by
    calc
      _ = (T / m * C ^ 2) * j := by ring
      _ = _ := by rw [hcoeff, one_mul]
  apply (le_of_mul_le_mul_left _ hC)
  calc
    C * (x * y) ≤ (C * x) ^ 2 + y ^ 2 := by
      nlinarith only [sq_nonneg (C * x - y), mul_nonneg (mul_nonneg hC.le hx.le) hy.le]
    _ = C * (C * (z + T * j / m)) := by
      calc
        _ = C ^ 2 * z + j := by rw [← hx2, hy2]; ring
        _ = C ^ 2 * z + C ^ 2 * (T * j / m) := by rw [hscale]
        _ = _ := by ring

lemma grid_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (r : ℝ)
    (hr : 0 < r ∧ r ≤ 1) (hrn : 1 ≤ (n : ℝ) * r) :
    (∑ u ∈ Finset.range n, ∑ j ∈ Finset.range m,
        (((u + 1 : ℕ) : ℝ) / n + r * (j : ℝ) / m)⁻¹) ≤
      (n : ℝ) * (1 + Real.log n) + (m : ℝ) * n * (5 + Real.log (1 / r)) := by
  let T := (n : ℝ) * r
  let s := ⌊T⌋₊
  let C := Real.sqrt ((m : ℝ) / T)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : 0 < T := mul_pos hnR hr.1
  have hsT : (s : ℝ) ≤ T := Nat.floor_le hT.le
  have hTs : T < (s : ℝ) + 1 := Nat.lt_floor_add_one T
  have hs : 0 < s := by
    by_contra! h
    have he : s = 0 := Nat.eq_zero_of_le_zero h
    rw [he, Nat.cast_zero, zero_add] at hTs
    exact (not_lt.mpr hrn) hTs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsn : s ≤ n := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hh : T ≤ (n : ℝ) := by dsimp [T]; nlinarith only [hr.2, hnR, mul_le_mul_of_nonneg_left hr.2 hnR.le]
    exact hsT.trans hh
  have hfrac : (n : ℝ) / s ≤ 2 / r := by
    rw [div_le_div_iff₀ hsR hr.1]
    have hh : (1 : ℝ) ≤ s := by exact_mod_cast hs
    change T ≤ (2 : ℝ) * s
    linarith only [hTs, hh]
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hroot : C * Real.sqrt s * Real.sqrt m ≤ m := by
    calc
      _ = Real.sqrt (((m : ℝ) / T * s) * m) := by
        dsimp [C]
        rw [Real.sqrt_mul (by positivity : 0 ≤ (m : ℝ) / T * s), Real.sqrt_mul (by positivity : 0 ≤ (m : ℝ) / T)]
      _ ≤ Real.sqrt ((m : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hbound : ((m : ℝ) / T) * s ≤ m := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hT]
          exact mul_le_mul_of_nonneg_left hsT hmR.le
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hbound hmR.le
      _ = _ := Real.sqrt_sq hmR.le
  let f (u j : ℕ) := (((u + 1 : ℕ) : ℝ) / n + r * (j : ℝ) / m)⁻¹
  have hf (u j : ℕ) : f u j = (n : ℝ) * (((u + 1 : ℕ) : ℝ) + T * (j : ℝ) / m)⁻¹ := by
    unfold f T
    rw [← div_inv_eq_mul, ← inv_div]
    field_simp
  have hzero : (∑ u ∈ Finset.range n, f u 0) ≤ (n : ℝ) * (1 + Real.log n) := by
    simp_rw [hf, Nat.cast_zero, mul_zero, zero_div, add_zero, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (harmonic_range n) hnR.le
  let h (u : ℕ) : ℝ := ∑ j ∈ Finset.range (m - 1), f u (j + 1)
  have hsmall : (∑ u ∈ Finset.range s, h u) ≤ 4 * (m : ℝ) * n := by
    have hpoint (u j : ℕ) : f u (j + 1) ≤ (n : ℝ) * C *
        (Real.sqrt (u + 1 : ℕ))⁻¹ * (Real.sqrt (j + 1 : ℕ))⁻¹ := by
      rw [hf]
      have h := mul_le_mul_of_nonneg_left (reciprocal_estimate T ((u + 1 : ℕ) : ℝ)
        ((j + 1 : ℕ) : ℝ) m hT (by positivity) (by positivity) hmR) hnR.le
      simpa only [C, ← mul_assoc] using h
    calc
      _ ≤ ∑ u ∈ Finset.range s, ∑ j ∈ Finset.range (m - 1), (n : ℝ) * C *
          (Real.sqrt (u + 1 : ℕ))⁻¹ * (Real.sqrt (j + 1 : ℕ))⁻¹ :=
        Finset.sum_le_sum (fun u _ ↦ Finset.sum_le_sum (fun j _ ↦ hpoint u j))
      _ = ((n : ℝ) * C) * (∑ u ∈ Finset.range s, (Real.sqrt (u + 1 : ℕ))⁻¹) *
          (∑ j ∈ Finset.range (m - 1), (Real.sqrt (j + 1 : ℕ))⁻¹) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ((n : ℝ) * C) * (2 * Real.sqrt s) * (2 * Real.sqrt m) := by
        have h1 := root_range s
        have h2 := (root_range (m - 1)).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) by exact_mod_cast Nat.sub_le m 1)) (by norm_num : (0 : ℝ) ≤ 2))
        gcongr
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 4 * (n : ℝ) by positivity)]
  have hlarge : (∑ u ∈ Finset.range (n - s), h (s + u)) ≤ (m : ℝ) * n * (1 + Real.log (1 / r)) := by
    have hpoint (u j : ℕ) : f (s + u) (j + 1) ≤ (n : ℝ) * (((s + u + 1 : ℕ) : ℝ)⁻¹) := by
      rw [hf]
      apply mul_le_mul_of_nonneg_left _ hnR.le
      apply inv_anti₀ (by positivity)
      exact le_add_of_nonneg_right (by positivity)
    have hrec (u : ℕ) : h (s + u) ≤ (m : ℝ) * ((n : ℝ) * (((s + u + 1 : ℕ) : ℝ)⁻¹)) := by
      apply (Finset.sum_le_sum (fun j _ ↦ hpoint u j)).trans
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le m 1) (by positivity)
    have hsum := harmonic_after s hs (n - s)
    rw [Nat.add_sub_of_le hsn] at hsum
    have hlog : Real.log n - Real.log s ≤ 1 + Real.log (1 / r) := by
      rw [← Real.log_div hnR.ne' hsR.ne']
      rw [show (2 : ℝ) / r = 2 * (1 / r) by ring] at hfrac
      have hh := Real.log_le_log (div_pos hnR hsR) hfrac
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (one_div_ne_zero hr.1.ne')] at hh
      have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [hh, htwo]
    calc
      _ ≤ ∑ u ∈ Finset.range (n - s), (m : ℝ) * ((n : ℝ) * (((s + u + 1 : ℕ) : ℝ)⁻¹)) :=
        Finset.sum_le_sum (fun u _ ↦ hrec u)
      _ = (m : ℝ) * n * (∑ u ∈ Finset.range (n - s), (((s + u + 1 : ℕ) : ℝ)⁻¹)) := by
        simp_rw [← mul_assoc, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.trans hlog) (by positivity)
  change (∑ u ∈ Finset.range n, ∑ j ∈ Finset.range m, f u j) ≤ _
  have hsplit (u : ℕ) : (∑ j ∈ Finset.range m, f u j) = f u 0 + h u := by
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ m), Finset.sum_range_succ']
    simp [h, add_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hsum : (∑ u ∈ Finset.range n, h u) =
      (∑ u ∈ Finset.range s, h u) + ∑ u ∈ Finset.range (n - s), h (s + u) := by
    simpa only [Nat.add_sub_of_le hsn] using Finset.sum_range_add h s (n - s)
  rw [hsum]
  nlinarith only [hzero, hsmall, hlarge]

end
end Lax637351Proofs.ArrivalCosts
