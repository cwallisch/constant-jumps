import Lax637351.Theorem1i
import Lax637351Proofs.UniformColumn

namespace Lax637351Proofs.Theorem1i

open Lax637351.Algorithm Lax637351.Runtime
open Lax637351Proofs.EntryScales Lax637351Proofs.UniformColumn
open Lax637351Proofs.SlopeReset Lax637351Proofs.SlopeCharge
open Lax637351Proofs.PowerBounds Lax637351Proofs.RegenerationBounds
open Filter
open scoped Classical ENNReal Topology

noncomputable section

lemma budget_small (n : ℕ) (hn : 2 ≤ n) (μ : ℕ+) (p : ℝ) (hpos : 0 < p)
    (s d ε : ℝ) (_hs : 0 < s) (hd : d ≤ 1 / 1000) (hlo : 4 * d ≤ s / 4) (he : 32 * ε ≤ s / 4)
    (hμ : ((μ : ℕ) : ℝ) ≤ (n : ℝ) ^ d) (hload : ((μ : ℕ) : ℝ) ≤ ε * Real.log n / p)
    (habsorb : (32 * Real.exp 16) * (n : ℝ) ^ (s / 2) ≤ (n : ℝ) ^ s) :
    copyBudget n (cutoff n) μ p ≤ (n : ℝ) ^ s := by
  let x : ℝ := n
  let m : ℝ := (μ : ℕ)
  let B : ℝ := cutoff n
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < n by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hB : B ≤ x ^ (1 / 5 : ℝ) := cutoff_upper n
  have hload' := (le_div_iff₀ hpos).mp hload
  have hC : 16 * m ^ 2 * B / x ≤ 16 := by
    apply (div_le_iff₀ hx).mpr
    have hm2 := pow_le_pow_left₀ hm hμ 2
    have h := mul_le_mul hm2 hB (by positivity : 0 ≤ B) (by positivity : 0 ≤ (x ^ d) ^ 2)
    have heq : (x ^ d) ^ 2 * x ^ (1 / 5 : ℝ) = x ^ (2 * d + 1 / 5) := by
      rw [rpow_pow _ _ hx.le, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    rw [heq] at h
    have hh : x ^ (2 * d + 1 / 5) ≤ x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx1 (show 2 * d + 1 / 5 ≤ 1 by linarith only [hd])
    have h' := h.trans hh
    nlinarith only [h']
  have hExp : 32 * m * p + 16 * m ^ 2 * B / x ≤ (s / 4) * Real.log x + 16 := by
    change m * p ≤ ε * Real.log x at hload'
    have h := mul_le_mul_of_nonneg_right he (Real.log_nonneg hx1)
    linarith only [h, hload', hC]
  have hpow : m ^ 4 ≤ x ^ (s / 4) := by
    have hh := pow_le_pow_left₀ hm hμ 4
    rw [rpow_pow _ _ hx.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by
      push_cast
      linarith only [hlo]))
  have hE : Real.exp (32 * m * p + 16 * m ^ 2 * B / x) ≤ x ^ (s / 4) * Real.exp 16 := by
    apply (Real.exp_le_exp.mpr hExp).trans_eq
    rw [Real.exp_add, Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
  have hf := mul_le_mul hpow hE (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)
  change 32 * m ^ 4 * Real.exp (32 * m * p + 16 * m ^ 2 * B / x) ≤ _
  rw [mul_assoc]
  apply (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 32)).trans
  have heq : 32 * (x ^ (s / 4) * (x ^ (s / 4) * Real.exp 16)) = (32 * Real.exp 16) * x ^ (s / 2) := by
    rw [← mul_assoc (x ^ (s / 4)), ← Real.rpow_add hx, show s / 4 + s / 4 = s / 2 by ring]
    ring
  rw [heq]
  exact habsorb

lemma charge_power (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (s : ℝ) :
    128 * slopeCharge n ((n : ℝ) ^ s) k =
      (128 * (k.factorial : ℝ) * 2 * (2 * (k : ℝ)) ^ (k - 1)) *
        (n : ℝ) ^ (s * ((k - 1 : ℕ) : ℝ) - k) := by
  let x : ℝ := n
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hn
  rw [slopeCharge_eq n (x ^ s) (Real.rpow_pos_of_pos hx _) k hk]
  change 128 * ((k.factorial : ℝ) * (2 / x) * (2 * (k : ℝ) * x ^ s / x) ^ (k - 1)) = _
  have hr : x ^ s / x = x ^ (s - 1) := by simpa only [Real.rpow_one] using (Real.rpow_sub hx s 1).symm
  rw [mul_div_assoc, hr, mul_pow, rpow_pow _ _ hx.le]
  have he : ((s - 1) * ((k - 1 : ℕ) : ℝ)) - 1 = s * ((k - 1 : ℕ) : ℝ) - k := by
    have hk' : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast Nat.sub_add_cancel hk
    linarith only [hk']
  have ht : x ^ ((s - 1) * ((k - 1 : ℕ) : ℝ)) / x = x ^ (s * ((k - 1 : ℕ) : ℝ) - k) := by
    simpa only [Real.rpow_one, he] using (Real.rpow_sub hx ((s - 1) * ((k - 1 : ℕ) : ℝ)) 1).symm
  rw [← ht]
  ring

/--
---
conclusion: Lax637351.Theorem1i.bound
---
-/
theorem bound :
    ∀ k : ℕ, 2 ≤ k →
    ∀ η : ℝ, 0 < η →
      ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ μ : ℕ+, 2 ≤ μ → μ ≤ (n : ℝ) ^ δ →
        ∀ p : ℝ, 0 < p → p ≤ 1 → μ ≤ ε * Real.log n / p →
          expectedOptimizationTime n k μ p false ≥
            ENNReal.ofReal ((n : ℝ) ^ ((k : ℝ) - η)) := by
  intro k hk η hη
  let s := min (1 / 10 : ℝ) (η / (2 * (k : ℝ)))
  let δ := min (1 / 1000 : ℝ) (s / 16)
  let ε := s / 128
  let C := 128 * (k.factorial : ℝ) * 2 * (2 * (k : ℝ)) ^ (k - 1)
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hs : 0 < s := lt_min (by norm_num) (div_pos hη (by positivity))
  have hs1 : s ≤ 1 / 10 := min_le_left _ _
  have hsη : s ≤ η / (2 * (k : ℝ)) := min_le_right _ _
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ1 : δ ≤ 1 / 1000 := min_le_left _ _
  have hδs : 4 * δ ≤ s / 4 := by
    have h : δ ≤ s / 16 := min_le_right _ _
    linarith only [h]
  have heps : 32 * ε ≤ s / 4 := by dsimp [ε]; linarith
  have htail : ∀ᶠ n : ℕ in atTop, ∀ μ : ℕ+, 2 ≤ μ → ((μ : ℕ) : ℝ) ≤ (n : ℝ) ^ δ →
      ∀ p : ℝ, 0 < p → p ≤ 1 → ((μ : ℕ) : ℝ) ≤ ε * Real.log n / p →
      expectedOptimizationTime n k μ p false ≥ ENNReal.ofReal ((n : ℝ) ^ ((k : ℝ) - η)) := by
    filter_upwards [
      eventually_ge_atTop (2 : ℕ), entry_scales_eventually k,
      power_absorb (32 * Real.exp 16) (s / 2) s (by linarith only [hs]),
      power_absorb (2 * Real.exp 1) (1 / 2) 1 (by norm_num),
      power_absorb 8 (3 / 10) 1 (by norm_num),
      power_absorb C (-η / 2) 0 (by linarith only [hη])] with n hnn hN hB hsmall hslack hscale
    intro μ hμ hμ' p hp hp1 hload
    let x : ℝ := n
    let M := x ^ s
    have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
    have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
    have S := hN μ (hμ'.trans (Real.rpow_le_rpow_of_exponent_le hx1 hδ1))
    have hM := budget_small n hnn μ p hp s δ ε hs hδ1 hδs heps hμ' hload hB
    have hM0 := Real.rpow_pos_of_pos hx s
    have hMx : M ≤ x ^ (1 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hs1
    have htmp : 2 * Real.exp 1 * (cutoff n : ℝ) ^ 2 * M / n ≤ 1 := by
      have hb := pow_le_pow_left₀ (show 0 ≤ (cutoff n : ℝ) by positivity) (cutoff_upper n) 2
      have hh := mul_le_mul hb hMx hM0.le (by positivity)
      rw [rpow_pow _ _ hx.le, ← Real.rpow_add hx] at hh
      norm_num at hh
      rw [Real.rpow_one] at hsmall
      apply (div_le_one hx).mpr
      have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * Real.exp 1 by positivity)
      exact (by nlinarith only [ht] :
        2 * Real.exp 1 * (cutoff n : ℝ) ^ 2 * M ≤ 2 * Real.exp 1 * x ^ (1 / 2 : ℝ)).trans hsmall
    have htmp' : 2 * (cutoff n : ℝ) * M / n ≤ 1 / 4 := by
      have hh := mul_le_mul (cutoff_upper n) hMx hM0.le (by positivity)
      rw [← Real.rpow_add hx] at hh
      norm_num at hh
      rw [Real.rpow_one] at hslack
      apply (div_le_iff₀ hx).mpr
      have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ (8 : ℝ) by norm_num)
      linarith only [ht, hslack]
    apply le_trans _ (from_uniform_column hk hμ S p ⟨hp.le, hp1⟩ M hM htmp htmp')
    apply ENNReal.ofReal_le_ofReal
    have hα := slopeCharge_pos n (by omega) M hM0 k hk0
    apply (le_div_iff₀ (mul_pos (by norm_num : 0 < (128 : ℝ)) hα)).mpr
    rw [charge_power n k (by omega) hk0 s]
    have heq : x ^ ((k : ℝ) - η) *
        (C * x ^ (s * ((k - 1 : ℕ) : ℝ) - k)) =
      C * x ^ (s * ((k - 1 : ℕ) : ℝ) - η) := by
      rw [mul_left_comm, ← Real.rpow_add hx]
      congr 2
      ring
    change x ^ ((k : ℝ) - η) * (C * x ^ (s * ((k - 1 : ℕ) : ℝ) - k)) ≤ 1
    rw [heq]
    rw [Real.rpow_zero] at hscale
    have hxη : s * ((k - 1 : ℕ) : ℝ) - η ≤ -η / 2 := by
      have hm := mul_le_mul_of_nonneg_left (show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.sub_le k 1) hs.le
      have ht := (le_div_iff₀ (show 0 < 2 * (k : ℝ) by positivity)).mp hsη
      linarith only [hm, ht]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hxη) (by dsimp [C]; positivity)).trans hscale
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  exact ⟨δ, ε, hδ, hε, N, hN⟩

end
end Lax637351Proofs.Theorem1i
