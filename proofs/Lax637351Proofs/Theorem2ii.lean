import Lax637351.Theorem2ii
import Lax637351Proofs.UpperRegimes

namespace Lax637351Proofs.Theorem2ii

open Lax637351.Algorithm Lax637351.Runtime
open Lax637351Proofs.ColumnParameters Lax637351Proofs.UpperSizes
open Lax637351Proofs.UpperRuntime Lax637351Proofs.UpperRegimes
open Lax637351Proofs.ArrivalProgress
open scoped Classical ENNReal

/--
---
conclusion: Lax637351.Theorem2ii.bound
---
-/
theorem bound :
    ∀ k : ℕ, 2 ≤ k →
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → (N : ℝ) / n ≤ p_c →
        ∀ μ : ℕ+, 2 ≤ μ → C * Real.log (n * p_c) ≤ μ →
          expectedOptimizationTime n k μ p_c (avoidReplications := true) ≤
            ENNReal.ofReal (D * μ * n * Real.log (1 + 1 / p_c)) := by
  intro k hk
  obtain ⟨a⟩ := settings_exists k hk
  obtain ⟨M, hM⟩ := population_exists k a hk
  obtain ⟨N, hN, hd⟩ := dimension_threshold k hk a
  have hC := (population_constants a M).1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨populationConstant a M, runtimeConstant a * (1 + (Real.log 2)⁻¹), by linarith only [hC],
    mul_pos (runtimeConstant_pos a hk) (add_pos one_pos (inv_pos.mpr hlog2)), N, ?_⟩
  intro n hn p hp hp' hpn μ _ h
  obtain ⟨hDim, hEntry, hError⟩ := hd n hn
  have hn₀ : 0 < n := by have := hDim.two; omega
  have hnp' : (N : ℝ) ≤ (n : ℝ) * p := by
    rw [mul_comm]
    exact (div_le_iff₀ (by exact_mod_cast hn₀)).mp hpn
  obtain ⟨hμ, hM', hnp, hlog, hc, hL, hf, ht⟩ :=
    avoidance_params a hk M n μ p hn₀ ⟨hp, hp'⟩ (hN.trans hnp') h
  have hr := runtime_upper hk a hDim (hM μ hM') hEntry hError hμ p ⟨hp, hp'⟩ true hnp hlog hc hL hf ht
  have hr' : expectedOptimizationTime n k μ p (avoidReplications := true) ≤
      ENNReal.ofReal (runtimeConstant a * μ * n * Real.log (Real.exp 1 / p)) := by
    simpa only [effective, if_true] using hr
  refine hr'.trans (ENNReal.ofReal_le_ofReal ?_)
  -- For 0 < p ≤ 1: ln(e/p) = 1 + ln(1/p) ≤ (1 + 1/ln 2) ln(1 + 1/p), since 1 + 1/p ≥ 2.
  have hinv : 1 ≤ 1 / p := by rw [le_div_iff₀ hp]; linarith
  have hL2 : Real.log 2 ≤ Real.log (1 + 1 / p) := Real.log_le_log (by norm_num) (by linarith)
  have hLp : Real.log (1 / p) ≤ Real.log (1 + 1 / p) :=
    Real.log_le_log (one_div_pos.mpr hp) (by linarith)
  have he : Real.log (Real.exp 1 / p) = 1 + Real.log (1 / p) := by
    rw [Real.log_div (Real.exp_pos 1).ne' hp.ne', Real.log_exp, one_div, Real.log_inv]; ring
  have h1 : 1 ≤ (Real.log 2)⁻¹ * Real.log (1 + 1 / p) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hlog2]; linarith
  have hcmp : Real.log (Real.exp 1 / p) ≤ (1 + (Real.log 2)⁻¹) * Real.log (1 + 1 / p) := by
    have hexp : (1 + (Real.log 2)⁻¹) * Real.log (1 + 1 / p) =
        Real.log (1 + 1 / p) + (Real.log 2)⁻¹ * Real.log (1 + 1 / p) := by ring
    rw [he, hexp]; linarith
  have hpos : 0 ≤ runtimeConstant a * μ * n :=
    mul_nonneg (mul_nonneg (runtimeConstant_pos a hk).le (by positivity)) (by positivity)
  calc _ ≤ runtimeConstant a * μ * n * ((1 + (Real.log 2)⁻¹) * Real.log (1 + 1 / p)) :=
        mul_le_mul_of_nonneg_left hcmp hpos
    _ = _ := by ring

end Lax637351Proofs.Theorem2ii
