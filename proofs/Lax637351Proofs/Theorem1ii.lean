import Lax637351.Theorem1ii
import Lax637351Proofs.UpperRegimes

namespace Lax637351Proofs.Theorem1ii

open Lax637351.Algorithm Lax637351.Runtime
open Lax637351Proofs.ColumnParameters Lax637351Proofs.UpperSizes
open Lax637351Proofs.UpperRuntime Lax637351Proofs.UpperRegimes
open Lax637351Proofs.ArrivalProgress
open scoped Classical ENNReal

/--
---
conclusion: Lax637351.Theorem1ii.bound
---
-/
theorem bound :
    ∀ k : ℕ, 2 ≤ k →
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ μ : ℕ+, 2 ≤ μ → μ ≤ n →
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → C * Real.log n / p_c ≤ μ →
          expectedOptimizationTime n k μ p_c (avoidReplications := false) ≤
            ENNReal.ofReal (D * μ * n) := by
  intro k hk
  obtain ⟨a⟩ := settings_exists k hk
  obtain ⟨M, hM⟩ := population_exists k a hk
  obtain ⟨N, hN, hd⟩ := dimension_threshold k hk a
  have hC := (population_constants a M).1
  refine ⟨populationConstant a M, runtimeConstant a, by linarith only [hC], runtimeConstant_pos a hk, N, ?_⟩
  intro n hn μ _ hμn p hp hp' h
  obtain ⟨hDim, hEntry, hError⟩ := hd n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hμ, hM', hnp, hlog, hc, hL, hf, ht⟩ :=
    vanilla_params a hk M n μ p (hN.trans hn') hμn ⟨hp, hp'⟩ h
  have hr := runtime_upper hk a hDim (hM μ hM') hEntry hError hμ p ⟨hp, hp'⟩ false hnp hlog hc hL hf ht
  simpa only [effective, Bool.false_eq_true, if_false, div_one, Real.log_exp, mul_one] using hr

end Lax637351Proofs.Theorem1ii
