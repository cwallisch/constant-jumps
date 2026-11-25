import Lax637351.Runtime
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Theorem 1(i)
type: theorem
---
Let $T$ be the optimization time of the $(\mu+1)$ genetic algorithm with crossover probability
$p_c$ on $\mathrm{Jump}_k$ without avoidance of replications, started from $\mu$ individuals
chosen independently and uniformly at random from $\{0,1\}^n$.

Let $k\ge2$ be a constant and $2\le\mu\le n^{o(1)}$. If $\mu=o(\log(n)/p_c)$, then
$\mathbb E[T]\ge n^{k-o(1)}$.

Formally, for every $k\ge2$ and every $\eta>0$ there are $\delta,\varepsilon>0$ and $N$ such
that for all $n\ge N$, all $\mu$ with $2\le\mu\le n^\delta$ and all $p_c\in(0,1]$ with
$\mu\le\varepsilon\ln(n)/p_c$,
$$\mathbb E[T]\ge n^{k-\eta}.$$
-/

namespace Lax637351.Theorem1i

open Lax637351.Algorithm Lax637351.Runtime
open scoped ENNReal

/-- $\mathbb E[T]\ge n^{k-\eta}$ for $2\le\mu\le n^\delta$ and $\mu\le\varepsilon\ln(n)/p_c$. -/
axiom bound :
    ∀ k : ℕ, 2 ≤ k →
    ∀ η : ℝ, 0 < η →
      ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ μ : ℕ+, 2 ≤ μ → μ ≤ (n : ℝ) ^ δ →
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → μ ≤ ε * Real.log n / p_c →
          expectedOptimizationTime n k μ p_c (avoidReplications := false) ≥
            ENNReal.ofReal ((n : ℝ) ^ ((k : ℝ) - η))

end Lax637351.Theorem1i
