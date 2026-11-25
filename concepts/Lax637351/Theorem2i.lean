import Lax637351.Runtime
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Theorem 2(i)
type: theorem
---
Let $T$ be the optimization time of the $(\mu+1)$ genetic algorithm with crossover probability
$p_c$ on $\mathrm{Jump}_k$ with avoidance of replications, started from $\mu$ individuals
chosen independently and uniformly at random from $\{0,1\}^n$.

Let $k\ge2$ be a constant, $\mu\ge2$, and $p_c=\omega(1/n)$. If $\mu=o(\log(np_c))$, then
$\mathbb E[T]\ge(np_c)^{k-o(1)}/p_c$.

Formally, for every $k\ge2$ and every $\eta>0$ there are $\varepsilon>0$ and $N$ such that for
all $n\ge N$, all $p_c\in(0,1]$ with $p_c\ge N/n$ and all $\mu$ with
$2\le\mu\le\varepsilon\ln(np_c)$,
$$\mathbb E[T]\ge\frac{(np_c)^{k-\eta}}{p_c}.$$
-/

namespace Lax637351.Theorem2i

open Lax637351.Algorithm Lax637351.Runtime
open scoped ENNReal

/-- $\mathbb E[T]\ge(np_c)^{k-\eta}/p_c$ for $0<p_c\le1$ with $p_c\ge N/n$ and
$2\le\mu\le\varepsilon\ln(np_c)$. -/
axiom bound :
    ∀ k : ℕ, 2 ≤ k →
    ∀ η : ℝ, 0 < η →
      ∃ ε : ℝ, 0 < ε ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → (N : ℝ) / n ≤ p_c →
        ∀ μ : ℕ+, 2 ≤ μ → μ ≤ ε * Real.log (n * p_c) →
          expectedOptimizationTime n k μ p_c (avoidReplications := true) ≥
            ENNReal.ofReal ((n * p_c) ^ ((k : ℝ) - η) / p_c)

end Lax637351.Theorem2i
