import Lax637351.Runtime
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
---
title: Theorem 2(iii)
type: theorem
---
Let $T$ be the optimization time of the $(\mu+1)$ genetic algorithm with crossover probability
$p_c$ on $\mathrm{Jump}_k$ with avoidance of replications, started from $\mu$ individuals
chosen independently and uniformly at random from $\{0,1\}^n$.

Let $k\ge2$ be a constant and $\mu\ge2$. If $p_c=O(1/n)$, then
$\mathbb E[T]=O(\mu n\log n+1/p_c)$.

Formally, for every $k\ge2$ and every $B>0$ there are $D>0$ and $N$ such that for all $n\ge N$,
all $p_c\in(0,1]$ with $p_c\le B/n$ and all $\mu\ge2$,
$$\mathbb E[T]\le D\left(\mu n\ln n+\frac1{p_c}\right).$$
-/

namespace Lax637351.Theorem2iii

open Lax637351.Algorithm Lax637351.Runtime
open scoped ENNReal

/-- $\mathbb E[T]\le D(\mu n\ln n+1/p_c)$ for $0<p_c\le\min\{1,B/n\}$ and $\mu\ge2$. -/
axiom bound :
    ∀ k : ℕ, 2 ≤ k →
    ∀ B : ℝ, 0 < B →
      ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → p_c ≤ B / n →
        ∀ μ : ℕ+, 2 ≤ μ →
          expectedOptimizationTime n k μ p_c (avoidReplications := true) ≤
            ENNReal.ofReal (D * (μ * n * Real.log n + 1 / p_c))

end Lax637351.Theorem2iii
