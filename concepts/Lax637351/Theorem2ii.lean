import Lax637351.Runtime
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
---
title: Theorem 2(ii)
type: theorem
---
Let $T$ be the optimization time of the $(\mu+1)$ genetic algorithm with crossover probability
$p_c$ on $\mathrm{Jump}_k$ with avoidance of replications, started from $\mu$ individuals
chosen independently and uniformly at random from $\{0,1\}^n$.

Let $k\ge2$ be a constant, $\mu\ge2$, and $p_c=\omega(1/n)$. If $\mu=\omega(\log(np_c))$, then
$\mathbb E[T]=O(\mu n\log(1+1/p_c))$.

Formally, for every $k\ge2$ there are $C,D>0$ and $N$ such that for all $n\ge N$, all
$p_c\in(0,1]$ with $p_c\ge N/n$ and all $\mu\ge2$ with $\mu\ge C\ln(np_c)$,
$$\mathbb E[T]\le D\mu n\ln(1+1/p_c).$$
-/

namespace Lax637351.Theorem2ii

open Lax637351.Algorithm Lax637351.Runtime
open scoped ENNReal

/-- $\mathbb E[T]\le D\mu n\ln(1+1/p_c)$ for $0<p_c\le1$ with $p_c\ge N/n$, $\mu\ge2$ and
$\mu\ge C\ln(np_c)$. -/
axiom bound :
    ∀ k : ℕ, 2 ≤ k →
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → (N : ℝ) / n ≤ p_c →
        ∀ μ : ℕ+, 2 ≤ μ → C * Real.log (n * p_c) ≤ μ →
          expectedOptimizationTime n k μ p_c (avoidReplications := true) ≤
            ENNReal.ofReal (D * μ * n * Real.log (1 + 1 / p_c))

end Lax637351.Theorem2ii
