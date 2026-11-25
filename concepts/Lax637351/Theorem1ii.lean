import Lax637351.Runtime
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
---
title: Theorem 1(ii)
type: theorem
---
Let $T$ be the optimization time of the $(\mu+1)$ genetic algorithm with crossover probability
$p_c$ on $\mathrm{Jump}_k$ without avoidance of replications, started from $\mu$ individuals
chosen independently and uniformly at random from $\{0,1\}^n$.

Let $k\ge2$ be a constant and $2\le\mu\le n$. If $\mu=\omega(\log(n)/p_c)$, then
$\mathbb E[T]=O(\mu n)$.

Formally, for every $k\ge2$ there are $C,D>0$ and $N$ such that for all $n\ge N$, all $\mu$
with $2\le\mu\le n$ and all $p_c\in(0,1]$ with $\mu\ge C\ln(n)/p_c$,
$$\mathbb E[T]\le D\mu n.$$
-/

namespace Lax637351.Theorem1ii

open Lax637351.Algorithm Lax637351.Runtime
open scoped ENNReal

/-- $\mathbb E[T]\le D\mu n$ for $2\le\mu\le n$ and $\mu\ge C\ln(n)/p_c$. Unlike part (i), this
part needs no bound $\mu\le n^{o(1)}$; $\mu\le n$ suffices. -/
axiom bound :
    ∀ k : ℕ, 2 ≤ k →
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ μ : ℕ+, 2 ≤ μ → μ ≤ n →
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → C * Real.log n / p_c ≤ μ →
          expectedOptimizationTime n k μ p_c (avoidReplications := false) ≤
            ENNReal.ofReal (D * μ * n)

end Lax637351.Theorem1ii
