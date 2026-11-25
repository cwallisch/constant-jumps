import Lax637351.Algorithm
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
---
title: Expected optimization time
type: definition
---
The $(\mu+1)$ genetic algorithm with crossover probability $p_c$ is run on
$\mathrm{Jump}_k$, starting from $\mu$ individuals chosen independently and uniformly at
random from $\{0,1\}^n$. Its optimization time $T$ is the number of iterations until the
population first contains the optimum $1^n$; iterations whose offspring is discarded by
avoidance of replications count as well. The expected optimization time is $\mathbb E[T]$.
-/

namespace Lax637351.Runtime

open Lax637351.Algorithm
open scoped ENNReal Classical

noncomputable section

/-- The population distribution after $t$ iterations of the $(\mu+1)$ GA.
Initialization is uniform over all populations, equivalently independent uniform initial
individuals. Each subsequent iteration uses `step` with fitness $\mathrm{Jump}_k$. -/
def populationDistribution (n k : ℕ) (μ : ℕ+) (p_c : ℝ) (avoidReplications : Bool) (t : ℕ) :
    PMF (Population n μ) :=
  match t with
  | 0 => PMF.uniformOfFintype (Population n μ)
  | s + 1 => do
      let P ← populationDistribution n k μ p_c avoidReplications s
      step (jump k) p_c avoidReplications P

/-- The expected optimization time $\mathbb E[T]=\sum_{t=0}^{\infty}\Pr[T>t]$. The inner sum is
the probability that the population after $t$ iterations does not contain $1^n$; for
$1\le k\le n$ it equals $\Pr[T>t]$, since $1^n$ has the unique maximal fitness and is never
lost once present. The sum is in nonnegative extended reals and may equal infinity. An optimum
already present in the initial population is found at time zero. -/
def expectedOptimizationTime (n k : ℕ) (μ : ℕ+) (p_c : ℝ) (avoidReplications : Bool) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑ P : Population n μ with (∀ i, P i ≠ optimum n),
    populationDistribution n k μ p_c avoidReplications t P

end
end Lax637351.Runtime
