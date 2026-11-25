import Mathlib.Data.PNat.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
---
title: The $(\mu+1)$ GA and the function $\mathrm{Jump}_k$
type: definition
---
For $x\in\{0,1\}^n$, let $|x|_1$ be its number of ones. For a jump size $k\in\{1,\dots,n\}$,
the function $\mathrm{Jump}_k\colon\{0,1\}^n\to\mathbb N$ is
$$\mathrm{Jump}_k(x)=\begin{cases}k+|x|_1 & \text{if } |x|_1\le n-k \text{ or } |x|_1=n,\\
n-|x|_1 & \text{otherwise.}\end{cases}$$

The $(\mu+1)$ genetic algorithm with crossover probability $p_c\in[0,1]$ maintains a
population, a multiset of $\mu$ individuals from $\{0,1\}^n$. One iteration, maximizing a
fitness function $f$, proceeds as follows:

1. With probability $p_c$, choose two parents $y_1,y_2$ uniformly at random with replacement
   from the population. Create $y$ by uniform crossover of $y_1$ and $y_2$, which takes each
   bit from $y_1$ or $y_2$ independently with probability $1/2$. Create the offspring $z$ by
   standard bit mutation of $y$, which flips each bit independently with probability $1/n$.
2. Otherwise, choose a parent $y$ uniformly at random and create $z$ by standard bit mutation
   of $y$. With avoidance of replications, if $z=y$, then $z$ is discarded and the iteration
   ends.
3. Add $z$ to the population and remove an individual with the lowest fitness, breaking ties
   uniformly at random.
-/

namespace Lax637351.Algorithm

open scoped ENNReal Classical

noncomputable section

/-- A bit string in $\{0,1\}^n$. `Fin n` indexes positions $0,\ldots,n-1$;
`Fin 2` consists of the values zero and one. -/
abbrev BitString (n : ℕ) := Fin n → Fin 2

/-- A population of positive size $\mu$, listed as $\mu$ individuals with indices, so that equal
individuals count separately. An iteration writes the offspring into the slot of the deleted
individual, or leaves the population unchanged if the offspring itself is deleted or discarded;
up to the order of the individuals, this is adding it and then deleting. -/
abbrev Population (n : ℕ) (μ : ℕ+) := Fin μ → BitString n

/-- The number of one-bits in a string. -/
def ones {n : ℕ} (x : BitString n) : ℕ :=
  ∑ j : Fin n, (x j : ℕ)

/-- The function $\mathrm{Jump}_k$ with jump size `k`, usually considered for $n\ge2$ and
$1\le k\le n/2$. Fitness values are real numbers; natural-number subtraction is truncated
at zero. -/
def jump {n : ℕ} (k : ℕ) (x : BitString n) : ℝ :=
  if ones x ≤ n - k ∨ ones x = n then (k + ones x : ℕ) else (n - ones x : ℕ)

/-- The all-one string $1^n$, the unique optimum of $\mathrm{Jump}_k$ when $1\le k\le n$. -/
def optimum (n : ℕ) : BitString n := fun _ ↦ 1

/-- A coin flip, `true` with probability $p$ for $0\le p\le1$.
Outside this interval it always returns `false`; all algorithm claims use valid probabilities. -/
def coin (p : ℝ) : PMF Bool :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    PMF.ofFintype (fun b : Bool ↦ ENNReal.ofReal (if b then p else 1 - p))
      -- Lean checks this proof that the probabilities sum to one; readers can skip it.
      (by simp_all [← ENNReal.ofReal_add])
  else PMF.pure false

/-- Independent random bits, each equal to one with probability $p$: a string $x$ has
probability $p^{|x|_1}(1-p)^{n-|x|_1}$ for $0\le p\le1$. Here `coin p (x j = 1)` is $p$ if
$x_j=1$ and $1-p$ if $x_j=0$. -/
def independentBits (n : ℕ) (p : ℝ) : PMF (BitString n) :=
  PMF.ofFintype (fun x ↦ ∏ j, coin p (x j = 1))
    -- Lean checks this proof that the probabilities sum to one; readers can skip it.
    (by
      have h := (coin p).tsum_coe
      rw [tsum_fintype] at h
      rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Fin 2) ↦ coin p (b = 1))]
      simp [Fin.sum_univ_two, add_comm] at h ⊢
      simp [h])

/-- Uniform crossover: at each position an independent fair mask bit selects one parent.
Sampling the mask uniformly among all bit strings gives independent fair choices. -/
def crossover {n : ℕ} (x y mask : BitString n) : BitString n :=
  fun j ↦ if mask j = 1 then x j else y j

/-- Flip exactly the positions where the mutation mask is one. -/
def mutate {n : ℕ} (x mask : BitString n) : BitString n :=
  fun j ↦ if mask j = 1 then 1 - x j else x j

/-- Uniform deletion among the individuals of minimal `fitness` in `Q`, the $\mu+1$ individuals of
the population with the offspring added. Such an individual exists because `Q` is finite and
nonempty. -/
def deletionIndex {n : ℕ} (fitness : BitString n → ℝ) {μ : ℕ+}
    (Q : Fin ((μ : ℕ) + 1) → BitString n) : PMF (Fin ((μ : ℕ) + 1)) :=
  PMF.uniformOfFinset
    (Finset.univ.filter fun i ↦ ∀ j, fitness (Q i) ≤ fitness (Q j))
    -- Lean checks this proof that a minimal individual exists; readers can skip it.
    (by simpa [Finset.filter_nonempty_iff] using Finite.exists_min fun j ↦ fitness (Q j))

/-- One iteration of the $(\mu+1)$ GA, maximizing `fitness`.
Crossover parents are independent uniform draws with replacement; the parent in a
mutation-only iteration is uniform. Mutation flips each bit independently with probability $1/n$.
The offspring is inserted even if it equals an existing individual, before a worst individual is
deleted. If `avoidReplications` is `true`, an offspring of a mutation-only iteration that equals
its parent is discarded instead.
Each `←` draws a sample from the distribution on its right. -/
def step {n : ℕ} (fitness : BitString n → ℝ) {μ : ℕ+} (p_c : ℝ) (avoidReplications : Bool)
    (P : Population n μ) : PMF (Population n μ) := do
  let useCrossover ← coin p_c
  -- `y` is the uniform crossover of two parents (if branch) or a single parent (else branch).
  let y ← if useCrossover then do
      let (u, v) ← PMF.uniformOfFintype (Fin μ × Fin μ)
      let crossMask ← PMF.uniformOfFintype (BitString n)
      pure (crossover (P u) (P v) crossMask)
    else do
      let u ← PMF.uniformOfFintype (Fin μ)
      pure (P u)
  let flipMask ← independentBits n (1 / (n : ℝ))
  let z := mutate y flipMask
  -- Avoidance of replications: discard a mutation-only offspring equal to its parent y.
  if avoidReplications ∧ ¬useCrossover ∧ z = y then
    pure P
  else
    -- `Q` lists the μ + 1 individuals: the population `P`, followed by the offspring `z`.
    let Q := Fin.lastCases z P
    let d ← deletionIndex fitness Q
    -- Deleting an old individual puts z into its slot; deleting the offspring (the last
    -- individual in `Q`) leaves P unchanged.
    pure (if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P)

end
end Lax637351.Algorithm
