import Lax637351.Algorithm

namespace Lax637351Proofs.OffspringEstimates.Algorithm

open scoped ENNReal Classical BigOperators

noncomputable section

export Lax637351.Algorithm (BitString Population ones jump optimum crossover mutate deletionIndex)

def coin (p : ℝ) : PMF (Fin 2) :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    PMF.ofFintype (fun b : Fin 2 ↦ ENNReal.ofReal (if b = 1 then p else 1 - p))
      -- Lean checks this proof that the probabilities sum to one; readers can skip it.
      (by simp_all [Fin.sum_univ_two, ← ENNReal.ofReal_add])
  else PMF.pure 0

/-- Independent Bernoulli bits, each equal to one with probability $p$: a string $x$ has
probability $\prod_j \Pr[\text{coin}=x_j]$, which is $p^{|x|_1}(1-p)^{n-|x|_1}$ for
$0\le p\le1$. Here `coin p b` is the probability that the coin shows the bit `b`. -/
def independentBits (n : ℕ) (p : ℝ) : PMF (BitString n) :=
  PMF.ofFintype (fun x ↦ ∏ j, coin p (x j))
    -- Lean checks this proof that the probabilities sum to one; readers can skip it.
    (by
      have h := (coin p).tsum_coe
      rw [tsum_fintype] at h
      rw [← Fintype.prod_sum]
      simp [h])

def step {n : ℕ} (fitness : BitString n → ℝ) {μ : ℕ+} (p_c : ℝ) (P : Population n μ) :
    PMF (Population n μ) := do
  let useCrossover ← coin p_c
  -- `z'` is the uniform crossover of the parents `P u` and `P v`, or the parent `P u` itself.
  let z' ← if useCrossover = 1 then do
      let (u, v) ← PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))
      let crossMask ← PMF.uniformOfFintype (BitString n)
      pure (crossover (P u) (P v) crossMask)
    else do
      let u ← PMF.uniformOfFintype (Fin (μ : ℕ))
      pure (P u)
  let flipMask ← independentBits n (1 / (n : ℝ))
  let z := mutate z' flipMask
  -- `Q` lists the μ + 1 entries: the population `P`, followed by the offspring `z`.
  let Q := Fin.lastCases z P
  let d ← deletionIndex fitness Q
  -- Deleting an old entry puts z into its slot; deleting the offspring (the last entry of
  -- `Q`) leaves P unchanged.
  pure (if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P)


end

end Lax637351Proofs.OffspringEstimates.Algorithm
