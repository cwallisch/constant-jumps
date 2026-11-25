import Lax637351Proofs.OffspringEstimates.Algorithm
import Mathlib.Tactic.NormNum

namespace Lax637351Proofs.OffspringEstimates.Sampling

open Lax637351Proofs.OffspringEstimates.Algorithm
open scoped ENNReal Classical BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

def parents {n : ℕ} {μ : ℕ+} (p_c : ℝ) (P : Population n μ) : PMF (BitString n) := do
  let b ← coin p_c
  if b = 1 then do
    let (u, v) ← PMF.uniformOfFintype (Fin (μ : ℕ) × Fin (μ : ℕ))
    let mask ← PMF.uniformOfFintype (BitString n)
    pure (crossover (P u) (P v) mask)
  else do
    let u ← PMF.uniformOfFintype (Fin (μ : ℕ))
    pure (P u)

def offspring {n : ℕ} {μ : ℕ+} (p_c : ℝ) (P : Population n μ) : PMF (BitString n) := do
  let y ← parents p_c P
  let mask ← independentBits n (1 / (n : ℝ))
  pure (mutate y mask)

def insert {n : ℕ} {μ : ℕ+} (fitness : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) : PMF (Population n μ) := do
  let d ← deletionIndex fitness (Fin.lastCases z P)
  pure (if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P)

@[simp] lemma coin_one (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : coin p 1 = ENNReal.ofReal p := by
  simp [coin, hp]

@[simp] lemma coin_zero (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    coin p 0 = ENNReal.ofReal (1 - p) := by
  simp [coin, hp]

lemma independentBits_apply (n : ℕ) (p : ℝ) (mask : BitString n) :
    independentBits n p mask = ∏ j, coin p (mask j) := rfl

lemma uniform_bits_eq (n : ℕ) :
    PMF.uniformOfFintype (BitString n) = independentBits n (1 / 2) := by
  ext mask
  rw [PMF.uniformOfFintype_apply, independentBits_apply]
  have hc : ∀ j : Fin n, coin (1 / 2) (mask j) = (2 : ℝ≥0∞)⁻¹ := by
    intro j
    have h := (mask j).isLt
    have hcases : mask j = 0 ∨ mask j = 1 := by omega
    rcases hcases with h | h <;> rw [h] <;> norm_num [coin, ENNReal.ofReal_div_of_pos]
  simp only [Fintype.card_fun, Fintype.card_fin, hc, Finset.prod_const, Finset.card_univ,
    ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat]

lemma product_indicator {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → Fin 2)
    (target mask : BitString n) :
    (∏ j, coin p (mask j)) * (if (fun j ↦ f j (mask j)) = target then 1 else 0) =
      ∏ j, coin p (mask j) * (if f j (mask j) = target j then 1 else 0) := by
  by_cases h : (fun j ↦ f j (mask j)) = target
  · have hj : ∀ j, f j (mask j) = target j := congrFun h
    simp only [if_pos h, if_pos (hj _), mul_one]
  · have hj : ∃ j, f j (mask j) ≠ target j := by
      simpa only [funext_iff, not_forall] using h
    obtain ⟨j, hj⟩ := hj
    rw [if_neg h, mul_zero]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj, mul_zero])

lemma independent_transform_apply {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → Fin 2)
    (target : BitString n) :
    ((independentBits n p).bind fun mask ↦ PMF.pure (fun j ↦ f j (mask j))) target =
      ∏ j, ∑ b : Fin 2, coin p b * (if f j b = target j then 1 else 0) := by
  rw [PMF.bind_apply, tsum_fintype, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independentBits_apply, PMF.pure_apply]
  have h := product_indicator p f target mask
  by_cases heq : (fun j ↦ f j (mask j)) = target
  · have heq' := heq.symm
    simpa only [if_pos heq, if_pos heq'] using h
  · have heq' : target ≠ (fun j ↦ f j (mask j)) := Ne.symm heq
    simpa only [if_neg heq, if_neg heq'] using h

lemma independent_weighted_sum {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → ℝ≥0∞) :
    (∑ mask : BitString n, independentBits n p mask * ∏ j, f j (mask j)) =
      ∏ j, ∑ b : Fin 2, coin p b * f j b := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independentBits_apply, Finset.prod_mul_distrib]

lemma independent_pair_transform_apply {n : ℕ} (p q : ℝ)
    (f : Fin n → Fin 2 → Fin 2 → Fin 2) (target : BitString n) :
    ((independentBits n p).bind fun mask ↦ (independentBits n q).bind fun mask' ↦
      PMF.pure (fun j ↦ f j (mask j) (mask' j))) target =
      ∏ j, ∑ b : Fin 2, coin p b *
        (∑ b' : Fin 2, coin q b' * (if f j b b' = target j then 1 else 0)) := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [← independent_weighted_sum p (fun j b ↦
    ∑ b' : Fin 2, coin q b' * (if f j b b' = target j then 1 else 0))]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independent_transform_apply q (fun j b' ↦ f j (mask j) b') target]

lemma ones_eq_count {n : ℕ} (x : BitString n) :
    ones x = (Finset.univ.filter (fun j ↦ x j = 1)).card := by
  rw [ones, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  have hc : x j = 0 ∨ x j = 1 := by have h := (x j).isLt; omega
  rcases hc with h | h <;> simp [h]

lemma zeros_eq_count {n : ℕ} (x : BitString n) :
    (Finset.univ.filter (fun j ↦ x j = 0)).card = n - ones x := by
  have hpartition : (Finset.univ.filter (fun j ↦ x j = 0)).card +
      (Finset.univ.filter (fun j ↦ x j = 1)).card = n := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      ∑ j : Fin n, ((if x j = 0 then 1 else 0) + (if x j = 1 then 1 else 0)) =
          ∑ _ : Fin n, 1 := by
        apply Finset.sum_congr rfl
        intro j _
        have hc : x j = 0 ∨ x j = 1 := by have h := (x j).isLt; omega
        rcases hc with h | h <;> simp [h]
      _ = n := by simp
  rw [← ones_eq_count] at hpartition
  omega

def zeros {n : ℕ} (x : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ x j = 0)

@[simp] lemma mem_zeros {n : ℕ} (x : BitString n) (j : Fin n) :
    j ∈ zeros x ↔ x j = 0 := by simp [zeros]

@[simp] lemma card_zeros {n : ℕ} (x : BitString n) : (zeros x).card = n - ones x :=
  zeros_eq_count x

lemma no_mutation_probability (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    independentBits n p (fun _ ↦ 0) = ENNReal.ofReal (1 - p) ^ n := by
  simp [independentBits_apply, coin_zero p hp]

lemma mutate_zero {n : ℕ} (x : BitString n) : mutate x (fun _ ↦ 0) = x := by
  funext j
  simp [mutate]

end
end Lax637351Proofs.OffspringEstimates.Sampling
