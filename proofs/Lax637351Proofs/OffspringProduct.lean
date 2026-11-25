import Lax637351Proofs.CrossoverSuccess
import Lax637351Proofs.MarkedStep

namespace Lax637351Proofs.OffspringProduct

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.CrossoverSuccess Lax637351Proofs.PairStep Lax637351Proofs.MarkedStep
open scoped BigOperators Classical ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma independentBits_apply {n : ℕ} (p : ℝ) (mask : BitString n) :
    independentBits n p mask = ∏ j, coin p (mask j = 1) := rfl

lemma product_indicator {n : ℕ} (p : ℝ) (f : Fin n → Fin 2 → Fin 2)
    (target mask : BitString n) :
    (∏ j, coin p ((mask j) = 1)) * (if (fun j ↦ f j (mask j)) = target then 1 else 0) =
      ∏ j, coin p ((mask j) = 1) * (if f j (mask j) = target j then 1 else 0) := by
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
      ∏ j, ∑ b : Fin 2, coin p (b = 1) * (if f j b = target j then 1 else 0) := by
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
      ∏ j, ∑ b : Fin 2, coin p (b = 1) * f j b := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independentBits_apply, Finset.prod_mul_distrib]

lemma independent_pair_transform_apply {n : ℕ} (p q : ℝ)
    (f : Fin n → Fin 2 → Fin 2 → Fin 2) (target : BitString n) :
    ((independentBits n p).bind fun mask ↦ (independentBits n q).bind fun mask' ↦
      PMF.pure (fun j ↦ f j (mask j) (mask' j))) target =
      ∏ j, ∑ b : Fin 2, coin p (b = 1) *
        (∑ b' : Fin 2, coin q (b' = 1) * (if f j b b' = target j then 1 else 0)) := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [← independent_weighted_sum p (fun j b ↦
    ∑ b' : Fin 2, coin q (b' = 1) * (if f j b b' = target j then 1 else 0))]
  apply Finset.sum_congr rfl
  intro mask _
  rw [independent_transform_apply q (fun j b' ↦ f j (mask j) b') target]

def pairMutation {n : ℕ} (x y : BitString n) (p : ℝ) : PMF (BitString n) :=
  (PMF.uniformOfFintype (BitString n)).bind fun mask ↦
    (independentBits n p).bind fun mask' ↦ PMF.pure (mutate (crossover x y mask) mask')

lemma pairMutation_self {n : ℕ} (x : BitString n) (p : ℝ) :
    pairMutation x x p = (independentBits n p).map (mutate x) := by
  have hc (mask : BitString n) : crossover x x mask = x := by
    funext j
    simp [Lax637351.Algorithm.crossover]
  simp only [pairMutation, hc, PMF.bind_const]
  rfl

def siteProbability (x y target : Fin 2) (p : ℝ) : ℝ≥0∞ :=
  if x = y then if target = x then ENNReal.ofReal (1 - p) else ENNReal.ofReal p
  else (2 : ℝ≥0∞)⁻¹

lemma site_probability_sum (x y target : Fin 2) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∑ b : Fin 2, coin (1 / 2) (b = 1) *
      (∑ b' : Fin 2, coin p (b' = 1) *
        (if (if b' = 1 then 1 - (if b = 1 then x else y) else (if b = 1 then x else y)) =
          target then 1 else 0))) = siteProbability x y target p := by
  have hsum : ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
    ring_nf
    norm_num
  have hfair (b : Bool) : coin (1 / 2) b = (2 : ℝ≥0∞)⁻¹ := by
    have hhalf : (0 : ℝ) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ 1 := by norm_num
    cases b <;> simp only [coin_false hhalf, coin_true hhalf]
    · rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    · rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
  simp only [Fin.sum_univ_two, hfair]
  fin_cases x <;> fin_cases y <;> fin_cases target <;>
    norm_num [siteProbability, coin_false hp, coin_true hp] <;>
    first
    | rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    | rw [← mul_add, hsum, mul_one]
    | rw [← mul_add, add_comm (ENNReal.ofReal p), hsum, mul_one]

lemma pairMutation_apply {n : ℕ} (x y target : BitString n) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    pairMutation x y p target = ∏ j, siteProbability (x j) (y j) (target j) p := by
  rw [pairMutation, ← fair_bits_uniform]
  change ((independentBits n (1 / 2)).bind fun mask ↦
    (independentBits n p).bind fun mask' ↦ PMF.pure (fun j ↦
      if mask' j = 1 then 1 - (if mask j = 1 then x j else y j)
      else (if mask j = 1 then x j else y j))) target = _
  rw [independent_pair_transform_apply (1 / 2) p
    (fun j b b' ↦ if b' = 1 then 1 - (if b = 1 then x j else y j)
      else (if b = 1 then x j else y j)) target]
  apply Finset.prod_congr rfl
  intro j _
  exact site_probability_sum (x j) (y j) (target j) p hp


lemma all_hit_probability {n : ℕ} {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (S : Finset (Fin n)) :
    mean (independentBits n p) (fun m ↦ indicator (∀ j ∈ S, m j = 1)) = p ^ S.card := by
  let G (j : Fin n) (b : Fin 2) : Prop := j ∈ S → b = 1
  change mean (independentBits n p) (fun m ↦ indicator (∀ j, G j (m j))) = _
  rw [mean_independent_all]
  have hj (j : Fin n) : (∑ b : Fin 2, (coin p (b = 1)).toReal * indicator (G j b)) =
      if j ∈ S then p else 1 := by
    rw [Fin.sum_univ_two]
    by_cases h : j ∈ S
    · simp [G, indicator, h, coin_true hp, ENNReal.toReal_ofReal hp.1]
    · simp [G, indicator, h, coin_true hp, coin_false hp, ENNReal.toReal_ofReal hp.1,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
  rw [Finset.prod_congr rfl (fun j _ ↦ hj j), ← Finset.prod_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]

lemma siteProbability_le_from_zero (a b : Fin 2) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1 / 2)
    (ha : a = 0) : siteProbability a b 1 p ≤ siteProbability a b 0 p := by
  subst a
  by_cases hb : b = 0
  · subst b
    simp only [siteProbability, if_true, one_ne_zero, if_false]
    exact ENNReal.ofReal_le_ofReal (by linarith [hp.2])
  · simp [siteProbability, Ne.symm hb]

lemma pairMutation_plateau_ge_optimum {n k : ℕ} (x y : BitString n)
    (hx : k ≤ (zeros x).card) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    (pairMutation x y p) (optimum n) ≤
      (pairMutation x y p).toOuterMeasure {z | (zeros z).card = k} := by
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hx
  let z : BitString n := fun j ↦ if j ∈ S then 0 else 1
  have hz : zeros z = S := by
    ext j
    by_cases hj : j ∈ S <;> simp [z, hj]
  have hmem : z ∈ {z' : BitString n | (zeros z').card = k} := by simp [hz, hcard]
  apply le_trans _ (((pairMutation x y p).toOuterMeasure_apply_singleton z).symm.le.trans
    ((pairMutation x y p).toOuterMeasure.mono (Set.singleton_subset_iff.mpr hmem)))
  have hp' : 0 ≤ p ∧ p ≤ 1 := ⟨hp.1, by linarith [hp.2]⟩
  rw [pairMutation_apply _ _ _ _ hp', pairMutation_apply _ _ _ _ hp']
  apply Finset.prod_le_prod'
  intro j _
  by_cases hj : j ∈ S
  · simpa only [z, if_pos hj, optimum] using
      siteProbability_le_from_zero (x j) (y j) hp ((mem_zeros x j).mp (hsub hj))
  · simp [z, hj, optimum]

lemma pairMutation_optimum_lower {n : ℕ} (x y : BitString n) (hn : 2 ≤ n) :
    ENNReal.ofReal ((1 / (n : ℝ)) ^ n) ≤ (pairMutation x y (1 / n)) (optimum n) := by
  have hp := rate_valid hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn'
  have heq : ENNReal.ofReal ((1 / (n : ℝ)) ^ n) =
      ∏ _j : Fin n, ENNReal.ofReal (1 / (n : ℝ)) := by
    rw [ENNReal.ofReal_pow hp.1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pairMutation_apply _ _ _ _ hp, heq]
  apply Finset.prod_le_prod'
  intro j _
  by_cases h : x j = y j
  · by_cases h' : optimum n j = x j
    · simp only [siteProbability, if_pos h, if_pos h']
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [siteProbability, if_pos h, if_neg h']
  · simp only [siteProbability, if_neg h]
    apply (ENNReal.ofReal_le_ofReal hh).trans_eq
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

end
end Lax637351Proofs.OffspringProduct
