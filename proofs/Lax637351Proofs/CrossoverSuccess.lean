import Lax637351Proofs.PairStep

namespace Lax637351Proofs.CrossoverSuccess

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma fair_bits_uniform (n : ℕ) :
    independentBits n (1 / 2) = PMF.uniformOfFintype (BitString n) := by
  have hp : (0 : ℝ) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ 1 := by norm_num
  apply PMF.ext
  intro x
  simp only [independentBits, PMF.ofFintype_apply, PMF.uniformOfFintype_apply]
  have hc (b : Bool) : coin (1 / 2) b = (2 : ℝ≥0∞)⁻¹ := by
    cases b <;> simp only [coin_true hp, coin_false hp]
    · rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    · rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
  simp_rw [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun,
    Nat.cast_pow, ENNReal.inv_pow]
  norm_num

lemma mean_independent_all (n : ℕ) (p : ℝ) (G : Fin n → Fin 2 → Prop) :
    mean (independentBits n p) (fun m ↦ indicator (∀ j, G j (m j))) =
      ∏ j, ∑ b : Fin 2, (coin p (b = 1)).toReal * indicator (G j b) := by
  let v (j : Fin n) (b : Fin 2) := (coin p (b = 1)).toReal * indicator (G j b)
  have hprod (m : BitString n) : (∏ j, v j (m j)) =
      (independentBits n p m).toReal * indicator (∀ j, G j (m j)) := by
    simp only [v, Finset.prod_mul_distrib, independentBits, PMF.ofFintype_apply, ENNReal.toReal_prod]
    congr 1
    by_cases h : ∀ j, G j (m j)
    · simp [indicator, h]
    · obtain ⟨j, hj⟩ := not_forall.mp h
      rw [indicator, if_neg (fun h ↦ hj (h j))]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [indicator, hj])
  unfold mean
  simp_rw [← hprod]
  exact (Fintype.prod_sum v).symm

lemma crossover_disjoint_probability (x y : BitString n)
    (hdis : Disjoint (zeros x) (zeros y)) :
    mean (PMF.uniformOfFintype (BitString n))
      (fun m ↦ indicator (crossover x y m = optimum n)) =
        (1 / 2 : ℝ) ^ ((zeros x).card + (zeros y).card) := by
  rw [← fair_bits_uniform]
  let G (j : Fin n) (b : Fin 2) : Prop := (if b = 1 then x j else y j) = 1
  have hG (m : BitString n) : crossover x y m = optimum n ↔ ∀ j, G j (m j) :=
    ⟨congrFun, funext⟩
  simp_rw [hG, mean_independent_all]
  have hp : (0 : ℝ) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ 1 := by norm_num
  have hsum (j : Fin n) : (∑ b : Fin 2, (coin (1 / 2) (b = 1)).toReal * indicator (G j b)) =
      if j ∈ zeros x ∪ zeros y then 1 / 2 else 1 := by
    by_cases hx : x j = 0
    · have hy : y j ≠ 0 := fun h ↦ Finset.disjoint_left.mp hdis (by simpa using hx) (by simpa using h)
      have hy' := bit_eq_one_of_ne_zero _ hy
      rw [Fin.sum_univ_two]
      norm_num [G, hx, hy', indicator, coin_true hp, coin_false hp]
    · have hx' := bit_eq_one_of_ne_zero _ hx
      by_cases hy : y j = 0
      · rw [Fin.sum_univ_two]
        norm_num [G, hx', hy, indicator, coin_true hp, coin_false hp]
      · have hy' := bit_eq_one_of_ne_zero _ hy
        rw [Fin.sum_univ_two]
        norm_num [G, hx', hy', indicator, coin_true hp, coin_false hp]
  rw [Finset.prod_congr rfl (fun j _ ↦ hsum j), ← Finset.prod_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
    Finset.card_union_of_disjoint hdis]

def success (P : Population n μ) : ℝ := indicator (¬ missing P)

lemma success_nonneg (P : Population n μ) : 0 ≤ success P := indic_nonneg _

lemma success_mean_of_success (hk : 0 < k) (p : ℝ) (avoid : Bool)
    (P : Population n μ) (hP : ¬ missing P) :
    mean (step (jump k) p avoid P) success = 1 := by
  apply mean_supported_const
  intro Q hQ
  simp [success, indicator, step_preserves_optimum hk p avoid hP hQ]

lemma selection_success (hk : 0 < k) (avoid : Bool) (P : Population n μ) (hP : missing P)
    (y : BitString n) :
    mean (select (jump k) avoid true P y (optimum n)) success = 1 := by
  simp only [select, not_true_eq_false, false_and, and_false, if_false]
  apply mean_supported_const
  intro Q hQ
  obtain ⟨d, rfl, _⟩ := insert_strict_improvement (jump k) P _
    (0 : Fin μ) (jump_lt_optimum hk _ (hP 0)) hQ
  have hn : ¬ missing (Function.update P d (optimum n)) :=
    fun hm ↦ hm d (Function.update_self d (optimum n) P)
  simp [success, indicator, hn]

lemma success_on_pair (hk : 0 < k) (hn : 2 ≤ n) (avoid : Bool)
    (P : Population n μ) (hP : missing P) (hpl : plateau (k := k) P)
    (i j : Fin μ) (hij : Disjoint (zeros (P i)) (zeros (P j))) :
    ((1 / 2 : ℝ) ^ (k + k) / 8) ≤
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
        mean (independentBits n (1 / (n : ℝ))) (fun flip ↦
          mean (select (jump k) avoid true P (crossover (P i) (P j) m)
            (mutate (crossover (P i) (P j) m) flip)) success)) := by
  have hprob := crossover_disjoint_probability (P i) (P j) hij
  rw [hpl i, hpl j] at hprob
  rw [← hprob, div_eq_inv_mul, ← mean_mul]
  apply mean_mono
  intro m
  by_cases hm : crossover (P i) (P j) m = optimum n
  · simp only [indicator, if_pos hm, mul_one]
    have hg := mean_single_lower (independentBits n (1 / (n : ℝ)))
      (fun flip ↦ mean (select (jump k) avoid true P (crossover (P i) (P j) m)
        (mutate (crossover (P i) (P j) m) flip)) success)
      (fun _ ↦ mean_nonneg _ success_nonneg) (mask ∅)
    have hmut (x : BitString n) : mutate x (mask ∅) = x := by
      funext j
      simp [mutate, mask]
    rw [hmut, hm, selection_success hk avoid P hP, mul_one] at hg
    have hzero : (1 / 8 : ℝ) ≤ (independentBits n (1 / (n : ℝ)) (mask ∅)).toReal := by
      simpa using weight_lower hn (∅ : Finset (Fin n))
    rw [hm, ← one_div]
    exact hzero.trans hg
  · simp only [indicator, if_neg hm, mul_zero]
    exact mean_nonneg _ (fun _ ↦ mean_nonneg _ success_nonneg)

end
end Lax637351Proofs.CrossoverSuccess
