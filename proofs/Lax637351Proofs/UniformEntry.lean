import Lax637351Proofs.Ordinary

namespace Lax637351Proofs.UniformEntry

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.Ordinary
open Filter
open scoped Classical ENNReal

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]

lemma uniform_fun_weight (x : ι → A) :
    (PMF.uniformOfFintype (ι → A) x).toReal =
      ∏ i, (PMF.uniformOfFintype A (x i)).toReal := by
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma uniform_product (f : A → ℝ) :
    mean (PMF.uniformOfFintype (ι → A)) (fun x ↦ ∏ i, f (x i)) =
      (mean (PMF.uniformOfFintype A) f) ^ Fintype.card ι := by
  simp only [mean, uniform_fun_weight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : ι) (a : A) ↦ (PMF.uniformOfFintype A a).toReal * f a)]
  simp

lemma uniform_coordinate (j : ι) (f : A → ℝ) :
    mean (PMF.uniformOfFintype (ι → A)) (fun x ↦ f (x j)) =
      mean (PMF.uniformOfFintype A) f := by
  let w (a : A) := (PMF.uniformOfFintype A a).toReal
  let v (i : ι) (a : A) := w a * if i = j then f a else 1
  have hp (x : ι → A) : (∏ i, v i (x i)) = (∏ i, w (x i)) * f (x j) := by
    simp only [v, Finset.prod_mul_distrib]
    congr 1
    simp
  simp only [mean, uniform_fun_weight]
  have he : (∑ x : ι → A, (∏ i, (PMF.uniformOfFintype A (x i)).toReal) * f (x j)) =
      ∑ x : ι → A, ∏ i, v i (x i) := Finset.sum_congr rfl fun x _ ↦ (hp x).symm
  rw [he, ← Fintype.prod_sum]
  have hh (i : ι) : ∑ a, v i a =
      if i = j then ∑ a, w a * f a else 1 := by
    by_cases hi : i = j <;> simp [v, hi, w]
  simp [hh, w, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma zero_moment (n : ℕ) :
    mean (PMF.uniformOfFintype (BitString n)) (fun x ↦ (1 / 2 : ℝ) ^ (zeros x).card) =
      (3 / 4 : ℝ) ^ n := by
  have hf (x : BitString n) : (1 / 2 : ℝ) ^ (zeros x).card =
      ∏ j, if x j = 0 then (1 / 2 : ℝ) else 1 := by
    rw [← Finset.prod_filter, Finset.prod_const]
    rfl
  simp_rw [hf]
  rw [uniform_product (ι := Fin n) (A := Fin 2) (fun b ↦ if b = 0 then (1 / 2 : ℝ) else 1)]
  norm_num [mean_uniform, Fin.sum_univ_two]

lemma too_few_zeros (n k : ℕ) :
    mean (PMF.uniformOfFintype (BitString n)) (fun x ↦ indicator ((zeros x).card < k)) ≤
      (2 : ℝ) ^ k * (3 / 4 : ℝ) ^ n := by
  rw [← zero_moment n, ← mean_mul]
  apply mean_mono
  intro x
  by_cases h : (zeros x).card < k
  · have hh : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (zeros x).card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h.le
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (2 : ℝ) ^ k)
    rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow] at hm
    simpa only [indicator, if_pos h] using hm
  · simp [indicator, h]

lemma initial_failure (n k : ℕ) (μ : ℕ+) :
    mean (PMF.uniformOfFintype (Population n μ)) (fun P ↦ indicator (¬ ordinary k P)) ≤
      ((μ : ℕ) : ℝ) * ((2 : ℝ) ^ k * (3 / 4 : ℝ) ^ n) := by
  let ν := PMF.uniformOfFintype (Population n μ)
  have hpt (P : Population n μ) : indicator (¬ ordinary k P) ≤
      ∑ i : Fin μ, indicator ((zeros (P i)).card < k) := by
    by_cases h : ordinary k P
    · rw [indicator, if_neg (not_not_intro h)]
      exact Finset.sum_nonneg (fun i _ ↦ indic_nonneg _)
    · obtain ⟨i, hi⟩ : ∃ i, (zeros (P i)).card < k := by
        simpa [ordinary, not_forall, not_le] using h
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin μ)))
        (f := fun i ↦ indicator ((zeros (P i)).card < k)) (fun i _ ↦ indic_nonneg _) (Finset.mem_univ i)
      simpa only [indicator, if_pos h, if_pos hi] using hh
  apply (mean_mono ν hpt).trans
  rw [mean_sum]
  calc
    _ ≤ ∑ _i : Fin μ, (2 : ℝ) ^ k * (3 / 4 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro i _
      change mean (PMF.uniformOfFintype (Fin μ → BitString n))
        (fun x ↦ indicator ((zeros (x i)).card < k)) ≤ _
      rw [uniform_coordinate (A := BitString n) i (fun x ↦ indicator ((zeros x).card < k))]
      exact too_few_zeros n k
    _ = _ := by simp [nsmul_eq_mul]

lemma initial_ordinary_eventually (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : ℕ+, (μ : ℕ) ≤ n →
      (1 / 2 : ℝ) ≤ mean (PMF.uniformOfFintype (Population n μ))
        (fun P ↦ indicator (ordinary k P)) := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * ((2 : ℝ) ^ k * (3 / 4 : ℝ) ^ n)) atTop (nhds 0) := by
    have hh := tendsto_pow_const_mul_const_pow_of_lt_one (k := 1) (r := (3 / 4 : ℝ))
      (by norm_num) (by norm_num)
    have ht := (tendsto_const_nhds (x := (2 : ℝ) ^ k)).mul hh
    simpa [pow_one, mul_left_comm, mul_comm, mul_assoc] using ht
  have he := (tendsto_order.mp ht).2 (1 / 2 : ℝ) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn μ hμ ↦ ?_⟩
  let ν := PMF.uniformOfFintype (Population n μ)
  have hm := initial_failure n k μ
  have he' := mul_le_mul_of_nonneg_right (show ((μ : ℕ) : ℝ) ≤ n by exact_mod_cast hμ)
    (show 0 ≤ (2 : ℝ) ^ k * (3 / 4 : ℝ) ^ n by positivity)
  have hall : (fun P : Population n μ ↦ indicator (ordinary k P)) =
      (fun P ↦ 1 - indicator (¬ ordinary k P)) := by
    funext P
    by_cases h : ordinary k P <;> simp [indicator, h]
  rw [hall, mean_sub, mean_const]
  linarith [hN n hn]

end
end Lax637351Proofs.UniformEntry
