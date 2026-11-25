import Lax637351Proofs.ArrivalCross
import Lax637351Proofs.ArrivalTime
import Lax637351Proofs.RankPotential

namespace Lax637351Proofs.ArrivalProgress

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.Mutation Lax637351Proofs.ArrivalMutation Lax637351Proofs.ArrivalCross
open Lax637351Proofs.ArrivalTime
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def fitterCount (k v : ℕ) (P : Population n μ) : ℕ :=
  (Finset.univ.filter (fun i ↦ v < fitnessLevel k (P i))).card

def effective (ar : Bool) (p : ℝ) : ℝ := if ar then p else 1

def progressRate (n k : ℕ) (μ : ℕ+) (p : ℝ) (ar : Bool) (v j : ℕ) : ℝ :=
  if v < k then 1 / 128
  else ordinaryChance k * (((n - (v - k) : ℕ) : ℝ) / n + effective ar p * j / (μ : ℕ))

lemma fitter_mono (P Q : Population n μ) (h : ∀ i, fitnessLevel k (P i) ≤ fitnessLevel k (Q i)) (v : ℕ) :
    fitterCount k v P ≤ fitterCount k v Q := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le (h i)

lemma fitter_strict (P Q : Population n μ) (h : ∀ i, fitnessLevel k (P i) ≤ fitnessLevel k (Q i)) (v : ℕ)
    (i : Fin μ) (hi : fitnessLevel k (P i) ≤ v) (hj : v < fitnessLevel k (Q i)) :
    fitterCount k v P < fitterCount k v Q := by
  unfold fitterCount
  apply Finset.card_lt_card
  have hs : Finset.univ.filter (fun j ↦ v < fitnessLevel k (P j)) ⊆
      Finset.univ.filter (fun j ↦ v < fitnessLevel k (Q j)) := by
    intro j hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
    exact hj'.trans_le (h j)
  exact (Finset.ssubset_iff_of_subset hs).mpr ⟨i, by simpa using hj, by simp [not_lt.mpr hi]⟩

lemma mean_fitter (P : Population n μ) (v : ℕ) :
    mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ indicator (v < fitnessLevel k (P i))) =
      (fitterCount k v P : ℝ) / (μ : ℕ) := by
  rw [mean_uniform]
  simp only [Fintype.card_fin, fitterCount, Finset.card_filter, indicator, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v < fitnessLevel k (P i) <;> simp [h]

lemma select_progress (hkn : k ≤ n) (P : Population n μ) (u : Fin μ) (v : ℕ)
    (hu : fitnessLevel k (P u) = v) (ar cross : Bool) (y z : BitString n)
    (hn : ¬ (ar = true ∧ ¬ cross = true ∧ z = y)) :
    indicator (v < fitnessLevel k z) ≤
      mean (select (jump k) ar cross P y z) (fun Q ↦ indicator (fitterCount k v P < fitterCount k v Q)) := by
  by_cases hz : v < fitnessLevel k z
  · rw [indicator, if_pos hz, ← mean_const (select (jump k) ar cross P y z) 1]
    apply mean_mono_on_support
    intro Q hQ
    rw [select, if_neg hn] at hQ
    have hb : jump k (P u) < jump k z := by
      rw [← fitnessLevel_eq hkn, ← fitnessLevel_eq hkn, hu]
      exact_mod_cast hz
    obtain ⟨d, hD, hmin⟩ := insert_strict_improvement (jump k) P z u hb hQ
    have hd : fitnessLevel k (P d) ≤ v := by
      rw [← fitnessLevel_eq hkn, ← fitnessLevel_eq hkn, hu] at hmin
      exact_mod_cast hmin
    have hQd : fitnessLevel k (Q d) = fitnessLevel k z := by simp [hD]
    have hmon (i : Fin μ) : fitnessLevel k (P i) ≤ fitnessLevel k (Q i) := by
      have hh := insert_fitness_mono (jump k) P z hQ i
      rw [← fitnessLevel_eq hkn, ← fitnessLevel_eq hkn] at hh
      exact_mod_cast hh
    simp only [indicator, if_pos (fitter_strict P Q hmon v d hd (hQd.symm ▸ hz)), le_refl]
  · rw [indicator, if_neg hz]
    exact mean_nonneg _ (fun _ ↦ indic_nonneg _)

lemma branch_cross (P : Population n μ) (f : BitString n → ℝ) :
    mean (parents P true) f =
      mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        mean (PMF.uniformOfFintype (Fin μ)) (fun j ↦
          mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ f (crossover (P i) (P j) m)))) := by
  simp only [parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
  exact mean_uniform_pair (fun i j : Fin μ ↦
    mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ f (crossover (P i) (P j) m)))

lemma mutation_branch_base (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (P : Population n μ) (hP : missing P)
    (u j : Fin μ) (v : ℕ) (hu : fitnessLevel k (P u) = v) (hj : v ≤ fitnessLevel k (P j)) (hv : v < n)
    (ar : Bool) :
    ((n - v : ℕ) : ℝ) / (32 * n) ≤ mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      mean (select (jump k) ar false P (P j) (mutate (P j) m))
        (fun Q ↦ indicator (fitterCount k v P < fitterCount k v Q))) := by
  apply (mutation_progress hk hkn v hv (P j) (hP j) hj).trans
  apply mean_mono
  intro m
  by_cases hf : favorable (k := k) v (P j) m
  · rw [if_pos hf]
    exact (show (1 : ℝ) ≤ indicator (v < fitnessLevel k (mutate (P j) m)) by simp [indicator, hf.2]).trans
      (select_progress (by omega) P u v hu ar false _ _ (fun h ↦ hf.1 h.2.2))
  · rw [if_neg hf]
    exact mean_nonneg _ (fun _ ↦ indic_nonneg _)

lemma profile_valley {x : BitString n} {v : ℕ} (hx : x ≠ optimum n) (hv : v ≤ fitnessLevel k x) (hvk : v < k) :
    v ≤ (zeros x).card := by
  rw [fitnessLevel, if_neg hx] at hv
  split_ifs at hv <;> omega

lemma improves_count (hk : 2 ≤ k) (hn : 2 * k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (ar : Bool) (P : Population n μ) (hP : missing P) (u : Fin μ) (v : ℕ)
    (hu : fitnessLevel k (P u) = v) (hv : v < n) (hmin : ∀ j, v ≤ fitnessLevel k (P j)) :
    progressRate n k μ p ar v (fitterCount k v P) ≤
      mean (step (jump k) p ar P) (fun Q ↦ indicator (fitterCount k v P < fitterCount k v Q)) := by
  let f (Q : Population n μ) := indicator (fitterCount k v P < fitterCount k v Q)
  let branch (c : Bool) (y : BitString n) :=
    mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      mean (select (jump k) ar c P y (mutate y m)) f)
  let X := mean (parents P true) (branch true)
  let Y := mean (PMF.uniformOfFintype (Fin μ)) (fun j ↦ branch false (P j))
  change _ ≤ mean (step (jump k) p ar P) f
  rw [mean_step hp]
  change _ ≤ p * X + (1 - p) * Y
  have hl (y : BitString n) : mean (independentBits n (1 / (n : ℝ)))
      (fun m ↦ indicator (v < fitnessLevel k (mutate y m))) ≤ branch true y := by
    apply mean_mono
    intro m
    exact select_progress (by omega) P u v hu ar true _ _ (by simp)
  have hm := mean_uniform_lower _ _ (fun j ↦ mutation_branch_base hk hn P hP u j v hu (hmin j) hv ar)
  change _ ≤ Y at hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  by_cases hvk : v < k
  · rw [progressRate, if_pos hvk]
    have hY : 1 / 128 ≤ Y := by
      apply le_trans _ hm
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * n)).mpr
      rw [Nat.cast_sub (by omega : v ≤ n)]
      have hh : (2 : ℝ) * v ≤ n := by exact_mod_cast (show 2 * v ≤ n by omega)
      linarith
    have hX : 1 / 32 ≤ X := by
      unfold X
      rw [branch_cross]
      apply mean_uniform_lower
      intro i
      apply mean_uniform_lower
      intro j
      apply (pair_valley hk hn v hvk (P i) (P j)
        (profile_valley (hP i) (hmin i) hvk) (profile_valley (hP j) (hmin j) hvk)).trans
      exact mean_mono _ (fun m ↦ hl (crossover (P i) (P j) m))
    have h₁ := mul_le_mul_of_nonneg_left ((by norm_num : (1 / 128 : ℝ) ≤ 1 / 32).trans hX) hp.1
    have h₂ := mul_le_mul_of_nonneg_left hY hp'
    linarith only [h₁, h₂]
  · rw [progressRate, if_neg hvk]
    let z := n - (v - k)
    let q := (z : ℝ) / n
    let g (j : Fin μ) := indicator (v < fitnessLevel k (P j))
    let ξ := (fitterCount k v P : ℝ) / (μ : ℕ)
    let c := ordinaryChance k
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hξ : 0 ≤ ξ := by dsimp [ξ]; positivity
    have hg (j : Fin μ) : 0 ≤ g j := indic_nonneg _
    have hc : 0 ≤ c := (ordinaryChance_pos k).le
    have hc' : c ≤ 1 / 32 := ordinaryChance_le k
    have hX : c * (q + ξ) ≤ X := by
      unfold X
      rw [branch_cross]
      have ha (i : Fin μ) : c * (q + g i) ≤ mean (PMF.uniformOfFintype (Fin μ)) (fun j ↦
          mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ branch true (crossover (P i) (P j) m))) := by
        apply mean_uniform_lower
        intro j
        exact (pair_ordinary hk hn v (by omega) hv (P i) (P j) (hP i) (hP j) (hmin i) (hmin j)).trans
          (mean_mono _ (fun m ↦ hl _))
      have hb := mean_mono (PMF.uniformOfFintype (Fin μ)) ha
      rw [mean_mul, mean_add, mean_const, show mean (PMF.uniformOfFintype (Fin μ)) g = ξ from mean_fitter P v] at hb
      exact hb
    cases ar
    · have hY : c * (q + ξ) ≤ Y := by
        have hbasic (j : Fin μ) : q / 8 ≤ branch false (P j) := by
          have hh := mutation_ordinary hk hn (P j) v z (by omega) hv rfl (profile_floor (hP j) (by omega) (hmin j))
          rw [show q / 8 = (z : ℝ) / (8 * n) by dsimp [q]; ring]
          exact hh.trans (mean_mono _ (fun m ↦ select_progress (by omega) P u v hu false false _ _ (by simp)))
        have hgood (j : Fin μ) : g j / 8 ≤ branch false (P j) := by
          by_cases h : v < fitnessLevel k (P j)
          · rw [show g j = 1 from if_pos h]
            exact (retain_lower (by omega : 2 ≤ n) (P j) (fun y ↦ v < fitnessLevel k y) h).trans
              (mean_mono _ (fun m ↦ select_progress (by omega) P u v hu false false _ _ (by simp)))
          · rw [show g j = 0 from if_neg h, zero_div]
            exact mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ indic_nonneg _))
        have hlocal (j : Fin μ) : c * (q + g j) ≤ branch false (P j) := by
          have hscale := mul_le_mul_of_nonneg_right hc' (add_nonneg hq (hg j))
          linarith [hbasic j, hgood j]
        have hh := mean_mono (PMF.uniformOfFintype (Fin μ)) hlocal
        rw [mean_mul, mean_add, mean_const, show mean (PMF.uniformOfFintype (Fin μ)) g = ξ from mean_fitter P v] at hh
        exact hh
      have h₁ := mul_le_mul_of_nonneg_left hX hp.1
      have h₂ := mul_le_mul_of_nonneg_left hY hp'
      change c * (q + 1 * (fitterCount k v P : ℝ) / (μ : ℕ)) ≤ _
      rw [one_mul]
      change c * (q + ξ) ≤ _
      linarith only [h₁, h₂]
    · have hY : c * q ≤ Y := by
        apply le_trans _ hm
        have hnr : (1 : ℝ) ≤ ((n - v : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - v by omega)
        have hzEq : (z : ℝ) = ((n - v : ℕ) : ℝ) + k := by
          exact_mod_cast (show z = n - v + k by dsimp [z]; omega)
        have hprod : (z : ℝ) ≤ ((k : ℝ) + 1) * ((n - v : ℕ) : ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hnr (show 0 ≤ (k : ℝ) by positivity)
          rw [hzEq]
          nlinarith only [hh]
        have htwo (j : ℕ) : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
          induction j with
          | zero => norm_num
          | succ j ih =>
            rw [pow_succ]
            push_cast
            have hj : (0 : ℝ) ≤ j := by positivity
            linarith
        have hpow : (k : ℝ) + 1 ≤ 2 ^ (2 * k + 1) := by
          exact (htwo k).trans (pow_le_pow_right₀ (by norm_num) (by omega : k ≤ 2 * k + 1))
        have hh := hprod.trans (mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ ((n - v : ℕ) : ℝ)))
        dsimp [c, ordinaryChance, q]
        rw [div_mul_div_comm, one_div_pow]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * n)).mpr
        field_simp
        linear_combination hh
      have h₁ := mul_le_mul_of_nonneg_left hX hp.1
      have h₂ := mul_le_mul_of_nonneg_left hY hp'
      change c * (q + p * (fitterCount k v P : ℝ) / (μ : ℕ)) ≤ _
      rw [mul_div_assoc]
      change c * (q + p * ξ) ≤ _
      linarith only [h₁, h₂]

end
end Lax637351Proofs.ArrivalProgress
