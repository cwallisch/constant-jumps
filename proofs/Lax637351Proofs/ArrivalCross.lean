import Lax637351Proofs.CrossBand

namespace Lax637351Proofs.ArrivalCross

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.Mutation Lax637351Proofs.CrossBand Lax637351Proofs.ArrivalMutation
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def ordinaryChance (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (2 * k + 1) / 32

lemma ordinaryChance_pos (k : ℕ) : 0 < ordinaryChance k := by
  unfold ordinaryChance
  positivity

lemma ordinaryChance_le (k : ℕ) : ordinaryChance k ≤ 1 / 32 := by
  unfold ordinaryChance
  exact div_le_div_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)

lemma profile_floor {x : BitString n} {v : ℕ} (hx : x ≠ optimum n) (hk : k ≤ v) (hv : v ≤ fitnessLevel k x) :
    k ≤ (zeros x).card ∧ (zeros x).card ≤ n - (v - k) := by
  have hz := Finset.card_le_univ (zeros x)
  rw [Fintype.card_fin] at hz
  rw [fitnessLevel, if_neg hx] at hv
  split_ifs at hv <;> omega

lemma profile_strict {x : BitString n} {v : ℕ} (hx : x ≠ optimum n) (hk : k ≤ v) (hv : v < fitnessLevel k x) :
    k ≤ (zeros x).card ∧ (zeros x).card < n - (v - k) := by
  have h := profile_floor hx hk hv.le
  rw [fitnessLevel, if_neg hx, if_pos h.1] at hv
  omega

lemma level_of_ordinary {x : BitString n} (h : k ≤ (zeros x : Finset (Fin n)).card) (hk : 0 < k) :
    fitnessLevel k x = k + (n - (zeros x).card) := by
  have hx : x ≠ optimum n := by
    intro he
    have hzero := (zeros_eq_empty_iff x).mpr he
    rw [hzero, Finset.card_empty] at h
    omega
  simp [fitnessLevel, hx, h]

lemma level_of_valley_success {x : BitString n} {v : ℕ} (_hk : 0 < k) (_hkn : k ≤ n) (hv : v < k)
    (hx : v < (zeros x : Finset (Fin n)).card) :
    v < fitnessLevel k x := by
  unfold fitnessLevel
  split_ifs <;> omega

lemma retain_lower (hn : 2 ≤ n) (x : BitString n) (F : BitString n → Prop) (hF : F x) :
    (1 / 8 : ℝ) ≤ mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (F (mutate x m))) := by
  have hh := mean_single_lower (independentBits n (1 / (n : ℝ)))
    (fun m ↦ indicator (F (mutate x m))) (fun _ ↦ indic_nonneg _) (mask ∅)
  have he : mutate x (mask ∅) = x := by funext j; simp [mutate, mask]
  rw [show indicator (F (mutate x (mask ∅))) = 1 by simp [indicator, he, hF], mul_one] at hh
  have hw := weight_lower hn (∅ : Finset (Fin n))
  simpa only [Finset.card_empty, pow_zero, one_mul] using hw.trans hh

lemma mutation_ordinary (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (x : BitString n)
    (v z : ℕ) (hv : k ≤ v) (hvn : v < n) (hz : z = n - (v - k))
    (hx : k ≤ (zeros x).card ∧ (zeros x).card ≤ z) :
    (z : ℝ) / (8 * n) ≤ mean (independentBits n (1 / (n : ℝ)))
      (fun m ↦ indicator (v < fitnessLevel k (mutate x m))) := by
  have hz' : z ≤ n := by omega
  have hn : 2 ≤ n := by omega
  obtain h | h := Nat.eq_or_lt_of_le hx.2
  · apply (single_mask_event hn (zeros x) (fun m ↦ v < fitnessLevel k (mutate x m)) ?_).trans' ?_
    · intro i hi
      have hj := flip_zero_card x hi
      have hm : k ≤ (zeros (mutate x (mask {i}))).card := by omega
      rw [level_of_ordinary hm (by omega)]
      omega
    · rw [h]
  · have hf : v < fitnessLevel k x := by
      rw [level_of_ordinary hx.1 (by omega)]
      omega
    apply le_trans _ (retain_lower hn x (fun y ↦ v < fitnessLevel k y) hf)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * n)).mpr
    have hh : (z : ℝ) ≤ n := by exact_mod_cast hz'
    linarith

lemma mutation_valley (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (x : BitString n)
    (v : ℕ) (hv : v < k) (hx : v ≤ (zeros x).card) :
    (1 / 16 : ℝ) ≤ mean (independentBits n (1 / (n : ℝ)))
      (fun m ↦ indicator (v < fitnessLevel k (mutate x m))) := by
  have hn : 2 ≤ n := by omega
  obtain h | h := Nat.eq_or_lt_of_le hx
  · apply le_trans _ (single_mask_event hn (zeros x)ᶜ (fun m ↦ v < fitnessLevel k (mutate x m)) ?_)
    · rw [Finset.card_compl, Fintype.card_fin, ← h]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * n)).mpr
      rw [Nat.cast_sub (by omega : v ≤ n)]
      have hh : (2 : ℝ) * v ≤ n := by exact_mod_cast (show 2 * v ≤ n by omega)
      linarith
    · intro j hj
      have hj' : j ∉ zeros x := Finset.mem_compl.mp hj
      have hh := flip_one_card x hj'
      exact level_of_valley_success (by omega) (by omega) hv (by omega)
  · exact (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8).trans
      (retain_lower hn x (fun y ↦ v < fitnessLevel k y) (level_of_valley_success (by omega) (by omega) hv h))

lemma pair_ordinary (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (v : ℕ) (hv : k ≤ v) (hvn : v < n)
    (x y : BitString n) (hx : x ≠ optimum n) (hy : y ≠ optimum n)
    (hX : v ≤ fitnessLevel k x) (hY : v ≤ fitnessLevel k y) :
    ordinaryChance k * (((n - (v - k) : ℕ) : ℝ) / n + indicator (v < fitnessLevel k x)) ≤
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
        mean (independentBits n (1 / (n : ℝ))) (fun r ↦
          indicator (v < fitnessLevel k (mutate (crossover x y m) r)))) := by
  let z := n - (v - k)
  let c := (1 / 2 : ℝ) ^ (2 * k + 1)
  let F (m : BitString n) := mean (independentBits n (1 / (n : ℝ))) (fun r ↦
    indicator (v < fitnessLevel k (mutate (crossover x y m) r)))
  have hX' := profile_floor hx hv hX
  have hY' := profile_floor hy hv hY
  have hnon (m : BitString n) : 0 ≤ F m := mean_nonneg _ (fun _ ↦ indic_nonneg _)
  have hn : 2 ≤ n := by omega
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hz : (z : ℝ) / n ≤ 1 := (div_le_one (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mpr
    (by dsimp [z]; exact_mod_cast Nat.sub_le n (v - k))
  change c / 32 * ((z : ℝ) / n + indicator (v < fitnessLevel k x)) ≤ mean _ F
  by_cases hbetter : v < fitnessLevel k x
  · have h := profile_strict hx hv hbetter
    let G (m : BitString n) :=
      indicator (k ≤ (zeros (crossover x y m)).card ∧ (zeros (crossover x y m)).card ≤ z - 1)
    have hG : c ≤ mean (PMF.uniformOfFintype (BitString n)) G := by
      apply available_band x y (z - 1) ⟨h.1, _⟩ hY'.1
      · have ha : (zeros x).card < z := h.2
        omega
      · have ha : (zeros x).card < z := h.2
        have hb : (zeros y).card ≤ z := hY'.2
        omega
    have hf (m : BitString n) : (1 / 8 : ℝ) * G m ≤ F m := by
      dsimp only [G, indicator]
      split_ifs with hb
      · rw [mul_one]
        apply retain_lower hn _ (fun y ↦ v < fitnessLevel k y)
        rw [level_of_ordinary hb.1 (by omega)]
        dsimp [z] at hb
        omega
      · simpa only [mul_zero] using hnon m
    have hh := mean_mono (PMF.uniformOfFintype (BitString n)) hf
    rw [mean_mul] at hh
    have hb := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [indicator, if_pos hbetter]
    nlinarith only [hh, hb, mul_le_mul_of_nonneg_left hz hc, hc]
  · let G (m : BitString n) :=
      indicator (k ≤ (zeros (crossover x y m)).card ∧ (zeros (crossover x y m)).card ≤ z)
    have hG : c ≤ mean (PMF.uniformOfFintype (BitString n)) G := by
      apply available_band x y z hX' hY'.1
      have ha : (zeros x).card ≤ z := hX'.2
      have hb : (zeros y).card ≤ z := hY'.2
      omega
    have hf (m : BitString n) : ((z : ℝ) / (8 * n)) * G m ≤ F m := by
      dsimp only [G, indicator]
      split_ifs with hb
      · rw [mul_one]
        exact mutation_ordinary hk hkn _ v z hv hvn rfl hb
      · simpa only [mul_zero] using hnon m
    have hh := mean_mono (PMF.uniformOfFintype (BitString n)) hf
    rw [mean_mul] at hh
    rw [indicator, if_neg hbetter, add_zero]
    rw [show c / 32 * ((z : ℝ) / n) = ((z : ℝ) / (8 * n)) * (c / 4) by ring]
    apply le_trans (mul_le_mul_of_nonneg_left _ (by positivity)) hh
    exact (by linarith only [hc] : c / 4 ≤ c).trans hG

lemma pair_valley (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (v : ℕ) (hv : v < k)
    (x y : BitString n) (hx : v ≤ (zeros x).card) (hy : v ≤ (zeros y).card) :
    (1 / 32 : ℝ) ≤ mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
      mean (independentBits n (1 / (n : ℝ))) (fun r ↦
        indicator (v < fitnessLevel k (mutate (crossover x y m) r)))) := by
  let G (m : BitString n) := indicator (v ≤ (zeros (crossover x y m)).card)
  have hh := cross_lower_half x y v hx hy
  change (1 / 2 : ℝ) ≤ mean _ G at hh
  have h (m : BitString n) : (1 / 16 : ℝ) * G m ≤
      mean (independentBits n (1 / (n : ℝ))) (fun r ↦
        indicator (v < fitnessLevel k (mutate (crossover x y m) r))) := by
    dsimp only [G, indicator]
    by_cases hb : v ≤ (zeros (crossover x y m)).card
    · rw [if_pos hb, mul_one]
      exact mutation_valley hk hkn _ v hv hb
    · rw [if_neg hb, mul_zero]
      exact mean_nonneg _ (fun _ ↦ indic_nonneg _)
  have hmean := mean_mono (PMF.uniformOfFintype (BitString n)) h
  rw [mean_mul] at hmean
  linarith

end
end Lax637351Proofs.ArrivalCross
