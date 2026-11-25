import Lax637351Proofs.FairCrossover
import Lax637351Proofs.SlopeCharge
import Lax637351Proofs.SlopeWindow

namespace Lax637351Proofs.SelectedProgress

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FairWalk Lax637351Proofs.FairCrossover
open Lax637351Proofs.Ordinary Lax637351Proofs.SlopeWindow
open Lax637351Proofs.Mutation Lax637351Proofs.MaskKernel Lax637351Proofs.SlopeCharge
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.PairAveraging Lax637351Proofs.SlopeCopy
open scoped Classical ENNReal

noncomputable section

variable {n k B : ℕ} {μ : ℕ+}

def rowZeros (x : BitString n) : ℝ := (zeros x).card

def crossoverGain (k : ℕ) (x y z : BitString n) : ℝ :=
  if k ≤ (zeros z).card then max 0 ((rowZeros x + rowZeros y) / 2 - rowZeros z) else 0

lemma fair_gain_lower (k B : ℕ) (hB : 0 < B) (hk : 4 * k ≤ B) (x y : BitString n)
    (hx : (B : ℝ) / 2 ≤ rowZeros x ∧ rowZeros x ≤ B)
    (hy : (B : ℝ) / 2 ≤ rowZeros y ∧ rowZeros y ≤ B) :
    Real.sqrt ((mismatch x y).card : ℝ) / (8 * Real.sqrt 6) - 2 ≤
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ crossoverGain k x y (crossover x y m)) := by
  let h := (mismatch x y).card
  let a := (rowZeros x + rowZeros y) / 2
  let c := (bothZero x y : ℝ)
  let b (w : Fin (h + 1)) := a - (c + (w.val : ℝ))
  let g (w : Fin (h + 1)) := max 0 (b w)
  have hbase : rowZeros x + rowZeros y = 2 * c + h := by
    dsimp [rowZeros, c, h]
    exact_mod_cast zero_mismatch_card x y
  have hb (w : Fin (h + 1)) : b w = -signSum h w / 2 := by
    dsimp only [b, a, signSum]
    linarith only [hbase]
  have hg (w : Fin (h + 1)) : g w = (|signSum h w| - signSum h w) / 4 := by
    dsimp [g]
    rw [hb]
    by_cases he : 0 ≤ signSum h w
    · rw [abs_of_nonneg he, max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonpos (le_of_not_ge he), max_eq_right (by linarith [le_of_not_ge he])]
      ring
  have hsq (w : Fin (h + 1)) : g w ^ 2 ≤ signSum h w ^ 2 / 4 := by
    dsimp [g]
    rw [hb, max_def]
    split_ifs <;> nlinarith [sq_nonneg (signSum h w)]
  have hG := mean_mono (countLaw h) hsq
  simp_rw [div_eq_inv_mul, mean_mul, sign_second] at hG
  have hmean (w : Fin (h + 1)) : g w = (1 / 4) * (|signSum h w| - signSum h w) := by rw [hg]; ring
  have hmeanG : Real.sqrt (h : ℝ) / (8 * Real.sqrt 6) ≤ mean (countLaw h) g := by
    change _ ≤ mean (countLaw h) (fun w ↦ g w)
    simp_rw [hmean, mean_mul, mean_sub, sign_mean, sub_zero]
    have hh := mul_le_mul_of_nonneg_left (absolute_lower h) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    refine le_trans ?_ hh
    exact le_of_eq (by ring)
  have hBk : (4 : ℝ) * k ≤ B := by exact_mod_cast hk
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hcost (w : Fin (h + 1)) :
      g w - g w ^ 2 * (4 / (B : ℝ)) ≤
        if (k : ℝ) ≤ c + (w.val : ℝ) then g w else 0 := by
    have hgn : 0 ≤ g w := le_max_left _ _
    split_ifs with hw
    · exact sub_le_self _ (by positivity)
    · have hd : (B : ℝ) / 4 ≤ g w := by
        have hh : (B : ℝ) / 4 ≤ b w := by dsimp only [b, a]; linarith only [hx.1, hy.1, hBk, le_of_not_ge hw]
        exact hh.trans (le_max_right _ _)
      have ht : (1 : ℝ) ≤ (4 * g w) / B := (le_div_iff₀ hB').mpr (by linarith only [hd])
      have hm := mul_le_mul_of_nonneg_right ht hgn
      rw [show g w ^ 2 * (4 / (B : ℝ)) = (4 * g w) / B * g w by ring]
      linarith only [hm]
  have hh := mean_mono (countLaw h) hcost
  have he (w : Fin (h + 1)) : g w ^ 2 * (4 / (B : ℝ)) = (4 / (B : ℝ)) * g w ^ 2 := by ring
  simp_rw [he, mean_sub, mean_mul] at hh
  have hcard : (h : ℝ) ≤ 2 * B := by
    have hc : 0 ≤ c := by dsimp [c]; positivity
    linarith only [hbase, hx.2, hy.2, hc]
  have hloss : 4 / (B : ℝ) * mean (countLaw h) (fun w ↦ g w ^ 2) ≤ 2 := by
    have hC : (0 : ℝ) ≤ 4 / B := by positivity
    have hh := mul_le_mul_of_nonneg_left hG hC
    have ht := (mul_le_mul_of_nonneg_left hcard (show 0 ≤ (B : ℝ)⁻¹ by positivity))
    have heq : (B : ℝ)⁻¹ * (2 * B) = 2 := by field_simp
    rw [heq] at ht
    apply hh.trans
    rw [show 4 / (B : ℝ) * (4⁻¹ * (h : ℝ)) = (B : ℝ)⁻¹ * h by ring]
    exact ht
  have hcross (m : BitString n) : crossoverGain k x y (crossover x y m) =
      (fun (w : Fin (h + 1)) ↦ if (k : ℝ) ≤ c + (w.val : ℝ) then g w else 0) (diffCount x y m) := by
    unfold crossoverGain rowZeros
    rw [cross_zeros_count]
    push_cast
    have he : k ≤ bothZero x y + (diffCount x y m).val ↔
        (k : ℝ) ≤ c + ((diffCount x y m).val : ℝ) := by dsimp [c]; exact_mod_cast (Iff.rfl)
    simp only [he]
    rfl
  simp_rw [hcross]
  rw [← mean_map _ (diffCount x y) (fun w ↦ if (k : ℝ) ≤ c + (w.val : ℝ) then g w else 0), diffCount_law]
  linarith only [hh, hloss, hmeanG]

def totalZeros (P : Population n μ) : ℝ := ∑ i, rowZeros (P i)

def averageZeros (P : Population n μ) : ℝ := totalZeros P / (μ : ℕ)

lemma totalGain_nonneg (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (z : BitString n) (Q : Population n μ) (hQ : Q ∈ (Transitions.insert (jump k) P z).support) :
    0 ≤ totalZeros P - totalZeros Q := by
  apply sub_nonneg.mpr
  exact Finset.sum_le_sum (fun i _ ↦ by
    unfold rowZeros
    exact_mod_cast (safe_insert hk hkn P (fun j ↦ Or.inl (hP j)) z Q hQ i).2)

lemma selected_gain (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (i j : Fin μ) (z : BitString n) (Q : Population n μ) (hQ : Q ∈ (Transitions.insert (jump k) P z).support) :
    crossoverGain k (P i) (P j) z ≤ totalZeros P - totalZeros Q := by
  have h0 := totalGain_nonneg hk hkn P hP z Q hQ
  unfold crossoverGain
  split_ifs with hz
  · apply max_le h0
    by_cases h : (rowZeros (P i) + rowZeros (P j)) / 2 - rowZeros z ≤ 0
    · exact h.trans h0
    have hmax : (rowZeros (P i) + rowZeros (P j)) / 2 ≤ max (rowZeros (P i)) (rowZeros (P j)) := by
      linarith [le_max_left (rowZeros (P i)) (rowZeros (P j)), le_max_right (rowZeros (P i)) (rowZeros (P j))]
    obtain ⟨u, hu⟩ : ∃ u : Fin μ, rowZeros (P u) = max (rowZeros (P i)) (rowZeros (P j)) := by
      rcases le_total (rowZeros (P i)) (rowZeros (P j)) with h | h
      · exact ⟨j, (max_eq_right h).symm⟩
      · exact ⟨i, (max_eq_left h).symm⟩
    have hbetter : (zeros z).card < (zeros (P u)).card := by
      have ht : rowZeros z < rowZeros (P u) := by linarith only [h, hmax, hu]
      unfold rowZeros at ht
      exact_mod_cast ht
    obtain ⟨d, he, hd⟩ := improved_site hkn P hP z hz u hbetter Q hQ
    have hsum := sum_update P d z rowZeros
    change totalZeros (Function.update P d z) - totalZeros P = rowZeros z - rowZeros (P d) at hsum
    have hh : rowZeros (P u) ≤ rowZeros (P d) := by unfold rowZeros; exact_mod_cast hd
    rw [he]
    linarith only [hmax, hsum, hu, hh]
  · exact h0

lemma selected_progress_pair (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (hB : 0 < B) (hkB : 4 * k ≤ B)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (hP : ordinary k P)
    (i j : Fin μ) (hi : (B : ℝ) / 2 ≤ rowZeros (P i) ∧ rowZeros (P i) ≤ B)
    (hj : (B : ℝ) / 2 ≤ rowZeros (P j) ∧ rowZeros (P j) ≤ B)
    (hd : 32 * Real.sqrt 6 ≤ Real.sqrt ((mismatch (P i) (P j)).card : ℝ)) :
    mean (step (jump k) p false P) averageZeros ≤ averageZeros P -
      p * Real.sqrt ((mismatch (P i) (P j)).card : ℝ) / (128 * Real.sqrt 6 * ((μ : ℕ) : ℝ) ^ 3) := by
  let f (Q : Population n μ) := totalZeros P - totalZeros Q
  let F (z : BitString n) := mean (independentBits n (1 / (n : ℝ))) (fun m ↦
    mean (Transitions.insert (jump k) P (mutate z m)) f)
  have hF (z : BitString n) : 0 ≤ F z := mean_nonneg _ (fun m ↦
    by rw [← mean_const (Transitions.insert (jump k) P (mutate z m)) (0 : ℝ)]
       exact mean_mono_on_support _ (totalGain_nonneg hk hkn P hP (mutate z m)))
  have hcopy (z : BitString n) : (1 / 8 : ℝ) * crossoverGain k (P i) (P j) z ≤ F z := by
    have hh := mean_single_lower (independentBits n (1 / (n : ℝ))) (fun m ↦
        mean (Transitions.insert (jump k) P (mutate z m)) f) (fun m ↦
        by rw [← mean_const (Transitions.insert (jump k) P (mutate z m)) (0 : ℝ)]
           exact mean_mono_on_support _ (totalGain_nonneg hk hkn P hP (mutate z m))) (mask ∅)
    have he : mutate z (mask ∅) = z := by funext j; simp [mutate, mask]
    rw [he] at hh
    have hpt := mean_mono_on_support (Transitions.insert (jump k) P z) (selected_gain hk hkn P hP i j z)
    rw [mean_const] at hpt
    apply le_trans _ hh
    exact mul_le_mul (cloneMass_lower hn) hpt (by unfold crossoverGain; split_ifs <;> positivity) ENNReal.toReal_nonneg
  have hM := mean_mono (PMF.uniformOfFintype (BitString n)) (fun m ↦ hcopy (crossover (P i) (P j) m))
  rw [mean_mul] at hM
  let s := Real.sqrt ((mismatch (P i) (P j)).card : ℝ)
  let b := s / (128 * Real.sqrt 6)
  have hS : (0 : ℝ) < Real.sqrt 6 := by positivity
  have hgain := fair_gain_lower k B hB hkB (P i) (P j) hi hj
  have hb : b ≤ mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ F (crossover (P i) (P j) m)) := by
    refine le_trans ?_ ((mul_le_mul_of_nonneg_left hgain (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans hM)
    have ht : 2 ≤ s / (16 * Real.sqrt 6) := (le_div_iff₀ (by positivity)).mpr (by
      change 32 * Real.sqrt 6 ≤ s at hd
      linarith only [hd])
    dsimp [b]
    have he : s / (8 * Real.sqrt 6) = 2 * (s / (16 * Real.sqrt 6)) := by field_simp; ring
    have he' : s / (128 * Real.sqrt 6) = (1 / 8) * (s / (16 * Real.sqrt 6)) := by field_simp; ring
    rw [he, he']
    linarith only [ht]
  have hpair := mean_single_lower (PMF.uniformOfFintype (Fin μ × Fin μ))
    (fun ij ↦ mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ F (crossover (P ij.1) (P ij.2) m)))
    (fun ij ↦ mean_nonneg _ (fun _ ↦ hF _)) (i, j)
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul] at hpair
  have htot : p * (((μ : ℕ) : ℝ) * (μ : ℕ))⁻¹ * b ≤ mean (step (jump k) p false P) f := by
    rw [mean_unmarked hp]
    change _ ≤ p * mean (parents P true) F + (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun a ↦ F (P a))
    have hCross : (((μ : ℕ) : ℝ) * (μ : ℕ))⁻¹ * b ≤ mean (parents P true) F := by
      simp only [parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
      exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans hpair
    have hRest := mul_nonneg (sub_nonneg.mpr hp.2) (mean_nonneg (PMF.uniformOfFintype (Fin μ)) (fun a ↦ hF (P a)))
    have hh := mul_le_mul_of_nonneg_left hCross hp.1
    nlinarith only [hh, hRest]
  have hf := htot
  dsimp [f] at hf
  rw [mean_sub, mean_const] at hf
  unfold averageZeros
  simp_rw [div_eq_inv_mul, mean_mul]
  have ht := mul_le_mul_of_nonneg_left hf (show 0 ≤ (((μ : ℕ) : ℝ))⁻¹ by positivity)
  have he : (((μ : ℕ) : ℝ))⁻¹ * (p * (((μ : ℕ) : ℝ) * (μ : ℕ))⁻¹ * b) =
      p * s / (128 * Real.sqrt 6 * ((μ : ℕ) : ℝ) ^ 3) := by dsimp [b]; field_simp
  rw [he] at ht
  have ht' : (128 * Real.sqrt 6 * ((μ : ℕ) : ℝ) ^ 3)⁻¹ * (p * s) ≤
      (((μ : ℕ) : ℝ))⁻¹ * totalZeros P -
        (((μ : ℕ) : ℝ))⁻¹ * mean (step (jump k) p false P) totalZeros := by
    simpa only [div_eq_inv_mul, mul_sub] using ht
  linarith only [ht']

end
end Lax637351Proofs.SelectedProgress
