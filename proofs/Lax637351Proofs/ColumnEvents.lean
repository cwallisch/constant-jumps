import Lax637351Proofs.ColumnReplacement
import Lax637351Proofs.CrossBand

namespace Lax637351Proofs.ColumnEvents

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.OffspringProduct Lax637351Proofs.CrossBand
open Lax637351Proofs.FairCrossover Lax637351Proofs.ColumnSlot Lax637351Proofs.PlateauKernel
open Lax637351Proofs.PlateauChanges Lax637351Proofs.PairSignal Lax637351Proofs.MarkedStep Lax637351Proofs.Auxiliary
open Lax637351Proofs.ColumnReplacement
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def immigrant (k : ℕ) (i : Fin n) (z : BitString n) : Prop :=
  (zeros z).card = k ∧ z i = 1

def immigrationRate (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (2 * k) / 16

lemma immigrationRate_pos (k : ℕ) : 0 < immigrationRate k := by unfold immigrationRate; positivity

lemma mutation_immigrant (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (i : Fin n) (x : BitString n)
    (hx : (zeros x).card = k) (hi : x i = 0) :
    (1 : ℝ) / (16 * n) ≤ mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (immigrant k i (mutate x m))) := by
  have hi' : i ∈ zeros x := (mem_zeros _ _).mpr hi
  let S := (zeros x)ᶜ
  have he : i ∉ S := by simp [S, hi']
  have h := swap_mask_event hn i S he (fun m ↦ immigrant k i (mutate x m)) (by
    intro j hj
    have hj' : j ∉ zeros x := Finset.mem_compl.mp hj
    have hc := swap_card x hi' hj'
    refine ⟨hc.trans hx, ?_⟩
    have hr : i ∈ ({i, j} : Finset (Fin n)) := by simp
    simp [mutate, mask, hr, hi])
  apply le_trans _ h
  rw [show S.card = n - k by dsimp [S]; rw [Finset.card_compl, Fintype.card_fin, hx]]
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : (n : ℝ) / 2 ≤ ((n - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n)]
    have hr : (2 : ℝ) * (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith only [hr]
  apply le_trans _ (div_le_div_of_nonneg_right hh (show 0 ≤ 8 * (n : ℝ) ^ 2 by positivity))
  field_simp
  norm_num

lemma crossed_immigrant (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (i : Fin n) (x y : BitString n)
    (hx : (zeros x).card = k) (hy : (zeros y).card = k) (hi : x i = 0) :
    immigrationRate k / n ≤
      mean (pairMutation x y (1 / (n : ℝ))) (fun z ↦ indicator (immigrant k i z)) := by
  rw [pairMutation, mean_bind]
  simp_rw [mean_bind, mean_pure]
  have h (m : BitString n) : (1 / (16 * (n : ℝ))) * indicator (crossover x y m = x) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun t ↦ indicator (immigrant k i (mutate (crossover x y m) t))) := by
    by_cases hm : crossover x y m = x
    · simpa only [hm, indicator, if_true, mul_one] using mutation_immigrant hn hkn i x hx hi
    · rw [indicator, if_neg hm, mul_zero]
      exact mean_nonneg _ (fun _ ↦ indic_nonneg _)
  have hm := mean_mono (PMF.uniformOfFintype (BitString n)) h
  rw [mean_mul] at hm
  have hcard : (mismatch x y).card ≤ 2 * k := by
    have h := zero_mismatch_card x y
    rw [hx, hy] at h
    omega
  have hs := (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hcard).trans (mask_copies_first x y)
  apply le_trans _ ((mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (16 * (n : ℝ)))).trans hm)
  unfold immigrationRate
  ring_nf
  exact le_rfl

lemma changed_mutation_row (hn : 2 ≤ n) (x : BitString n) (hx : (zeros x).card = k) :
    mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      indicator ((zeros (mutate x m)).card = k ∧ mutate x m ≠ x)) ≤ (k : ℝ) / n := by
  have h := mask_hit_upper hn (zeros x)
  rw [hx] at h
  apply le_trans _ h
  apply mean_mono
  intro m
  by_cases hm : (zeros (mutate x m)).card = k ∧ mutate x m ≠ x
  · have hh : ∃ j ∈ zeros x, m j = 1 := by
      by_contra h
      exact hm.2 (equal_card_no_hit x m h (hm.1.trans hx.symm))
    simp only [indicator, if_pos hm, if_pos hh, le_refl]
  · rw [indicator, if_neg hm]
    split_ifs <;> norm_num

lemma cross_mutant_row (hn : 2 ≤ n) (i : Fin n) (x y : BitString n) :
    mean (pairMutation x y (1 / (n : ℝ))) (fun z ↦ indicator (z i = 1)) ≤
      indicator (x i = 1) + indicator (y i = 1) + 1 / n := by
  have hn₀ : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  by_cases hx : x i = 1
  · rw [show indicator (x i = 1) = 1 from if_pos hx]
    have h := (mean_mono (pairMutation x y (1 / (n : ℝ))) (fun z ↦ indic_le_one (z i = 1))).trans_eq (mean_const _ 1)
    linarith only [h, indic_nonneg (y i = 1), hn₀]
  by_cases hy : y i = 1
  · rw [show indicator (y i = 1) = 1 from if_pos hy]
    have h := (mean_mono (pairMutation x y (1 / (n : ℝ))) (fun z ↦ indic_le_one (z i = 1))).trans_eq (mean_const _ 1)
    linarith only [h, indic_nonneg (x i = 1), hn₀]
  have hx0 : x i = 0 := by by_contra h; exact hx (bit_eq_one_of_ne_zero _ h)
  have hy0 : y i = 0 := by by_contra h; exact hy (bit_eq_one_of_ne_zero _ h)
  rw [show indicator (x i = 1) = 0 from if_neg hx, show indicator (y i = 1) = 0 from if_neg hy, zero_add, zero_add]
  rw [pairMutation, mean_bind]
  simp_rw [mean_bind, mean_pure]
  apply (mean_mono _ (fun m ↦ show mean (independentBits n (1 / (n : ℝ)))
    (fun t ↦ indicator (mutate (crossover x y m) t i = 1)) ≤ 1 / n by
      have h0 : crossover x y m i = 0 := by simp [crossover, hx0, hy0]
      have h (t : BitString n) : indicator (mutate (crossover x y m) t i = 1) = indicator (t i = 1) := by
        by_cases ht : t i = 1 <;> simp [mutate, h0, ht]
      simp_rw [h]
      have h' : (fun t : BitString n ↦ indicator (t i = 1)) =
          (fun t ↦ @ite ℝ (t i = 1) (instDecidableEqFin 2 (t i) 1) 1 0) := by
        funext t
        by_cases h : t i = 1 <;> simp [indicator, h]
      rw [h']
      exact (mask_coord_mean (rate_valid hn) i).le)).trans_eq (mean_const _ _)

def crossPairs (P : Population n μ) (f : BitString n → BitString n → BitString n → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin μ)) fun x ↦
    mean (PMF.uniformOfFintype (Fin μ)) fun y ↦
      mean (pairMutation (P x) (P y) (1 / (n : ℝ))) (f (P x) (P y))

lemma crossed_as_pairs (P : Population n μ) (f : BitString n → ℝ) :
    crossed k P f = crossPairs P (fun _ _ z ↦ indicator ((zeros z).card = k) * f z) := by
  unfold crossed crossOffspring crossPairs
  rw [mean_bind, ArrivalProgress.branch_cross]
  simp only [pairMutation, mean_bind, mean_pure, mean_map]

lemma aux_mean_proposal (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (i : Fin n) (H : ℕ) :
    mean (auxiliary k p ar P) (fun Q ↦ populationPotential k i H Q - populationPotential k i H P) =
      p * crossed k P (replaceMean k i H P) +
        (1 - p) * changedMutation k P (replaceMean k i H P) +
        copyRate n p ar * slotMean (replaceMean k i H P) P := by
  rw [← submit_split p hp ar P hP, auxiliary, mean_bind, submitMean]
  congr 1
  funext d
  rw [rejectSelect_plateau hk hkn ar P hP]
  by_cases h : submitted k ar d
  · rw [if_pos h, mean_map, indicator, if_pos h, one_mul]
    rfl
  · simp only [if_neg h, mean_pure, sub_self, indicator, zero_mul]

end
end Lax637351Proofs.ColumnEvents
