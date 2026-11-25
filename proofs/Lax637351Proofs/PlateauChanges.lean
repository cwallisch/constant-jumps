import Lax637351Proofs.PairSignal
import Lax637351Proofs.SlopeCopy

namespace Lax637351Proofs.PlateauChanges

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.MarkedStep
open Lax637351Proofs.Auxiliary Lax637351Proofs.PairAveraging Lax637351Proofs.PlateauKernel
open Lax637351Proofs.PairSignal Lax637351Proofs.SlopeCopy
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def changedMutation (k : ℕ) (P : Population n μ) (f : BitString n → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin μ)) fun i ↦ mean (independentBits n (1 / (n : ℝ))) fun m ↦
    let z := mutate (P i) m
    indicator ((zeros z).card = k ∧ z ≠ P i) * f z

lemma changed_nonneg (P : Population n μ) (f : BitString n → ℝ) (hf : ∀ z, 0 ≤ f z) :
    0 ≤ changedMutation k P f := by
  exact mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ mul_nonneg (indic_nonneg _) (hf _)))

lemma crossed_rate (P : Population n μ) : crossed k P (fun _ ↦ 1) ≤ 1 := by
  unfold crossed
  simp only [mul_one]
  exact (mean_mono _ (fun z ↦ indic_le_one ((zeros z).card = k))).trans_eq (mean_const _ 1)

lemma changed_rate (hn : 2 ≤ n) (P : Population n μ) (hP : plateau (k := k) P) :
    changedMutation k P (fun _ ↦ 1) ≤ (k : ℝ) / n := by
  unfold changedMutation
  apply le_trans (b := mean (PMF.uniformOfFintype (Fin μ)) (fun _ ↦ (k : ℝ) / n)) _ (mean_const _ _).le
  apply mean_mono
  intro i
  let G (m : BitString n) := ∃ j ∈ zeros (P i), m j = 1
  have h := mask_hit_upper hn (zeros (P i))
  rw [hP i] at h
  apply le_trans _ h
  apply mean_mono
  intro m
  simp only [mul_one]
  by_cases ht : (zeros (mutate (P i) m)).card = k ∧ mutate (P i) m ≠ P i
  · have hh : G m := by
      by_contra h
      exact ht.2 (equal_card_no_hit (P i) m h (ht.1.trans (hP i).symm))
    simp only [indicator, if_pos ht, if_pos (show ∃ j ∈ zeros (P i), m j = 1 from hh), le_refl]
  · simp only [indicator, if_neg ht]
    split_ifs <;> norm_num

lemma noFlip_iff (x m : BitString n) : mutate x m = x ↔ m = mask ∅ := by
  constructor
  · intro h
    rw [← mask_zeros_compl m]
    have he : (zeros m)ᶜ = ∅ := by
      by_contra hh
      exact mutate_mask_ne x (Finset.nonempty_iff_ne_empty.mpr hh)
        (by rw [mask_zeros_compl]; exact h)
    rw [he]
  · rintro rfl
    funext j
    simp [mutate, mask]

lemma noFlip_mean (n : ℕ) :
    mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (m = mask ∅)) = cloneMass n := by
  unfold mean cloneMass
  rw [Finset.sum_eq_single (mask ∅)]
  · simp [indicator]
  · intro m _ hm
    simp [indicator, hm]
  · simp

def copyRate (n : ℕ) (p : ℝ) (ar : Bool) : ℝ :=
  if ar then 0 else (1 - p) * cloneMass n

lemma copyRate_nonneg (n : ℕ) (p : ℝ) (hp : p ≤ 1) (ar : Bool) :
    0 ≤ copyRate n p ar := by
  cases ar
  · exact mul_nonneg (sub_nonneg.mpr hp) ENNReal.toReal_nonneg
  · exact le_rfl

lemma copyRate_le_one (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool) :
    copyRate n p ar ≤ 1 := by
  unfold copyRate
  split_ifs
  · norm_num
  · have h : cloneMass n ≤ 1 := by
      rw [← noFlip_mean]
      exact (mean_mono _ (fun m ↦ indic_le_one (m = mask ∅))).trans_eq (mean_const _ 1)
    have h' : (1 : ℝ) - p ≤ 1 := by linarith only [hp.1]
    simpa only [mul_one] using mul_le_mul h' h ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1)

lemma submit_split (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (f : BitString n → ℝ) :
    submitMean k p ar P f =
      p * crossed k P f + (1 - p) * changedMutation k P f + copyRate n p ar * slotMean f P := by
  unfold submitMean
  rw [mean_draws hp]
  have hc (z m : BitString n) : indicator (submitted k ar (true, z, m)) =
      indicator ((zeros (mutate z m)).card = k) := by simp [submitted, discarded, child]
  have hm (i : Fin μ) (m : BitString n) :
      indicator (submitted k ar (false, P i, m)) * f (mutate (P i) m) =
        indicator ((zeros (mutate (P i) m)).card = k ∧ mutate (P i) m ≠ P i) * f (mutate (P i) m) +
          (if ar then 0 else f (P i)) * indicator (m = mask ∅) := by
    by_cases h : m = mask ∅
    · subst m
      have hm : mutate (P i) (mask ∅) = P i := (noFlip_iff _ _).mpr rfl
      cases ar <;> simp [submitted, discarded, child, indicator, hm, hP i]
    · have hm : mutate (P i) m ≠ P i := fun hh ↦ h ((noFlip_iff (P i) m).mp hh)
      simp [indicator, submitted, discarded, child, hm, h]
  simp only [child]
  simp_rw [hc, hm, mean_add, mean_mul, noFlip_mean]
  unfold crossed crossOffspring changedMutation
  simp only [mean_bind, mean_map]
  have hf (i : Fin μ) : (if ar then 0 else f (P i)) * cloneMass n = (if ar then 0 else cloneMass n) * f (P i) := by
    cases ar <;> simp [mul_comm]
  simp_rw [hf, mean_mul, ← slotMean_eq f P]
  cases ar <;> simp [copyRate]; ring

lemma rate_split (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) :
    submitRate k p ar P =
      p * crossed k P (fun _ ↦ 1) + (1 - p) * changedMutation k P (fun _ ↦ 1) + copyRate n p ar := by
  have he : slotMean (fun _ ↦ 1) P = 1 := by rw [slotMean_eq, mean_const]
  have hh := submit_split p hp ar P hP (fun _ ↦ 1)
  simpa only [submitMean, mul_one, he, submitRate] using hh

lemma mean_change (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : plateau (k := k) P) :
    mean (auxiliary k p true P) (fun Q ↦ indicator (Q ≠ P)) ≤ p + (k : ℝ) / n := by
  have h : mean (auxiliary k p true P) (fun Q ↦ indicator (Q ≠ P)) ≤ submitRate k p true P := by
    rw [auxiliary, mean_bind, submitRate]
    apply mean_mono
    intro d
    rw [rejectSelect_plateau hk hkn true P hP]
    by_cases hs : submitted k true d
    · rw [if_pos hs, indicator, if_pos hs]
      exact (mean_mono _ (fun Q ↦ indic_le_one (Q ≠ P))).trans_eq (mean_const _ 1)
    · simp [indicator, hs, mean_pure]
  apply h.trans
  rw [rate_split p hp true P hP]
  rw [show copyRate n p true = 0 by rfl, add_zero]
  have h₁ := mul_le_mul_of_nonneg_left (crossed_rate (k := k) P) hp.1
  have h₂ := mul_le_mul_of_nonneg_left (changed_rate hn P hP) (sub_nonneg.mpr hp.2)
  linarith only [h₁, h₂, mul_nonneg hp.1 (show (0 : ℝ) ≤ (k : ℝ) / n by positivity)]

end
end Lax637351Proofs.PlateauChanges
