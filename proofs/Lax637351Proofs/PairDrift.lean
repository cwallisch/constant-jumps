import Lax637351Proofs.PlateauChanges
import Lax637351Proofs.RareSuccess

namespace Lax637351Proofs.PairDrift

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.MarkedStep
open Lax637351Proofs.Auxiliary Lax637351Proofs.PairAveraging Lax637351Proofs.PlateauKernel
open Lax637351Proofs.SubsetPairs Lax637351Proofs.CoordinateExtension Lax637351Proofs.PairSignal
open Lax637351Proofs.PlateauChanges Lax637351Proofs.RareSuccess
open Lax637351Proofs.CrossoverSuccess Lax637351Proofs.Mutation Lax637351Proofs.SlopeCopy
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma partner_nonneg (j : ℕ) (P : Population n μ) (z : BitString n) : 0 ≤ partnerMean (choosePair j) P z := by
  rw [partnerMean_eq]
  exact mean_nonneg _ (fun _ ↦ choosePair_nonneg _ _ _)

lemma subsetScore_nonneg (j : ℕ) (P : Population n μ) : 0 ≤ subsetScore j P := by
  rw [subsetScore_eq]
  exact mean_nonneg _ (fun _ ↦ partner_nonneg _ _ _)

lemma subsetScore_upper (j : ℕ) (P : Population n μ) (hP : plateau (k := k) P) : subsetScore j P ≤ (2 : ℝ) ^ k := by
  rw [subsetScore_eq]
  refine (mean_mono _ (fun i ↦ ?_)).trans_eq (mean_const _ _)
  rw [partnerMean_eq]
  exact (mean_mono _ (fun x ↦ choosePair_upper j (P i) (P x) (hP i).le)).trans_eq (mean_const _ _)

lemma pair_advance (hk : 0 < k) (hn : 2 ≤ n) (hnk : 4 * k ≤ n) (hμ : 2 ≤ μ)
    (r : ℕ) (hr : r < k) (P : Population n μ) (hP : plateau (k := k) P)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool) (δ M : ℝ) (hδ : 0 ≤ δ)
    (hcol : ∀ i : Fin n, δ ≤ avoidsRate {i} P)
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ M * p) :
    (1 - 2 * M * p / ((μ : ℕ) + 1)) * subsetScore (r + 1) P +
      (p * extensionConstant k * δ / ((k : ℝ) * ((μ : ℕ) + 1))) * subsetScore r P ≤
      mean (auxiliary k p ar P) (subsetScore (r + 1)) := by
  let nμ : ℝ := (μ : ℕ)
  let v := (1 - (1 / nμ))
  let q := copyRate n p ar
  let A := subsetScore (r + 1) P
  let R := subsetScore r P
  let F := partnerMean (choosePair (r + 1)) P
  let c := extensionConstant k * δ / k
  have hm : 2 ≤ nμ := by dsimp [nμ]; exact_mod_cast hμ
  have hm' : 0 < nμ := by linarith
  have hv : 1 / 2 ≤ v := by
    have h := one_div_le_one_div_of_le (show 0 < (2 : ℝ) by norm_num) hm
    dsimp [v]
    linarith only [h]
  have hv0 : 0 ≤ v := by linarith
  have hc : 0 ≤ c := by dsimp [c, extensionConstant]; positivity
  have hA : 0 ≤ A := subsetScore_nonneg _ _
  have hR : 0 ≤ R := subsetScore_nonneg _ _
  have hχ : c * R ≤ crossed k P F := crossed_lower hk hn hnk r hr P hP δ hδ hcol
  have he := pair_drift hk (by omega) p ar P hP (choosePair (r + 1))
    (choosePair_symm _) (choosePair_diag (Nat.succ_pos r))
  change mean (auxiliary k p ar P) (fun Q ↦ subsetScore (r + 1) Q - A) =
    (2 / (nμ + 1)) * (v * submitMean k p ar P F - submitRate k p ar P * A) at he
  rw [mean_sub, mean_const, submit_split p hp ar P hP F, rate_split p hp ar P hP] at he
  have hl : slotMean F P = A := by
    rw [slotMean_eq]
    exact (subsetScore_eq (r + 1) P).symm
  rw [hl] at he
  have hUV : p * crossed k P (fun _ ↦ 1) + (1 - p) * changedMutation k P (fun _ ↦ 1) + q / nμ ≤ M * p := by
    have h₁ := mul_le_mul_of_nonneg_left (crossed_rate (k := k) P) hp.1
    have h₂ := mul_le_mul_of_nonneg_left (changed_rate hn P hP) (sub_nonneg.mpr hp.2)
    have h₃ : 0 ≤ p * ((k : ℝ) / n) := mul_nonneg hp.1 (by positivity)
    change p + (k : ℝ) / n + q / nμ ≤ M * p at hLoss
    linarith only [h₁, h₂, h₃, hLoss]
  have hC : v * (p * crossed k P F) ≥ (1 / 2) * p * c * R := by
    have h := mul_le_mul (show (1 / 2 : ℝ) ≤ v from hv)
      (mul_le_mul_of_nonneg_left hχ hp.1) (mul_nonneg hp.1 (mul_nonneg hc hR)) hv0
    exact (by ring : (1 / 2 : ℝ) * p * c * R = (1 / 2) * (p * (c * R))) ▸ h
  have ht : 0 ≤ v * ((1 - p) * changedMutation k P F) :=
    mul_nonneg hv0 (mul_nonneg (sub_nonneg.mpr hp.2) (changed_nonneg P F (partner_nonneg _ _)))
  have hneg := mul_le_mul_of_nonneg_right hUV hA
  have hcenter : (1 / 2) * p * c * R - M * p * A ≤
      v * (p * crossed k P F + (1 - p) * changedMutation k P F + q * A) -
        (p * crossed k P (fun _ ↦ 1) + (1 - p) * changedMutation k P (fun _ ↦ 1) + q) * A := by
    calc
      _ ≤ v * (p * crossed k P F) + v * ((1 - p) * changedMutation k P F) -
            (p * crossed k P (fun _ ↦ 1) + (1 - p) * changedMutation k P (fun _ ↦ 1) + q / nμ) * A := by
        linarith only [hC, ht, hneg]
      _ = _ := by dsimp only [v]; ring
  have hstep := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ (2 : ℝ) / (nμ + 1) by positivity)
  rw [← he] at hstep
  have heq : (2 / (nμ + 1)) * ((1 / 2) * p * c * R - M * p * A) =
      (p * extensionConstant k * δ / ((k : ℝ) * (nμ + 1))) * R - 2 * M * p / (nμ + 1) * A := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    dsimp only [c]
    field_simp
  rw [heq] at hstep
  change (1 - 2 * M * p / (nμ + 1)) * A + (p * extensionConstant k * δ / ((k : ℝ) * (nμ + 1))) * R ≤ _
  linarith only [hstep]

lemma choosePair_full (_hk : 0 < k) (x y : BitString n)
    (hx : (zeros x).card = k) (hy : (zeros y).card = k) :
    choosePair k x y = indicator (Disjoint (zeros x) (zeros y)) := by
  have h : (zeros x \ zeros y).card = (zeros y \ zeros x).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, hx, hy, Finset.inter_comm]
  have hs : (zeros x \ zeros y).card ≤ k := (Finset.card_le_card Finset.sdiff_subset).trans_eq hx
  unfold choosePair
  rw [h, min_self, ← h]
  by_cases hd : Disjoint (zeros x) (zeros y)
  · simp [indicator, hd, hd.sdiff_eq_left, hx]
  · have hh : (zeros x \ zeros y).card < k := by
      apply lt_of_le_of_ne hs
      intro he
      have hset : zeros x \ zeros y = zeros x := Finset.eq_of_subset_of_card_le Finset.sdiff_subset (he.trans hx.symm).ge
      exact hd (sdiff_eq_left.mp hset)
    simp [indicator, hd, Nat.choose_eq_zero_of_lt hh]

lemma subsetScore_pair_mean (r : ℕ) (P : Population n μ) :
    subsetScore r P = mean (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ij ↦ choosePair r (P ij.1) (P ij.2)) := by
  rw [mean_uniform_pair (fun i j : Fin μ ↦ choosePair r (P i) (P j)), subsetScore_eq]
  simp_rw [partnerMean_eq]

lemma probability_child_opt (hk : 0 < k) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : plateau (k := k) P) :
    (p * crossRate k) * subsetScore k P ≤
      mean (draws p P) (fun d ↦ indicator (child d = optimum n)) := by
  let QM := independentBits n (1 / (n : ℝ))
  have hpair (i j : Fin μ) :
      crossRate k * choosePair k (P i) (P j) ≤
        mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ mean QM (fun flip ↦
          indicator (mutate (crossover (P i) (P j) m) flip = optimum n))) := by
    rw [choosePair_full hk _ _ (hP i) (hP j)]
    by_cases hd : Disjoint (zeros (P i)) (zeros (P j))
    · have hc := crossover_disjoint_probability (P i) (P j) hd
      rw [hP i, hP j] at hc
      have hp (m : BitString n) : (1 / 8 : ℝ) * indicator (crossover (P i) (P j) m = optimum n) ≤
          mean QM (fun flip ↦ indicator (mutate (crossover (P i) (P j) m) flip = optimum n)) := by
        by_cases h : crossover (P i) (P j) m = optimum n
        · have hclone : mutate (crossover (P i) (P j) m) (mask ∅) = optimum n := by
            rw [(noFlip_iff _ _).mpr rfl, h]
          have ht := mean_single_lower QM (fun flip ↦ indicator (mutate (crossover (P i) (P j) m) flip = optimum n))
            (fun _ ↦ indic_nonneg _) (mask ∅)
          rw [indicator, if_pos hclone, mul_one] at ht
          rw [indicator, if_pos h, mul_one]
          exact (cloneMass_lower hn).trans ht
        · rw [indicator, if_neg h, mul_zero]
          exact mean_nonneg _ (fun _ ↦ indic_nonneg _)
      have hh := mean_mono (PMF.uniformOfFintype (BitString n)) hp
      rw [mean_mul, hc] at hh
      simpa only [indicator, if_pos hd, mul_one, crossRate, div_eq_mul_inv, one_div, one_mul, mul_comm] using hh
    · rw [indicator, if_neg hd, mul_zero]
      exact mean_nonneg _ fun _ ↦ mean_nonneg _ fun _ ↦ indic_nonneg _
  have he := mean_mono (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ij ↦ hpair ij.1 ij.2)
  rw [mean_mul, ← subsetScore_pair_mean] at he
  rw [mean_draws hp]
  simp only [child, parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
  have h := mul_le_mul_of_nonneg_left he hp.1
  rw [← mul_assoc] at h
  exact h.trans (le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hp.2)
    (mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ indic_nonneg _)))))

end
end Lax637351Proofs.PairDrift
