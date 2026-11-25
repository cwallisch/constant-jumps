import Lax637351Proofs.ColumnCrossoverMean

namespace Lax637351Proofs.ColumnCrossDrift

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.OffspringProduct Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear
open Lax637351Proofs.ColumnGain Lax637351Proofs.ColumnPrediction
open Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnSlot
open Lax637351Proofs.PlateauKernel Lax637351Proofs.ColumnEvents Lax637351Proofs.ColumnReplacement
open Lax637351Proofs.ColumnContrast Lax637351Proofs.ColumnCrossoverMean Lax637351Proofs.PairSignal
open Lax637351Proofs.SpeciesDrift (genotypeList)
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma mateMean_mono (P : Population n μ) (hP : plateau (k := k) P)
    (f g : Genotype n k → Genotype n k → BitString n → ℝ)
    (h : ∀ x y z, f x y z ≤ g x y z) :
    mateMean P hP f ≤ mateMean P hP g :=
  mean_mono _ (fun u ↦ mean_mono _ (fun v ↦ mean_mono _ (h (genotypeList P hP u) (genotypeList P hP v))))

lemma mateMean_add (P : Population n μ) (hP : plateau (k := k) P)
    (f g : Genotype n k → Genotype n k → BitString n → ℝ) :
    mateMean P hP (fun x y z ↦ f x y z + g x y z) = mateMean P hP f + mateMean P hP g := by
  unfold mateMean
  simp_rw [mean_add]

lemma mateMean_sub (P : Population n μ) (hP : plateau (k := k) P)
    (f g : Genotype n k → Genotype n k → BitString n → ℝ) :
    mateMean P hP (fun x y z ↦ f x y z - g x y z) = mateMean P hP f - mateMean P hP g := by
  unfold mateMean
  simp_rw [mean_sub]

lemma mateMean_mul (P : Population n μ) (hP : plateau (k := k) P)
    (a : ℝ) (f : Genotype n k → Genotype n k → BitString n → ℝ) :
    mateMean P hP (fun x y z ↦ a * f x y z) = a * mateMean P hP f := by
  unfold mateMean
  simp_rw [mean_mul]

lemma mateMean_const (P : Population n μ) (hP : plateau (k := k) P) (a : ℝ) :
    mateMean P hP (fun _ _ _ ↦ a) = a := by unfold mateMean; simp only [mean_const]

lemma mutation_frequency (k : ℕ) (P : Population n μ) (i : Fin n) :
    mean (PMF.uniformOfFintype (Fin μ)) (fun u ↦ indicator (P u i = 1)) = frequency k i P :=
  (slotMean_eq (fun x ↦ indicator (x i = 1)) P).symm

lemma resident_frequency (k : ℕ) (P : Population n μ) (i : Fin n) :
    mean (PMF.uniformOfFintype (Fin μ)) (fun u ↦ indicator (P u i = 0)) = 1 - frequency k i P := by
  have h (u : Fin μ) : indicator (P u i = 0) = 1 - indicator (P u i = 1) := by
    by_cases h : P u i = 0
    · simp [indicator, h]
    · simp [indicator, bit_eq_one_of_ne_zero _ h]
  simp_rw [h]
  rw [mean_sub, mean_const, mutation_frequency]

def crossImmigrant (i : Fin n) (x y : Genotype n k) (raw : BitString n) : Prop :=
  x ∉ mutants i ∧ y ∉ mutants i ∧ immigrant k i raw

lemma mateMean_immigrant (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (i : Fin n)
    (P : Population n μ) (hP : plateau (k := k) P) :
    immigrationRate k / (n : ℝ) * (1 - frequency k i P) ^ 2 ≤
      mateMean P hP (fun x y raw ↦ indicator (crossImmigrant i x y raw)) := by
  let ν := PMF.uniformOfFintype (Fin μ)
  let b := immigrationRate k / (n : ℝ)
  let d (u : Fin μ) := indicator (P u i = 0)
  have h (u v : Fin μ) : b * d u * d v ≤ mean (pairMutation (P u) (P v) (1 / (n : ℝ))) (fun raw ↦
      indicator (crossImmigrant i (genotypeList P hP u) (genotypeList P hP v) raw)) := by
    by_cases hU : P u i = 0
    · by_cases hV : P v i = 0
      · have hx : genotypeList P hP u ∉ mutants i := by
          change ¬Genotypes.toString (ofString (P u) (hP u)) i = 1
          rw [toString_ofString, hU]
          exact Fin.zero_ne_one
        have hy : genotypeList P hP v ∉ mutants i := by
          change ¬Genotypes.toString (ofString (P v) (hP v)) i = 1
          rw [toString_ofString, hV]
          exact Fin.zero_ne_one
        have he (raw : BitString n) :
            crossImmigrant i (genotypeList P hP u) (genotypeList P hP v) raw = immigrant k i raw :=
          propext ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx, hy, h⟩⟩
        have hd : d u = 1 := if_pos hU
        have hd' : d v = 1 := if_pos hV
        rw [hd, hd', mul_one, mul_one]
        simp_rw [he]
        exact crossed_immigrant hn hkn i (P u) (P v) (hP u) (hP v) hU
      · simpa only [d, indicator, if_neg hV, mul_zero] using
          mean_nonneg (pairMutation (P u) (P v) (1 / (n : ℝ))) (fun raw ↦
            indic_nonneg (crossImmigrant i (genotypeList P hP u) (genotypeList P hP v) raw))
    · simpa only [d, indicator, if_neg hU, mul_zero, zero_mul] using
        mean_nonneg (pairMutation (P u) (P v) (1 / (n : ℝ))) (fun raw ↦
          indic_nonneg (crossImmigrant i (genotypeList P hP u) (genotypeList P hP v) raw))
  have hh := mean_mono ν (fun u ↦ mean_mono ν (h u))
  simp only [mean_mul] at hh
  have he : mean ν d = 1 - frequency k i P := resident_frequency k P i
  rw [he, show (fun u ↦ b * d u * (1 - frequency k i P)) =
      (fun u ↦ (b * (1 - frequency k i P)) * d u) by funext u; ring, mean_mul, he] at hh
  simpa only [mateMean, b, pow_two, mul_assoc] using hh

lemma mateMean_mutant_upper (hn : 2 ≤ n) (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P) :
    mateMean P hP (fun _ _ z ↦ indicator (z i = 1)) ≤ 2 * frequency k i P + 1 / n := by
  unfold mateMean
  have h := mean_mono (PMF.uniformOfFintype (Fin μ)) (fun u ↦
    mean_mono (PMF.uniformOfFintype (Fin μ)) (fun v ↦ cross_mutant_row hn i (P u) (P v)))
  simp only [mean_add, mean_const] at h
  rw [mutation_frequency k P i] at h
  exact h.trans_eq (by ring)

lemma crossover_drift_lower (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (i : Fin n) (H : ℕ) (hH : 0 < H)
    (T : ℝ) (hT : eps μ * H = T) (hsmall : 48 * remainderLimit T * eps μ * T ≤ 1)
    (P : Population n μ) (hP : plateau (k := k) P)
    (hf : frequency k i P < 1)
    (hf₁ : 24 * T * Real.exp (6 * T) * frequency k i P ≤ Real.exp (-2 * T) / 2)
    (hf₂ : (Real.exp (-2 * T) / 2 + 2 * responseLimit T) * frequency k i P ≤ Real.exp (-2 * T) / 4)
    (hg : 3 * frequency k i P ≤ fraction i (predict (replaceKernel i) (eps μ) H (empiricalWeights P hP))) :
    let f := frequency k i P
    let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
    coeff μ * (f / T + (Real.exp (-2 * T) / 4) * (immigrationRate k / n) * (1 - f) ^ 2) -
      R * (4 * f + 1 / n) ≤ crossed k P (replaceMean k i H P) := by
  let f := frequency k i P
  let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
  let A := Real.exp (-2 * T) / 4
  let C := coeff μ
  let J := rawContrast k i H P hP
  let W := replaceMean k i H P
  let I (x y : Genotype n k) (z : BitString n) := indicator (crossImmigrant i x y z)
  let S (x y : Genotype n k) (z : BitString n) := if (proposal i x y z).isSome then J z else 0
  have hT0 := (mul_nonneg (eps_bounds μ).1.le (Nat.cast_nonneg H)).trans hT.le
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (coeff_bounds μ).1
  have hA : 0 ≤ A := by unfold A; positivity
  have hf0 : 0 ≤ f := by
    change 0 ≤ frequency k i P
    rw [← empirical_fraction i P hP]
    exact (fraction_bounds i _ (empirical_probability P hP)).1
  have hpoint (x y : Genotype n k) (z : BitString n) :
      C * (S x y z + A * I x y z) - R * (2 * f + indicator (z i = 1)) ≤ indicator ((zeros z).card = k) * W z := by
    have hr : 0 ≤ R * (2 * f + indicator (z i = 1)) := mul_nonneg hR
      (add_nonneg (mul_nonneg (by norm_num) hf0) (indic_nonneg _))
    by_cases hz : (zeros z).card = k
    · have hh := (replaceMean_lower i H hH T hT.le P hP z hz).2
      change C * J z - R * (2 * f + indicator (z i = 1)) ≤ W z at hh
      rw [show indicator ((zeros z).card = k) = 1 from if_pos hz, one_mul]
      by_cases hx : x ∉ mutants i ∧ y ∉ mutants i ∧ z i = 1
      · have h := contrast_immigrant_lower hn i H hH T hT.le P hP z hz hx.2.2 hf hf₁ hf₂
        have h' := mul_le_mul_of_nonneg_left h hC
        have hS : S x y z = 0 := by simp only [S, proposal, dif_pos hz, if_pos hx,
          Option.isSome_none, Bool.false_eq_true, if_false]
        have hI : I x y z = 1 := if_pos (show crossImmigrant i x y z from ⟨hx.1, hx.2.1, hz, hx.2.2⟩)
        rw [hS, hI, mul_one, zero_add]
        exact (sub_le_sub_right h' _).trans hh
      · have hi : ¬ crossImmigrant i x y z := fun h ↦ hx ⟨h.1, h.2.1, h.2.2.2⟩
        simpa only [S, proposal, dif_pos hz, if_neg hx, Option.isSome_some, if_true, I, indicator,
          if_neg hi, mul_zero, add_zero] using hh
    · have hi : ¬ crossImmigrant i x y z := fun h ↦ hz h.2.2.1
      simp only [S, proposal, dif_neg hz, Option.isSome_none, Bool.false_eq_true, if_false, I, indicator,
        if_neg hi, mul_zero, add_zero, zero_mul, zero_sub, if_neg hz]
      exact neg_nonpos.mpr hr
  have hm := mateMean_mono P hP _ _ hpoint
  rw [mateMean_sub, mateMean_mul, mateMean_add, mateMean_mul, mateMean_mul, mateMean_add, mateMean_const] at hm
  have hphys : mateMean P hP (fun _ _ z ↦ indicator ((zeros z).card = k) * W z) = crossed k P W := by
    rw [crossed_as_pairs]
    rfl
  rw [hphys] at hm
  have hp := predictedContrast_lower i H hH T hT hsmall P hP hg
  have hi := mateMean_immigrant hn hkn i P hP
  have hr := mateMean_mutant_upper hn i P hP
  change f / T ≤ mateMean P hP S at hp
  change immigrationRate k / (n : ℝ) * (1 - f) ^ 2 ≤ mateMean P hP I at hi
  have hJ := mul_le_mul_of_nonneg_left (add_le_add hp (mul_le_mul_of_nonneg_left hi hA)) hC
  have hZ := mul_le_mul_of_nonneg_left (add_le_add_left hr (2 * f)) hR
  change C * (f / T + A * (immigrationRate k / n) * (1 - f) ^ 2) - R * (4 * f + 1 / n) ≤ crossed k P W
  change R * ((mateMean P hP fun _ _ z ↦ indicator (z i = 1)) + 2 * f) ≤ R * (2 * f + 1 / n + 2 * f) at hZ
  linarith only [hm, hJ, hZ]

end
end Lax637351Proofs.ColumnCrossDrift
