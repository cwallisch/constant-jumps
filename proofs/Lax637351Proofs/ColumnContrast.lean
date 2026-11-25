import Lax637351Proofs.ColumnEvents

namespace Lax637351Proofs.ColumnContrast

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnGradient Lax637351Proofs.ColumnSlot
open Lax637351Proofs.PlateauKernel Lax637351Proofs.Auxiliary
open Lax637351Proofs.SpeciesDrift (genotypeList)
open Lax637351Proofs.ColumnReplacement
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma contrast_by_slot (i : Fin n) (H : ℕ) (P : Population n μ) (hP : plateau (k := k) P)
    (z : BitString n) (hz : (zeros z).card = k) :
    rawContrast k i H P hP z = mean (PMF.uniformOfFintype (Fin μ)) (fun d ↦
      meanResponse i (eps μ) H (empiricalWeights P hP) (atom (ofString z hz) - atom (genotypeList P hP d))) := by
  let w := empiricalWeights P hP
  let L := responseMap i (eps μ) H w
  let g := rawGradient L
  have he (d : Fin μ) : meanResponse i (eps μ) H w (atom (ofString z hz) - atom (genotypeList P hP d)) =
      g z - g (P d) := by
    change L (atom (ofString z hz) - atom (genotypeList P hP d)) = _
    rw [map_sub, show g z = _ from rawGradient_of_plateau L z hz,
       show g (P d) = _ from rawGradient_of_plateau L (P d) (hP d)]
    rfl
  change g z - slotMean g P = _
  rw [funext he, mean_sub, mean_const, ← slotMean_eq]

lemma gradient_atom_diff (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (x y : Genotype n k) :
    |meanResponse i (eps μ) H w (atom x - atom y)| ≤ 2 * responseLimit T := by
  have h := eps_bounds μ
  have hh := meanResponse_bound i (eps μ) ⟨h.1.le, by linarith [h.2]⟩ H hH T hT 0 (by norm_num) w
    (atom x - atom y) hw (by simp)
  simp only [fractionScale, if_true, one_mul, weighted, zero_mul, add_zero] at hh
  exact hh.trans (by
    rw [mul_comm 2]
    exact mul_le_mul_of_nonneg_left (variation_atom_diff x y) (Real.exp_pos _).le)

lemma contrast_lower (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) (z : BitString n) (hz : (zeros z).card = k) :
    -(2 * responseLimit T) ≤ rawContrast k i H P hP z := by
  rw [contrast_by_slot i H P hP z hz]
  apply mean_uniform_lower
  intro d
  exact (abs_le.mp (gradient_atom_diff i H hH T hT _ (empirical_probability P hP) (ofString z hz)
    (genotypeList P hP d))).1

lemma contrast_resident_lower (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) (z : BitString n) (hz : (zeros z).card = k)
    (hz0 : z i = 0) :
    -(4 * responseLimit T * frequency k i P) ≤ rawContrast k i H P hP z := by
  let w := empiricalWeights P hP
  let f := frequency k i P
  let C := responseLimit T
  let ν := PMF.uniformOfFintype (Fin μ)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hf : 0 ≤ f := by
    change 0 ≤ frequency k i P
    rw [← empirical_fraction i P hP]
    exact (fraction_bounds i w (empirical_probability P hP)).1
  have h (d : Fin μ) : -(2 * C * f) - (2 * C) * indicator (P d i = 1) ≤
      meanResponse i (eps μ) H w (atom (ofString z hz) - atom (genotypeList P hP d)) := by
    by_cases hd : P d i = 0
    · have hx : ofString z hz ∉ mutants i := by
        change ¬toString (ofString z hz) i = 1
        rw [toString_ofString, hz0]
        exact Fin.zero_ne_one
      have hy : genotypeList P hP d ∉ mutants i := by
        change ¬toString (ofString (P d) (hP d)) i = 1
        rw [toString_ofString, hd]
        exact Fin.zero_ne_one
      have he := eps_bounds μ
      have hB := meanResponse_resident i (eps μ) ⟨he.1.le, by linarith [he.2]⟩ H hH T hT w _
        (empirical_probability P hP) (projection_resident_replacement i _ _ hx hy)
      have hA := mul_le_mul_of_nonneg_left (variation_atom_diff (ofString z hz) (genotypeList P hP d)) hC
      have hA' := mul_le_mul_of_nonneg_left hA hf
      have hB' := (abs_le.mp hB).1
      rw [show fraction i w = f from empirical_fraction i P hP] at hB'
      simp only [indicator, hd, Fin.zero_ne_one, if_false, mul_zero, sub_zero]
      nlinarith only [hA', hB']
    · rw [show indicator (P d i = 1) = 1 from if_pos (bit_eq_one_of_ne_zero _ hd), mul_one]
      have hA := (abs_le.mp (gradient_atom_diff i H hH T hT w (empirical_probability P hP) (ofString z hz)
        (genotypeList P hP d))).1
      have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hf
      nlinarith only [hA, hh]
  have hh := mean_mono ν h
  rw [mean_sub, mean_const, mean_mul] at hh
  rw [contrast_by_slot i H P hP z hz]
  change _ ≤ mean ν _
  rw [show mean ν (fun d ↦ indicator (P d i = 1)) = f from (slotMean_eq (fun z : BitString n ↦ indicator (z i = 1)) P).symm] at hh
  nlinarith only [hh]

lemma contrast_immigrant_lower (hn : 2 ≤ n) (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) (z : BitString n) (hz : (zeros z).card = k)
    (hz1 : z i = 1) (hf : frequency k i P < 1)
    (hf₁ : 24 * T * Real.exp (6 * T) * frequency k i P ≤ Real.exp (-2 * T) / 2)
    (hf₂ : (Real.exp (-2 * T) / 2 + 2 * responseLimit T) * frequency k i P ≤ Real.exp (-2 * T) / 4) :
    Real.exp (-2 * T) / 4 ≤ rawContrast k i H P hP z := by
  let w := empiricalWeights P hP
  let ν := PMF.uniformOfFintype (Fin μ)
  let A := Real.exp (-2 * T) / 2
  let B := 2 * responseLimit T
  let f := frequency k i P
  have h (d : Fin μ) : A - (A + B) * indicator (P d i = 1) ≤
      meanResponse i (eps μ) H w (atom (ofString z hz) - atom (genotypeList P hP d)) := by
    by_cases hd : P d i = 0
    · have hx : ofString z hz ∈ mutants i := by
        change toString (ofString z hz) i = 1
        rw [toString_ofString, hz1]
      have hy : genotypeList P hP d ∉ mutants i := by
        change ¬toString (ofString (P d) (hP d)) i = 1
        rw [toString_ofString, hd]
        exact Fin.zero_ne_one
      rw [show indicator (P d i = 1) = 0 by simp [indicator, hd], mul_zero, sub_zero]
      exact meanResponse_immigrant hn i (eps μ) ⟨(eps_bounds μ).1.le, (eps_bounds μ).2⟩ H hH T hT w
        (empirical_probability P hP) (by rwa [empirical_fraction i P hP]) (by rwa [empirical_fraction i P hP]) _ _ hx hy
    · rw [show indicator (P d i = 1) = 1 from if_pos (bit_eq_one_of_ne_zero _ hd), mul_one]
      have he := (abs_le.mp (gradient_atom_diff i H hH T hT w (empirical_probability P hP) (ofString z hz)
        (genotypeList P hP d))).1
      change -B ≤ _ at he
      linarith only [he]
  have hh := mean_mono ν h
  rw [mean_sub, mean_const, mean_mul] at hh
  rw [contrast_by_slot i H P hP z hz]
  change _ ≤ mean ν _
  rw [show mean ν (fun d ↦ indicator (P d i = 1)) = f from (slotMean_eq (fun z : BitString n ↦ indicator (z i = 1)) P).symm] at hh
  change (A + B) * f ≤ Real.exp (-2 * T) / 4 at hf₂
  change A - (A + B) * f ≤ mean ν _ at hh
  dsimp [A] at *
  linarith only [hh, hf₂]

end
end Lax637351Proofs.ColumnContrast
