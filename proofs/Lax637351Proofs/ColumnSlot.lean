import Lax637351Proofs.ColumnGradient

namespace Lax637351Proofs.ColumnSlot

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ColumnMixture Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnGradient
open Lax637351Proofs.PlateauKernel Lax637351Proofs.Auxiliary
open Lax637351Proofs.SpeciesDrift (genotypeList)
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def eps (μ : ℕ+) : ℝ := 1 / (((μ : ℕ) : ℝ) + 1)

lemma eps_bounds (μ : ℕ+) : 0 < eps μ ∧ eps μ ≤ 1 / 2 := by
  have h : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  unfold eps
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (by linarith only [h])⟩

def coeff (μ : ℕ+) : ℝ := ((μ : ℕ) : ℝ) * eps μ

lemma coeff_bounds (μ : ℕ+) : (1 / 2 : ℝ) ≤ coeff μ ∧ coeff μ ≤ 1 := by
  have h : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hp : (0 : ℝ) < ((μ : ℕ) : ℝ) + 1 := by positivity
  unfold coeff eps
  rw [mul_one_div]
  constructor
  · exact (le_div_iff₀ hp).mpr (by linarith only [h])
  · exact (div_le_one hp).mpr (by linarith)

def populationPotential (k : ℕ) (i : Fin n) (H : ℕ) (P : Population n μ) : ℝ :=
  if hP : plateau (k := k) P then
    ((μ : ℕ) : ℝ) * meanPotential i (eps μ) H (empiricalWeights P hP)
  else 0

def frequency (_k : ℕ) (i : Fin n) (P : Population n μ) : ℝ :=
  slotMean (fun x ↦ indicator (x i = 1)) P

lemma empirical_fraction (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P) :
    fraction i (empiricalWeights P hP) = frequency k i P := by
  let L : PredictionMeasure.Weights (Genotype n k) →ₗ[ℝ] ℝ :=
    { toFun := fraction i
      map_add' := fraction_add i
      map_smul' := fraction_smul i }
  change L (empiricalWeights P hP) = _
  rw [empirical_apply_linear]
  unfold frequency slotMean
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change fraction i (atom (genotypeList P hP j)) = indicator (P j i = 1)
  rw [atom_fraction]
  congr 1
  change (toString (genotypeList P hP j) i = 1) = (P j i = 1)
  rw [show toString (genotypeList P hP j) = P j from toString_ofString (P j) (hP j)]

lemma population_bounds (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) :
    Real.exp (-2 * T) * ((μ : ℕ) : ℝ) * frequency k i P ≤ populationPotential k i H P ∧
      populationPotential k i H P ≤ Real.exp (2 * T) * ((μ : ℕ) : ℝ) * frequency k i P := by
  have he := eps_bounds μ
  have hh := meanPotential_bounds i (eps μ) ⟨he.1.le, he.2⟩ H hH T hT _ (empirical_probability P hP)
  rw [empirical_fraction i P hP] at hh
  rw [populationPotential, dif_pos hP]
  have hm : (0 : ℝ) ≤ (μ : ℕ) := by positivity
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hh.1 hm]
  · nlinarith only [mul_le_mul_of_nonneg_left hh.2 hm]

lemma replacement_error (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) (z : BitString n) (hz : (zeros z).card = k)
    (d : Fin μ) (hQ : plateau (k := k) (Function.update P d z)) :
    let w := empiricalWeights P hP
    let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
    let j := meanResponse i (eps μ) H w (atom (ofString z hz) - atom (genotypeList P hP d))
    let Δ := populationPotential k i H (Function.update P d z) - populationPotential k i H P
    |Δ - j| ≤ R ∧
      (z i = 0 → P d i = 0 → |Δ - j| ≤ fraction i w * R) := by
  let w := empiricalWeights P hP
  let Q := Function.update P d z
  let v := empiricalWeights Q hQ
  let e := eps μ
  let m : ℝ := (μ : ℕ)
  let x := ofString z hz
  let y := genotypeList P hP d
  let L := meanResponse i e H w
  let V := meanPotential (k := k) i e H
  let R := 4 * remainderLimit T / m
  let Δ := populationPotential k i H Q - populationPotential k i H P
  have hm : 0 < m := by unfold m; exact_mod_cast μ.pos
  have he := eps_bounds μ
  have he' : 0 ≤ e ∧ e ≤ 1 := ⟨he.1.le, by linarith [he.2]⟩
  have hT0 : 0 ≤ T := (mul_nonneg he.1.le (Nat.cast_nonneg H)).trans hT
  have hR : 0 ≤ remainderLimit T := by unfold remainderLimit normLimit; positivity
  have hw := empirical_probability P hP
  have hv := empirical_probability Q hQ
  have hδ : v - w = (1 / m) • (atom x - atom y) := empirical_replace P hP z hz d hQ
  have hnorm : variation (v - w) ≤ 2 / m := by
    rw [hδ, variation_smul, abs_of_nonneg (by positivity)]
    apply (mul_le_mul_of_nonneg_left (variation_atom_diff x y) (by positivity : 0 ≤ 1 / m)).trans_eq
    ring
  have heq : Δ - L (atom x - atom y) = m * (V v - V w - L (v - w)) := by
    unfold Δ populationPotential
    rw [dif_pos hQ, dif_pos hP]
    change m * V v - m * V w - L (atom x - atom y) = _
    rw [hδ, show L ((1 / m) • (atom x - atom y)) = (1 / m) * L (atom x - atom y) from meanResponse_smul _ _ _ _ _ _]
    field_simp
  have heq' : |Δ - L (atom x - atom y)| = m * |V v - V w - L (v - w)| := by
    rw [heq, abs_mul, abs_of_nonneg hm.le]
  have hn := (pow_le_pow_left₀ (variation_nonneg (v - w)) hnorm 2)
  have hs := mul_le_mul_of_nonneg_left hn hR
  have hA : |V v - V w - L (v - w)| ≤ 4 * remainderLimit T / m ^ 2 := by
    apply (meanPotential_remainder i e he' H hH T hT 0 (by norm_num) w v hw hv (by simp) (by simp)).trans
    simp only [fractionScale, if_true, one_mul, weighted, zero_mul, add_zero]
    exact hs.trans_eq (by ring)
  change |Δ - L (atom x - atom y)| ≤ R ∧
    (z i = 0 → P d i = 0 → |Δ - L (atom x - atom y)| ≤ fraction i w * R)
  constructor
  · rw [heq']
    exact (mul_le_mul_of_nonneg_left hA hm.le).trans_eq (by unfold R; field_simp)
  · intro hx hy
    have hx' : x ∉ mutants i := by
      change ¬toString (ofString z hz) i = 1
      rw [toString_ofString, hx]
      exact Fin.zero_ne_one
    have hy' : y ∉ mutants i := by
      change ¬toString (ofString (P d) (hP d)) i = 1
      rw [toString_ofString, hy]
      exact Fin.zero_ne_one
    have hproj : project (mutants i) (v - w) = 0 := by
      rw [hδ, project_smul, projection_resident_replacement i x y hx' hy', smul_zero]
    have hB := remainder_resident i e he' H hH T hT w v hw hv hproj
    have hB' := hB.trans (mul_le_mul_of_nonneg_left (hs.trans_eq (by ring : remainderLimit T * (2 / m) ^ 2 = 4 * remainderLimit T / m ^ 2))
      (fraction_bounds i w hw).1)
    rw [heq']
    exact (mul_le_mul_of_nonneg_left hB' hm.le).trans_eq (by unfold R; field_simp)

end
end Lax637351Proofs.ColumnSlot
