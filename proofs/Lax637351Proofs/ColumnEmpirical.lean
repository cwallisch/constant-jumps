import Lax637351Proofs.ColumnAverages
import Lax637351Proofs.SpeciesEntry

namespace Lax637351Proofs.ColumnEmpirical

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnPrediction
open Lax637351Proofs.SpeciesDrift (genotypeList)
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def empiricalWeights (P : Population n μ) (hP : plateau (k := k) P) :
    PredictionMeasure.Weights (Genotype n k) :=
  density (EmpiricalKernels.empirical (genotypeList P hP))

lemma empirical_probability (P : Population n μ) (hP : plateau (k := k) P) :
    probability (empiricalWeights P hP) := probability_density _

lemma empirical_mean (P : Population n μ) (hP : plateau (k := k) P) (x : Genotype n k) :
    empiricalWeights P hP x =
      (1 / ((μ : ℕ) : ℝ)) * ∑ i : Fin μ, atom (genotypeList P hP i) x := by
  let π := EmpiricalKernels.empirical (genotypeList P hP)
  have h := OffspringEstimates.FiniteComparison.mean_pick π x 1
  dsimp only [π] at h
  rw [EmpiricalKernels.empirical, OffspringEstimates.FiniteComparison.mean_map,
    OffspringEstimates.FiniteComparison.mean_uniform] at h
  have hn : (Fintype.card (Fin μ) : ℝ) = (μ : ℕ) := by simp
  rw [hn, mul_one] at h
  change ((PMF.uniformOfFintype (Fin μ)).map (genotypeList P hP) x).toReal = _
  rw [← h, one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : genotypeList P hP i = x <;> simp [atom, he]

lemma empirical_apply_linear (P : Population n μ) (hP : plateau (k := k) P)
    (L : PredictionMeasure.Weights (Genotype n k) →ₗ[ℝ] ℝ) :
    L (empiricalWeights P hP) = (∑ i : Fin μ, L (atom (genotypeList P hP i))) / ((μ : ℕ) : ℝ) := by
  have hvec : empiricalWeights P hP = (1 / ((μ : ℕ) : ℝ)) • ∑ i : Fin μ, atom (genotypeList P hP i) := by
    funext x
    rw [empirical_mean]
    simp [Pi.smul_apply, Finset.sum_apply]
  rw [hvec, map_smul, map_sum]
  simp [smul_eq_mul, div_eq_inv_mul]

def rawGradient (L : PredictionMeasure.Weights (Genotype n k) →ₗ[ℝ] ℝ) (x : BitString n) : ℝ :=
  if h : (zeros x).card = k then L (atom (ofString x h)) else 0

lemma rawGradient_of_plateau (L : PredictionMeasure.Weights (Genotype n k) →ₗ[ℝ] ℝ)
    (x : BitString n) (hx : (zeros x).card = k) :
    rawGradient L x = L (atom (ofString x hx)) := by simp [rawGradient, hx]

lemma empirical_slot (P : Population n μ) (hP : plateau (k := k) P)
    (L : PredictionMeasure.Weights (Genotype n k) →ₗ[ℝ] ℝ) :
    L (empiricalWeights P hP) = slotMean (rawGradient L) P := by
  rw [empirical_apply_linear, slotMean]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [rawGradient_of_plateau L (P i) (hP i)]
  rfl

lemma empirical_replace (P : Population n μ) (hP : plateau (k := k) P)
    (z : BitString n) (hz : (zeros z).card = k) (d : Fin μ)
    (hQ : plateau (k := k) (Function.update P d z)) :
    empiricalWeights (Function.update P d z) hQ - empiricalWeights P hP =
      (1 / ((μ : ℕ) : ℝ)) • (atom (ofString z hz) - atom (genotypeList P hP d)) := by
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, empirical_mean, ← mul_sub]
  congr 1
  have hY : genotypeList (Function.update P d z) hQ = Function.update (genotypeList P hP) d (ofString z hz) := by
    funext i
    by_cases hi : i = d
    · subst i
      rw [Function.update_self]
      apply Subtype.ext
      simp [genotypeList, ofString]
    · rw [Function.update_of_ne hi]
      apply Subtype.ext
      simp [genotypeList, ofString, Function.update_of_ne hi]
  rw [hY]
  have he := PairAveraging.sum_update (genotypeList P hP) d (ofString z hz) (fun y : Genotype n k ↦ atom y x)
  rw [he]

def responseMap (i : Fin n) (e : ℝ) (H : ℕ) (w : PredictionMeasure.Weights (Genotype n k)) :
    PredictionMeasure.Weights (Genotype n k) →ₗ[ℝ] ℝ where
  toFun := meanResponse i e H w
  map_add' := meanResponse_add i e H w
  map_smul' c y := meanResponse_smul i e H w y c

lemma empirical_delta_gradient (i : Fin n) (e : ℝ) (H : ℕ) (P Q : Population n μ)
    (hP : plateau (k := k) P) (hQ : plateau (k := k) Q) :
    meanResponse i e H (empiricalWeights P hP) (empiricalWeights Q hQ - empiricalWeights P hP) =
      slotMean (rawGradient (responseMap i e H (empiricalWeights P hP))) Q -
        slotMean (rawGradient (responseMap i e H (empiricalWeights P hP))) P := by
  change responseMap i e H (empiricalWeights P hP) (empiricalWeights Q hQ - empiricalWeights P hP) = _
  rw [map_sub, empirical_slot Q hQ, empirical_slot P hP]

lemma atom_fraction (i : Fin n) (x : Genotype n k) :
    fraction i (atom x) = indicator (x ∈ mutants i) := by
  unfold fraction mass
  rw [Finset.sum_eq_single x]
  · by_cases hx : x ∈ mutants i <;> simp [project, atom, indicator, hx]
  · intro y _ hy
    by_cases h : y ∈ mutants i <;> simp [project, atom, h, Ne.symm hy]
  · simp

end
end Lax637351Proofs.ColumnEmpirical
