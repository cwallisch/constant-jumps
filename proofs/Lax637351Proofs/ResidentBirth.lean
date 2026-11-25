import Lax637351Proofs.ResidentScore

namespace Lax637351Proofs.ResidentBirth

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.OffspringProduct
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnClasses
open Lax637351Proofs.ColumnEvolution Lax637351Proofs.ResidentScore Lax637351Proofs.OffspringBridge
open OffspringEstimates.ActualBirthKernels OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma columnZero (i : Fin n) (x : Genotype n k) (hx : x ∉ mutants i) : toString x i = 0 := by
  by_contra h
  exact hx (bit_eq_one_of_ne_zero _ h)

lemma resident_flip_rate (hn : 2 ≤ n) (i : Fin n) (x y : Genotype n k) (hx : x ∉ mutants i) (hy : y ∉ mutants i) :
    mean (pairMutation (toString x) (toString y) (1 / n)) (fun z ↦ if z i = 1 then 1 else 0) = 1 / n := by
  rw [breed_eq]
  have hr := Lax637351Proofs.Mutation.rate_valid hn
  change OffspringEstimates.FiniteDrift.mean _ _ = _
  rw [pairMutation_class_mass _ _ _ hr, columnZero i x hx, columnZero i y hy,
    PhysicalOffspring.siteLaw_apply _ _ _ _ hr]
  simp [PhysicalOffspring.siteProbability]

lemma mean_birth_weight (i : Fin n) (B x y : Genotype n k) :
    (∑ u, birthMass i x y u * W B u) =
      mean (pairMutation (toString x) (toString y) (1 / n)) (fun raw ↦
        ((proposal i x y raw).map (W B)).getD 0) := by
  let p := pairMutation (toString x) (toString y) (1 / n)
  let q := p.map (proposal i x y)
  have h := mean_map p (proposal i x y) (fun o ↦ (o.map (W B)).getD 0)
  rw [← h]
  unfold mean
  rw [Fintype.sum_option]
  simp only [Option.map_none, Option.getD_none, mul_zero, zero_add, Option.map_some, Option.getD_some]
  rfl

lemma weighted_birth_row (hn : 2 ≤ n) (hkn : k ≤ n) (i : Fin n) (B x y : Genotype n k)
    (hx : x ∉ mutants i) (hy : y ∉ mutants i) :
    weightedBirth B x y - 5 / (4 * (n : ℝ)) ≤ ∑ u, birthMass i x y u * W B u := by
  let p := pairMutation (toString x) (toString y) (1 / (n : ℝ))
  let f (raw : BitString n) := ((proposal i x y raw).map (W B)).getD 0
  have h (raw : BitString n) :
      acceptedWeight B raw ≤ f raw + 5 / 4 * (if raw i = 1 then 1 else 0) := by
    by_cases hp : (zeros raw).card = k
    · have hO := (old_onPlateau hkn raw).mpr hp
      have hp' : (OffspringEstimates.Sampling.zeros raw).card = k := hp
      have hconnect : W B (ofString raw hp') = weightFunction B raw := by
        unfold W
        rw [← weightFunction_toString, toString_ofString raw hp']
      have he : acceptedWeight B raw = weightFunction B raw := by
        simp [acceptedWeight, weightFunction, hO]
      by_cases hbit : raw i = 1
      · have hh : f raw = 0 := by simp [f, proposal, hx, hy, hp, hbit]
        rw [hh, if_pos hbit, he, mul_one, zero_add]
        exact (weightFunction_bounds B raw).2
      · have hh : f raw = weightFunction B raw := by simp [f, proposal, hx, hy, hp, hbit, hconnect]
        simp [hbit, he, hh]
    · have hO : ¬ PlateauDynamics.onPlateau k raw := fun h ↦ hp ((old_onPlateau hkn raw).mp h)
      have hf : f raw = 0 := by simp [f, proposal, hp]
      simp only [acceptedWeight, if_neg hO, hf, zero_add]
      split_ifs <;> norm_num
  have hm := mean_mono p h
  rw [mean_add, mean_mul, resident_flip_rate hn i x y hx hy] at hm
  rw [mean_birth_weight i B x y]
  change weightedBirth B x y - _ ≤ mean p f
  have hEq : mean p (acceptedWeight B) = weightedBirth B x y := by
    unfold weightedBirth p
    rw [breed_eq]
    rfl
  rw [hEq] at hm
  linarith only [hm, show (5 / 4 : ℝ) * (1 / (n : ℝ)) = 5 / (4 * (n : ℝ)) by ring]

lemma weighted_birth_law (hn : 2 ≤ n) (hkn : k ≤ n) (i : Fin n) (B : Genotype n k)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) :
    EmpiricalKernels.pairMean (asPMF w hw) (weightedBirth B) - 5 / (4 * (n : ℝ)) ≤
      weightedMass B (births i w w) := by
  let ν := asPMF w hw
  have hν (x : Genotype n k) : (ν x).toReal = w x := congrFun (asPMF_density w hw) x
  have h (x y : Genotype n k) :
      w x * w y * (weightedBirth B x y - 5 / (4 * (n : ℝ))) ≤
        w x * w y * ∑ z, birthMass i x y z * W B z := by
    by_cases hx : x ∈ mutants i
    · simp [hR x hx]
    by_cases hy : y ∈ mutants i
    · simp [hR y hy]
    exact mul_le_mul_of_nonneg_left (weighted_birth_row hn hkn i B x y hx hy) (mul_nonneg (hw.1 x) (hw.1 y))
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦
    Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) ↦ h x y))
  have hg (x : Genotype n k) : ∑ y, w x * w y = w x := by
    rw [← Finset.mul_sum, show ∑ y, w y = 1 from hw.2, mul_one]
  have hg' : ∑ x, ∑ y, w x * w y = 1 := by simpa only [hg] using (show ∑ x, w x = 1 from hw.2)
  have hleft : (∑ x, ∑ y, w x * w y * weightedBirth B x y) =
      EmpiricalKernels.pairMean ν (weightedBirth B) := by
    unfold EmpiricalKernels.pairMean OffspringEstimates.FiniteDrift.mean
    simp only [hν, Finset.mul_sum, mul_assoc]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hleft, hg', one_mul] at hsum
  apply hsum.trans_eq
  unfold weightedMass births
  simp only [Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma clone_birth_law (i : Fin n) (B : Genotype n k) (hB : B ∉ mutants i)
    (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    births i w w B = EmpiricalKernels.pairMean (asPMF w hw) (cloneBirth B) := by
  unfold births EmpiricalKernels.pairMean OffspringEstimates.FiniteDrift.mean
  simp only [show ∀ x : Genotype n k, ((asPMF w hw) x).toReal = w x from congrFun (asPMF_density w hw),
    Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [birthMass_exact i x y B (fun h ↦ hB h.2.2), breed_eq, AnchorMutation.cloneBirth_mass]

end
end Lax637351Proofs.ResidentBirth
