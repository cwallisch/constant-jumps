import Lax637351Proofs.ColumnEvolution
import Lax637351Proofs.SpeciesCap

namespace Lax637351Proofs.ResidentScore

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.OffspringProduct
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnClasses
open Lax637351Proofs.ColumnEvolution Lax637351Proofs.SpeciesCap
open OffspringEstimates.ActualBirthKernels OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def W (B x : Genotype n k) : ℝ := OffspringEstimates.Weights.weight (distance B x)

def weightedMass (B : Genotype n k) (w : PredictionMeasure.Weights (Genotype n k)) : ℝ :=
  ∑ x, w x * W B x

def lawScore (B : Genotype n k) (w : PredictionMeasure.Weights (Genotype n k)) : ℝ :=
  weightedMass B w / max (w B) (1 / 2)

lemma weightedMass_add (B : Genotype n k) (w z : PredictionMeasure.Weights (Genotype n k)) :
    weightedMass B (w + z) = weightedMass B w + weightedMass B z := by
  simp [weightedMass, add_mul, Finset.sum_add_distrib]

lemma weightedMass_smul (B : Genotype n k) (w : PredictionMeasure.Weights (Genotype n k)) (a : ℝ) :
    weightedMass B (a • w) = a * weightedMass B w := by
  simp [weightedMass, mul_assoc, Finset.mul_sum]

lemma W_bounds (B x : Genotype n k) : 0 ≤ W B x ∧ W B x ≤ 5 / 4 :=
  ⟨OffspringEstimates.Weights.weight_nonneg _, OffspringEstimates.WeightSums.weight_upper _⟩

lemma weightedMass_cloud (B : Genotype n k) (w : PredictionMeasure.Weights (Genotype n k)) :
    weightedMass B w = Species.cloud B w := by
  unfold weightedMass Species.cloud Species.cloudValue W
  rw [Species.sum_split B]
  simp only [distance_self, OffspringEstimates.Weights.weight_zero, mul_zero, zero_add]

lemma weightedMass_bounds (B : Genotype n k) (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    floorWeight k * (1 - w B) ≤ weightedMass B w ∧ weightedMass B w ≤ (5 / 4 : ℝ) * (1 - w B) := by
  have he : 1 - w B = ∑ x ∈ Finset.univ.erase B, w x := by
    have h := hw.2
    rw [mass, Species.sum_split B] at h
    unfold Species.offSum at h
    linarith only [h]
  rw [weightedMass_cloud, Species.cloud, Species.cloudValue, Species.offSum, he, Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro x hx
    have hxB := (Finset.mem_erase.mp hx).1
    have h := OffspringEstimates.Weights.uniform_weight_lower (distance_pos B x hxB) (distance_le B x)
    dsimp [floorWeight, W]
    have hh := mul_le_mul_of_nonneg_left h (hw.1 x)
    simpa only [mul_comm (w x)] using hh
  · apply Finset.sum_le_sum
    intro x _
    have h := mul_le_mul_of_nonneg_left (W_bounds B x).2 (hw.1 x)
    simpa only [W, mul_comm (5 / 4 : ℝ)] using h

lemma atom_upper (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) (x : Genotype n k) :
    w x ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.univ) (fun y _ ↦ hw.1 y) (Finset.mem_univ x)
  exact h.trans_eq hw.2

lemma lawScore_bounds (B : Genotype n k) (w : PredictionMeasure.Weights (Genotype n k)) (hw : probability w) :
    floorWeight k * (1 - w B) ≤ lawScore B w ∧ lawScore B w ≤ (5 / 2 : ℝ) * (1 - w B) := by
  have hwB := atom_upper w hw B
  have hq : 0 < max (w B) (1 / 2 : ℝ) := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right _ _)
  have hq1 : max (w B) (1 / 2 : ℝ) ≤ 1 := max_le hwB (by norm_num)
  have h := weightedMass_bounds B w hw
  have hW : 0 ≤ floorWeight k := by unfold floorWeight; positivity
  unfold lawScore
  constructor
  · rw [le_div_iff₀ hq]
    exact (mul_le_of_le_one_right (mul_nonneg hW (sub_nonneg.mpr hwB)) hq1).trans h.1
  · rw [div_le_iff₀ hq]
    have h' := mul_le_mul_of_nonneg_left (le_max_right (w B) (1 / 2 : ℝ))
      (show 0 ≤ (5 / 2 : ℝ) * (1 - w B) from mul_nonneg (by norm_num) (sub_nonneg.mpr hwB))
    nlinarith only [h.2, h']

lemma weightedMass_change (B : Genotype n k) (w z : PredictionMeasure.Weights (Genotype n k)) :
    |weightedMass B w - weightedMass B z| ≤ (5 / 4 : ℝ) * variation (w - z) := by
  unfold weightedMass variation
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul, abs_mul, abs_of_nonneg (W_bounds B x).1, Pi.sub_apply, mul_comm (5 / 4 : ℝ)]
  exact mul_le_mul_of_nonneg_left (W_bounds B x).2 (abs_nonneg _)

lemma point_change (w z : PredictionMeasure.Weights (Genotype n k)) (B : Genotype n k) :
    |w B - z B| ≤ variation (w - z) := by
  exact Finset.single_le_sum (fun x _ ↦ abs_nonneg ((w - z) x)) (Finset.mem_univ B)

lemma lawScore_change (B : Genotype n k) (w z : PredictionMeasure.Weights (Genotype n k))
    (hw : probability w) (_hz : probability z) :
    |lawScore B z - lawScore B w| ≤ 8 * variation (z - w) := by
  let g (v : PredictionMeasure.Weights (Genotype n k)) := max (v B) (1 / 2 : ℝ)
  let m := weightedMass B
  have hg (v : PredictionMeasure.Weights (Genotype n k)) : (1 / 2 : ℝ) ≤ g v := le_max_right _ _
  have hg' (v : PredictionMeasure.Weights (Genotype n k)) : 0 < g v := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hg v)
  have hq (v : PredictionMeasure.Weights (Genotype n k)) : (1 : ℝ) / g v ≤ 2 :=
    (div_le_iff₀ (hg' v)).mpr (by linarith only [hg v])
  have hm : 0 ≤ m w := Finset.sum_nonneg (fun x _ ↦ mul_nonneg (hw.1 x) (W_bounds B x).1)
  have hm' : m w / g w ≤ 5 / 2 := by
    have hh := (lawScore_bounds B w hw).2
    change m w / g w ≤ _ at hh
    linarith only [hh, hw.1 B]
  have hd : |g w - g z| ≤ variation (z - w) := by
    have ht := abs_le.mp (point_change z w B)
    apply abs_le.mpr
    constructor
    · have hh : g z ≤ g w + variation (z - w) := by
        apply max_le
        · linarith only [ht.2, le_max_left (w B) (1 / 2 : ℝ)]
        · linarith only [hg w, variation_nonneg (z - w)]
      linarith only [hh]
    · have hh : g w ≤ g z + variation (z - w) := by
        apply max_le
        · linarith only [ht.1, le_max_left (z B) (1 / 2 : ℝ)]
        · linarith only [hg z, variation_nonneg (z - w)]
      linarith only [hh]
  change |m z / g z - m w / g w| ≤ _
  rw [show m z / g z - m w / g w = (1 / g z) * (m z - m w) +
      ((1 / g z) * (m w / g w)) * (g w - g z) by field_simp [(hg' _).ne']; ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg zero_le_one (hg' z).le),
    abs_of_nonneg (mul_nonneg (div_nonneg zero_le_one (hg' z).le) (div_nonneg hm (hg' w).le))]
  have h₁ := mul_le_mul (hq z) (weightedMass_change B z w) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hD := mul_le_mul (hq z) hm' (div_nonneg hm (hg' w).le) (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := mul_le_mul hD hd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * (5 / 2))
  linarith only [h₁, h₂, variation_nonneg (z - w)]

end
end Lax637351Proofs.ResidentScore
