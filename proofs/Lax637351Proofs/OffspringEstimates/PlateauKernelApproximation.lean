import Lax637351Proofs.OffspringEstimates.IdealCountKernel
import Lax637351Proofs.OffspringEstimates.Genotypes

namespace Lax637351Proofs.OffspringEstimates.PlateauKernelApproximation

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.Sampling Lax637351Proofs.OffspringEstimates.PhysicalOffspring
open Lax637351Proofs.OffspringEstimates.RegionGeometry Lax637351Proofs.OffspringEstimates.PlateauDynamics
open Lax637351Proofs.OffspringEstimates.FiniteDrift Lax637351Proofs.OffspringEstimates.PlateauApproximation
open Lax637351Proofs.OffspringEstimates.IdealCountKernel Lax637351Proofs.OffspringEstimates.IdealKernel
open Lax637351Proofs.OffspringEstimates.Genotypes Lax637351Proofs.OffspringEstimates.Weights Lax637351Proofs.OffspringEstimates.WeightSums
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def approximationError (n k : ℕ) : ℝ :=
  (4 * (k : ℝ) + 3 * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1)) / n

lemma plateau_of_zero_card {n k : ℕ} (hk : k ≤ n) (B : BitString n)
    (hB : (zeros B).card = k) : onPlateau k B := by
  rw [card_zeros] at hB
  have hle := Lax637351Proofs.OffspringEstimates.Dynamics.ones_le B
  unfold onPlateau
  omega

lemma geometry_ideal_weight {n k : ℕ} (B x y : BitString n)
    (hB : (zeros B).card = k) (hx : (zeros x).card = k) (hy : (zeros y).card = k) :
    idealMean k (regionSize B x y 2) (regionSize B x y 5)
      (regionSize B x y 1) (regionSize B x y 3) weight =
        Real.exp (-1) * weightedKernel (ofString B hB) (ofString x hx) (ofString y hy) := by
  have hinside := inside_parent_pair_sum B x y
  have houtside := outside_parent_pair_sum B x y
  have hbalx := zero_count_balance B x
  have hbaly := zero_count_balance B y
  rw [hB, hx] at hbalx
  rw [hB, hy] at hbaly
  have ht : 2 * regionSize B x y 1 ≤ insideCount B x + insideCount B y := by omega
  have hu : 2 * regionSize B x y 3 ≤ insideCount B x + insideCount B y := by omega
  have hA : regionSize B x y 1 +
      (insideCount B x + insideCount B y - 2 * regionSize B x y 1) ≤ k := by
    rw [← differing_inside_size]
    simpa only [hB] using variable_inside_size B x y
  rw [differing_inside_size, differing_outside_size B x y (hx.trans hB.symm) (hy.trans hB.symm),
    idealMean_weight_kernel ht hu hA]
  unfold weightedKernel distance missingBoth sharedOutside ofString
  rw [anchor_missing_eq, anchor_missing_eq]
  rw [regionSize, region_one_set, regionSize, region_three_set]

lemma geometry_ideal_clone {n k : ℕ} (B x y : BitString n)
    (hB : (zeros B).card = k) (hx : (zeros x).card = k) (hy : (zeros y).card = k) :
    idealMean k (regionSize B x y 2) (regionSize B x y 5)
      (regionSize B x y 1) (regionSize B x y 3) cloneWeight =
        Real.exp (-1) * cloneKernel (ofString B hB) (ofString x hx) (ofString y hy) := by
  have hA : regionSize B x y 1 +
      (insideCount B x + insideCount B y - 2 * regionSize B x y 1) ≤ k := by
    rw [← differing_inside_size]
    simpa only [hB] using variable_inside_size B x y
  rw [differing_inside_size, differing_outside_size B x y (hx.trans hB.symm) (hy.trans hB.symm),
    idealMean_clone_kernel hA]
  unfold cloneKernel distance missingBoth sharedOutside ofString
  rw [anchor_missing_eq, anchor_missing_eq]
  rw [regionSize, region_one_set, regionSize, region_three_set]

lemma physical_weighted_kernel {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B x y : BitString n) (hB : (zeros B).card = k) (hx : (zeros x).card = k)
    (hy : (zeros y).card = k) :
    |mean (pairMutation x y (1 / n)) (fun child ↦
        if onPlateau k child then weight (insideCount B child) else 0) -
      Real.exp (-1) * weightedKernel (ofString B hB) (ofString x hx) (ofString y hy)| ≤
        (5 / 4 : ℝ) * approximationError n k := by
  have hψ : ∀ r ≤ k, |weight r| ≤ (5 / 4 : ℝ) := by
    intro r _
    rw [abs_of_nonneg (weight_nonneg r)]
    exact weight_upper r
  have h := physical_ideal_error hn hlarge B x y hB hx hy weight (5 / 4) (by norm_num) hψ
  rw [geometry_ideal_weight B x y hB hx hy] at h
  have hkn : k ≤ n := by omega
  have heq : (fun child ↦ if onPlateau k child then weight (insideCount B child) else 0) =
      (fun child ↦ balanced weight (insideCount B child) (outsideCount B child)) := by
    funext child
    rw [plateau_iff_counts hkn B child (plateau_of_zero_card hkn B hB)]
    by_cases hc : insideCount B child = outsideCount B child <;> simp [balanced, hc]
  rw [heq]
  exact h.trans_eq (by unfold approximationError; ring)

lemma physical_clone_kernel {n k : ℕ} (hn : 2 ≤ n) (hlarge : 4 * k ≤ n)
    (B x y : BitString n) (hB : (zeros B).card = k) (hx : (zeros x).card = k)
    (hy : (zeros y).card = k) :
    |mean (pairMutation x y (1 / n)) (fun child ↦
        if onPlateau k child then cloneWeight (insideCount B child) else 0) -
      Real.exp (-1) * cloneKernel (ofString B hB) (ofString x hx) (ofString y hy)| ≤
        approximationError n k := by
  have hψ : ∀ r ≤ k, |cloneWeight r| ≤ (1 : ℝ) := by
    intro r _
    unfold cloneWeight
    split_ifs <;> norm_num
  have h := physical_ideal_error hn hlarge B x y hB hx hy cloneWeight 1 (by norm_num) hψ
  rw [geometry_ideal_clone B x y hB hx hy] at h
  have hkn : k ≤ n := by omega
  have heq : (fun child ↦ if onPlateau k child then cloneWeight (insideCount B child) else 0) =
      (fun child ↦ balanced cloneWeight (insideCount B child) (outsideCount B child)) := by
    funext child
    rw [plateau_iff_counts hkn B child (plateau_of_zero_card hkn B hB)]
    by_cases hc : insideCount B child = outsideCount B child <;> simp [balanced, hc]
  rw [heq]
  exact h.trans_eq (by unfold approximationError; ring)

lemma insideCount_self {n : ℕ} (x : BitString n) : insideCount x x = 0 := by
  rw [← anchor_missing_eq]
  simp

end
end Lax637351Proofs.OffspringEstimates.PlateauKernelApproximation
