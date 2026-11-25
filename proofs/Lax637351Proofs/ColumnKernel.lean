import Lax637351Proofs.OffspringBridge
import Lax637351Proofs.OffspringProduct
import Lax637351Proofs.PredictionBounds
import Lax637351Proofs.OffspringEstimates.ShadowComparison

namespace Lax637351Proofs.ColumnKernel

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringBridge Lax637351Proofs.OffspringProduct
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def mutants (i : Fin n) : Set (Genotype n k) := {x | toString x i = 1}

def proposal (i : Fin n) (x y : Genotype n k) (raw : BitString n) : Option (Genotype n k) :=
  if h : (zeros raw).card = k then
    if x ∉ mutants i ∧ y ∉ mutants i ∧ raw i = 1 then none else some (ofString raw h)
  else none

def replaceKernel (i : Fin n) (x y z : Genotype n k) : PMF (Genotype n k) :=
  (pairMutation (toString x) (toString y) (1 / (n : ℝ))).map
    (fun raw ↦ (proposal i x y raw).getD z)

lemma breed_eq (x y : BitString n) (p : ℝ) :
    pairMutation x y p = OffspringEstimates.PhysicalOffspring.pairMutation x y p := by
  simp [pairMutation, OffspringEstimates.PhysicalOffspring.pairMutation, independent_eq]

lemma breed_comm (hn : 2 ≤ n) (x y : BitString n) :
    pairMutation x y (1 / (n : ℝ)) = pairMutation y x (1 / (n : ℝ)) := by
  ext z
  simp only [pairMutation_apply _ _ _ _ (Lax637351Proofs.Mutation.rate_valid hn)]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : x j = y j <;> simp [siteProbability, h, eq_comm]

lemma proposal_comm (i : Fin n) (x y : Genotype n k) (raw : BitString n) :
    proposal i x y raw = proposal i y x raw := by
  have h : (x ∉ mutants i ∧ y ∉ mutants i ∧ raw i = 1) ↔
      (y ∉ mutants i ∧ x ∉ mutants i ∧ raw i = 1) := by tauto
  simp [proposal, h]

lemma replace_resident (i : Fin n) (k : ℕ) : residentRule (replaceKernel (k := k) i) (mutants i) := by
  intro x y z hx hy hz u hu
  have h : ∀ raw : BitString n, (proposal i x y raw).getD z ∉ mutants i := by
    intro raw
    unfold proposal
    by_cases hp : (zeros raw).card = k
    · rw [dif_pos hp]
      by_cases hm : raw i = 1
      · rw [if_pos (show x ∉ mutants i ∧ y ∉ mutants i ∧ raw i = 1 from ⟨hx, hy, hm⟩), Option.getD_none]
        exact hz
      · rw [if_neg (show ¬ (x ∉ mutants i ∧ y ∉ mutants i ∧ raw i = 1) from fun hh ↦ hm hh.2.2)]
        change ¬ Genotypes.toString (ofString raw hp) i = 1
        simpa only [toString_ofString raw hp] using hm
    · simpa [hp] using hz
  by_contra he
  have hs : u ∈ (replaceKernel i x y z).support := (PMF.mem_support_iff _ _).mpr he
  rcases (PMF.mem_support_map_iff _ _ _).mp hs with ⟨r, _, rfl⟩
  exact h r hu

def birthMass (i : Fin n) (x y z : Genotype n k) : ℝ :=
  ((pairMutation (toString x) (toString y) (1 / (n : ℝ))).map (proposal i x y) (some z)).toReal

lemma birthMass_nonneg (i : Fin n) (x y z : Genotype n k) : 0 ≤ birthMass i x y z :=
  ENNReal.toReal_nonneg

lemma birthMass_comm (hn : 2 ≤ n) (i : Fin n) (x y z : Genotype n k) :
    birthMass i x y z = birthMass i y x z := by
  unfold birthMass
  rw [breed_comm hn]
  rw [show proposal i x y = proposal i y x from funext (proposal_comm i x y)]

lemma birthMass_exact (i : Fin n) (x y z : Genotype n k)
    (h : ¬ (x ∉ mutants i ∧ y ∉ mutants i ∧ z ∈ mutants i)) :
    birthMass i x y z = (pairMutation (toString x) (toString y) (1 / (n : ℝ)) (toString z)).toReal := by
  unfold birthMass
  congr 1
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (toString z)]
  · have hkz : (zeros (Genotypes.toString z)).card = k := by
      change (OffspringEstimates.Sampling.zeros (Genotypes.toString z)).card = k
      rw [zeros_toString]
      exact z.property
    change ¬ (x ∉ mutants i ∧ y ∉ mutants i ∧ Genotypes.toString z i = 1) at h
    simp [proposal, h, hkz, ofString_toString]
  · intro raw _ hr
    have hneq : some z ≠ proposal i x y raw := by
      unfold proposal
      split_ifs with hp hi
      · simp
      · intro he
        have hh : z = ofString raw hp := Option.some.inj he
        exact hr ((congrArg Genotypes.toString hh).trans (toString_ofString _ _)).symm
      · simp
    simp [hneq]
  · simp

lemma birthMass_rejected (i : Fin n) (x y z : Genotype n k)
    (hx : x ∉ mutants i) (hy : y ∉ mutants i) (hz : z ∈ mutants i) : birthMass i x y z = 0 := by
  unfold birthMass
  rw [PMF.map_apply, tsum_fintype]
  have h (raw : BitString n) : some z ≠ proposal i x y raw := by
    unfold proposal
    split_ifs with hr hs
    · simp
    · intro he
      have hh : z = ofString raw hr := Option.some.inj he
      have hb : raw i = 1 := by
        rw [show raw = toString z by simpa only [toString_ofString] using (congrArg Genotypes.toString hh).symm]
        exact hz
      exact hs ⟨hx, hy, hb⟩
    · simp
  simp [h]

def births (i : Fin n) (a b : Weights (Genotype n k)) : Weights (Genotype n k) :=
  fun u ↦ ∑ x, ∑ y, a x * b y * birthMass i x y u

lemma births_resident (i : Fin n) (w : Weights (Genotype n k))
    (hw : ∀ x ∈ mutants i, w x = 0) (u : Genotype n k) (hu : u ∈ mutants i) :
    births i w w u = 0 := by
  unfold births
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_cases hx : x ∈ mutants i
  · simp [hw x hx]
  by_cases hy : y ∈ mutants i
  · simp [hw y hy]
  rw [birthMass_rejected i x y u hx hy hu, mul_zero]

lemma births_comm (hn : 2 ≤ n) (i : Fin n) (a b : Weights (Genotype n k)) :
    births i a b = births i b a := by
  funext u
  unfold births
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [birthMass_comm hn i x y u, mul_comm (a y)]

end
end Lax637351Proofs.ColumnKernel
