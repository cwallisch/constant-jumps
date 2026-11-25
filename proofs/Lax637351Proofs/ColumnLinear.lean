import Lax637351Proofs.ColumnKernel

namespace Lax637351Proofs.ColumnLinear

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.FiniteDrift Lax637351Proofs.ColumnKernel Lax637351Proofs.OffspringProduct
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma redirect_mass {α : Type*} [Fintype α] (p : PMF (Option α)) (z u : α) :
    ((p.map (fun a ↦ a.getD z)) u).toReal = (p (some u)).toReal +
      (if z = u then 1 - ∑ y, (p (some y)).toReal else 0) := by
  have h := sum_mass p
  rw [Fintype.sum_option] at h
  have he : (∑ a : Option α, p a * (if u = a.getD z then 1 else 0)) =
      p (some u) + (if z = u then p none else 0) := by
    rw [Fintype.sum_option]
    norm_num only [Option.getD_none, Option.getD_some]
    rw [Finset.sum_eq_single u]
    · by_cases hz : z = u
      · subst z
        simp [add_comm]
      · simp [hz, Ne.symm hz]
    · intro v _ hv
      simp [Ne.symm hv]
    · simp
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [mul_ite, mul_one, mul_zero] at he
  rw [he, ENNReal.toReal_add (p.apply_ne_top _) (by split_ifs; exact p.apply_ne_top _; simp)]
  by_cases hz : z = u
  · rw [if_pos hz, if_pos hz]
    linarith only [h]
  · simp [hz]

lemma replacement_point (i : Fin n) (x y z u : Genotype n k) :
    density (replaceKernel i x y z) u = birthMass i x y u +
      (1 - ∑ v, birthMass i x y v) * atom z u := by
  unfold density replaceKernel birthMass atom
  change (((pairMutation (Genotypes.toString x) (Genotypes.toString y) (1 / (n : ℝ))).map
    ((fun a : Option (Genotype n k) ↦ a.getD z) ∘ proposal i x y)) u).toReal = _
  rw [← PMF.map_comp, redirect_mass]
  split_ifs <;> ring

lemma mass_smul {α : Type*} [Fintype α] (c : ℝ) (a : Weights α) :
    mass (c • a) = c * mass a := by simp [mass, Finset.mul_sum]

lemma mass_add {α : Type*} [Fintype α] (a b : Weights α) :
    mass (a + b) = mass a + mass b := by simp [mass, Finset.sum_add_distrib]

lemma mass_sub {α : Type*} [Fintype α] (a b : Weights α) :
    mass (a - b) = mass a - mass b := by simp [mass, Finset.sum_sub_distrib]

lemma mass_atom {α : Type*} [Fintype α] (x : α) : mass (atom x) = 1 := by
  unfold mass atom
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [Ne.symm hy]
  · simp

lemma birth_sum (i : Fin n) (a b : Weights (Genotype n k)) :
    mass (births i a b) = ∑ x, ∑ y, a x * b y * ∑ u, birthMass i x y u := by
  unfold births mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]

lemma transform_replacement (i : Fin n) (a b c : Weights (Genotype n k)) :
    transform (replaceKernel i) a b c =
      mass c • births i a b + (mass a * mass b - mass (births i a b)) • c := by
  funext u
  unfold transform
  simp_rw [replacement_point, mul_add, Finset.sum_add_distrib]
  have ha (x y : Genotype n k) : (∑ z, a x * b y * c z * birthMass i x y u) =
      a x * b y * birthMass i x y u * mass c := by
    rw [mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hb (x y : Genotype n k) : (∑ z,
      a x * b y * c z * ((1 - ∑ v, birthMass i x y v) * atom z u)) =
      a x * b y * c u * (1 - ∑ v, birthMass i x y v) := by
    rw [Finset.sum_eq_single u]
    · simp [atom]
    · intro z _ hz; simp [atom, hz]
    · simp
  simp_rw [ha, hb, ← Finset.sum_mul]
  have h (x y : Genotype n k) :
      a x * b y * c u * (1 - ∑ v, birthMass i x y v) =
      (a x * b y - a x * b y * ∑ v, birthMass i x y v) * c u := by ring
  simp only [h]
  simp_rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [show (∑ x, ∑ y, a x * b y) = mass a * mass b by
    simp_rw [← Finset.mul_sum]
    unfold mass
    rw [Finset.sum_mul]]
  rw [← birth_sum]
  change births i a b u * mass c + _ = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma resident_step (i : Fin n) (e : ℝ) (w : Weights (Genotype n k)) (hw : probability w) :
    update (replaceKernel i) e w =
      (1 - e * mass (births i w w)) • w + e • births i w w := by
  rw [update, transform_replacement, hw.2]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma tangent_linear (hn : 2 ≤ n) (i : Fin n) (e : ℝ) (w h : Weights (Genotype n k))
    (hw : probability w) (hh : mass h = 0) :
    tangent (replaceKernel i) e w h =
      (1 - e * mass (births i w w)) • h +
        (2 * e) • births i w h - (2 * e * mass (births i w h)) • w := by
  rw [tangent, transform_replacement, transform_replacement, transform_replacement, hh, hw.2, births_comm hn i h w]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma projection_resident_tangent (hn : 2 ≤ n) (i : Fin n) (e : ℝ)
    (w h : Weights (Genotype n k)) (hw : probability w) (hh : mass h = 0)
    (hR : ∀ x ∈ mutants i, w x = 0) (u : Genotype n k) (hu : u ∈ mutants i) :
    tangent (replaceKernel i) e w h u =
      (1 - e * mass (births i w w)) * h u +
        (2 * e) * births i w (project (mutants i) h) u := by
  rw [tangent_linear hn i e w h hw hh]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hR u hu, mul_zero, sub_zero]
  congr 1
  congr 1
  unfold births
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ mutants i
  · simp [hR x hx]
  by_cases hy : y ∈ mutants i
  · simp [project, hy]
  simp [birthMass_rejected i x y u hx hy hu]

end
end Lax637351Proofs.ColumnLinear
