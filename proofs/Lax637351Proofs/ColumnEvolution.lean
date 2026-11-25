import Lax637351Proofs.ColumnClasses

namespace Lax637351Proofs.ColumnEvolution

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.FiniteDrift Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear
open Lax637351Proofs.ColumnClasses Lax637351Proofs.LinearInvasion
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

lemma row_birth_mass (i : Fin n) (x y : Genotype n k) :
    0 ≤ ∑ z, birthMass i x y z ∧ ∑ z, birthMass i x y z ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun z _ ↦ birthMass_nonneg i x y z), ?_⟩
  let q := (OffspringProduct.pairMutation (toString x) (toString y) (1 / (n : ℝ))).map (proposal i x y)
  have h := sum_mass q
  rw [Fintype.sum_option] at h
  have h' : (q none).toReal + ∑ z, birthMass i x y z = 1 := h
  linarith only [h', ENNReal.toReal_nonneg (a := q none)]

lemma total_birth_mass (i : Fin n) (w : Weights (Genotype n k)) (hw : probability w) :
    0 ≤ mass (births i w w) ∧ mass (births i w w) ≤ 1 := by
  rw [birth_sum]
  constructor
  · exact Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun y _ ↦
      mul_nonneg (mul_nonneg (hw.1 x) (hw.1 y)) (row_birth_mass i x y).1
  · calc
      _ ≤ ∑ x, ∑ y, w x * w y := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact (mul_le_mul_of_nonneg_left (row_birth_mass i x y).2
          (mul_nonneg (hw.1 x) (hw.1 y))).trans_eq (mul_one _)
      _ = _ := by
        simp_rw [← Finset.mul_sum]
        rw [show ∑ y, w y = 1 from hw.2]
        simp only [mul_one]
        exact hw.2

lemma resident_preserved (i : Fin n) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w : Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (t : ℕ) :
    ∀ x ∈ mutants i, predict (replaceKernel i) e t w x = 0 := by
  induction t with
  | zero => exact hR
  | succ t ih =>
    intro x hx
    rw [predict, resident_step i e _ (predict_probability _ e he w hw t)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih x hx, births_resident i _ ih x hx, mul_zero, add_zero]

lemma tangent_mass_zero (T : Genotype n k → Genotype n k → Genotype n k → PMF (Genotype n k))
    (e : ℝ) (w h : Weights (Genotype n k)) (hh : mass h = 0) :
    mass (tangent T e w h) = 0 := by
  simp [tangent, mass_add, mass_smul, transform_mass, hh]

lemma response_mass_zero (T : Genotype n k → Genotype n k → Genotype n k → PMF (Genotype n k))
    (e : ℝ) (w h : Weights (Genotype n k)) (hh : mass h = 0) (t : ℕ) :
    mass (response T e t w h) = 0 := by
  induction t with
  | zero => exact hh
  | succ t ih => exact tangent_mass_zero T e _ _ ih

lemma view_mutant_step (hn : 2 ≤ n) (i : Fin n) (e : ℝ)
    (w h : Weights (Genotype n k)) (hw : probability w) (hh : mass h = 0) (hR : ∀ x ∈ mutants i, w x = 0) :
    view i 1 (tangent (replaceKernel i) e w h) =
      (1 - e * mass (births i w w)) • view i 1 h +
        e • forward (mixedKernel (partners w hw)) (view i 1 h) := by
  funext u
  have hu : fromClass u ∈ mutants i := by
    change toString (fromClass u) i = 1
    rw [string_fromClass]
    exact u.property.2
  change tangent (replaceKernel i) e w h (fromClass u) =
     (1 - e * mass (births i w w)) * h (fromClass u) +
        e * forward (mixedKernel (partners w hw)) (view i 1 h) u
  rw [projection_resident_tangent hn i e w h hw hh hR _ hu, forward_mixed hn i 1 w h hw hR u]
  simp only [Ne.symm (Fin.zero_ne_one : (0 : Fin 2) ≠ 1), if_false]
  have he : (fun x : Genotype n k ↦ if toString x i = (1 : Fin 2) then h x else 0) = project (mutants i) h := by
    funext x
    by_cases hx : toString x i = 1 <;> simp [project, mutants, hx]
  rw [he]
  ring

lemma view_resident_step (hn : 2 ≤ n) (i : Fin n) (e : ℝ) (w : Weights (Genotype n k))
    (hw : probability w) (hR : ∀ x ∈ mutants i, w x = 0) :
    view i 0 (update (replaceKernel i) e w) =
      (1 - e * mass (births i w w)) • view i 0 w +
        e • forward (mixedKernel (partners w hw)) (view i 0 w) := by
  funext u
  rw [resident_step i e w hw]
  change (1 - e * mass (births i w w)) * w (fromClass u) + e * births i w w (fromClass u) =
    (1 - e * mass (births i w w)) * w (fromClass u) +
      e * forward (mixedKernel (partners w hw)) (view i 0 w) u
  rw [forward_mixed hn i 0 w w hw hR u]
  have he : (fun x : Genotype n k ↦ if toString x i = (0 : Fin 2) then w x else 0) = w := by
    funext x
    by_cases h : toString x i = 0
    · simp [h]
    · have hx : x ∈ mutants i := bit_eq_one_of_ne_zero _ h
      simp [h, hR x hx]
  rw [he]
  simp

end
end Lax637351Proofs.ColumnEvolution
