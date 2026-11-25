import Lax637351Proofs.ColumnLinear
import Lax637351Proofs.LinearInvasion

namespace Lax637351Proofs.ColumnClasses

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.LinearInvasion
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {i : Fin n} {b : Fin 2}

def fromClass (x : ColumnClass n k i b) : Genotype n k := ofString x.val x.property.1

@[simp] lemma string_fromClass (x : ColumnClass n k i b) : toString (fromClass x) = x.val :=
  toString_ofString _ _

def classEquiv (n k : ℕ) (i : Fin n) (b : Fin 2) :
    ColumnClass n k i b ≃ {x : Genotype n k // toString x i = b} where
  toFun x := ⟨fromClass x, (string_fromClass x) ▸ x.property.2⟩
  invFun x := ⟨toString x.val, by rw [zeros_toString]; exact x.val.property, x.property⟩
  left_inv x := Subtype.ext (string_fromClass x)
  right_inv x := Subtype.ext (ofString_toString x.val)

def view (i : Fin n) (b : Fin 2) (w : Weights (Genotype n k)) : Weights (ColumnClass n k i b) :=
  fun x ↦ w (fromClass x)

lemma class_sum_eq (i : Fin n) (b : Fin 2) (f : Genotype n k → ℝ) :
    (∑ x : ColumnClass n k i b, f (fromClass x)) = ∑ x : Genotype n k, if toString x i = b then f x else 0 := by
  calc
    _ = ∑ x : {x : Genotype n k // toString x i = b}, f x.val :=
      (classEquiv n k i b).sum_comp (fun x ↦ f x.val)
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (F := inferInstance) _ (by simp) f).symm

lemma mutant_view_mass (i : Fin n) (w : Weights (Genotype n k)) :
    mass (view i 1 w) = mass (project (mutants i) w) := by
  simp only [mass, view, class_sum_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : toString x i = 1 <;> simp [project, mutants, hx]

lemma resident_view_mass (i : Fin n) (w : Weights (Genotype n k))
    (hw : ∀ x ∈ mutants i, w x = 0) : mass (view i 0 w) = mass w := by
  simp only [mass, view, class_sum_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : toString x i = 0
  · simp [h]
  · have hz : x ∈ mutants i := bit_eq_one_of_ne_zero _ h
    simp [h, hw x hz]

def asPMF (w : Weights (Genotype n k)) (hw : probability w) : PMF (Genotype n k) :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (w x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ hw.1 x), show ∑ x, w x = 1 from hw.2, ENNReal.ofReal_one])

lemma asPMF_density (w : Weights (Genotype n k)) (hw : probability w) :
    density (asPMF w hw) = w := by
  funext x
  simp [density, asPMF, ENNReal.toReal_ofReal (hw.1 x)]

def partners (w : Weights (Genotype n k)) (hw : probability w) : PMF (BitString n) :=
  (asPMF w hw).map Genotypes.toString

lemma partners_plateau (w : Weights (Genotype n k)) (hw : probability w) (u : BitString n)
    (hu : u ∈ (partners w hw).support) : (zeros u).card = k := by
  obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hu
  have h : (OffspringEstimates.Sampling.zeros (toString x)).card = k := by rw [zeros_toString]; exact x.property
  exact h

lemma partners_point (w : Weights (Genotype n k)) (hw : probability w) (x : Genotype n k) :
    (partners w hw (toString x)).toReal = w x := by
  have h := congrFun (asPMF_density w hw) x
  unfold partners
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single x]
  · simpa [density] using h
  · intro y _ hy
    have hn : toString x ≠ toString y := fun h ↦ hy ((toString_injective h).symm)
    simp [hn]
  · simp

lemma forward_mixed (hn : 2 ≤ n) (i : Fin n) (b : Fin 2) (w h : Weights (Genotype n k)) (hw : probability w)
    (hR : ∀ x ∈ mutants i, w x = 0) (u : ColumnClass n k i b) :
    forward (mixedKernel (partners w hw)) (view i b h) u =
      (if b = 0 then 1 else 2) * births i w
        (fun x ↦ if toString x i = b then h x else 0) (fromClass u) := by
  have hrow (x : ColumnClass n k i b) :
      (mixedKernel (partners w hw)).mass x u =
        (if b = 0 then (1 : ℝ) else 2) * ∑ y, w y * birthMass i y (fromClass x) (fromClass u) := by
    unfold mixedKernel
    change mean (partners w hw) (fun z ↦ kernel x z u) = _
    rw [partners, mean_map]
    unfold mean
    simp_rw [show ∀ y : Genotype n k, ((asPMF w hw) y).toReal = w y from congrFun (asPMF_density w hw)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ mutants i
    · simp [hR y hy]
    · have hy0 : toString y i = 0 := by
        by_contra hc
        exact hy (bit_eq_one_of_ne_zero _ hc)
      have hc : ¬ (y ∉ mutants i ∧ fromClass x ∉ mutants i ∧ fromClass u ∈ mutants i) := by
        rintro ⟨_, hx, hu⟩
        have h1 : b = 1 := by simpa only [mutants, Set.mem_ofPred_eq, string_fromClass, u.property.2] using hu
        exact hx (by simpa only [mutants, Set.mem_ofPred_eq, string_fromClass, x.property.2] using h1)
      rw [birthMass_exact i _ _ _ hc, breed_comm hn, string_fromClass, string_fromClass, breed_eq]
      simp only [kernel, classFactor, hy0]
      ring
  let d : ℝ := if b = 0 then 1 else 2
  change ∀ x, (mixedKernel (partners w hw)).mass x u =
    d * ∑ y, w y * birthMass i y (fromClass x) (fromClass u) at hrow
  change forward (mixedKernel (partners w hw)) (view i b h) u = d * _
  unfold forward view births
  simp_rw [hrow]
  have he (x : ColumnClass n k i b) :
      h (fromClass x) * (d * ∑ y, w y * birthMass i y (fromClass x) (fromClass u)) =
        d * ∑ y, h (fromClass x) * (w y * birthMass i y (fromClass x) (fromClass u)) := by
    rw [mul_left_comm (h (fromClass x)) d, Finset.mul_sum (s := Finset.univ)]
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [class_sum_eq i b (fun x ↦ h x * (w y * birthMass i y x (fromClass u)))]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : toString x i = b <;> simp [h]; ring

end
end Lax637351Proofs.ColumnClasses
