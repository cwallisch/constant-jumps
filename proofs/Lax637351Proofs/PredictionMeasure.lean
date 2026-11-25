import Lax637351Proofs.FiniteDrift
import Mathlib.Tactic.FunProp

namespace Lax637351Proofs.PredictionMeasure

open Lax637351Proofs.FiniteDrift
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

abbrev Weights (α : Type*) := α → ℝ

def variation (w : Weights α) : ℝ := ∑ x, |w x|

def mass (w : Weights α) : ℝ := ∑ x, w x

def positive (w : Weights α) : Prop := ∀ x, 0 ≤ w x

def probability (w : Weights α) : Prop := positive w ∧ mass w = 1

def density (ν : PMF α) : Weights α := fun x ↦ (ν x).toReal

def project (E : Set α) (w : Weights α) : Weights α := fun x ↦ if x ∈ E then w x else 0

def atom (x : α) : Weights α := fun y ↦ if x = y then 1 else 0

def transform (T : α → α → α → PMF α) (a b c : Weights α) : Weights α :=
  fun y ↦ ∑ x, ∑ u, ∑ v, a x * b u * c v * density (T x u v) y

lemma variation_nonneg (w : Weights α) : 0 ≤ variation w :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

lemma variation_add (w z : Weights α) : variation (w + z) ≤ variation w + variation z := by
  unfold variation
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ ↦ abs_add_le _ _

lemma variation_smul (a : ℝ) (w : Weights α) : variation (a • w) = |a| * variation w := by
  unfold variation
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

lemma mass_pos_eq {w : Weights α} (h : positive w) : variation w = mass w := by
  exact Finset.sum_congr rfl fun x _ ↦ abs_of_nonneg (h x)

lemma abs_mass_le (w : Weights α) : |mass w| ≤ variation w := by
  exact Finset.abs_sum_le_sum_abs _ _

lemma mass_density (ν : PMF α) : mass (density ν) = 1 := by
  exact sum_mass ν

lemma probability_density (ν : PMF α) : probability (density ν) :=
  ⟨fun _ ↦ ENNReal.toReal_nonneg, mass_density ν⟩

lemma variation_probability {w : Weights α} (h : probability w) : variation w = 1 :=
  (mass_pos_eq h.1).trans h.2

omit [Fintype α] in
lemma project_add (E : Set α) (w z : Weights α) :
    project E (w + z) = project E w + project E z := by
  funext x
  by_cases hx : x ∈ E <;> simp [project, hx]

omit [Fintype α] in
lemma project_sub (E : Set α) (w z : Weights α) :
    project E (w - z) = project E w - project E z := by
  funext x
  by_cases hx : x ∈ E <;> simp [project, hx]

omit [Fintype α] in
lemma project_smul (E : Set α) (a : ℝ) (w : Weights α) :
    project E (a • w) = a • project E w := by
  funext x
  by_cases hx : x ∈ E <;> simp [project, hx]

omit [Fintype α] in
lemma project_positive (E : Set α) {w : Weights α} (hw : positive w) :
    positive (project E w) := by
  intro x
  by_cases hx : x ∈ E <;> simp [project, hx, hw x]

omit [Fintype α] in
lemma conserve_split (E : Set α) (w : Weights α) :
    project E w + project Eᶜ w = w := by
  funext x
  by_cases hx : x ∈ E <;> simp [project, hx]

lemma variation_project (E : Set α) (w : Weights α) :
    variation (project E w) ≤ variation w := by
  unfold variation
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ E <;> simp [project, hx]

lemma variation_atom (x : α) : variation (atom x) = 1 := by
  unfold variation
  rw [Finset.sum_eq_single x]
  · simp [atom]
  · intro y _ h
    simp [atom, Ne.symm h]
  · simp

lemma variation_atom_diff (x y : α) : variation (atom x - atom y) ≤ 2 := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (atom y)]
  refine (variation_add _ _).trans_eq ?_
  rw [variation_smul, variation_atom, variation_atom]
  norm_num

lemma transform_add₁ (T : α → α → α → PMF α) (a b u v : Weights α) :
    transform T (a + b) u v = transform T a u v + transform T b u v := by
  funext y
  simp [transform, add_mul, Finset.sum_add_distrib]

lemma transform_add₂ (T : α → α → α → PMF α) (a b u v : Weights α) :
    transform T u (a + b) v = transform T u a v + transform T u b v := by
  funext y
  simp [transform, mul_add, add_mul, Finset.sum_add_distrib]

lemma transform_add₃ (T : α → α → α → PMF α) (a b u v : Weights α) :
    transform T u v (a + b) = transform T u v a + transform T u v b := by
  funext y
  simp [transform, mul_add, add_mul, Finset.sum_add_distrib]

lemma transform_smul₁ (T : α → α → α → PMF α) (g : ℝ) (a b c : Weights α) :
    transform T (g • a) b c = g • transform T a b c := by
  funext y
  simp [transform, mul_assoc, Finset.mul_sum]

lemma transform_smul₂ (T : α → α → α → PMF α) (g : ℝ) (a b c : Weights α) :
    transform T a (g • b) c = g • transform T a b c := by
  funext y
  simp [transform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma transform_smul₃ (T : α → α → α → PMF α) (g : ℝ) (a b c : Weights α) :
    transform T a b (g • c) = g • transform T a b c := by
  funext y
  simp [transform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma transform_sub₁ (T : α → α → α → PMF α) (a b u v : Weights α) :
    transform T (a - b) u v = transform T a u v - transform T b u v := by
  have h := transform_add₁ T (a - b) b u v
  rw [sub_add_cancel] at h
  rw [h]
  abel

lemma transform_sub₂ (T : α → α → α → PMF α) (a b u v : Weights α) :
    transform T u (a - b) v = transform T u a v - transform T u b v := by
  have h := transform_add₂ T (a - b) b u v
  rw [sub_add_cancel] at h
  rw [h]
  abel

lemma transform_sub₃ (T : α → α → α → PMF α) (a b u v : Weights α) :
    transform T u v (a - b) = transform T u v a - transform T u v b := by
  have h := transform_add₃ T (a - b) b u v
  rw [sub_add_cancel] at h
  rw [h]
  abel

lemma transform_mass (T : α → α → α → PMF α) (a b c : Weights α) :
    mass (transform T a b c) = mass a * mass b * mass c := by
  unfold mass transform
  calc
    _ = ∑ x, ∑ u, ∑ v, a x * b u * c v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, show ∑ y, density (T x u v) y = 1 from mass_density _, mul_one]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      have h : (∑ i : α, ∑ j : α, a i * b j) = (∑ i, a i) * ∑ j, b j := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_mul]
      rw [h]

lemma transform_positive (T : α → α → α → PMF α) {a b c : Weights α}
    (ha : positive a) (hb : positive b) (hc : positive c) : positive (transform T a b c) := by
  intro y
  exact Finset.sum_nonneg (fun x _ ↦ Finset.sum_nonneg (fun u _ ↦ Finset.sum_nonneg (fun v _ ↦
    mul_nonneg (mul_nonneg (mul_nonneg (ha x) (hb u)) (hc v)) ENNReal.toReal_nonneg)))

lemma variation_transform (T : α → α → α → PMF α) (a b c : Weights α) :
    variation (transform T a b c) ≤ variation a * variation b * variation c := by
  let av (x : α) := |a x|
  let bv (x : α) := |b x|
  let cv (x : α) := |c x|
  have he : mass (transform T av bv cv) = variation a * variation b * variation c :=
    transform_mass T av bv cv
  rw [← he]
  apply Finset.sum_le_sum
  intro y _
  unfold transform
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro u _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro v _
  simp only [abs_mul, density, abs_of_nonneg ENNReal.toReal_nonneg, av, bv, cv, le_refl]

def residentRule (T : α → α → α → PMF α) (E : Set α) : Prop :=
  ∀ x u v, x ∉ E → u ∉ E → v ∉ E → ∀ y ∈ E, T x u v y = 0

lemma transform_resident (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    (a b c : Weights α) :
    project E (transform T (project Eᶜ a) (project Eᶜ b) (project Eᶜ c)) = 0 := by
  funext y
  by_cases hy : y ∈ E
  · simp only [project, if_pos hy, transform, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro v _
    by_cases hx : x ∈ E <;> by_cases hu : u ∈ E <;> by_cases hv : v ∈ E <;>
      simp [hx, hu, hv, density]
    exact Or.inr (by rw [hT x u v hx hu hv y hy, ENNReal.toReal_zero])
  · simp [project, hy]

lemma variation_project_transform (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    (a b c : Weights α) :
    variation (project E (transform T a b c)) ≤
      variation (project E a) * variation b * variation c +
      variation a * variation (project E b) * variation c +
      variation a * variation b * variation (project E c) := by
  have h (w z v : Weights α) := (variation_project E (transform T w z v)).trans (variation_transform T w z v)
  have he : transform T a b c =
      ((transform T (project E a) b c + transform T (project Eᶜ a) (project E b) c) +
        transform T (project Eᶜ a) (project Eᶜ b) (project E c)) +
        transform T (project Eᶜ a) (project Eᶜ b) (project Eᶜ c) := by
    conv_lhs =>
      rw [← conserve_split E a, transform_add₁]
      congr
      · rfl
      · rw [← conserve_split E b, transform_add₂]
        congr
        · rfl
        · rw [← conserve_split E c, transform_add₃]
    abel
  rw [he]
  simp only [project_add, transform_resident T E hT, add_zero]
  apply (variation_add _ _).trans
  apply add_le_add _ _
  · apply (variation_add _ _).trans
    refine add_le_add (h _ _ _) ((h _ _ _).trans ?_)
    gcongr <;> first | exact variation_project Eᶜ a | exact variation_nonneg _
  · apply (h _ _ _).trans
    gcongr <;> first | exact variation_project Eᶜ a | exact variation_project Eᶜ b | exact variation_nonneg _

end
end Lax637351Proofs.PredictionMeasure
