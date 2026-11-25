import Lax637351Proofs.RetainedValues
import Lax637351Proofs.PredictionMeasure

namespace Lax637351Proofs.LinearInvasion

open Lax637351Proofs.OffspringEstimates.ReproductiveValues
open Lax637351Proofs.RetainedValues Lax637351Proofs.PredictionMeasure
open scoped Classical ENNReal

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

def forward (A : Kernel α) (w : Weights α) : Weights α :=
  fun y ↦ ∑ x, w x * A.mass x y

def evolves (A : ℕ → Kernel α) (e : ℝ) (c : ℕ → ℝ) (w : ℕ → Weights α) : Prop :=
  ∀ s, w (s + 1) = c s • w s + e • forward (A s) (w s)

def dot (w g : Weights α) : ℝ := ∑ x, w x * g x

lemma dot_forward (A : Kernel α) (w g : Weights α) :
    dot (forward A w) g = dot w (fun x ↦ action A g x) := by
  unfold dot forward action
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma dot_add₁ (a b c : Weights α) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add₂ (a b c : Weights α) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul₁ (a b : Weights α) (c : ℝ) : dot (c • a) b = c * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_smul₂ (a b : Weights α) (c : ℝ) : dot a (c • b) = c * dot a b := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma dot_one (a : Weights α) : dot a (fun _ ↦ 1) = mass a := by simp [dot, mass]

lemma dot_mono (w g h : Weights α) (hw : positive w) (hle : ∀ x, g x ≤ h x) :
    dot w g ≤ dot w h := Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hle x) (hw x)

lemma dot_const (w : Weights α) (c : ℝ) : dot w (fun _ ↦ c) = mass w * c := by
  simp [dot, mass, Finset.sum_mul]

lemma retained_dual (A : ℕ → Kernel α) (e : ℝ) (c : ℕ → ℝ) (w : ℕ → Weights α)
    (hw : evolves A e c w) (s t : ℕ) :
    dot (w s) (retained A e c s t) = mass (w (s + t)) := by
  induction t generalizing s with
  | zero => simp [retained, dot_one]
  | succ t ih =>
    change dot (w s) (c s • retained A e c (s + 1) t +
      e • (fun x ↦ action (A s) (retained A e c (s + 1) t) x)) = _
    rw [show s + (t + 1) = s + 1 + t by omega, ← ih (s + 1), hw s]
    rw [dot_add₁, dot_add₂, dot_smul₁, dot_smul₁, dot_smul₂, dot_smul₂, dot_forward]

lemma relative_mass (A : ℕ → Kernel α) (B : ℕ → Kernel β)
    (hrel : α → β → Prop) (hshadow : ∀ x, ∃ y, hrel x y)
    (e : ℝ) (c : ℕ → ℝ) (H : ℕ) (he : 0 ≤ e ∧ e < 1)
    (hc : ∀ s, 1 - e ≤ c s ∧ c s ≤ 1)
    (hpert : (e / (1 - e) - e) * H * (1 + e / (1 - e)) ^ H ≤ 1)
    (D g : ℝ) (hD : 0 < D) (hg : 0 ≤ g)
    (hcomp : ∀ x y, hrel x y → g * value B e 0 H y ≤ value A e 0 H x)
    (hratio : ∀ y z, value B e 0 H z ≤ D * value B e 0 H y)
    (w : ℕ → Weights α) (π : ℕ → Weights β)
    (hw : evolves A e c w) (hπ : evolves B e c π)
    (hw₀ : probability (w 0)) (hπ₀ : probability (π 0)) (hπH : mass (π H) = 1) :
    g / (2 * D) ≤ mass (w H) := by
  let r := retention c 0 H
  have hr : 0 ≤ r := retention_nonneg c (fun s ↦ (sub_nonneg.mpr he.2.le).trans (hc s).1) 0 H
  have hR (y : β) : 1 / (2 * D) ≤ r * value B e 0 H y := by
    have hpoint (z : β) : retained B e c 0 H z ≤ 2 * D * (r * value B e 0 H y) := by
      have h1 := (retained_normalization B he c hc 0 H z hpert).2
      have h2 := mul_le_mul_of_nonneg_left (hratio y z) (show 0 ≤ 2 * r by positivity)
      dsimp [r] at *
      nlinarith only [h1, h2]
    have hv := dot_mono (π 0) (retained B e c 0 H) (fun _ ↦ 2 * D * (r * value B e 0 H y))
      hπ₀.1 hpoint
    rw [retained_dual B e c π hπ, dot_const, hπ₀.2, one_mul, zero_add, hπH] at hv
    exact (div_le_iff₀ (by positivity : 0 < 2 * D)).mpr (by nlinarith only [hv])
  have hpoint (x : α) : g / (2 * D) ≤ retained A e c 0 H x := by
    obtain ⟨y, hy⟩ := hshadow x
    have h1 := mul_le_mul_of_nonneg_left (hR y) hg
    have h2 := mul_le_mul_of_nonneg_left (hcomp x y hy) hr
    have h3 := (retained_normalization A he c hc 0 H x hpert).1
    change r * value A e 0 H x ≤ _ at h3
    rw [show g / (2 * D) = g * (1 / (2 * D)) by ring]
    nlinarith only [h1, h2, h3]
  have ht := dot_mono (w 0) (fun _ ↦ g / (2 * D)) (retained A e c 0 H) hw₀.1 hpoint
  rw [retained_dual A e c w hw, dot_const, hw₀.2, one_mul, zero_add] at ht
  exact ht

end
end Lax637351Proofs.LinearInvasion
