import Lax637351Proofs.PredictionMeasure

namespace Lax637351Proofs.PredictionNorm

open Lax637351Proofs.PredictionMeasure
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

def weighted (E : Set α) (c : ℝ) (w : Weights α) :=
  variation w + c * variation (project E w)

lemma weighted_nonneg (E : Set α) {c : ℝ} (hc : 0 ≤ c) (w : Weights α) :
    0 ≤ weighted E c w := add_nonneg (variation_nonneg w) (mul_nonneg hc (variation_nonneg _))

lemma weighted_add (E : Set α) {c : ℝ} (hc : 0 ≤ c) (a b : Weights α) :
    weighted E c (a + b) ≤ weighted E c a + weighted E c b := by
  unfold weighted
  rw [project_add]
  have h := mul_le_mul_of_nonneg_left (variation_add (project E a) (project E b)) hc
  linarith only [h, variation_add a b]

lemma weighted_smul (E : Set α) (c g : ℝ) (a : Weights α) :
    weighted E c (g • a) = |g| * weighted E c a := by
  rw [weighted, project_smul, variation_smul, variation_smul, weighted]
  ring

lemma weighted_zero (E : Set α) (c : ℝ) : weighted E c (0 : Weights α) = 0 := by
  have h : project E (0 : Weights α) = 0 := by
    funext x
    simp [project]
  simp [weighted, h, variation]

lemma weighted_transform (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    {c : ℝ} (hc : 0 ≤ c) (a b v : Weights α) :
    weighted E c (transform T a b v) ≤ weighted E c a * weighted E c b * weighted E c v := by
  unfold weighted
  have h1 := variation_transform T a b v
  have h2 := mul_le_mul_of_nonneg_left (variation_project_transform T E hT a b v) hc
  have ha := variation_nonneg a
  have hb := variation_nonneg b
  have hv := variation_nonneg v
  have hA := mul_nonneg hc (variation_nonneg (project E a))
  have hB := mul_nonneg hc (variation_nonneg (project E b))
  have hV := mul_nonneg hc (variation_nonneg (project E v))
  nlinarith only [h1, h2, mul_nonneg (mul_nonneg hA hB) hv,
    mul_nonneg (mul_nonneg hA hb) hV, mul_nonneg (mul_nonneg ha hB) hV,
    mul_nonneg (mul_nonneg hA hB) hV]

def update (T : α → α → α → PMF α) (e : ℝ) (w : Weights α) : Weights α :=
  (1 - e) • w + e • transform T w w w

def tangent (T : α → α → α → PMF α) (e : ℝ) (w h : Weights α) : Weights α :=
  (1 - e) • h + e • ((transform T h w w + transform T w h w) + transform T w w h)

def predict (T : α → α → α → PMF α) (e : ℝ) : ℕ → Weights α → Weights α
  | 0, w => w
  | t + 1, w => update T e (predict T e t w)

def response (T : α → α → α → PMF α) (e : ℝ) : ℕ → Weights α → Weights α → Weights α
  | 0, _, h => h
  | t + 1, w, h => tangent T e (predict T e t w) (response T e t w h)

lemma tangent_add (T : α → α → α → PMF α) (e : ℝ) (w a b : Weights α) :
    tangent T e w (a + b) = tangent T e w a + tangent T e w b := by
  simp only [tangent, transform_add₁, transform_add₂, transform_add₃, smul_add]
  abel

lemma tangent_smul (T : α → α → α → PMF α) (e : ℝ) (w h : Weights α) (c : ℝ) :
    tangent T e w (c • h) = c • tangent T e w h := by
  simp only [tangent, transform_smul₁, transform_smul₂, transform_smul₃, smul_add]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma response_add (T : α → α → α → PMF α) (e : ℝ) (t : ℕ) (w a b : Weights α) :
    response T e t w (a + b) = response T e t w a + response T e t w b := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [response, ih, tangent_add]

lemma response_smul (T : α → α → α → PMF α) (e : ℝ) (t : ℕ) (w h : Weights α) (c : ℝ) :
    response T e t w (c • h) = c • response T e t w h := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [response, ih, tangent_smul]

lemma remainder_identity (T : α → α → α → PMF α) (e : ℝ) (a b : Weights α) :
    update T e b - update T e a - tangent T e a (b - a) =
      e • (transform T (b - a) (b - a) b +
        transform T (b - a) a (b - a) + transform T a (b - a) (b - a)) := by
  have h1 : transform T b b b - transform T a a a =
      transform T (b - a) b b + transform T a (b - a) b + transform T a a (b - a) := by
    simp only [transform_sub₁, transform_sub₂, transform_sub₃]
    abel
  rw [update, update, tangent]
  rw [show (1 - e) • b + e • transform T b b b -
      ((1 - e) • a + e • transform T a a a) =
      (1 - e) • (b - a) + e • (transform T b b b - transform T a a a) by
    simp only [smul_sub]; abel]
  rw [h1]
  have h2 : transform T (b - a) b b - transform T (b - a) a a =
      transform T (b - a) (b - a) b + transform T (b - a) a (b - a) := by
    simp only [transform_sub₂, transform_sub₃]
    abel
  have h3 : transform T a (b - a) b - transform T a (b - a) a =
      transform T a (b - a) (b - a) := by
    exact (transform_sub₃ T b a a (b - a)).symm
  have he : transform T (b - a) b b + transform T a (b - a) b + transform T a a (b - a) -
      (transform T (b - a) a a + transform T a (b - a) a + transform T a a (b - a)) =
      (transform T (b - a) b b - transform T (b - a) a a) +
      (transform T a (b - a) b - transform T a (b - a) a) := by abel
  rw [← h2, ← h3, ← he]
  simp only [smul_add, smul_sub]
  abel

lemma difference_identity (T : α → α → α → PMF α) (e : ℝ) (a b : Weights α) :
    update T e b - update T e a =
      (1 - e) • (b - a) + e •
        ((transform T (b - a) b b + transform T a (b - a) b) + transform T a a (b - a)) := by
  simp only [update, transform_sub₁, transform_sub₂, transform_sub₃, smul_add, smul_sub]
  abel

end
end Lax637351Proofs.PredictionNorm
