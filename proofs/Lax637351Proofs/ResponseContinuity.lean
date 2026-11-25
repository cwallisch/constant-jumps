import Lax637351Proofs.PredictionBounds

namespace Lax637351Proofs.ResponseContinuity

open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

lemma variation_zero : variation (0 : Weights α) = 0 := by simp [variation]

lemma tangent_sub (T : α → α → α → PMF α) (e : ℝ) (w a b : Weights α) :
    tangent T e w (a - b) = tangent T e w a - tangent T e w b := by
  have h := tangent_add T e w (a - b) b
  rw [sub_add_cancel] at h
  rw [h]
  abel

lemma tangent_difference (T : α → α → α → PMF α) (e : ℝ) (he : 0 ≤ e)
    (w z h : Weights α) (hw : probability w) (hz : probability z) :
    variation (tangent T e z h - tangent T e w h) ≤ 6 * e * variation (z - w) * variation h := by
  let d := z - w
  have heq : tangent T e z h - tangent T e w h = e •
      ((transform T h d z + transform T h w d) +
        (transform T d h z + transform T w h d) +
        (transform T d z h + transform T w d h)) := by
    dsimp only [d]
    simp only [tangent, transform_sub₁, transform_sub₂, transform_sub₃, smul_add, smul_sub]
    abel
  rw [heq, variation_smul, abs_of_nonneg he]
  have hnorm (p q r : Weights α) := variation_transform T p q r
  have h₁ := hnorm h d z
  have h₂ := hnorm h w d
  have h₃ := hnorm d h z
  have h₄ := hnorm w h d
  have h₅ := hnorm d z h
  have h₆ := hnorm w d h
  simp only [variation_probability hw, variation_probability hz, mul_one, one_mul] at h₁ h₂ h₃ h₄ h₅ h₆
  have hA := (variation_add (transform T h d z) _).trans (add_le_add h₁ h₂)
  have hB := (variation_add (transform T d h z) _).trans (add_le_add h₃ h₄)
  have hC := (variation_add (transform T d z h) _).trans (add_le_add h₅ h₆)
  have hD := (variation_add (_ + _) _).trans
    (add_le_add ((variation_add _ _).trans (add_le_add hA hB)) hC)
  have hscaled := mul_le_mul_of_nonneg_left hD he
  dsimp only [d] at hscaled
  nlinarith only [hscaled]

lemma response_continuity (T : α → α → α → PMF α) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w z h : Weights α) (hw : probability w) (hz : probability z) (t : ℕ) :
    variation (response T e t z h - response T e t w h) ≤
      6 * e * t * (1 + 3 * e) ^ (2 * t) * variation (z - w) * variation h := by
  let E : Set α := ∅
  have hT : residentRule T E := by intro x y z hx hy hz u hu; exact hu.elim
  let A := 1 + 3 * e
  have hA : 0 ≤ A := by unfold A; linarith only [he.1]
  have hA' : 1 ≤ A := by unfold A; linarith only [he.1]
  have hwv (s : ℕ) : weighted E 0 (predict T e s w) ≤ 1 := by simp [weighted, variation_probability (predict_probability _ _ he _ hw _)]
  have hzv (s : ℕ) : weighted E 0 (predict T e s z) ≤ 1 := by simp [weighted, variation_probability (predict_probability _ _ he _ hz _)]
  change _ ≤ 6 * e * t * A ^ (2 * t) * variation (z - w) * variation h
  induction t with
  | zero => simp [response, variation_zero]
  | succ t ih =>
    let W := predict T e t w
    let Z := predict T e t z
    let j := response T e t w h
    let u := response T e t z h
    have hiter := iterate_bounds T E hT (c := 0) (by norm_num) he w z h 1 t (fun s _ ↦ hwv s) (fun s _ ↦ hzv s)
    dsimp only at hiter
    have hd : variation (Z - W) ≤ A ^ t * variation (z - w) := by
      simpa only [weighted, zero_mul, add_zero, one_pow, mul_one, Z, W, A] using hiter.1
    have hj : variation j ≤ A ^ t * variation h := by
      simpa only [weighted, zero_mul, add_zero, one_pow, mul_one, A, j] using hiter.2.1
    have hpart := tangent_bound T E hT (c := 0) (by norm_num) he Z (u - j) 1 (hzv t)
    have hpart' : variation (tangent T e Z (u - j)) ≤ A * variation (u - j) := by
      simpa only [weighted, zero_mul, add_zero, one_pow, mul_one, A] using hpart
    have hs := tangent_difference T e he.1 W Z j
      (predict_probability T e he w hw t) (predict_probability T e he z hz t)
    rw [response, response, show tangent T e Z u - tangent T e W j =
        tangent T e Z (u - j) + (tangent T e Z j - tangent T e W j) by rw [tangent_sub]; abel]
    apply (variation_add _ _).trans
    have hfirst := hpart'.trans (mul_le_mul_of_nonneg_left ih hA)
    have hsecond := hs.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hd (show 0 ≤ 6 * e by linarith only [he.1])) hj
      (variation_nonneg _) (mul_nonneg (by linarith only [he.1] : 0 ≤ 6 * e) (mul_nonneg (pow_nonneg hA _) (variation_nonneg _))))
    have hP : A ^ (2 * t) ≤ A ^ (2 * (t + 1)) := pow_le_pow_right₀ hA' (by omega)
    have hP' : A * A ^ (2 * t) ≤ A ^ (2 * (t + 1)) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hA' (by omega)
    have hc : 0 ≤ 6 * e * variation (z - w) * variation h :=
      mul_nonneg (mul_nonneg (by linarith only [he.1]) (variation_nonneg _)) (variation_nonneg _)
    have hc' : 0 ≤ 6 * e * t * variation (z - w) * variation h := by
      have h := mul_nonneg hc (Nat.cast_nonneg (α := ℝ) t)
      nlinarith only [h]
    have heq : A ^ t * A ^ t = A ^ (2 * t) := by rw [two_mul, pow_add]
    push_cast
    nlinarith only [hfirst, hsecond, mul_le_mul_of_nonneg_left hP hc, mul_le_mul_of_nonneg_left hP' hc', heq,
      show 6 * e * (A ^ t * variation (z - w)) * (A ^ t * variation h) =
        (6 * e * variation (z - w) * variation h) * A ^ (2 * t) by rw [← heq]; ring]

end
end Lax637351Proofs.ResponseContinuity
