import Lax637351Proofs.PredictionNorm
import Mathlib.Analysis.Complex.Exponential

namespace Lax637351Proofs.PredictionBounds

open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

lemma update_probability (T : α → α → α → PMF α) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w : Weights α) (hw : probability w) : probability (update T e w) := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr he.2) (hw.1 x))
      (mul_nonneg he.1 (transform_positive T hw.1 hw.1 hw.1 x))
  · have h := transform_mass T w w w
    unfold update mass at h ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h, show ∑ x, w x = 1 from hw.2]
    ring

lemma predict_probability (T : α → α → α → PMF α) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (w : Weights α) (hw : probability w) (t : ℕ) : probability (predict T e t w) := by
  induction t with
  | zero => exact hw
  | succ t ih => exact update_probability T e he _ ih

lemma weighted_three (E : Set α) {c : ℝ} (hc : 0 ≤ c) (a b d : Weights α) :
    weighted E c (a + b + d) ≤ weighted E c a + weighted E c b + weighted E c d :=
  (weighted_add E hc _ _).trans (add_le_add_left (weighted_add E hc _ _) _)

lemma tangent_bound (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    {c : ℝ} (hc : 0 ≤ c) {e : ℝ} (he : 0 ≤ e ∧ e ≤ 1)
    (w h : Weights α) (B : ℝ) (hB : weighted E c w ≤ B) :
    weighted E c (tangent T e w h) ≤ (1 + 3 * e * B ^ 2) * weighted E c h := by
  let N := weighted E c
  have hL (a b d : Weights α) := weighted_transform T E hT hc a b d
  have hB' : 0 ≤ B := (weighted_nonneg E hc w).trans hB
  have hnw : 0 ≤ N w := weighted_nonneg E hc w
  have hnh : 0 ≤ N h := weighted_nonneg E hc h
  have htri : N (transform T h w w + transform T w h w + transform T w w h) ≤ 3 * B ^ 2 * N h := by
    refine (weighted_three E hc _ _ _).trans ?_
    have hA : N h * N w * N w ≤ N h * B * B := by
      gcongr
    have hB : N w * N h * N w ≤ B * N h * B := by
      gcongr
    have hC : N w * N w * N h ≤ B * B * N h := by
      gcongr
    linarith only [(hL h w w).trans hA, (hL w h w).trans hB, (hL w w h).trans hC,
      show N h * B * B + B * N h * B + B * B * N h = 3 * B ^ 2 * N h by ring]
  apply (weighted_add E hc _ _).trans
  rw [weighted_smul, weighted_smul, abs_of_nonneg (sub_nonneg.mpr he.2), abs_of_nonneg he.1]
  have ht := mul_le_mul_of_nonneg_left htri he.1
  have h := mul_nonneg he.1 (weighted_nonneg E hc h)
  nlinarith only [ht, h]

lemma difference_bound (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    {c : ℝ} (hc : 0 ≤ c) {e : ℝ} (he : 0 ≤ e ∧ e ≤ 1)
    (a b : Weights α) (B : ℝ) (ha : weighted E c a ≤ B) (hb : weighted E c b ≤ B) :
    weighted E c (update T e b - update T e a) ≤ (1 + 3 * e * B ^ 2) * weighted E c (b - a) := by
  let N := weighted E c
  let h := b - a
  have hL (a b d : Weights α) := weighted_transform T E hT hc a b d
  have hB : 0 ≤ B := (weighted_nonneg E hc a).trans ha
  have hna : 0 ≤ N a := weighted_nonneg E hc a
  have hnb : 0 ≤ N b := weighted_nonneg E hc b
  have hnh : 0 ≤ N h := weighted_nonneg E hc h
  have htri : N (transform T h b b + transform T a h b + transform T a a h) ≤ 3 * B ^ 2 * N h := by
    refine (weighted_three E hc _ _ _).trans ?_
    have hA : N h * N b * N b ≤ N h * B * B := by
      gcongr
    have hB : N a * N h * N b ≤ B * N h * B := by
      gcongr
    have hC : N a * N a * N h ≤ B * B * N h := by
      gcongr
    linarith only [(hL h b b).trans hA, (hL a h b).trans hB, (hL a a h).trans hC,
      show N h * B * B + B * N h * B + B * B * N h = 3 * B ^ 2 * N h by ring]
  rw [difference_identity]
  apply (weighted_add E hc _ _).trans
  rw [weighted_smul, weighted_smul, abs_of_nonneg (sub_nonneg.mpr he.2), abs_of_nonneg he.1]
  have ht := mul_le_mul_of_nonneg_left htri he.1
  have h := mul_nonneg he.1 (weighted_nonneg E hc h)
  nlinarith only [ht, h]

lemma remainder_bound (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    {c : ℝ} (hc : 0 ≤ c) {e : ℝ} (he : 0 ≤ e)
    (a b : Weights α) (B : ℝ) (ha : weighted E c a ≤ B) (hb : weighted E c b ≤ B) :
    weighted E c (update T e b - update T e a - tangent T e a (b - a)) ≤
      3 * B * e * (weighted E c (b - a)) ^ 2 := by
  let N := weighted E c
  let h := b - a
  have hL (a b d : Weights α) := weighted_transform T E hT hc a b d
  have hB : 0 ≤ B := (weighted_nonneg E hc a).trans ha
  have hna : 0 ≤ N a := weighted_nonneg E hc a
  have hnb : 0 ≤ N b := weighted_nonneg E hc b
  have hnh : 0 ≤ N h := weighted_nonneg E hc h
  have htri : N (transform T h h b + transform T h a h + transform T a h h) ≤ 3 * B * (N h) ^ 2 := by
    refine (weighted_three E hc _ _ _).trans ?_
    have hA : N h * N h * N b ≤ N h * N h * B := by
      gcongr
    have hB : N h * N a * N h ≤ N h * B * N h := by
      gcongr
    have hC : N a * N h * N h ≤ B * N h * N h := by
      gcongr
    linarith only [(hL h h b).trans hA, (hL h a h).trans hB, (hL a h h).trans hC,
      show N h * N h * B + N h * B * N h + B * N h * N h = 3 * B * (N h) ^ 2 by ring]
  rw [remainder_identity, weighted_smul, abs_of_nonneg he]
  have ht := mul_le_mul_of_nonneg_left htri he
  apply ht.trans
  exact le_of_eq (by ring)

lemma iterate_bounds (T : α → α → α → PMF α) (E : Set α) (hT : residentRule T E)
    {c : ℝ} (hc : 0 ≤ c) {e : ℝ} (he : 0 ≤ e ∧ e ≤ 1)
    (a b h : Weights α) (B : ℝ) (t : ℕ)
    (ha : ∀ s < t, weighted E c (predict T e s a) ≤ B)
    (hb : ∀ s < t, weighted E c (predict T e s b) ≤ B) :
    let A := 1 + 3 * e * B ^ 2
    weighted E c (predict T e t b - predict T e t a) ≤ A ^ t * weighted E c (b - a) ∧
    weighted E c (response T e t a h) ≤ A ^ t * weighted E c h ∧
    weighted E c (predict T e t b - predict T e t a - response T e t a (b - a)) ≤
      3 * B * e * t * A ^ (2 * t) * weighted E c (b - a) ^ 2 := by
  let N := weighted E c
  let A := 1 + 3 * e * B ^ 2
  have hA : 1 ≤ A := by unfold A; nlinarith only [mul_nonneg he.1 (sq_nonneg B)]
  change N (predict T e t b - predict T e t a) ≤ A ^ t * N (b - a) ∧
    N (response T e t a h) ≤ A ^ t * N h ∧
    N (predict T e t b - predict T e t a - response T e t a (b - a)) ≤
      3 * B * e * t * A ^ (2 * t) * N (b - a) ^ 2
  induction t with
  | zero => simp [predict, response, N, weighted_zero]
  | succ t ih =>
    obtain ⟨hd, ht, hR⟩ := ih (fun s hs ↦ ha s (by omega)) (fun s hs ↦ hb s (by omega))
    let at' := predict T e t a
    let bt := predict T e t b
    let D := bt - at'
    let J := response T e t a (b - a)
    have hA' : 0 ≤ A := by linarith only [hA]
    have ha' : N at' ≤ B := ha t (by omega)
    have hb' : N bt ≤ B := hb t (by omega)
    have hB : 0 ≤ B := (weighted_nonneg E hc _).trans ha'
    have hRcoeff : 0 ≤ 3 * B * e := mul_nonneg (mul_nonneg (by norm_num) hB) he.1
    constructor
    · rw [predict, predict, pow_succ']
      apply (difference_bound T E hT hc he at' bt B ha' hb').trans
      change A * N D ≤ (A * A ^ t) * N (b - a)
      exact (mul_le_mul_of_nonneg_left hd hA').trans_eq (by ring)
    constructor
    · rw [response, pow_succ']
      exact (tangent_bound T E hT hc he at' _ B ha').trans
        ((mul_le_mul_of_nonneg_left ht hA').trans_eq (by ring))
    · rw [predict, predict, response]
      have heq : update T e bt - update T e at' - tangent T e at' J =
          (update T e bt - update T e at' - tangent T e at' D) + tangent T e at' (D - J) := by
        have hj := tangent_add T e at' (D - J) J
        rw [sub_add_cancel] at hj
        rw [hj]
        abel
      rw [heq]
      apply (weighted_add E hc _ _).trans
      have hrem := remainder_bound T E hT hc he.1 at' bt B ha' hb'
      have hTan := tangent_bound T E hT hc he at' (D - J) B ha'
      have hDsq : N D ^ 2 ≤ A ^ (2 * t) * N (b - a) ^ 2 := by
        rw [mul_comm 2 t, pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (weighted_nonneg E hc D) hd _
      have hmain := hrem.trans (mul_le_mul_of_nonneg_left hDsq hRcoeff)
      have hrest := hTan.trans (mul_le_mul_of_nonneg_left hR hA')
      have hPow : A ^ (2 * t) ≤ A ^ (2 * (t + 1)) := pow_le_pow_right₀ hA (by omega)
      have hPow' : A * A ^ (2 * t) ≤ A ^ (2 * (t + 1)) := by
        rw [← pow_succ']
        exact pow_le_pow_right₀ hA (by omega)
      have hK : 0 ≤ 3 * B * e * N (b - a) ^ 2 := mul_nonneg hRcoeff (sq_nonneg _)
      have hKt : 0 ≤ 3 * B * e * t * N (b - a) ^ 2 :=
        mul_nonneg (mul_nonneg hRcoeff (Nat.cast_nonneg _)) (sq_nonneg _)
      push_cast
      nlinarith only [hmain, hrest, mul_le_mul_of_nonneg_left hPow hK, mul_le_mul_of_nonneg_left hPow' hKt]

end
end Lax637351Proofs.PredictionBounds
