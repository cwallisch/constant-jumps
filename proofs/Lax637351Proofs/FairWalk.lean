import Lax637351Proofs.Sampling
import Lax637351Proofs.Barrier
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Lax637351Proofs.FairWalk

open Lax637351.Algorithm
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

def countLaw : (m : ℕ) → PMF (Fin (m + 1))
  | 0 => PMF.pure 0
  | m + 1 => (countLaw m).bind fun w ↦ (coin (1 / 2)).map
      (fun b ↦ if b then w.succ else w.castSucc)

def signSum (m : ℕ) (w : Fin (m + 1)) : ℝ := 2 * (w.val : ℝ) - m

lemma sign_succ (m : ℕ) (w : Fin (m + 1)) :
    signSum (m + 1) w.succ = signSum m w + 1 := by
  unfold signSum
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

lemma sign_castSucc (m : ℕ) (w : Fin (m + 1)) :
    signSum (m + 1) w.castSucc = signSum m w - 1 := by
  unfold signSum
  simp only [Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

lemma mean_sign_step (m : ℕ) (g : ℝ → ℝ) :
    mean (countLaw (m + 1)) (fun w ↦ g (signSum (m + 1) w)) =
      mean (countLaw m) (fun w ↦ (g (signSum m w + 1) + g (signSum m w - 1)) / 2) := by
  rw [countLaw, mean_bind]
  simp only [mean_map, mean_coin (p := (1 / 2 : ℝ)) (by norm_num), if_true,
    Bool.false_eq_true, if_false, sign_succ, sign_castSucc]
  congr 1
  funext w
  ring

lemma sign_mean (m : ℕ) : mean (countLaw m) (signSum m) = 0 := by
  induction m with
  | zero => simp [countLaw, mean_pure, signSum]
  | succ m ih =>
    change mean (countLaw (m + 1)) (fun w ↦ id (signSum (m + 1) w)) = _
    rw [mean_sign_step]
    have hh : (fun w ↦ (id (signSum m w + 1) + id (signSum m w - 1)) / 2) = signSum m := by
      funext w
      simp only [id_eq]
      ring
    rw [hh, ih]

lemma sign_second (m : ℕ) : mean (countLaw m) (fun w ↦ signSum m w ^ 2) = m := by
  induction m with
  | zero => simp [countLaw, mean_pure, signSum]
  | succ m ih =>
    rw [mean_sign_step m (fun x ↦ x ^ 2)]
    have hh : (fun w ↦ ((signSum m w + 1) ^ 2 + (signSum m w - 1) ^ 2) / 2) =
        fun w ↦ signSum m w ^ 2 + 1 := by funext w; ring
    rw [hh, mean_add, mean_const, ih, Nat.cast_succ]

lemma sign_fourth (m : ℕ) : mean (countLaw m) (fun w ↦ signSum m w ^ 4) ≤ 3 * (m : ℝ) ^ 2 := by
  induction m with
  | zero => simp [countLaw, mean_pure, signSum]
  | succ m ih =>
    rw [mean_sign_step m (fun x ↦ x ^ 4)]
    have hh : (fun w ↦ ((signSum m w + 1) ^ 4 + (signSum m w - 1) ^ 4) / 2) =
        fun w ↦ (signSum m w ^ 4 + 6 * signSum m w ^ 2) + 1 := by funext w; ring
    rw [hh, mean_add, mean_add, mean_mul, sign_second, mean_const, Nat.cast_succ]
    nlinarith only [ih]

lemma absolute_lower (m : ℕ) :
    Real.sqrt (m : ℝ) / (2 * Real.sqrt 6) ≤
      mean (countLaw m) (fun w ↦ |signSum m w|) := by
  by_cases hm : m = 0
  · subst m
    simp [countLaw, mean_pure, signSum]
  let L := Real.sqrt (6 * (m : ℝ))
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hL : 0 < L := Real.sqrt_pos.2 (by positivity)
  have hLsq : L ^ 2 = 6 * (m : ℝ) := Real.sq_sqrt (by positivity)
  have hscalar (x : ℝ) : x ^ 2 ≤ L * |x| + x ^ 4 / L ^ 2 := by
    let z := |x| / L
    have hz : 0 ≤ z := div_nonneg (abs_nonneg _) hL.le
    have hh : z ^ 2 ≤ z + z ^ 4 := by
      rcases le_or_gt z 1 with h | h
      · nlinarith only [mul_nonneg hz (sub_nonneg.mpr h), pow_nonneg hz 4]
      · have h1 := mul_nonneg (sq_nonneg z) (show 0 ≤ z ^ 2 - 1 by nlinarith)
        nlinarith only [h1, hz]
    have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg L)
    dsimp [z] at hmul
    have heq₁ : (|x| / L) ^ 2 * L ^ 2 = x ^ 2 := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hL.ne'), sq_abs]
    have heq₂ : |x| / L * L ^ 2 = L * |x| := by field_simp
    have heq₃ : (|x| / L) ^ 4 * L ^ 2 = x ^ 4 / L ^ 2 := by
      rw [div_pow]
      have hh : |x| ^ 4 = x ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs, ← pow_mul]
      rw [hh]
      field_simp
    rw [add_mul, heq₁, heq₂, heq₃] at hmul
    exact hmul
  have hh := mean_mono (countLaw m) (fun w ↦ hscalar (signSum m w))
  simp only [div_eq_inv_mul] at hh
  rw [mean_add, mean_mul, mean_mul, sign_second] at hh
  have hp := mul_le_mul_of_nonneg_left (sign_fourth m) (inv_nonneg.mpr (sq_nonneg L))
  rw [hLsq] at hp hh
  have he : (6 * (m : ℝ))⁻¹ * (3 * (m : ℝ) ^ 2) = (m : ℝ) / 2 := by field_simp; norm_num
  rw [he] at hp
  have ht : (m : ℝ) / 2 ≤ L * mean (countLaw m) (fun w ↦ |signSum m w|) := by linarith
  have hres : (m : ℝ) / (2 * L) ≤ mean (countLaw m) (fun w ↦ |signSum m w|) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [ht]
  have heq : (m : ℝ) / (2 * L) = Real.sqrt (m : ℝ) / (2 * Real.sqrt 6) := by
    dsimp [L]
    rw [Real.sqrt_mul (by norm_num)]
    have hmS : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm'
    have h6 : 0 < Real.sqrt 6 := by positivity
    field_simp
    nlinarith [Real.sq_sqrt hm'.le]
  simpa only [heq] using hres

end
end Lax637351Proofs.FairWalk
