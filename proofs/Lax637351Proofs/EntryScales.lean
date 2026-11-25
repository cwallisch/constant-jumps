import Lax637351Proofs.BandColumn
import Lax637351Proofs.PowerBounds
import Lax637351Proofs.UniformEntry

namespace Lax637351Proofs.EntryScales

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.PowerBounds Lax637351Proofs.TapeConcentration
open Lax637351Proofs.FillBand Lax637351Proofs.CutoffEntry Lax637351Proofs.BandColumn
open Lax637351Proofs.UniformEntry Lax637351Proofs.Ordinary
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Filter
open scoped Classical ENNReal Topology

noncomputable section

def cutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
def length (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 20 : ℝ)⌋₊
def landingWidth (n : ℕ) : ℝ := (n : ℝ) ^ (11 / 100 : ℝ)
def landingTilt (n : ℕ) : ℝ := (1 / 2) * (n : ℝ) ^ (-9 / 100 : ℝ)
def tapeWidth (n : ℕ) : ℝ := (n : ℝ) ^ (13 / 100 : ℝ)
def tapeTilt (n : ℕ) : ℝ := (n : ℝ) ^ (-3 / 40 : ℝ)
def splitRate (n : ℕ) : ℝ := (n : ℝ) ^ (-1 / 100 : ℝ)

lemma cutoff_upper (n : ℕ) : (cutoff n : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
  Nat.floor_le (by positivity)

lemma length_upper (n : ℕ) : (length n : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) :=
  Nat.floor_le (by positivity)

lemma tilt_bounds (n : ℕ) (hn : 1 ≤ n) :
    (0 ≤ landingTilt n ∧ landingTilt n ≤ 1) ∧ (0 ≤ tapeTilt n ∧ tapeTilt n ≤ 1) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ := Real.rpow_le_one_of_one_le_of_nonpos hnr (show (-9 / 100 : ℝ) ≤ 0 by norm_num)
  have h₂ := Real.rpow_le_one_of_one_le_of_nonpos hnr (show (-3 / 40 : ℝ) ≤ 0 by norm_num)
  unfold landingTilt tapeTilt
  exact ⟨⟨by positivity, by linarith only [h₁]⟩, ⟨by positivity, h₂⟩⟩

lemma landing_exponent (n : ℕ) (hn : 1 ≤ n) :
    (cutoff n : ℝ) * landingTilt n ^ 2 - landingTilt n * landingWidth n ≤
      -(1 / 4) * (n : ℝ) ^ (1 / 50 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht := mul_le_mul_of_nonneg_right (cutoff_upper n) (sq_nonneg (landingTilt n))
  have he : (n : ℝ) ^ (1 / 5 : ℝ) * landingTilt n ^ 2 = (1 / 4) * (n : ℝ) ^ (1 / 50 : ℝ) := by
    unfold landingTilt
    rw [mul_pow, rpow_pow _ _ hn'.le]
    calc
      _ = ((1 / 2 : ℝ) ^ 2) * ((n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ ((-9 / 100 : ℝ) * (2 : ℕ))) := by ring
      _ = _ := by rw [← Real.rpow_add hn']; norm_num
  have he' : landingTilt n * landingWidth n = (1 / 2) * (n : ℝ) ^ (1 / 50 : ℝ) := by
    unfold landingTilt landingWidth
    rw [mul_assoc, ← Real.rpow_add hn']
    norm_num
  rw [he] at ht
  rw [he']
  linarith only [ht]

lemma tape_bound (n : ℕ) (hn : 2 ≤ n) (μ : ℕ+) (hμ : (μ : ℕ) ≤ n)
    (hbig : 1608 * (n : ℝ) ^ (21 / 400 : ℝ) ≤ (n : ℝ) ^ (11 / 200 : ℝ)) :
    tapeDelta (length n) μ (cutoff n) (tapeWidth n) (tapeTilt n) ≤
      Real.exp (-(1 / 2) * (n : ℝ) ^ (11 / 200 : ℝ)) := by
  let x : ℝ := n
  let m : ℝ := (μ : ℕ)
  let B : ℝ := cutoff n
  let L : ℝ := length n
  have hx : 0 < x := by dsimp [x]; positivity
  have hx' : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (Nat.succ_le_of_lt μ.pos)
  have hm' : m ≤ x := by dsimp [m, x]; exact_mod_cast hμ
  have hlog : Real.log x ≤ 400 * x ^ (1 / 400 : ℝ) := (log_rpow_upper x (1 / 400) hx (by norm_num)).trans_eq (by ring)
  have hlog' : Real.log (m + 1) ≤ 401 * x ^ (1 / 400 : ℝ) := by
    have hmx : m + 1 ≤ 2 * x := by linarith only [hm', hx']
    have ht := Real.log_le_log (show 0 < m + 1 by linarith) hmx
    have hlog₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hp : 1 ≤ x ^ (1 / 400 : ℝ) := Real.one_le_rpow hx' (by norm_num)
    rw [Real.log_mul (by norm_num) hx.ne'] at ht
    linarith only [ht, hlog, hlog₂, hp]
  have hBL : B + L ≤ 2 * x ^ (1 / 5 : ℝ) := by
    have h := (length_upper n).trans (Real.rpow_le_rpow_of_exponent_le hx' (by norm_num : (1 / 20 : ℝ) ≤ 1 / 5))
    linarith only [cutoff_upper n, h]
  have hpow : (B + L) * tapeTilt n ^ 2 ≤ 2 * x ^ (1 / 20 : ℝ) := by
    have ht := mul_le_mul_of_nonneg_right hBL (sq_nonneg (tapeTilt n))
    apply ht.trans_eq
    change 2 * x ^ (1 / 5 : ℝ) * (x ^ (-3 / 40 : ℝ)) ^ 2 = _
    rw [rpow_pow _ _ hx.le, mul_assoc, ← Real.rpow_add hx]
    norm_num
  have htape : tapeTilt n * tapeWidth n = x ^ (11 / 200 : ℝ) := by
    change x ^ (-3 / 40 : ℝ) * x ^ (13 / 100 : ℝ) = _
    rw [← Real.rpow_add hx]
    norm_num
  have hL : L * Real.log (m + 1) ≤ 401 * x ^ (21 / 400 : ℝ) := by
    have h := mul_le_mul (length_upper n) hlog' (Real.log_nonneg (by linarith only [hm])) (by positivity)
    apply h.trans_eq
    change x ^ (1 / 20 : ℝ) * (401 * x ^ (1 / 400 : ℝ)) = _
    rw [mul_left_comm, ← Real.rpow_add hx]
    norm_num
  have hM : Real.log m ≤ 400 * x ^ (21 / 400 : ℝ) :=
    ((Real.log_le_log (by linarith only [hm]) hm').trans hlog).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx' (by norm_num)) (by norm_num))
  have hMut := hpow.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx' (show (1 / 20 : ℝ) ≤ 21 / 400 by norm_num)) (by norm_num : (0 : ℝ) ≤ 2))
  have hE : tapeDelta (length n) μ (cutoff n) (tapeWidth n) (tapeTilt n) =
      Real.exp (L * Real.log (m + 1) + Real.log m + (B + L) * tapeTilt n ^ 2 - tapeTilt n * tapeWidth n) := by
    have he : Real.exp (L * Real.log (m + 1)) = (m + 1) ^ length n := by
      change Real.exp ((length n : ℝ) * Real.log (m + 1)) = _
      rw [Real.exp_nat_mul, Real.exp_log (show 0 < m + 1 by linarith)]
    symm
    rw [Real.exp_sub, Real.exp_add, Real.exp_add, he, Real.exp_log (show 0 < m by linarith)]
    change _ = (m + 1) ^ length n * m * Real.exp ((B + L) * tapeTilt n ^ 2 - tapeTilt n * tapeWidth n)
    rw [Real.exp_sub]
    ring
  rw [hE, htape]
  apply Real.exp_le_exp.mpr
  have hb : 1608 * x ^ (21 / 400 : ℝ) ≤ x ^ (11 / 200 : ℝ) := hbig
  have hh : 0 ≤ x ^ (21 / 400 : ℝ) := by positivity
  linarith only [hL, hM, hMut, hb, hh]

lemma initial_high (n : ℕ) (μ : ℕ+) (hn : 4 * (cutoff n + 1) ≤ n)
    (hμ : (μ : ℕ) ≤ n) (he : (n : ℝ) * (9 / 10 : ℝ) ^ n ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ mean (PMF.uniformOfFintype (Population n μ))
      (fun P ↦ indicator (ordinary (cutoff n + 1) P)) := by
  let B := cutoff n + 1
  let ν := PMF.uniformOfFintype (Population n μ)
  have h := initial_failure n B μ
  have h₂ : (2 : ℝ) ^ B ≤ (6 / 5 : ℝ) ^ n := calc
    _ ≤ ((6 / 5 : ℝ) ^ 4) ^ B := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (6 / 5 : ℝ) ^ (4 * B) := by rw [pow_mul]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
  have h₃ := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ (3 / 4 : ℝ) ^ n by positivity)
  rw [← mul_pow, show ((6 / 5 : ℝ) * (3 / 4)) = 9 / 10 by norm_num] at h₃
  have hs := mul_le_mul (show ((μ : ℕ) : ℝ) ≤ n by exact_mod_cast hμ) h₃ (by positivity) (by positivity)
  have hn' : mean ν (fun P ↦ indicator (¬ ordinary B P)) ≤ 1 / 2 := h.trans (hs.trans he)
  have hf : (fun P : Population n μ ↦ indicator (ordinary B P)) =
      fun P ↦ 1 - indicator (¬ ordinary B P) := by
    funext P
    by_cases hz : ordinary B P <;> simp [indicator, hz]
  change _ ≤ mean ν (fun P ↦ indicator (ordinary B P))
  rw [hf, mean_sub, mean_const]
  linarith only [hn']

def bandLow (n : ℕ) (μ : ℕ+) : ℝ := (cutoff n : ℝ) - ((fillLength μ : ℝ) + 1) * landingWidth n

structure Conditions (k n : ℕ) (μ : ℕ+) : Prop where
  dimension : 2 ≤ n
  cutoff_le : 4 * (cutoff n + 1) ≤ n
  cutoff_ge : 4 * k ≤ cutoff n
  initial : (1 / 2 : ℝ) ≤ mean (PMF.uniformOfFintype (Population n μ))
    (fun P ↦ indicator (ordinary (cutoff n + 1) P))
  land_error : (cutoffLength n μ : ℝ) *
    Real.exp ((cutoff n : ℝ) * landingTilt n ^ 2 - landingTilt n * landingWidth n) ≤ 1 / 4
  fill_error : (fillLength μ : ℝ) *
    Real.exp ((cutoff n : ℝ) * landingTilt n ^ 2 - landingTilt n * landingWidth n) ≤ 1 / 4
  clean_error : (fillLength μ : ℝ) * (splitRate n + ((cutoff n : ℝ) + 1) / n) ≤ 1 / 4
  band : (cutoff n : ℝ) / 2 < bandLow n μ - length n - tapeWidth n
  far : 64 * Real.sqrt 6 * (μ : ℕ) ≤ Real.sqrt (cutoff n : ℝ)
  tape_error : tapeDelta (length n) μ (cutoff n) (tapeWidth n) (tapeTilt n) ≤ 1 / 8
  progress : 0 < columnProgress (cutoff n) μ (splitRate n) * (length n : ℝ)
  work : (cutoff n : ℝ) - (bandLow n μ - length n - tapeWidth n) +
      n * tapeDelta (length n) μ (cutoff n) (tapeWidth n) (tapeTilt n) ≤
    columnProgress (cutoff n) μ (splitRate n) * (length n : ℝ) / 8

lemma entry_scales_eventually (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ μ : ℕ+, ((μ : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 1000 : ℝ) → Conditions k n μ := by
  have hgeo : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (9 / 10 : ℝ) ^ n ≤ 1 / 2 := by
    have ht := tendsto_pow_const_mul_const_pow_of_lt_one (k := 1) (r := (9 / 10 : ℝ)) (by norm_num) (by norm_num)
    filter_upwards [(tendsto_order.mp ht).2 (1 / 2) (by norm_num)] with n hn
    simpa only [pow_one] using hn.le
  filter_upwards [
    eventually_ge_atTop (2 : ℕ),
    (nat_rpow_tendsto (by norm_num : 0 < (1 / 5 : ℝ))).eventually (eventually_ge_atTop (max 2 (8 * (k : ℝ)))),
    (nat_rpow_tendsto (by norm_num : 0 < (1 / 20 : ℝ))).eventually (eventually_ge_atTop (2 : ℝ)),
    power_absorb 8 (1 / 5) 1 (by norm_num),
    power_absorb 160 (13 / 100) (1 / 5) (by norm_num),
    power_absorb (128 * Real.sqrt 6) (1 / 1000) (1 / 10) (by norm_num),
    power_absorb 384 (-7 / 1000) 0 (by norm_num),
    power_absorb 1608 (21 / 400) (11 / 200) (by norm_num),
    power_absorb (40 * 8192 * Real.sqrt 6) (13 / 100) (17 / 125) (by norm_num),
    exponential_domination 32 4 (1 / 4) (1 / 50) (1 / 4) (by norm_num) (by norm_num) (by norm_num),
    exponential_domination 1 3 (1 / 2) (11 / 200) (1 / 8) (by norm_num) (by norm_num) (by norm_num),
    hgeo] with n hn hb₀ hL₀ hcut hband hfar hclean htape hprog herror hterror hinit
  intro μ hμ
  let x : ℝ := n
  let m : ℝ := (μ : ℕ)
  let B : ℝ := cutoff n
  let L : ℝ := length n
  let U : ℝ := fillLength μ
  let e := Real.exp ((cutoff n : ℝ) * landingTilt n ^ 2 - landingTilt n * landingWidth n)
  let Δ := tapeDelta (length n) μ (cutoff n) (tapeWidth n) (tapeTilt n)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < n by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hm : 0 < m := by dsimp [m]; positivity
  have hmN : m ≤ x := hμ.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 1000 : ℝ) ≤ 1 by norm_num))
  have hmNat : (μ : ℕ) ≤ n := by dsimp [m, x] at hmN; exact_mod_cast hmN
  have hBn : B ≤ x ^ (1 / 5 : ℝ) := cutoff_upper n
  have hb1 : 1 ≤ x ^ (1 / 5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hL : x ^ (1 / 20 : ℝ) / 2 ≤ L := floor_half hL₀
  have hB : x ^ (1 / 5 : ℝ) / 2 ≤ B := floor_half ((le_max_left _ _).trans hb₀)
  have hB2 : (4 * (k : ℝ)) ≤ B := by linarith only [hB, (le_max_right 2 _).trans hb₀]
  have hbk : 4 * k ≤ cutoff n := by dsimp [B] at hB2; exact_mod_cast hB2
  have hcn : 4 * (cutoff n + 1) ≤ n := by
    have he : 4 * (B + 1) ≤ x := by
      rw [Real.rpow_one] at hcut
      change 8 * x ^ (1 / 5 : ℝ) ≤ x at hcut
      linarith only [hcut, hb1, hBn]
    dsimp [B, x] at he
    exact_mod_cast he
  have hU : U ≤ 32 * x ^ (3 / 1000 : ℝ) := by
    dsimp only [U, fillLength]
    push_cast
    have hh := pow_le_pow_left₀ hm.le hμ 3
    rw [rpow_pow _ _ hx.le] at hh
    norm_num at hh
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hU1 : U + 1 ≤ 33 * x ^ (3 / 1000 : ℝ) := by
    linarith only [hU, Real.one_le_rpow hx1 (show (0 : ℝ) ≤ 3 / 1000 by norm_num)]
  have hC : (cutoffLength n μ : ℝ) ≤ 32 * x ^ (4 : ℝ) := by
    dsimp only [cutoffLength]
    push_cast
    rw [show x ^ (4 : ℝ) = x ^ (4 : ℕ) from Real.rpow_natCast x 4]
    change 32 * x ^ 2 * m ^ 2 ≤ _
    have ht := pow_le_pow_left₀ hm.le hmN 2
    nlinarith only [mul_le_mul_of_nonneg_left ht (sq_nonneg x)]
  have hUcut : U ≤ (cutoffLength n μ : ℝ) := by
    dsimp only [U, fillLength, cutoffLength]
    push_cast
    have hh' : m ≤ x ^ 2 := hmN.trans (by simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1 ≤ (2 : ℕ) by decide))
    have ht := mul_le_mul_of_nonneg_right hh' (sq_nonneg m)
    nlinarith only [ht]
  have hExp : e ≤ Real.exp (-(1 / 4) * x ^ (1 / 50 : ℝ)) := Real.exp_le_exp.mpr (landing_exponent n (by omega))
  have hE : (cutoffLength n μ : ℝ) * e ≤ 1 / 4 :=
    (mul_le_mul hC hExp (Real.exp_pos _).le (by positivity)).trans herror
  have hClean : U * (splitRate n + (B + 1) / x) ≤ 1 / 4 := by
    have hB₁ : B + 1 ≤ 2 * x ^ (1 / 5 : ℝ) := by linarith only [hBn, hb1]
    have hh : splitRate n + (B + 1) / x ≤ 3 * x ^ (-1 / 100 : ℝ) := by
      have h := div_le_div_of_nonneg_right hB₁ hx.le
      have he : 2 * x ^ (1 / 5 : ℝ) / x = 2 * x ^ (-4 / 5 : ℝ) := by
        have h : x ^ (1 / 5 : ℝ) / x = x ^ (-4 / 5 : ℝ) := by
          have ht := Real.rpow_sub hx (1 / 5 : ℝ) 1
          rw [Real.rpow_one] at ht
          rw [← ht]
          norm_num
        rw [mul_div_assoc, h]
      rw [he] at h
      have ht := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (show (-4 / 5 : ℝ) ≤ -1 / 100 by norm_num))
        (by norm_num : (0 : ℝ) ≤ 2)
      change x ^ (-1 / 100 : ℝ) + (B + 1) / x ≤ _
      linarith only [h, ht]
    have hs := mul_le_mul hU hh (by unfold splitRate; dsimp [B]; positivity : 0 ≤ splitRate n + (B + 1) / x) (by positivity)
    have he : (32 * x ^ (3 / 1000 : ℝ)) * (3 * x ^ (-1 / 100 : ℝ)) = 96 * x ^ (-7 / 1000 : ℝ) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hx]
      norm_num
    rw [he] at hs
    rw [Real.rpow_zero] at hclean
    linarith only [hs, hclean]
  have hWidth : (U + 1) * landingWidth n ≤ 33 * x ^ (13 / 100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hU1 (show 0 ≤ landingWidth n by unfold landingWidth; positivity)
    change _ ≤ 33 * x ^ (3 / 1000 : ℝ) * x ^ (11 / 100 : ℝ) at hh
    rw [mul_assoc, ← Real.rpow_add hx] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num))
  have hLength : L ≤ x ^ (13 / 100 : ℝ) :=
    (length_upper n).trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hWidthAll : (U + 1) * landingWidth n + L + tapeWidth n ≤ 35 * x ^ (13 / 100 : ℝ) := by
    change (U + 1) * landingWidth n + L + x ^ (13 / 100 : ℝ) ≤ _
    linarith only [hWidth, hLength]
  have hBand : B / 2 < bandLow n μ - L - tapeWidth n := by
    have hpos : 0 < x ^ (13 / 100 : ℝ) := Real.rpow_pos_of_pos hx _
    change 160 * x ^ (13 / 100 : ℝ) ≤ x ^ (1 / 5 : ℝ) at hband
    change B / 2 < B - (U + 1) * landingWidth n - L - tapeWidth n
    linarith only [hWidthAll, hB, hband, hpos]
  have hsqrt : x ^ (1 / 10 : ℝ) / 2 ≤ Real.sqrt B := by
    have ht : (x ^ (1 / 10 : ℝ) / 2) ^ 2 = x ^ (1 / 5 : ℝ) / 4 := by
      rw [div_pow, rpow_pow _ _ hx.le]
      norm_num
    have hl : (x ^ (1 / 10 : ℝ) / 2) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
      rw [ht, Real.sq_sqrt (by positivity : 0 ≤ B)]
      linarith only [hB, show 0 ≤ x ^ (1 / 5 : ℝ) by positivity]
    have hS : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
    nlinarith only [hl, hS, show 0 ≤ x ^ (1 / 10 : ℝ) / 2 by positivity]
  have hFar : 64 * Real.sqrt 6 * m ≤ Real.sqrt B := by
    have hh := mul_le_mul_of_nonneg_left hμ (show 0 ≤ 64 * Real.sqrt 6 by positivity)
    linarith only [hh, hfar, hsqrt]
  have hΔ : Δ ≤ Real.exp (-(1 / 2) * x ^ (11 / 200 : ℝ)) := tape_bound n hn μ hmNat htape
  have hδ0 : 0 ≤ Δ := by dsimp [Δ, tapeDelta]; positivity
  have hδ : x ^ (3 : ℝ) * Δ ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hΔ (Real.rpow_nonneg hx.le (3 : ℝ))
    rw [one_mul] at hterror
    exact h.trans hterror
  have hXδ : x * Δ ≤ 1 / 8 := by
    apply le_trans _ hδ
    apply mul_le_mul_of_nonneg_right _ hδ0
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) ≤ 3 by norm_num)
  have hδ' : Δ ≤ 1 / 8 := (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx1 hδ0 : Δ ≤ x * Δ).trans hXδ
  have hProg : x ^ (17 / 125 : ℝ) / (1024 * Real.sqrt 6) ≤ columnProgress (cutoff n) μ (splitRate n) * L := by
    have hm4 : m ^ 4 ≤ x ^ (4 / 1000 : ℝ) := by
      have hh := pow_le_pow_left₀ hm.le hμ 4
      rw [rpow_pow _ _ hx.le] at hh
      norm_num at hh ⊢
      exact hh
    have hNum : splitRate n * (x ^ (1 / 10 : ℝ) / 2) * (x ^ (1 / 20 : ℝ) / 2) ≤
        splitRate n * Real.sqrt B * L := mul_le_mul
          (mul_le_mul_of_nonneg_left hsqrt (by unfold splitRate; positivity)) hL (by positivity)
          (mul_nonneg (by unfold splitRate; positivity) (Real.sqrt_nonneg _))
    have hh := div_le_div_of_nonneg_right hNum (show 0 ≤ 256 * Real.sqrt 6 * m ^ 4 by positivity)
    have hN : 0 ≤ splitRate n * (x ^ (1 / 10 : ℝ) / 2) * (x ^ (1 / 20 : ℝ) / 2) := by unfold splitRate; positivity
    have hDen := mul_le_mul_of_nonneg_left hm4 (show 0 ≤ 256 * Real.sqrt 6 by positivity)
    have ht := div_le_div_of_nonneg_left hN (show 0 < 256 * Real.sqrt 6 * m ^ 4 by positivity) hDen
    have he : splitRate n * (x ^ (1 / 10 : ℝ) / 2) * (x ^ (1 / 20 : ℝ) / 2) = x ^ (7 / 50 : ℝ) / 4 := by
      change x ^ (-1 / 100 : ℝ) * (x ^ (1 / 10 : ℝ) / 2) * (x ^ (1 / 20 : ℝ) / 2) = _
      calc
        _ = (x ^ (-1 / 100 : ℝ) * x ^ (1 / 10 : ℝ) * x ^ (1 / 20 : ℝ)) / 4 := by ring
        _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num
    calc
      _ = _ := by
        show x ^ (17 / 125 : ℝ) / (1024 * Real.sqrt 6) =
          (splitRate n * (x ^ (1 / 10 : ℝ) / 2) * (x ^ (1 / 20 : ℝ) / 2)) / (256 * Real.sqrt 6 * x ^ (4 / 1000 : ℝ))
        rw [he]
        have h : x ^ (7 / 50 : ℝ) / x ^ (4 / 1000 : ℝ) = x ^ (17 / 125 : ℝ) := by rw [← Real.rpow_sub hx]; norm_num
        rw [← h]
        ring
      _ ≤ _ := ht.trans hh
      _ = _ := by unfold columnProgress; change splitRate n * Real.sqrt B * L / _ = _; ring
  have hWork : B - (bandLow n μ - L - tapeWidth n) + x * Δ ≤ 40 * x ^ (13 / 100 : ℝ) := by
    change B - (B - (U + 1) * landingWidth n - L - tapeWidth n) + x * Δ ≤ _
    linarith only [hXδ, hWidthAll, Real.one_le_rpow hx1 (show (0 : ℝ) ≤ 13 / 100 by norm_num)]
  have hWork' : 40 * x ^ (13 / 100 : ℝ) ≤ columnProgress (cutoff n) μ (splitRate n) * L / 8 := by
    refine le_trans ?_ (div_le_div_of_nonneg_right hProg (by norm_num))
    have h : 40 * x ^ (13 / 100 : ℝ) ≤ x ^ (17 / 125 : ℝ) / (8192 * Real.sqrt 6) :=
      (le_div_iff₀ (by positivity)).mpr (by
        change 40 * 8192 * Real.sqrt 6 * x ^ (13 / 100 : ℝ) ≤ x ^ (17 / 125 : ℝ) at hprog
        nlinarith only [hprog])
    refine h.trans_eq ?_
    ring
  refine ⟨hn, hcn, hbk, initial_high n μ hcn hmNat hinit, hE, ?_, hClean, hBand, hFar, hδ', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hUcut (Real.exp_pos _).le).trans hE
  · exact (show 0 < x ^ (17 / 125 : ℝ) / (1024 * Real.sqrt 6) by positivity).trans_le hProg
  · exact hWork.trans hWork'

end
end Lax637351Proofs.EntryScales
