import Lax637351Proofs.SlopeCopy
import Lax637351Proofs.UpDownCost
import Lax637351Proofs.CopyingExponential
import Lax637351Proofs.MaskKernel

namespace Lax637351Proofs.SlopeReset

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Ordinary
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.BestRank Lax637351Proofs.SlopeCopy Lax637351Proofs.UpDownCost
open Lax637351Proofs.CopyingModel Lax637351Proofs.CopyingProb Lax637351Proofs.CopyingWindow
open Lax637351Proofs.CopyingExponential Lax637351Proofs.MarkedStep
open Lax637351Proofs.Regeneration Lax637351Proofs.Charge Lax637351Proofs.MaskKernel
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def cutoffResets (k B : ℕ) : Set (Population n μ) :=
  {P | ¬ ordinary k P ∨ B < bestZeros P ∨ homogeneous P}

def slopeRate (m i : ℕ) : ℝ := if 1 ≤ i ∧ i < m then birth m i (1 / 16) else 0

lemma rate_pos {m i : ℕ} (hi : 1 ≤ i) (hi' : i < m) : 0 < slopeRate m i := by
  have h₁ : (0 : ℝ) < i := by exact_mod_cast hi
  have h₂ : (i : ℝ) < m := by exact_mod_cast hi'
  have h : 1 ≤ i ∧ i < m := ⟨hi, hi'⟩
  simp only [slopeRate, if_pos h, birth]
  have hm : (0 : ℝ) < m := h₁.trans h₂
  exact div_pos (mul_pos (mul_pos (by norm_num) (div_pos h₁ hm)) (sub_pos.mpr h₂)) (by positivity)

lemma rate_nonneg (m i : ℕ) : 0 ≤ slopeRate m i := by
  by_cases h : 1 ≤ i ∧ i < m
  · exact (rate_pos h.1 h.2).le
  · simp [slopeRate, h]

def deathRatio (n B : ℕ) (μ : ℕ+) (p : ℝ) : ℝ :=
  1 + 32 * p + 16 * (μ : ℕ) * B / n

def exactBirth (n : ℕ) (μ : ℕ+) (p : ℝ) (i : ℕ) : ℝ :=
  birth μ i ((1 - p) * cloneMass n)

lemma ratio_bound (hn : 2 ≤ n) (B : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1 / 2)
    (P : Population n μ) (hB : bestZeros P ≤ B) (hP : ¬ homogeneous P) :
    let f : ℝ := (bestCount P : ℝ) / (μ : ℕ)
    (((1 - p) * cloneMass n) * (1 - f) + (bestZeros P : ℝ) / n + p * (1 - f ^ 2)) *
          ((bestCount P : ℝ) / ((μ : ℕ) + 1)) ≤
      deathRatio n B μ p * exactBirth n μ p (bestCount P) := by
  let m : ℝ := (μ : ℕ)
  let i : ℝ := bestCount P
  let c := (1 - p) * cloneMass n
  let f := i / m
  let w := i / (m + 1)
  have hm : 0 < m := by dsimp [m]; positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hi : 0 ≤ i := by dsimp [i]; positivity
  have hlt : bestCount P < (μ : ℕ) :=
    lt_of_le_of_ne (bestCount_le P) (fun h ↦ hP ((bestCount_full P).mp h))
  have hmi : 1 ≤ m - i := by
    have h : (bestCount P : ℝ) + 1 ≤ (μ : ℕ) := by exact_mod_cast hlt
    linarith
  have hf : 0 ≤ f := div_nonneg hi hm.le
  have hf1 : f ≤ 1 := (div_le_one hm).mpr (by linarith)
  have hc : 1 / 16 ≤ c := by
    have hh := mul_le_mul (show (1 / 2 : ℝ) ≤ 1 - p by linarith) (cloneMass_lower hn)
      (by norm_num) (by linarith)
    linarith
  have hw : 0 ≤ w := div_nonneg hi (by positivity)
  have hfmin : 1 ≤ m * (1 - f) := by
    have he : m * (1 - f) = m - i := by dsimp [f]; field_simp
    simpa only [he] using hmi
  have he₁ : (bestZeros P : ℝ) / n ≤ (16 * m * B / n) * (c * (1 - f)) := by
    have hh : (bestZeros P : ℝ) ≤ B := by exact_mod_cast hB
    have hc1 : 1 ≤ 16 * c := by linarith
    have hprod := one_le_mul_of_one_le_of_one_le hc1 hfmin
    have hpB := mul_le_mul_of_nonneg_right hprod (show 0 ≤ (B : ℝ) / n by positivity)
    apply (div_le_div_of_nonneg_right hh hn'.le).trans
    convert hpB using 1 <;> ring
  have he₂ : p * (1 - f ^ 2) ≤ (32 * p) * (c * (1 - f)) := by
    have hh : p * (1 + f) ≤ (32 * p) * c := by
      have h₁ := mul_le_mul_of_nonneg_left (show 1 + f ≤ 2 by linarith) hp.1
      have h₂ := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hp.1)
      linarith
    have hprod := mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hf1)
    nlinarith only [hprod]
  change (c * (1 - f) + (bestZeros P : ℝ) / n + p * (1 - f ^ 2)) * w ≤ _
  have hbirth : exactBirth n μ p (bestCount P) = c * (1 - f) * w := by
    unfold exactBirth birth
    dsimp [c, w, f, i, m]
    field_simp
  rw [hbirth, deathRatio]
  have hh := mul_le_mul_of_nonneg_right (add_le_add (add_le_add_left he₁ (c * (1 - f))) he₂) hw
  dsimp only [m] at hh
  nlinarith only [hh]

lemma slope_rate_le (hn : 2 ≤ n) (p : ℝ) (hp : p ≤ 1 / 2) (i : ℕ) (hi : 1 ≤ i) (hi' : i < (μ : ℕ)) :
    slopeRate μ i ≤ exactBirth n μ p i := by
  have h : (i : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hi'.le
  have hu := mul_le_mul (show (1 / 2 : ℝ) ≤ 1 - p by linarith) (cloneMass_lower hn)
    (by norm_num) (by linarith)
  rw [slopeRate, if_pos ⟨hi, hi'⟩, exactBirth, birth, birth]
  gcongr
  linarith

lemma rate_inverse (m i : ℕ) (hi : 1 ≤ i) (hi' : i < m) :
    (slopeRate m i)⁻¹ ≤ 32 * (m : ℝ) ^ 2 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hmi : (1 : ℝ) ≤ (m : ℝ) - i := by
    have h : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi'
    linarith
  have hb : (0 : ℝ) < slopeRate m i := rate_pos hi hi'
  apply (inv_le_iff_one_le_mul₀ hb).mpr
  rw [slopeRate, if_pos ⟨hi, hi'⟩, birth]
  have hh : (1 : ℝ) ≤ (i : ℝ) * (m - i) := one_le_mul_of_one_le_of_one_le hiR hmi
  have hm' : (1 : ℝ) ≤ m := hiR.trans (by linarith)
  have he : (32 * (m : ℝ) ^ 2) * (1 / 16 * ((i : ℝ) / m) * (m - i) / (m + 1)) =
      (2 * m / (m + 1)) * ((i : ℝ) * (m - i)) := by field_simp; ring
  rw [he]
  exact one_le_mul_of_one_le_of_one_le ((le_div_iff₀ (by positivity)).mpr (by linarith)) hh

def rankBudget (n B : ℕ) (μ : ℕ+) (p : ℝ) : ℝ :=
  32 * ((μ : ℕ) : ℝ) ^ 4 * deathRatio n B μ p ^ (μ : ℕ)

lemma rankBudget_one (n B : ℕ) (μ : ℕ+) {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ rankBudget n B μ p := by
  have hρ : 1 ≤ deathRatio n B μ p := by
    unfold deathRatio
    exact (le_add_of_nonneg_right (mul_nonneg (by norm_num) hp)).trans (le_add_of_nonneg_right (by positivity))
  have hμ : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  unfold rankBudget
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hμ))
    (one_le_pow₀ hρ)

lemma slope_span (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (B : ℕ) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) (t : ℕ) (P : Population n μ) :
    span (masked (jump k) p false) (cutoffResets k B) t P ≤
      ((B - k + 1 : ℕ) : ℝ) * rankBudget n B μ p := by
  let J := masked (jump k) p false (n := n) (μ := μ)
  let K := step (jump k) p false (n := n) (μ := μ)
  let R := cutoffResets (μ := μ) (n := n) k B
  let u := slopeRate μ
  let ρ := deathRatio n B μ p
  let f := rankCost μ u ρ
  let M := rankBudget n B μ p
  let V (Q : Population n μ) :=
    if Q ∈ R then 0 else ((bestZeros Q - k : ℕ) : ℝ) * M + f (bestCount Q)
  have hρ : 1 ≤ ρ := by
    dsimp only [ρ, deathRatio]
    exact (le_add_of_nonneg_right (mul_nonneg (by norm_num) hp.1)).trans (le_add_of_nonneg_right (by positivity))
  have hρ0 : 0 ≤ ρ := by linarith
  have hM := rankBudget_one n B μ hp.1
  have hf := rankCost_nonneg μ u (rate_nonneg μ) ρ hρ0
  have hf' := rankCost_antitone μ u (rate_nonneg μ) ρ hρ0
  have hbound (i : ℕ) : f i ≤ M := by
    apply (rankCost_upper μ u (rate_nonneg μ) ρ (32 * ((μ : ℕ) : ℝ) ^ 2) hρ (by positivity)
      (fun j hj hj' ↦ rate_inverse μ j hj hj') i).trans_eq
    dsimp [M, rankBudget, ρ]
    ring
  have hV (Q : Population n μ) : 0 ≤ V Q := by
    dsimp only [V]
    split_ifs
    · norm_num
    · exact add_nonneg (mul_nonneg (by positivity) (by linarith)) (hf _)
  have hPV (Q : Population n μ) : V Q ≤ ((B - k + 1 : ℕ) : ℝ) * M := by
    dsimp only [V]
    split_ifs with hQ
    · positivity
    · have hB : bestZeros Q ≤ B := by
        by_contra! hh
        exact hQ (Or.inr (Or.inl hh))
      have hle : ((bestZeros Q - k : ℕ) : ℝ) ≤ (B - k : ℕ) := by
        exact_mod_cast Nat.sub_le_sub_right hB k
      push_cast
      linarith only [hbound (bestCount Q), mul_le_mul_of_nonneg_right hle (show 0 ≤ M by linarith)]
  apply (span_le_potential J R V hV (fun x hx ↦ ?_) t P).trans (hPV P)
  rw [marginal_masked]
  have hxO : ordinary k x := by by_contra! hh; exact hx (Or.inl hh)
  have hxB : bestZeros x ≤ B := by by_contra! hh; exact hx (Or.inr (Or.inl hh))
  have hxN : ¬ homogeneous x := fun hh ↦ hx (Or.inr (Or.inr hh))
  let i := bestCount x
  have hi : 1 ≤ i := bestCount_pos x
  have hi' : i < (μ : ℕ) := lt_of_le_of_ne (bestCount_le x) (fun h ↦ hxN ((bestCount_full x).mp h))
  let a := exactBirth n μ p i
  let d := increments u ρ i
  let d' := increments u ρ (i - 1)
  have hU : 0 < u i := rate_pos hi hi'
  have ha := slope_rate_le (μ := μ) hn p hp.2 i hi hi'
  have hd' := increments_nonneg u (rate_nonneg μ) ρ hρ0 (i - 1)
  have hd : d = (u i)⁻¹ + ρ * d' := by
    dsimp only [d, d']
    nth_rw 1 [← Nat.sub_add_cancel hi]
    rw [increments, Nat.sub_add_cancel hi]
  have hUP := upward_prob hk hkn p ⟨hp.1, by linarith [hp.2]⟩ x hxO
  have hDN := (downward_prob hkn hn p ⟨hp.1, by linarith [hp.2]⟩ x hxO).trans (ratio_bound hn B p hp x hxB hxN)
  have hdpt (y : Population n μ) (hy : y ∈ (K x).support) :
      d * indicator (up x y) - d' * indicator (down x y) ≤ V x - V y := by
    have hd0 : 0 ≤ d := increments_nonneg u (rate_nonneg μ) ρ hρ0 i
    have hinc : f i - f (i + 1) = d := cost_difference μ u ρ hi'
    have hdec : f (i - 1) - f i = d' := by
      have hh := cost_difference μ u ρ (show i - 1 < (μ : ℕ) by omega)
      rw [Nat.sub_add_cancel hi] at hh
      exact hh
    have hdM : d ≤ f i := by linarith only [hinc, hf (i + 1)]
    have hs : ∃ z j, y = replace x z j := by
      change y ∈ (step (jump k) p false x).support at hy
      rw [← stepMarked_population] at hy
      obtain ⟨v, hv, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      obtain ⟨e, _, hh⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
      obtain ⟨Q, hQ, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
      have hQ' : Q ∈ (Transitions.insert (jump k) x (child e)).support := by
        simpa [select] using hQ
      obtain ⟨j, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ'
      exact ⟨child e, j, he.symm⟩
    rw [show V x = ((bestZeros x - k : ℕ) : ℝ) * M + f i by simp [V, hx, i]]
    by_cases hR : y ∈ R
    · rw [show V y = 0 by simp [V, hR]]
      have hh : d * indicator (up x y) ≤ d := by simpa using mul_le_mul_of_nonneg_left (indic_le_one _) hd0
      linarith only [hh, hdM, mul_nonneg hd' (indic_nonneg (down x y)),
        show 0 ≤ ((bestZeros x - k : ℕ) : ℝ) * M by positivity]
    have hyO : ordinary k y := by by_contra! hh; exact hR (Or.inl hh)
    have hmon := lower_best_notlost hkn x y hxO hyO (fun j ↦ step_fitness_mono _ _ _ _ hy j)
    rw [show V y = ((bestZeros y - k : ℕ) : ℝ) * M + f (bestCount y) by simp [V, hR]]
    by_cases hsame : bestZeros y = bestZeros x
    · rw [hsame]
      by_cases hup : up x y
      · have hdown : ¬ down x y := fun hh ↦ by have hu := hup.2; have hd := hh.2; omega
        simp only [indicator, if_pos hup, if_neg hdown, mul_one, mul_zero, sub_zero]
        have hh := hf' hup.2
        change f (bestCount y) ≤ f (i + 1) at hh
        linarith only [hinc, hh]
      by_cases hdown : down x y
      · obtain ⟨z, j, hreplace⟩ := hs
        have ha := bestCount_adjacent x z j (by simpa only [← hreplace] using hsame)
        rw [← hreplace] at ha
        have hh := hf' (show i - 1 ≤ bestCount y by dsimp [i]; omega)
        simp only [indicator, if_neg hup, if_pos hdown, mul_zero, mul_one]
        linarith only [hdec, hh]
      · have hh : bestCount y = i := by
          simp only [up, down, hsame, true_and] at hup hdown
          dsimp [i]
          omega
        simp [indicator, hup, hdown, hh]
    · have hlt : bestZeros y < bestZeros x := lt_of_le_of_ne hmon hsame
      have hky := (ordinary_iff_bestZeros y).mp hyO
      have hh : ((bestZeros y - k : ℕ) : ℝ) + 1 ≤ ((bestZeros x - k : ℕ) : ℝ) := by
        exact_mod_cast (show bestZeros y - k + 1 ≤ bestZeros x - k by omega)
      have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ M by linarith)
      simp only [indicator, up, down, hsame, false_and, if_false, mul_zero, sub_self]
      linarith only [hm, hbound (bestCount y), hf i]
  have hh := mean_mono_on_support (K x) hdpt
  rw [mean_sub, mean_mul, mean_mul, mean_sub, mean_const] at hh
  have hD : 0 ≤ d := increments_nonneg u (rate_nonneg μ) ρ hρ0 i
  have hl : d * a ≤ d * mean (K x) (fun y ↦ indicator (up x y)) := mul_le_mul_of_nonneg_left hUP hD
  have hld := mul_le_mul_of_nonneg_left hDN hd'
  change d' * mean (K x) (fun y ↦ indicator (down x y)) ≤ d' * (ρ * a) at hld
  change mean (K x) V + 1 ≤ V x
  have hdiff : d * a - d' * (ρ * a) = (u i)⁻¹ * a := by rw [hd]; ring
  have hscale : 1 ≤ (u i)⁻¹ * a := by
    have hh := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hU.le)
    rwa [inv_mul_cancel₀ hU.ne'] at hh
  linarith only [hh, hl, hld, hdiff, hscale]

lemma growth_preserves_best (hkn : k ≤ n) (p : ℝ) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : (zeros A).card = bestZeros P)
    (v : Draw n × Population n μ) (hv : v ∈ (stepMarked (jump k) p false P).support)
    (hg : grow k A P v) : bestZeros v.2 = bestZeros P := by
  obtain ⟨e, _, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
  obtain ⟨Q, hQ, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
  have hQ' : Q ∈ (Transitions.insert (jump k) P (child e)).support := by simpa [select] using hQ
  suffices h : child e = A by
    rw [h] at hQ'
    exact copy_sel hkn P hP A hA Q hQ'
  by_contra hn
  have hg' := hg.2.2
  change copyCount A Q = copyCount A P + 1 at hg'
  obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ'
  revert hg'
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [replace]
  · simp only [replace, Fin.lastCases_castSucc]
    intro hg'
    by_cases h : P i = A
    · have hh := PairAveraging.sum_update P i (child e) (fun b ↦ indicator (b = A))
      rw [← count_cast_sum, ← count_cast_sum] at hh
      simp only [indicator, if_pos h, if_neg hn] at hh
      rw [hg'] at hh
      push_cast at hh
      linarith
    · rw [copyCount_update_other _ _ _ _ h hn] at hg'
      omega

lemma consecutive_copying (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (B : ℕ) (p : ℝ)
    (hp : 1 / 2 ≤ p ∧ p ≤ 1) (A : BitString n) :
    ∀ (r : ℕ) (P : Population n μ),
      ordinary k P → (zeros A).card = bestZeros P →
      copyCount A P = (μ : ℕ) - r → r ≤ (μ : ℕ) →
      (∏ i ∈ Finset.Ico ((μ : ℕ) - r) (μ : ℕ), stageFactor μ i) ≤
        visit (step (jump k) p false) (cutoffResets k B) r P := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let R := cutoffResets (μ := μ) (n := n) k B
  intro r
  induction r with
  | zero =>
    intro P hP hA hc _
    have hh : homogeneous P := fun i ↦
      ((copyCount_full_iff A P).mp (by simpa using hc) i).trans
        (((copyCount_full_iff A P).mp (by simpa using hc) 0).symm)
    simpa only [Nat.sub_zero, Finset.Ico_self, Finset.prod_empty] using
      (visit_in K R 0 P (Or.inr (Or.inr hh))).ge
  | succ r ih =>
    intro P hP hA hc hr
    let i := (μ : ℕ) - (r + 1)
    have hi : i < (μ : ℕ) := by dsimp only [i]; omega
    have hf : i + 1 = (μ : ℕ) - r := by dsimp only [i]; omega
    let C := ∏ j ∈ Finset.Ico (i + 1) (μ : ℕ), stageFactor μ j
    have hC : 0 ≤ C := Finset.prod_nonneg (fun j hj ↦ stageFactor_nonneg (Finset.mem_Ico.mp hj).2.le)
    have hγ : stageFactor μ i ≤ goodRate μ i p := by
      have hh : (i : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hi.le
      have h := mul_le_mul_of_nonneg_right (show (1 / 128 : ℝ) ≤ p / 8 by linarith [hp.1])
        (show 0 ≤ ((i : ℝ) / (μ : ℕ)) ^ 2 * (((μ : ℕ) - (i : ℝ)) / ((μ : ℕ) + 1)) by positivity)
      unfold stageFactor goodRate
      simpa only [mul_assoc, ← mul_div_assoc] using h
    change (∏ j ∈ Finset.Ico i (μ : ℕ), stageFactor μ j) ≤ visit K R (r + 1) P
    by_cases hR : P ∈ R
    · rw [visit_in _ _ _ _ hR]
      exact Finset.prod_le_one (fun j hj ↦ stageFactor_nonneg (Finset.mem_Ico.mp hj).2.le)
        (fun j hj ↦ stageFactor_le_one (Finset.mem_Ico.mp hj).2)
    · rw [visit, if_neg hR, Finset.prod_eq_prod_Ico_succ_bot hi]
      change _ ≤ mean (step (jump k) p false P) _
      rw [← stepMarked_population (jump k) p false P, mean_map]
      apply (mul_le_mul_of_nonneg_right hγ hC).trans
      have hAk : k ≤ (zeros A).card := hA.symm ▸ (ordinary_iff_bestZeros P).mp hP
      have hp' : 0 ≤ p ∧ p ≤ 1 := ⟨by linarith [hp.1], hp.2⟩
      have hh := grow_best_probability hk hkn hn p hp' P hP A hAk (best_fitness hkn P hP A hA) false
      rw [hc] at hh
      refine (mul_le_mul_of_nonneg_right hh hC).trans ?_
      rw [mul_comm, ← mean_mul]
      apply mean_mono_on_support
      intro v hv
      by_cases hg : grow k A P v
      · have hz := growth_preserves_best hkn p P hP A hA v hv hg
        have hc' : copyCount A v.2 = (μ : ℕ) - r := hg.2.2.trans (hc ▸ hf)
        have hh := ih v.2 hg.2.1 (hA.trans hz.symm) hc' (by omega)
        simpa only [indicator, if_pos hg, mul_one, C, hf] using hh
      · simp only [indicator, if_neg hg, mul_zero]
        exact visit_nonneg K R r v.2

def copyBudget (n B : ℕ) (μ : ℕ+) (p : ℝ) : ℝ :=
  32 * ((μ : ℕ) : ℝ) ^ 4 * Real.exp (32 * (μ : ℕ) * p + 16 * ((μ : ℕ) : ℝ) ^ 2 * B / n)

lemma copyBudget_one (n B : ℕ) (μ : ℕ+) {p : ℝ} (hp : 0 ≤ p) : 1 ≤ copyBudget n B μ p := by
  have hμ : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  unfold copyBudget
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hμ))
    (Real.one_le_exp (by positivity))

lemma rankBudget_le (n B : ℕ) (μ : ℕ+) (p : ℝ) (hp : 0 ≤ p) :
    rankBudget n B μ p ≤ copyBudget n B μ p := by
  unfold rankBudget copyBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let x : ℝ := 32 * p + 16 * (μ : ℕ) * B / n
  have hx : deathRatio n B μ p = x + 1 := by unfold deathRatio x; ring
  rw [hx, show 32 * (μ : ℕ) * p + 16 * ((μ : ℕ) : ℝ) ^ 2 * B / n = (μ : ℕ) * x by dsimp [x]; ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by dsimp [x]; positivity) (Real.add_one_le_exp x) _

lemma cutoff_span (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (hμ : 2 ≤ μ)
    (B : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (t : ℕ) (P : Population n μ) :
    span (masked (jump k) p false) (cutoffResets k B) t P ≤
      ((B - k + 1 : ℕ) : ℝ) * copyBudget n B μ p := by
  by_cases hp' : p ≤ 1 / 2
  · exact (slope_span hk hkn hn B p ⟨hp.1, hp'⟩ t P).trans
      (mul_le_mul_of_nonneg_left (rankBudget_le n B μ p hp.1) (by positivity))
  let J := masked (jump k) p false (n := n) (μ := μ)
  let K := step (jump k) p false (n := n) (μ := μ)
  let R := cutoffResets (μ := μ) (n := n) k B
  let q := Real.exp (-16 * ((μ : ℕ) : ℝ))
  have hq : 0 < q := Real.exp_pos _
  have hq' : q ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hm : (0 : ℝ) ≤ (μ : ℕ) := by positivity
    linarith)
  have hblock (Q : Population n μ) : q ≤ visit (marginal J) R μ Q := by
    rw [marginal_masked]
    by_cases hQ : Q ∈ R
    · exact hq'.trans (visit_in K R μ Q hQ).ge
    · have hOrd : ordinary k Q := by by_contra! ho; exact hQ (Or.inl ho)
      obtain ⟨i, hi, hs⟩ := bestCount_exists Q
      let A := Q i
      let s := copyCount A Q
      let r := (μ : ℕ) - s
      have hs' : 1 ≤ s := by dsimp [s, A]; rw [hs]; exact bestCount_pos Q
      have ha : s = (μ : ℕ) - r := (Nat.sub_sub_self (copyCount_le A Q)).symm
      have hr : r ≤ (μ : ℕ) := Nat.sub_le _ _
      have hh := consecutive_copying hk hkn hn B p ⟨le_of_not_ge hp', hp.2⟩ A r Q hOrd hi ha hr
      rw [← ha] at hh
      have hsSub : Finset.Ico s (μ : ℕ) ⊆ Finset.Ico 1 (μ : ℕ) := by
        intro j hj
        exact Finset.mem_Ico.mpr ⟨hs'.trans (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2⟩
      have hprod := Finset.prod_le_prod_of_subset_of_le_one hsSub
        (fun j hj ↦ stageFactor_nonneg (Finset.mem_Ico.mp hj).2.le)
        (fun j hj _ ↦ stageFactor_le_one (Finset.mem_Ico.mp hj).2)
      exact (complete_product μ (by exact_mod_cast hμ)).trans (hprod.trans (hh.trans (visit_monotone K R Q hr)))
  have hh := span_le_of_block J R (μ : ℕ) μ.pos q hq hq' hblock t P
  have hm : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hm' : ((μ : ℕ) : ℝ) ≤ 32 * ((μ : ℕ) : ℝ) ^ 4 := by
    have h := pow_le_pow_right₀ hm (show 1 ≤ (4 : ℕ) by decide)
    have hn := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 32 by norm_num) (by positivity : 0 ≤ ((μ : ℕ) : ℝ) ^ 4)
    simpa only [pow_one, one_mul] using le_trans h (by simpa only [one_mul] using hn)
  have hExp : 16 * ((μ : ℕ) : ℝ) ≤ 32 * (μ : ℕ) * p + 16 * ((μ : ℕ) : ℝ) ^ 2 * B / n := by
    have ht := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ p from le_of_not_ge hp') (show 0 ≤ 32 * ((μ : ℕ) : ℝ) by positivity)
    linarith only [ht, show 0 ≤ 16 * ((μ : ℕ) : ℝ) ^ 2 * B / n by positivity]
  have hcut : (1 : ℝ) ≤ ((B - k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (B - k)
  have hM := copyBudget_one n B μ hp.1
  calc
    _ ≤ ((μ : ℕ) : ℝ) / q := hh
    _ = ((μ : ℕ) : ℝ) * Real.exp (16 * ((μ : ℕ) : ℝ)) := by
      dsimp [q]
      rw [show (-16 : ℝ) * ((μ : ℕ) : ℝ) = -(16 * ((μ : ℕ) : ℝ)) by ring,
        Real.exp_neg, div_inv_eq_mul]
    _ ≤ copyBudget n B μ p := mul_le_mul hm' (Real.exp_le_exp.mpr hExp) (by positivity) (by positivity)
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcut (show 0 ≤ copyBudget n B μ p by linarith)

end
end Lax637351Proofs.SlopeReset
