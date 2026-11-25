import Lax637351Proofs.CopyingProb
import Lax637351Proofs.FiniteRace
import Mathlib.Analysis.Complex.Exponential

namespace Lax637351Proofs.CopyingWindow

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.CopyingStage
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.MarkedStep Lax637351Proofs.Ordinary Lax637351Proofs.CopyingModel
open Lax637351Proofs.CopyingProb Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open scoped Classical ENNReal

noncomputable section

def stageLength (p : ℝ) : ℕ := max 1 ⌊1 / (4 * p)⌋₊

lemma stageLength_pos (p : ℝ) : 0 < stageLength p := by
  change 1 ≤ max 1 _
  exact le_max_left _ _

lemma stageLength_upper {p : ℝ} (hp : 0 < p ∧ p ≤ 1) : (stageLength p : ℝ) ≤ 1 / p := by
  unfold stageLength
  push_cast
  apply max_le
  · exact (le_div_iff₀ hp.1).mpr (by simpa using hp.2)
  · apply (Nat.floor_le (one_div_nonneg.mpr (mul_nonneg (by norm_num) hp.1.le))).trans
    exact one_div_le_one_div_of_le hp.1 (by linarith [hp.1])

lemma waiting_lower {p : ℝ} (hp : 0 < p) :
    1 / (16 * p) ≤ waitingSum (1 - min 1 (2 * p)) (stageLength p) := by
  by_cases hp' : p ≤ 1 / 4
  · let H := stageLength p
    have hbase : 1 ≤ 1 / (4 * p) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hH' : 1 ≤ ⌊1 / (4 * p)⌋₊ := Nat.le_floor (by simpa using hbase)
    have heq : H = ⌊1 / (4 * p)⌋₊ := max_eq_right hH'
    have hpos : (1 : ℝ) ≤ H := by exact_mod_cast stageLength_pos p
    have hH₁ : 1 / (4 * p) ≤ 2 * (H : ℝ) := by
      have hh := Nat.lt_floor_add_one (1 / (4 * p))
      rw [← heq] at hh
      linarith
    have hH₂ : (H : ℝ) ≤ 1 / (4 * p) := heq ▸ Nat.floor_le (by positivity)
    have hH₃ : (H : ℝ) * (2 * p) ≤ 1 / 2 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 4 * p)).mp hH₂
      linarith
    have hH₄ : 1 / (8 * p) ≤ (H : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hH₁ (show 0 ≤ 4 * p by positivity)
      rw [div_mul_cancel₀ _ (by positivity : 4 * p ≠ 0)] at hh
      linarith
    have hq : min 1 (2 * p) = 2 * p := min_eq_right (by linarith)
    have ha : 0 ≤ 1 - 2 * p := by linarith
    have hb := one_add_mul_le_pow (a := -(2 * p)) (by linarith : (-2 : ℝ) ≤ -(2 * p)) (H - 1)
    have hs : (1 : ℝ) / 2 ≤ (1 - 2 * p) ^ (H - 1) := by
      have hh := mul_le_mul_of_nonneg_right (show ((H - 1 : ℕ) : ℝ) ≤ H by exact_mod_cast Nat.sub_le H 1)
        (show 0 ≤ 2 * p by positivity)
      simp only [← sub_eq_add_neg, mul_neg] at hb
      linarith
    have hh := waitingSum_lower ha (by linarith : 1 - 2 * p ≤ 1) H
    have hscale := mul_le_mul hH₄ hs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : 0 ≤ (H : ℝ))
    rw [hq]
    change 1 / (16 * p) ≤ waitingSum _ H
    apply le_trans _ (hscale.trans hh)
    ring_nf
    exact le_rfl
  · have hs : ⌊1 / (4 * p)⌋₊ ≤ 1 := by
      have hlt : 1 / (4 * p) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      exact Nat.floor_le_one_of_le_one hlt.le
    rw [stageLength, max_eq_left hs, waitingSum]
    simp only [Finset.sum_range_one, pow_zero]
    exact (div_le_one (by positivity)).mpr (by linarith)

def stageFactor (m i : ℕ) : ℝ :=
  (1 / 128) * ((i : ℝ) / m) ^ 2 * (((m : ℝ) - i) / (m + 1))

lemma stageFactor_nonneg {m i : ℕ} (hi : i ≤ m) : 0 ≤ stageFactor m i := by
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi
  unfold stageFactor
  positivity

lemma stageFactor_le_one {m i : ℕ} (hi : i < m) : stageFactor m i ≤ 1 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi.le
  have ha : 0 ≤ (i : ℝ) / m := by positivity
  have ha' : (i : ℝ) / m ≤ 1 := (div_le_one hm).mpr hi'
  have hb : 0 ≤ ((m : ℝ) - i) / (m + 1) := by positivity
  have hb' : ((m : ℝ) - i) / (m + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hh : ((i : ℝ) / m) ^ 2 ≤ 1 := pow_le_one₀ ha ha'
  unfold stageFactor
  calc
    _ ≤ (1 : ℝ) * 1 * 1 := mul_le_mul
      (mul_le_mul (by norm_num) hh (by positivity) (by norm_num)) hb' hb (by norm_num)
    _ = _ := by norm_num

lemma factor_le_waiting (m i : ℕ) (hi : i ≤ m) {p : ℝ} (hp : 0 < p) :
    stageFactor m i ≤ goodRate m i p * waitingSum (1 - min 1 (2 * p)) (stageLength p) := by
  have heq : stageFactor m i = goodRate m i p * (1 / (16 * p)) := by
    unfold stageFactor goodRate
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (waiting_lower hp) (goodRate_nonneg hi hp.le)

variable {n k : ℕ} {μ : ℕ+}

lemma copying_product (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (hp' : (k + 1 : ℝ) / n ≤ p) (A : BitString n)
    (hA : (zeros A).card = k) (r : ℕ) (hr : r ≤ (μ : ℕ))
    (P : Population n μ) (hP : ordinary k P) (hcount : copyCount A P = (μ : ℕ) - r) :
    (∏ i ∈ Finset.Ico ((μ : ℕ) - r) (μ : ℕ), stageFactor μ i) ≤
      visit (step (jump k) p true) {Q | copyCount A Q = (μ : ℕ)} (r * stageLength p) P := by
  let J := stepMarked (jump k) p true (n := n) (μ := μ)
  let K := step (jump k) p true (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | copyCount A Q = (μ : ℕ)}
  have heq : (fun x ↦ (J x).map Prod.snd) = K := funext (stepMarked_population _ _ _)
  induction r generalizing P with
  | zero =>
    simp only [Nat.sub_zero, Finset.Ico_self, Finset.prod_empty, zero_mul] at hcount ⊢
    exact (visit_in K G 0 P hcount).ge
  | succ r ih =>
    let i := (μ : ℕ) - (r + 1)
    let I : Set (Population n μ) := {Q | ordinary k Q ∧ copyCount A Q = i}
    let N : Set (Population n μ) := {Q | ordinary k Q ∧ copyCount A Q = i + 1}
    let B := ∏ j ∈ Finset.Ico (i + 1) (μ : ℕ), stageFactor μ j
    have hB : 0 ≤ B := Finset.prod_nonneg (fun j hj ↦ stageFactor_nonneg (Finset.mem_Ico.mp hj).2.le)
    have ha : 0 ≤ 1 - min 1 (2 * p) := sub_nonneg.mpr (min_le_left _ _)
    have hi : i < (μ : ℕ) := by dsimp [i]; omega
    have hγ := goodRate_nonneg hi.le hp.1.le
    have hI : Disjoint I G := Set.disjoint_left.mpr (fun Q hQ hG ↦ by
      have h₁ : copyCount A Q = i := hQ.2
      have h₂ : copyCount A Q = (μ : ℕ) := hG
      omega)
    have hN (Q : Population n μ) (hQ : Q ∈ N) :
        B ≤ visit (fun x ↦ (J x).map Prod.snd) G (r * stageLength p) Q := by
      rw [heq]
      have hc : copyCount A Q = (μ : ℕ) - r := hQ.2.trans (by dsimp [i]; omega)
      simpa [B, show i + 1 = (μ : ℕ) - r by dsimp [i]; omega] using ih (by omega) Q hQ.1 hc
    have hh := copying_stage J G I N B hB (1 - min 1 (2 * p)) (goodRate μ i p) ha hγ
      (r * stageLength p) (fun _ v ↦ idle k v.1) (grow k A) hI hN
      (fun x _ v hIdle hGrow ↦ by have h₁ := hIdle.1; have h₂ := hGrow.1; simp_all)
      (fun x hx v hv hIdle ↦ by
        obtain ⟨ho, hc⟩ := idle_support hk hkn p A hA x hx.1 v hv hIdle
        exact ⟨ho, hc.trans hx.2⟩)
      (fun x hx v _ hGrow ↦ ⟨hGrow.2.1, hGrow.2.2.trans (congrArg (· + 1) hx.2)⟩)
      (fun x hx ↦ idle_probability hn p ⟨hp.1.le, hp.2⟩ hp' x hx.1)
      (fun x hx ↦ by
        rw [← show copyCount A x = i from hx.2]
        exact grow_probability hk hkn hn p ⟨hp.1.le, hp.2⟩ x hx.1 A hA)
      (stageLength p) P ⟨hP, hcount⟩
    rw [heq] at hh
    change (∏ j ∈ Finset.Ico i (μ : ℕ), stageFactor μ j) ≤
      visit K G ((r + 1) * stageLength p) P
    rw [Nat.succ_mul, Finset.prod_eq_prod_Ico_succ_bot hi]
    calc
      stageFactor μ i * B ≤ (goodRate μ i p * waitingSum (1 - min 1 (2 * p)) (stageLength p)) * B :=
        mul_le_mul_of_nonneg_right (factor_le_waiting _ _ hi.le hp.1) hB
      _ ≤ _ := by
        rw [show goodRate μ i p * waitingSum (1 - min 1 (2 * p)) (stageLength p) * B =
          B * goodRate μ i p * waitingSum (1 - min 1 (2 * p)) (stageLength p) by ring]
        exact hh

end
end Lax637351Proofs.CopyingWindow
