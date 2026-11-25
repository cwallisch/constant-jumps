import Lax637351Proofs.FillBand
import Lax637351Proofs.SelectedProgress

namespace Lax637351Proofs.BandColumn

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.Ordinary Lax637351Proofs.BestRank Lax637351Proofs.SlopeWindow
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.PairStep Lax637351Proofs.MaskKernel Lax637351Proofs.SlopeCharge
open Lax637351Proofs.TapeConcentration Lax637351Proofs.SelectedProgress Lax637351Proofs.FairCrossover
open Lax637351Proofs.FillBand
open scoped Classical ENNReal

noncomputable section

variable {n k B : ℕ} {μ : ℕ+}

def hasColumn (P : Population n μ) : Prop := ∃ j : Fin n, intact {j} P

lemma far_pair (P : Population n μ) (hP : ¬ hasColumn P) :
    ∃ i : Fin μ, rowZeros (P 0) ≤ (μ : ℕ) * ((mismatch (P 0) (P i)).card : ℝ) := by
  let Z := zeros (P 0)
  let D (i : Fin μ) := mismatch (P 0) (P i)
  have hd : Z ⊆ Finset.univ.biUnion D := by
    intro j hj
    have h : ∃ i, P i j ≠ 0 := by
      by_contra! hn
      exact hP ⟨j, fun t ht i ↦ by rw [Finset.mem_singleton.mp ht]; exact hn i⟩
    obtain ⟨i, hi⟩ := h
    have h0 : P 0 j = 0 := (mem_zeros _ _).mp hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [D, mismatch, h0, Ne.symm hi]⟩
  have hC := (Finset.card_le_card hd).trans (Finset.card_biUnion_le (s := Finset.univ) (t := D))
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i ↦ (D i).card)
  refine ⟨i, ?_⟩
  have hsum : Z.card ≤ (μ : ℕ) * (D i).card := by
    calc
      _ ≤ ∑ j, (D j).card := hC
      _ ≤ ∑ _j : Fin μ, (D i).card := Finset.sum_le_sum (fun j _ ↦ hi j)
      _ = _ := by simp
  dsimp only [rowZeros, D, Z] at *
  exact_mod_cast hsum

def columnProgress (B : ℕ) (μ : ℕ+) (p : ℝ) : ℝ :=
  p * Real.sqrt (B : ℝ) / (256 * Real.sqrt 6 * ((μ : ℕ) : ℝ) ^ 4)

lemma progress_no_column (hk : 0 < k) (hn : 2 ≤ n) (hkn : k ≤ n) (hBk : 4 * k ≤ B)
    (hB : 64 * Real.sqrt 6 * (μ : ℕ) ≤ Real.sqrt (B : ℝ))
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (hP : ordinary k P)
    (hband : ∀ i, (B : ℝ) / 2 ≤ rowZeros (P i) ∧ rowZeros (P i) ≤ B)
    (hcol : ¬ hasColumn P) :
    mean (step (jump k) p false P) averageZeros ≤ averageZeros P - columnProgress B μ p := by
  obtain ⟨j, hj⟩ := far_pair P hcol
  let m : ℝ := (μ : ℕ)
  let H : ℝ := (mismatch (P 0) (P j)).card
  have hm : 0 < m := by dsimp [m]; positivity
  have hm' : 1 ≤ m := by dsimp [m]; exact_mod_cast (Nat.succ_le_of_lt μ.pos)
  have hHN : 0 ≤ H := by dsimp [H]; positivity
  have hb : (B : ℝ) / 2 ≤ m * H := (hband 0).1.trans hj
  have hT : Real.sqrt (B : ℝ) ≤ 2 * m * Real.sqrt H := by
    have hB2 := Real.sq_sqrt (show (0 : ℝ) ≤ B by positivity)
    have hH2 := Real.sq_sqrt hHN
    have ha := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * m by positivity)
    have hn := mul_nonneg (show 0 ≤ (2 : ℝ) * m - 1 by linarith) (show 0 ≤ (B : ℝ) by positivity)
    have hc : Real.sqrt (B : ℝ) ^ 2 ≤ (2 * m * Real.sqrt H) ^ 2 := by
      rw [hB2, mul_pow, hH2]
      nlinarith only [ha, hn]
    nlinarith only [hc, show (0 : ℝ) ≤ Real.sqrt B from Real.sqrt_nonneg _, show 0 ≤ 2 * m * Real.sqrt H by positivity]
  have hh : Real.sqrt (B : ℝ) / (2 * m) ≤ Real.sqrt H := (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm (Real.sqrt H)] using hT)
  have hd : 32 * Real.sqrt 6 ≤ Real.sqrt H := by
    have h : 32 * Real.sqrt 6 ≤ Real.sqrt (B : ℝ) / (2 * m) := (le_div_iff₀ (by positivity)).mpr (by
      change 64 * Real.sqrt 6 * m ≤ _ at hB
      nlinarith only [hB])
    exact h.trans hh
  have hpos : 0 < B := by omega
  have Hprog := selected_progress_pair hk hkn hn hpos hBk p hp P hP 0 j (hband 0) (hband j) hd
  apply Hprog.trans
  apply sub_le_sub_left
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hp.1)
    (show 0 ≤ 128 * Real.sqrt 6 * m ^ 3 by positivity)
  unfold columnProgress
  change p * Real.sqrt (B : ℝ) / (256 * Real.sqrt 6 * m ^ 4) ≤ p * Real.sqrt H / (128 * Real.sqrt 6 * m ^ 3)
  convert h using 1; field_simp; ring

lemma average_bound (P : Population n μ) (b : ℝ) (h : ∀ i, b ≤ rowZeros (P i)) : b ≤ averageZeros P := by
  have hμ : (0 : ℝ) < (μ : ℕ) := by positivity
  apply (le_div_iff₀ hμ).mpr
  unfold totalZeros
  calc
    _ = ∑ _i : Fin μ, b := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ h i)

lemma average_upper (P : Population n μ) (b : ℝ) (h : ∀ i, rowZeros (P i) ≤ b) : averageZeros P ≤ b := by
  have hμ : (0 : ℝ) < (μ : ℕ) := by positivity
  apply (div_le_iff₀ hμ).mpr
  unfold totalZeros
  calc
    _ ≤ ∑ _i : Fin μ, b := Finset.sum_le_sum (fun i _ ↦ h i)
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

lemma column_window (hk : 0 < k) (hn : 2 ≤ n) (hBk : 4 * k ≤ B) (hBn : B ≤ n)
    (hB : 64 * Real.sqrt 6 * (μ : ℕ) ≤ Real.sqrt (B : ℝ))
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ)
    (a w lam : ℝ) (L : ℕ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) (hw : 0 ≤ w)
    (hP : fillBand a B P) (ha : (B : ℝ) / 2 < a - L - w)
    (hδ : tapeDelta L μ B w lam ≤ 1 / 8)
    (hwork : (B : ℝ) - (a - L - w) + n * tapeDelta L μ B w lam ≤ columnProgress B μ p * L / 8)
    (hpos : 0 < columnProgress B μ p * L) :
    (3 / 4 : ℝ) ≤ visit (step (jump k) p false) {Q | fixedColumn k B Q} L P := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | fixedColumn k B Q}
  let A : Set (Population n μ) := {Q | fillBand (B / 2 : ℝ) B Q ∧ ¬ hasColumn Q}
  let V (Q : Population n μ) := averageZeros Q
  let b := a - L - w
  let E : Set (Population n μ) := {Q | ∃ i, rowZeros (Q i) < b}
  let T := columnProgress B μ p
  let δ := tapeDelta L μ B w lam
  let ν := law (stopped K A) (PMF.pure P) L
  have hkn : k ≤ n := by omega
  have hBR : (4 : ℝ) * k ≤ B := by exact_mod_cast hBk
  have haB : a ≤ (B : ℝ) := (hP 0).1.trans (by exact_mod_cast (hP 0).2)
  have hb : 0 ≤ b := by dsimp only [b]; linarith only [ha, show (0 : ℝ) ≤ B by positivity]
  have hbn : b ≤ n := by
    have ht : (B : ℝ) ≤ n := by exact_mod_cast hBn
    dsimp only [b]
    linarith only [haB, ht, hw, show (0 : ℝ) ≤ L by positivity]
  have hOrd (Q : Population n μ) (hQ : fillBand (B / 2 : ℝ) B Q) : ordinary k Q := by
    intro i
    have hi : (k : ℝ) ≤ ((zeros (Q i)).card : ℝ) := by
      linarith only [(hQ i).1, hBR, show (0 : ℝ) ≤ k by positivity]
    exact_mod_cast hi
  let C : Set (Population n μ) := {Q | ∀ i, (zeros (Q i)).card ≤ B}
  have hC : ∀ Q ∈ ν.support, Q ∈ C := law_invariant (stopped K A) (PMF.pure P) C
    (fun Q hQ ↦ by rw [PMF.mem_support_pure_iff] at hQ; subst Q; exact fun i ↦ (hP i).2)
    (fun X hX Y hY ↦ by
      by_cases hs : X ∈ A
      · rw [stopped, if_pos hs] at hY
        exact fun i ↦ (safe_step hk hkn p false X (fun i ↦ Or.inl (hOrd X hs.1 i)) Y hY i).2.trans (hX i)
      · rw [stopped, if_neg hs, PMF.mem_support_pure_iff] at hY
        exact hY.symm ▸ hX) L
  have hE : mean ν (fun Q ↦ indicator (Q ∈ E)) ≤ δ := by
    exact stopped_count_concentration hn k p A L P a B (fun i ↦ ⟨(hP i).1, by exact_mod_cast (hP i).2⟩)
      w lam hlam hlam'
  have hV : b - n * δ ≤ mean ν V := by
    have hpt (Q : Population n μ) : b * (1 - indicator (Q ∈ E)) ≤ V Q := by
      by_cases hQ : Q ∈ E
      · have he : indicator (Q ∈ E) = 1 := if_pos hQ
        rw [he, sub_self, mul_zero]
        exact average_bound Q 0 (fun _ ↦ by unfold rowZeros; positivity)
      · rw [show indicator (Q ∈ E) = 0 from if_neg hQ, sub_zero, mul_one]
        exact average_bound Q b (fun i ↦ le_of_not_gt (fun hi ↦ hQ ⟨i, hi⟩))
    have hm := mean_mono ν hpt
    rw [mean_mul, mean_sub, mean_const] at hm
    have hh := mul_le_mul hbn hE (mean_nonneg _ (fun Q ↦ indic_nonneg (Q ∈ E))) (by positivity : 0 ≤ (n : ℝ))
    nlinarith only [hm, hh]
  have hT : 0 ≤ T := div_nonneg (mul_nonneg hp.1 (Real.sqrt_nonneg _)) (by positivity)
  have ht := active_window K A V T hT (fun Q hQ ↦ progress_no_column hk hn hkn hBk hB p hp Q
    (hOrd Q hQ.1) (fun i ↦ ⟨(hQ.1 i).1, by unfold rowZeros; exact_mod_cast (hQ.1 i).2⟩) hQ.2) L P
  have hvP : V P ≤ B := average_upper P B (fun i ↦ by unfold rowZeros; exact_mod_cast (hP i).2)
  have hlive : (ν.toOuterMeasure A).toReal ≤ 1 / 8 := by
    apply le_of_mul_le_mul_left _ hpos
    change mean ν V + T * L * (ν.toOuterMeasure A).toReal ≤ V P at ht
    change B - b + n * δ ≤ T * L / 8 at hwork
    nlinarith only [ht, hvP, hV, hwork]
  have hh := terminal_partition ν G A E (fun Q hQ ↦ by
    by_cases hE : Q ∈ E
    · exact Or.inr (Or.inr hE)
    have hBand : fillBand (B / 2 : ℝ) B Q := fun i ↦
      ⟨ha.le.trans (le_of_not_gt (fun hi ↦ hE ⟨i, hi⟩)), hC Q hQ i⟩
    by_cases hcol : hasColumn Q
    · exact Or.inl ⟨hOrd Q hBand, (bestZeros_le Q 0).trans (hC Q hQ 0), hcol⟩
    · exact Or.inr (Or.inl ⟨hBand, hcol⟩))
  have hvisit := terminal_mass_le_visit K A G L P
  change mean ν (fun Q ↦ indicator (Q ∈ G)) ≤ _ at hvisit
  linarith only [hh, hvisit, hE, hδ, hlive]

end
end Lax637351Proofs.BandColumn
