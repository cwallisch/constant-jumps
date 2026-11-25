import Lax637351Proofs.CutoffEntry

namespace Lax637351Proofs.FillBand

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.Descent Lax637351Proofs.Ordinary Lax637351Proofs.BestRank
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.Mutation Lax637351Proofs.PairStep Lax637351Proofs.SlopeWindow
open Lax637351Proofs.CutoffEntry Lax637351Proofs.PairAveraging
open scoped Classical ENNReal

noncomputable section

variable {n k B : ℕ} {μ : ℕ+}

def unfinished (B : ℕ) (P : Population n μ) : ℝ :=
  ∑ i, indicator (B < (zeros (P i)).card)

def fillLength (μ : ℕ+) : ℕ := 32 * (μ : ℕ) ^ 3

def fillBand (a : ℝ) (B : ℕ) (P : Population n μ) : Prop :=
  ∀ i, a ≤ ((zeros (P i)).card : ℝ) ∧ (zeros (P i)).card ≤ B

lemma unfinished_nonneg (B : ℕ) (P : Population n μ) : 0 ≤ unfinished B P :=
  Finset.sum_nonneg (fun _ _ ↦ indic_nonneg _)

lemma unfinished_upper (B : ℕ) (P : Population n μ) : unfinished B P ≤ (μ : ℕ) := by
  unfold unfinished
  calc
    _ ≤ ∑ _i : Fin μ, (1 : ℝ) := Finset.sum_le_sum (fun _ _ ↦ indic_le_one _)
    _ = _ := by simp

lemma fill_drift (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ordinary k P) (hbest : bestZeros P ≤ B)
    (hbad : ∃ i, B < (zeros (P i)).card) :
    mean (step (jump k) p false P) (unfinished B) ≤
      unfinished B P - 1 / (8 * ((μ : ℕ) : ℝ) ^ 2) := by
  obtain ⟨i, hi⟩ := bestZeros_attains P
  obtain ⟨j, hj⟩ := hbad
  let A := P i
  let f (Q : Population n μ) := unfinished B P - unfinished B Q
  have hsup (Q : Population n μ) (hQ : Q ∈ (Transitions.insert (jump k) P A).support) :
      1 ≤ f Q := by
    obtain ⟨d, he, hd⟩ := improved_site hkn P hP A (hP i) j (by dsimp [A]; omega) Q hQ
    have hh := sum_update P d A (fun z ↦ indicator (B < (zeros z).card))
    have hd' : B < (zeros (P d)).card := hj.trans_le hd
    have hi' : ¬ B < (zeros A).card := not_lt_of_ge (hi.trans_le hbest)
    have heq₁ : indicator (B < (zeros A).card) = 0 := if_neg hi'
    have heq₂ : indicator (B < (zeros (P d)).card) = 1 := if_pos hd'
    rw [heq₁, heq₂] at hh
    dsimp only [f]
    rw [he]
    change unfinished B (Function.update P d A) - unfinished B P = 0 - 1 at hh
    linarith only [hh]
  let F (Q : Population n μ) := indicator (1 ≤ f Q)
  have hchoice : 1 ≤ mean (Transitions.insert (jump k) P (mutate (P i) (mask ∅))) F := by
    have he : mutate (P i) (mask ∅) = A := by funext j; simp [A, mutate, mask]
    rw [he, ← mean_const (Transitions.insert (jump k) P A) (1 : ℝ)]
    apply mean_mono_on_support
    intro Q hQ
    have he : F Q = 1 := if_pos (hsup Q hQ)
    rw [he]
  have hm := mutation_choice_lower hn P i F (fun Q ↦ indic_nonneg _) ∅ 1 (by norm_num) hchoice
  simp only [Finset.card_empty, pow_zero, mul_one] at hm
  have hpF := same_parent_lower p hp P i F (fun Q ↦ indic_nonneg _) (1 / 8) (by norm_num) hm
  have hpoint (Q : Population n μ) (hQ : Q ∈ (step (jump k) p false P).support) : F Q ≤ f Q := by
    by_cases hf : 1 ≤ f Q
    · simpa only [F, indicator, if_pos hf] using hf
    · simp only [F, indicator, if_neg hf]
      apply sub_nonneg.mpr
      apply Finset.sum_le_sum
      intro j _
      have hmon := (safe_step hk hkn p false P (fun i ↦ Or.inl (hP i)) Q hQ j).2
      by_cases h : B < (zeros (Q j)).card
      · simp [indicator, h, h.trans_le hmon]
      · simpa only [indicator, if_neg h] using indic_nonneg (B < (zeros (P j)).card)
  have hf := mean_mono_on_support _ hpoint
  change _ ≤ mean _ (fun Q ↦ unfinished B P - unfinished B Q) at hf
  rw [mean_sub, mean_const] at hf
  have he : (1 / 8 : ℝ) / ((μ : ℕ) : ℝ) ^ 2 = 1 / (8 * ((μ : ℕ) : ℝ) ^ 2) := by ring
  rw [he] at hpF
  linarith only [hf, hpF]

lemma fill_window (hk : 0 < k) (hn : 2 ≤ n) (hkn : k ≤ B ∧ 2 * B ≤ n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (d lam : ℝ) (hd : 0 ≤ d) (hl : 0 ≤ lam) (hl' : lam ≤ 1)
    (ha : (k : ℝ) ≤ (B : ℝ) - ((fillLength μ : ℝ) + 1) * d)
    (P : Population n μ) (hP : (B : ℝ) - d ≤ (bestZeros P : ℝ) ∧ bestZeros P ≤ B) :
    (3 / 4 : ℝ) - (fillLength μ : ℝ) * Real.exp ((B : ℝ) * lam ^ 2 - lam * d) ≤
      visit (step (jump k) p false) {Q | fillBand ((B : ℝ) - ((fillLength μ : ℝ) + 1) * d) B Q}
        (fillLength μ) P := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let T := fillLength μ
  let a := (B : ℝ) - ((T : ℝ) + 1) * d
  let A : Set (Population n μ) := {Q | a ≤ (bestZeros Q : ℝ) ∧ bestZeros Q ≤ B ∧ ∃ i, B < (zeros (Q i)).card}
  let C : Set (Population n μ) := {Q | bestZeros Q ≤ B}
  let G : Set (Population n μ) := {Q | fillBand a B Q}
  let E (t : ℕ) : Set (Population n μ) := {Q | (bestZeros Q : ℝ) < (B : ℝ) - ((t : ℝ) + 1) * d}
  let W := stopped K A
  let ν (t : ℕ) := law W (PMF.pure P) t
  let q := Real.exp ((B : ℝ) * lam ^ 2 - lam * d)
  let δ := 1 / (8 * ((μ : ℕ) : ℝ) ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hni : k ≤ n := by omega
  have hxOrd (Q : Population n μ) (hQ : Q ∈ A) : ordinary k Q := by
    apply (ordinary_iff_bestZeros Q).mpr
    have h : (k : ℝ) ≤ bestZeros Q := ha.trans hQ.1
    exact_mod_cast h
  have hsupp (t : ℕ) (Q : Population n μ) (hQ : Q ∈ (ν t).support) : Q ∈ C := by
    apply law_invariant W (PMF.pure P) C
    · intro X hX
      have he := (PMF.mem_support_pure_iff _ _).mp hX
      exact he.symm ▸ hP.2
    · intro X hX Y hY
      by_cases hA : X ∈ A
      · rw [show W X = K X by simp [W, stopped, hA]] at hY
        exact (best_decreases hk hni p X (hxOrd X hA) Y hY).trans hX
      · rw [show W X = PMF.pure X by simp [W, stopped, hA], PMF.mem_support_pure_iff] at hY
        exact hY.symm ▸ hX
    · exact hQ
  have hbad (t : ℕ) : mean (ν t) (fun Y ↦ indicator (Y ∈ E t)) ≤ (t : ℝ) * q := by
    induction t with
    | zero =>
      have he : P ∉ E 0 := by
        change ¬ (bestZeros P : ℝ) < (B : ℝ) - (((0 : ℕ) : ℝ) + 1) * d
        push_cast
        linarith only [hP.1]
      simp [ν, law_zero, mean_pure, indicator, he]
    | succ t ih =>
      have hpt (X : Population n μ) :
          mean (W X) (fun Y ↦ indicator (Y ∈ E (t + 1))) ≤ indicator (X ∈ E t) + q := by
        by_cases hx : X ∈ E t
        · have h := (mean_mono (W X) (fun Y ↦ indic_le_one (Y ∈ E (t + 1)))).trans_eq (mean_const _ 1)
          rw [indicator, if_pos hx]
          exact h.trans (le_add_of_nonneg_right (show 0 ≤ q from (Real.exp_pos _).le))
        have hX : (B : ℝ) - ((t : ℝ) + 1) * d ≤ (bestZeros X : ℝ) := le_of_not_gt hx
        have he : (B : ℝ) - (((t + 1 : ℕ) : ℝ) + 1) * d = (B : ℝ) - ((t : ℝ) + 1) * d - d := by
          push_cast
          ring
        by_cases hA : X ∈ A
        · rw [show W X = K X by simp [W, stopped, hA], indicator, if_neg hx, zero_add]
          let r := (B : ℝ) - ((t : ℝ) + 1) * d
          have hrB : r ≤ B := sub_le_self _ (by positivity)
          have hr : r ≤ n / 2 := by
            have hh : (2 : ℝ) * B ≤ n := by exact_mod_cast hkn.2
            linarith only [hrB, hh]
          have hh := one_step_drop (k := k) hn p hp false X r d lam hr hX hd hl hl'
          have he' : (fun Y : Population n μ ↦ indicator (Y ∈ E (t + 1))) =
              fun Y ↦ indicator ((bestZeros Y : ℝ) < r - d) := by
            funext Y
            change indicator ((bestZeros Y : ℝ) < (B : ℝ) - (((t + 1 : ℕ) : ℝ) + 1) * d) = _
            rw [he]
          rw [he']
          exact hh.trans (Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_right hrB (sq_nonneg lam)
            linarith only [h]))
        · have hE : X ∉ E (t + 1) := by
            change ¬ (bestZeros X : ℝ) < (B : ℝ) - (((t + 1 : ℕ) : ℝ) + 1) * d
            rw [he]
            linarith only [hX, hd]
          simp [W, stopped, hA, mean_pure, indicator, hE, hx, q, (Real.exp_pos _).le]
      have hh := mean_mono (ν t) hpt
      rw [mean_add, mean_const] at hh
      simp only [ν, law_succ, mean_bind]
      push_cast
      linarith only [hh, ih]
  have hmean := active_window K A (unfinished B) δ hδ.le
    (fun X hX ↦ fill_drift hk hni hn p hp X (hxOrd X hX) hX.2.1 hX.2.2) T P
  have hconst : δ * (T : ℝ) = 4 * (μ : ℕ) := by
    dsimp [δ, T, fillLength]
    push_cast
    field_simp; norm_num
  rw [hconst] at hmean
  have hactive : ((ν T).toOuterMeasure A).toReal ≤ 1 / 4 := by
    have h0 := mean_nonneg (ν T) (unfinished_nonneg B)
    have h1 := unfinished_upper B P
    have hμ : 0 < 4 * ((μ : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hμ
    change mean (ν T) (unfinished B) + (4 * ((μ : ℕ) : ℝ)) * ((ν T).toOuterMeasure A).toReal ≤ unfinished B P at hmean
    nlinarith only [h0, h1, hmean]
  have hp := terminal_partition (ν T) G A (E T) (fun X hX ↦ by
    by_cases hE : X ∈ E T
    · exact Or.inr (Or.inr hE)
    have hs : a ≤ (bestZeros X : ℝ) := le_of_not_gt hE
    have hc : bestZeros X ≤ B := hsupp T X hX
    by_cases hA : ∃ i, B < (zeros (X i)).card
    · exact Or.inr (Or.inl ⟨hs, hc, hA⟩)
    · apply Or.inl
      intro i
      exact ⟨hs.trans (by exact_mod_cast bestZeros_le X i),
        le_of_not_gt (fun h ↦ hA ⟨i, h⟩)⟩)
  have hfin := terminal_mass_le_visit K A G T P
  have hb := hbad T
  change mean (ν T) (fun Y ↦ indicator (Y ∈ G)) ≤ _ at hfin
  linarith only [hp, hfin, hb, hactive]

end
end Lax637351Proofs.FillBand
