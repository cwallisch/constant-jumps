import Lax637351Proofs.FillBand
import Lax637351Proofs.SlopeCharge

namespace Lax637351Proofs.CleanCopyEntry

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.Ordinary Lax637351Proofs.BestRank Lax637351Proofs.SlopeCopy
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.Mutation Lax637351Proofs.PairStep Lax637351Proofs.SlopeWindow
open Lax637351Proofs.CutoffEntry Lax637351Proofs.FillBand
open Lax637351Proofs.MaskKernel Lax637351Proofs.SlopeCharge
open scoped Classical ENNReal

noncomputable section

variable {n k B : ℕ} {μ : ℕ+}

def uniqueBest (A : BitString n) (P : Population n μ) : Prop :=
  (∃ i, P i = A) ∧ ∀ i, P i = A ∨ (zeros A).card < (zeros (P i)).card

lemma best_eq (A : BitString n) (P : Population n μ) (hP : uniqueBest A P) :
    bestZeros P = (zeros A).card := by
  obtain ⟨i, hi⟩ := hP.1
  obtain ⟨j, hj⟩ := bestZeros_attains P
  apply le_antisymm
  · simpa only [hi] using bestZeros_le P i
  · rw [← hj]
    rcases hP.2 j with he | he
    · rw [he]
    · exact he.le

lemma safe_clone (hkn : k ≤ n) (A : BitString n) (hA : k ≤ (zeros A).card)
    (P : Population n μ) (hP : uniqueBest A P)
    (i : Fin μ) (m : BitString n) (hm : ¬ dangerous (zeros A).card (P i) m)
    (Q : Population n μ) (hQ : Q ∈ (Transitions.insert (jump k) P (mutate (P i) m)).support) :
    uniqueBest A Q := by
  let z := mutate (P i) m
  have hz : z = A ∨ (zeros A).card < (zeros z).card := by
    by_cases he : z = P i
    · simpa only [he] using hP.2 i
    · exact Or.inr (lt_of_not_ge (fun h ↦ hm ⟨he, h⟩))
  have hf (j : Fin μ) (hj : P j = A) : Q j = A := by
    rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨v, hv, hvQ⟩
    rw [← hvQ]
    revert hv
    refine Fin.lastCases ?_ (fun u ↦ ?_) v
    · simp [replace, hj]
    · intro hv
      by_cases he : j = u
      · have hh := deletion_min_lastCases (jump k) P z u.castSucc hv (Fin.last (μ : ℕ))
        rw [Fin.lastCases_castSucc, Fin.lastCases_last, ← he, hj] at hh
        rcases hz with hz | hz
        · simpa [replace, he] using hz
        · have ht := (slope_order hkn hA (hA.trans hz.le)).mp hh
          omega
      · simp [replace, Function.update_of_ne he, hj]
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hP.1
    exact ⟨i, hf i hi⟩
  · intro i
    rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨v, _, rfl⟩
    refine Fin.lastCases ?_ (fun u ↦ ?_) v
    · simpa [replace] using hP.2 i
    · by_cases h : i = u
      · simpa [replace, h] using hz
      · simpa [replace, Function.update_of_ne h] using hP.2 i

lemma clean_exit_prob (hkn : k ≤ n) (hn : 2 ≤ n) (A : BitString n) (hA : k ≤ (zeros A).card)
    (P : Population n μ) (hP : uniqueBest A P) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    mean (step (jump k) p false P) (fun Q ↦ indicator (¬ uniqueBest A Q)) ≤
      p + ((zeros A).card + 1 : ℝ) / n := by
  let f (Q : Population n μ) := indicator (¬ uniqueBest A Q)
  let r := ((zeros A).card + 1 : ℝ) / n
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpt (i : Fin μ) (m : BitString n) :
      mean (Transitions.insert (jump k) P (mutate (P i) m)) f ≤
        indicator (dangerous (zeros A).card (P i) m) := by
    by_cases hm : dangerous (zeros A).card (P i) m
    · rw [indicator, if_pos hm]
      exact (mean_mono _ (fun Q ↦ indic_le_one (¬ uniqueBest A Q))).trans_eq (mean_const _ 1)
    · rw [indicator, if_neg hm]
      apply le_trans (b := mean (Transitions.insert (jump k) P (mutate (P i) m)) (fun _ ↦ 0)) _ (mean_const _ 0).le
      apply mean_mono_on_support
      intro Q hQ
      have ht := safe_clone hkn A hA P hP i m hm Q hQ
      simp [f, indicator, ht]
  have hs (i : Fin μ) :
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦
        mean (Transitions.insert (jump k) P (mutate (P i) m)) f) ≤ r := by
    apply (mean_mono _ (hpt i)).trans
    have hp := bestZeros_le P i
    rw [best_eq A P hP] at hp
    exact danger_bound hn (P i) hp
  have hCross : mean (parents P true) (fun z ↦
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦
        mean (Transitions.insert (jump k) P (mutate z m)) f)) ≤ 1 := by
    apply le_trans (b := mean (parents P true) (fun _ ↦ 1)) _ (mean_const _ 1).le
    apply mean_mono
    intro z
    apply le_trans (b := mean (independentBits n (1 / (n : ℝ))) (fun _ ↦ 1)) _ (mean_const _ 1).le
    apply mean_mono
    intro m
    exact (mean_mono _ (fun Q ↦ indic_le_one (¬ uniqueBest A Q))).trans_eq (mean_const _ 1)
  have hu := mean_mono (PMF.uniformOfFintype (Fin μ)) hs
  rw [mean_const] at hu
  change mean _ f ≤ _
  rw [mean_unmarked hp]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hCross hp.1)
    (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hp.2))
  apply hh.trans
  change p * 1 + (1 - p) * r ≤ p + r
  linarith only [mul_nonneg hp.1 hr]

lemma clean_copy_window (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ)
    (A : BitString n) (hA : k ≤ (zeros A).card ∧ (zeros A).card ≤ B) (hP : uniqueBest A P) :
    (3 / 4 : ℝ) - (fillLength μ : ℝ) * (p + ((B : ℝ) + 1) / n) ≤
      visit (step (jump k) p false) {Q | fixedColumn k B Q} (fillLength μ) P := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let r := (zeros A).card
  let I : Set (Population n μ) := {Q | uniqueBest A Q ∧ ∃ i, r < (zeros (Q i)).card}
  let G : Set (Population n μ) := {Q | fixedColumn k B Q}
  let E : Set (Population n μ) := {Q | ¬ uniqueBest A Q}
  let T := fillLength μ
  let q := p + (r + 1 : ℝ) / n
  let ν := law (stopped K I) (PMF.pure P) T
  have hbad := stopped_bad_mass K I E q (show 0 ≤ q from add_nonneg hp.1 (by positivity))
    (fun Q hQ ↦ clean_exit_prob hkn hn A hA.1 Q hQ.1 p hp) (PMF.pure P) T
  have hE : P ∉ E := not_not_intro hP
  rw [mean_pure, indicator, if_neg hE, zero_add] at hbad
  have hmOrd (Q : Population n μ) (hQ : uniqueBest A Q) : ordinary k Q := by
    rw [ordinary_iff_bestZeros, best_eq A Q hQ]
    exact hA.1
  have hδ : 0 < 1 / (8 * ((μ : ℕ) : ℝ) ^ 2) := by positivity
  have hmean := active_window K I (unfinished r) (1 / (8 * ((μ : ℕ) : ℝ) ^ 2)) hδ.le
    (fun Q hQ ↦ fill_drift hk hkn hn p hp Q (hmOrd Q hQ.1) (best_eq A Q hQ.1).le hQ.2) T P
  have hconst : (1 / (8 * ((μ : ℕ) : ℝ) ^ 2)) * (T : ℝ) = 4 * (μ : ℕ) := by
    dsimp [T, fillLength]
    push_cast
    field_simp; norm_num
  have hactive : (ν.toOuterMeasure I).toReal ≤ 1 / 4 := by
    rw [hconst] at hmean
    have h0 := mean_nonneg ν (unfinished_nonneg r)
    have h1 := unfinished_upper r P
    have hμ : 0 < 4 * ((μ : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hμ
    change mean ν (unfinished r) + (4 * ((μ : ℕ) : ℝ)) * (ν.toOuterMeasure I).toReal ≤ unfinished r P at hmean
    nlinarith only [h0, h1, hmean]
  have hc := terminal_partition ν G I E (fun Q _ ↦ by
    by_cases hE : Q ∈ E
    · exact Or.inr (Or.inr hE)
    have he : uniqueBest A Q := not_not.mp hE
    by_cases ht : ∃ i, r < (zeros (Q i)).card
    · exact Or.inr (Or.inl ⟨he, ht⟩)
    · have heq (i : Fin μ) : Q i = A := (he.2 i).resolve_right (fun hh ↦ ht ⟨i, hh⟩)
      have hPos : (zeros A).Nonempty := Finset.card_pos.mp (hk.trans_le hA.1)
      obtain ⟨j, hj⟩ := hPos
      have hi : intact {j} Q := by
        intro u hu i
        have hu' : u = j := Finset.mem_singleton.mp hu
        subst u
        rw [heq i]
        exact (mem_zeros A j).mp hj
      exact Or.inl ⟨hmOrd Q he, (best_eq A Q he).trans_le hA.2, j, hi⟩)
  have hgoal := terminal_mass_le_visit K I G T P
  change mean ν (fun Q ↦ indicator (Q ∈ G)) ≤ _ at hgoal
  change mean ν (fun Q ↦ indicator (Q ∈ E)) ≤ _ at hbad
  have hq : q ≤ p + ((B : ℝ) + 1) / n := by
    have he : (r : ℝ) ≤ B := by
      dsimp [r]
      exact_mod_cast hA.2
    dsimp only [q]
    gcongr
  have hscale := mul_le_mul_of_nonneg_left hq (show 0 ≤ (T : ℝ) by positivity)
  linarith only [hc, hgoal, hbad, hactive, hscale]

end
end Lax637351Proofs.CleanCopyEntry
