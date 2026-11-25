import Lax637351Proofs.SparseBarrier

namespace Lax637351Proofs.BarrierWindows

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting
open Lax637351Proofs.FiniteWindows Lax637351Proofs.SparseBarrier Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

lemma visit_after (K : α → PMF α) (E : Set α) (t s : ℕ) (x : α) :
    mean (law K (PMF.pure x) t) (visit K E s) ≤ visit K E (t + s) x := by
  induction t generalizing x with
  | zero => simp [mean_pure]
  | succ t ih =>
    by_cases hx : x ∈ E
    · rw [visit_in _ _ _ _ hx, ← mean_const (law K (PMF.pure x) (t + 1)) 1]
      exact mean_mono _ (visit_le_one K E s)
    · rw [law_first_step, mean_bind, show t + 1 + s = (t + s) + 1 by omega, visit, if_neg hx]
      exact mean_mono _ ih

lemma stop_visit_union (K : α → PMF α) (S E : Set α) (t : ℕ) (x : α) :
    visit K E t x ≤ visit K S t x + visit (stopped K Sᶜ) E t x := by
  induction t generalizing x with
  | zero => simpa only [visit, zero_add] using
      le_add_of_nonneg_left (show 0 ≤ if x ∈ S then (1 : ℝ) else 0 by split_ifs <;> norm_num)
  | succ t ih =>
    by_cases hx : x ∈ E
    · rw [visit_in _ _ _ _ hx, visit_in _ _ _ _ hx]
      exact le_add_of_nonneg_left (visit_nonneg _ _ _ _)
    by_cases hs : x ∈ S
    · rw [visit_in _ _ _ _ hs]
      exact (visit_le_one _ _ _ _).trans (le_add_of_nonneg_right (visit_nonneg _ _ _ _))
    rw [visit, if_neg hx, visit, if_neg hs, visit, if_neg hx, stopped, if_pos (show x ∈ Sᶜ from hs), ← mean_add]
    exact mean_mono _ ih

lemma visit_mono_on_invariant (K : α → PMF α) (C E F : Set α)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C)
    (hef : ∀ x ∈ C, x ∈ E → x ∈ F) (t : ℕ) (x : α) (hx : x ∈ C) :
    visit K E t x ≤ visit K F t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : x ∈ E
    · rw [visit_in _ _ _ _ h, visit_in _ _ _ _ (hef x hx h)]
    · rw [visit, if_neg h]
      exact visit_nonneg _ _ _ _
  | succ t ih =>
    by_cases h : x ∈ F
    · rw [visit_in _ _ _ _ h]
      exact visit_le_one _ _ _ _
    have he : x ∉ E := fun he ↦ h (hef x hx he)
    rw [visit, if_neg he, visit, if_neg h]
    exact mean_mono_on_support _ (fun y hy ↦ ih y (hC x hx y hy))

lemma stopped_good_le (K : α → PMF α) (A G : Set α) (hG : G ⊆ A) (t : ℕ) (x : α) :
    mean (law (stopped K A) (PMF.pure x) t) (fun y ↦ indicator (y ∈ G)) ≤
      mean (law K (PMF.pure x) t) (fun y ↦ indicator (y ∈ G)) := by
  induction t generalizing x with
  | zero => simp only [law_zero, le_refl]
  | succ t ih =>
    by_cases hx : x ∈ A
    · rw [law_first_step, law_first_step, mean_bind, mean_bind, stopped, if_pos hx]
      exact mean_mono _ ih
    · have he : x ∉ G := fun h ↦ hx (hG h)
      have hconst (t : ℕ) : law (stopped K A) (PMF.pure x) t = PMF.pure x := by
        induction t with
        | zero => rfl
        | succ t ih =>
          rw [law, ih, PMF.pure_bind, stopped, if_neg hx]
      rw [hconst, mean_pure, indicator, if_neg he]
      exact mean_nonneg _ (fun y ↦ indic_nonneg (y ∈ G))

lemma visit_recovery (K : α → PMF α) (G E : Set α) (s : ℕ) (q : ℝ) (_hq : 0 ≤ q)
    (h : ∀ x ∈ G, visit K E s x ≥ q) (t : ℕ) (x : α) :
    q * visit K G t x ≤ visit K E (t + s) x := by
  by_cases hg : Set.Nonempty G
  · obtain ⟨y, hy⟩ := hg
    have hq' : q ≤ 1 := (h y hy).trans (visit_le_one _ _ _ _)
    induction t generalizing x with
    | zero =>
      by_cases hx : x ∈ G
      · rw [visit_in _ _ _ _ hx, mul_one, zero_add]
        exact h x hx
      · simp only [visit, if_neg hx, mul_zero, zero_add]
        exact visit_nonneg _ _ _ _
    | succ t ih =>
      by_cases hx : x ∈ G
      · rw [visit_in _ _ _ _ hx, mul_one]
        exact (h x hx).trans (visit_monotone K E x (by omega))
      · by_cases he : x ∈ E
        · rw [visit_in _ _ _ _ he]
          exact mul_le_one₀ hq' (visit_nonneg _ _ _ _) (visit_le_one _ _ _ _)
        · rw [visit, if_neg hx, show t + 1 + s = (t + s) + 1 by omega, visit, if_neg he, ← mean_mul]
          exact mean_mono _ ih
  · have hh : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hg
    have hz := visit_eq_zero_of_absorbed K G Set.univ (by simp [hh])
      (fun _ _ _ _ ↦ Set.mem_univ _) t x (Set.mem_univ x)
    rw [hz, mul_zero]
    exact visit_nonneg _ _ _ _

lemma visit_rate_of_additive_drift (K : α → PMF α) (G : Set α) (X : α → ℝ) (B d : ℝ)
    (hB : ∀ x, 0 ≤ X x ∧ X x ≤ B) (hd : 0 ≤ d)
    (hdrift : ∀ x ∉ G, d ≤ mean (K x) (fun y ↦ X y - X x))
    (t : ℕ) (x : α) : d * t * (1 - visit K G t x) ≤ B := by
  let V (x : α) := B - X x
  have hV (x : α) (hx : x ∈ Gᶜ) : mean (K x) V ≤ V x - d := by
    have h := hdrift x hx
    unfold V
    rw [mean_sub, mean_const]
    rw [mean_sub, mean_const] at h
    linarith only [h]
  have h := active_window K Gᶜ V d hd hV t x
  rw [active_mass_compl, compl_compl] at h
  have hn := mean_nonneg (law (stopped K Gᶜ) (PMF.pure x) t) (f := V) (fun x ↦ sub_nonneg.mpr (hB x).2)
  dsimp only [V] at h
  linarith only [h, hn, (hB x).1]

end
end Lax637351Proofs.BarrierWindows
