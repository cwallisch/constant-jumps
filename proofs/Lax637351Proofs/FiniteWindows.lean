import Lax637351Proofs.FiniteHitting
import Lax637351Proofs.PairStep

namespace Lax637351Proofs.FiniteWindows

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

omit [Fintype α] in
lemma indicator_eq_membership (E : Set α) :
    (fun x ↦ indicator (x ∈ E)) = (fun x ↦ if x ∈ E then 1 else 0) := by
  funext x
  by_cases h : x ∈ E <;> simp [indicator, h]

lemma mean_event (p : PMF α) (E : Set α) :
    mean p (fun x ↦ indicator (x ∈ E)) = (p.toOuterMeasure E).toReal := by
  rw [indicator_eq_membership, mean_indicator]

lemma active_mass_compl (K : α → PMF α) (A : Set α) (x : α) (t : ℕ) :
    ((law (stopped K A) (PMF.pure x) t).toOuterMeasure A).toReal = 1 - visit K Aᶜ t x := by
  let p := law (stopped K A) (PMF.pure x) t
  have hh := congrArg ENNReal.toReal (event_add_compl p A)
  have hn (E : Set α) : p.toOuterMeasure E ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _)
  rw [ENNReal.toReal_add (hn A) (hn Aᶜ), ENNReal.toReal_one] at hh
  have he := visit_eq_mean_stopped K Aᶜ t x
  rw [compl_compl, mean_indicator] at he
  change (p.toOuterMeasure A).toReal = 1 - _
  change _ = (p.toOuterMeasure Aᶜ).toReal at he
  linarith only [hh, he]

lemma active_window (K : α → PMF α) (A : Set α) (V : α → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hV : ∀ x ∈ A, mean (K x) V ≤ V x - g) (t : ℕ) (x : α) :
    mean (law (stopped K A) (PMF.pure x) t) V +
      g * t * ((law (stopped K A) (PMF.pure x) t).toOuterMeasure A).toReal ≤ V x := by
  have hh := stopped_telescoping K A V g hV (PMF.pure x) t
  rw [mean_pure] at hh
  have hsum : (t : ℝ) * ((law (stopped K A) (PMF.pure x) t).toOuterMeasure A).toReal ≤
      ∑ s ∈ Finset.range t, ((law (stopped K A) (PMF.pure x) s).toOuterMeasure A).toReal := by
    calc
      _ = ∑ _s ∈ Finset.range t, ((law (stopped K A) (PMF.pure x) t).toOuterMeasure A).toReal := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        rw [active_mass_compl, active_mass_compl]
        exact sub_le_sub_left (visit_monotone K Aᶜ x (Finset.mem_range.mp hs).le) 1
  have ht := mul_le_mul_of_nonneg_left hsum hg
  nlinarith only [ht, hh]

lemma stopped_bad_mass (K : α → PMF α) (A E : Set α) (q : ℝ) (hq : 0 ≤ q)
    (h : ∀ x ∈ A, mean (K x) (fun y ↦ indicator (y ∈ E)) ≤ q)
    (ν : PMF α) (t : ℕ) :
    mean (law (stopped K A) ν t) (fun y ↦ indicator (y ∈ E)) ≤
      mean ν (fun y ↦ indicator (y ∈ E)) + (t : ℝ) * q := by
  induction t with
  | zero => simp [law_zero]
  | succ t ih =>
    rw [law_succ, mean_bind]
    have hh := mean_mono (law (stopped K A) ν t) (fun (x : α) ↦
      show mean (stopped K A x) (fun y ↦ indicator (y ∈ E)) ≤ indicator (x ∈ E) + q by
        by_cases hx : x ∈ A
        · rw [stopped, if_pos hx]
          exact (h x hx).trans (le_add_of_nonneg_left (indic_nonneg _))
        · rw [stopped, if_neg hx, mean_pure]
          exact le_add_of_nonneg_right hq)
    rw [mean_add, mean_const] at hh
    push_cast
    linarith only [hh, ih]

lemma terminal_mass_le_visit (K : α → PMF α) (A G : Set α) (t : ℕ) (x : α) :
    mean (law (stopped K A) (PMF.pure x) t) (fun y ↦ indicator (y ∈ G)) ≤ visit K G t x := by
  induction t generalizing x with
  | zero =>
    rw [law_zero, mean_pure, visit]
    by_cases h : x ∈ G <;> simp [indicator, h]
  | succ t ih =>
    by_cases hx : x ∈ G
    · rw [visit_in _ _ _ _ hx, ← mean_const (law (stopped K A) (PMF.pure x) (t + 1)) (1 : ℝ)]
      exact mean_mono _ (fun y ↦ indic_le_one (y ∈ G))
    · rw [law_first_step, mean_bind]
      by_cases ha : x ∈ A
      · rw [stopped, if_pos ha, visit, if_neg hx]
        exact mean_mono _ ih
      · rw [stopped, if_neg ha, mean_pure]
        exact (ih x).trans (visit_monotone K G x (by omega))

lemma terminal_partition (ν : PMF α) (G A E : Set α)
    (h : ∀ x ∈ ν.support, x ∈ G ∨ x ∈ A ∨ x ∈ E) :
    1 ≤ mean ν (fun x ↦ indicator (x ∈ G)) +
      (ν.toOuterMeasure A).toReal + mean ν (fun x ↦ indicator (x ∈ E)) := by
  rw [← mean_event, ← mean_add, ← mean_add, ← mean_const ν (1 : ℝ)]
  apply mean_mono_on_support
  intro x hx
  rcases h x hx with hG | hA | hE
  · rw [indicator, if_pos hG]
    linarith only [indic_nonneg (x ∈ A), indic_nonneg (x ∈ E)]
  · have he : indicator (x ∈ A) = 1 := if_pos hA
    rw [he]
    linarith only [indic_nonneg (x ∈ G), indic_nonneg (x ∈ E)]
  · have he : indicator (x ∈ E) = 1 := if_pos hE
    rw [he]
    linarith only [indic_nonneg (x ∈ G), indic_nonneg (x ∈ A)]

lemma visit_union_upper (K : α → PMF α) (E F : Set α) (t : ℕ) (x : α) :
    visit K (E ∪ F) t x ≤ visit K E t x + visit K F t x := by
  induction t generalizing x with
  | zero =>
    simp only [visit, Set.mem_union]
    split_ifs <;> simp_all
  | succ t ih =>
    by_cases he : x ∈ E
    · rw [visit_in _ _ _ _ (Set.mem_union_left F he), visit_in _ _ _ _ he]
      exact le_add_of_nonneg_right (visit_nonneg _ _ _ _)
    by_cases hf : x ∈ F
    · rw [visit_in _ _ _ _ (Set.mem_union_right E hf), visit_in _ _ _ _ hf]
      exact le_add_of_nonneg_left (visit_nonneg _ _ _ _)
    rw [visit, if_neg (by simp [Set.mem_union, he, hf] : x ∉ E ∪ F),
      visit, if_neg he, visit, if_neg hf, ← mean_add]
    exact mean_mono _ ih

lemma visit_map {β : Type*} [Fintype β]
    (K : α → PMF α) (L : β → PMF β) (proj : α → β)
    (h : ∀ x, (K x).map proj = L (proj x)) (E : Set β) (t : ℕ) (x : α) :
    visit K (proj ⁻¹' E) t x = visit L E t (proj x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hx : proj x ∈ E
    · simp [visit, hx]
    · rw [visit, if_neg (show x ∉ proj ⁻¹' E from hx), visit, if_neg hx]
      have he : visit K (proj ⁻¹' E) t = fun y ↦ visit L E t (proj y) := funext ih
      rw [he, ← mean_map, h]

lemma visit_eq_mean_of_absorbing (K : α → PMF α) (E : Set α)
    (h : ∀ x ∈ E, ∀ y ∈ (K x).support, y ∈ E) (t : ℕ) (x : α) :
    visit K E t x = mean (law K (PMF.pure x) t) (fun y ↦ indicator (y ∈ E)) := by
  induction t generalizing x with
  | zero => simp [visit, mean_pure, indicator]
  | succ t ih =>
    by_cases hx : x ∈ E
    · rw [visit_in _ _ _ _ hx, ← mean_const (law K (PMF.pure x) (t + 1)) (1 : ℝ)]
      apply le_antisymm
      · apply mean_mono_on_support
        intro y hy
        have hy' := law_invariant K (PMF.pure x) E
          (fun z hz ↦ ((PMF.mem_support_pure_iff _ _).mp hz).symm ▸ hx) h (t + 1) y hy
        simp [indicator, hy']
      · exact mean_mono _ (fun y ↦ indic_le_one (y ∈ E))
    · rw [visit, if_neg hx, law_first_step, mean_bind]
      congr 1
      exact funext ih

end
end Lax637351Proofs.FiniteWindows
