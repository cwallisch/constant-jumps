import Lax637351Proofs.Sampling

namespace Lax637351Proofs.FiniteHitting

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

def visit (K : α → PMF α) (G : Set α) : ℕ → α → ℝ
  | 0, x => if x ∈ G then 1 else 0
  | t + 1, x => if x ∈ G then 1 else mean (K x) (visit K G t)

lemma visit_in (K : α → PMF α) (G : Set α) (t : ℕ) (x : α) (hx : x ∈ G) :
    visit K G t x = 1 := by cases t <;> simp [visit, hx]

lemma visit_nonneg (K : α → PMF α) (G : Set α) (t : ℕ) (x : α) :
    0 ≤ visit K G t x := by
  induction t generalizing x with
  | zero => unfold visit; split_ifs <;> norm_num
  | succ t ih =>
    simp only [visit]
    split_ifs
    · norm_num
    · exact mean_nonneg _ ih

lemma visit_le_one (K : α → PMF α) (G : Set α) (t : ℕ) (x : α) :
    visit K G t x ≤ 1 := by
  induction t generalizing x with
  | zero => unfold visit; split_ifs <;> norm_num
  | succ t ih =>
    simp only [visit]
    split_ifs
    · exact le_rfl
    · exact (mean_mono _ ih).trans_eq (mean_const _ 1)

lemma visit_monotone (K : α → PMF α) (G : Set α) (x : α) : Monotone (fun t ↦ visit K G t x) := by
  apply monotone_nat_of_le_succ
  intro t
  induction t generalizing x with
  | zero =>
    by_cases hx : x ∈ G
    · simp [visit, hx]
    · simpa [visit, hx] using visit_nonneg K G 1 x
  | succ t ih =>
    by_cases hx : x ∈ G
    · simp [visit, hx]
    · simpa only [visit, if_neg hx] using
        mean_mono (K x) (fun y ↦ ih y)

omit [Fintype α] in
lemma law_first_step (K : α → PMF α) (x : α) (t : ℕ) :
    law K (PMF.pure x) (t + 1) = (K x).bind (fun y ↦ law K (PMF.pure y) t) := by
  rw [Nat.add_comm, law_add, law_succ, law_zero, PMF.pure_bind]

lemma visit_eq_mean_stopped (K : α → PMF α) (G : Set α) (t : ℕ) (x : α) :
    visit K G t x = mean (law (stopped K Gᶜ) (PMF.pure x) t)
      (fun y ↦ if y ∈ G then 1 else 0) := by
  induction t generalizing x with
  | zero => simp [visit, mean_pure]
  | succ t ih =>
    rw [law_first_step, mean_bind]
    simp_rw [← ih]
    by_cases hx : x ∈ G
    · have hy : x ∉ Gᶜ := by simpa
      simp [stopped, hy, visit_in K G t x hx, visit, hx, mean_pure]
    · have hy : x ∈ Gᶜ := hx
      simp [stopped, hy, visit, hx]

lemma mean_visit_eq (K : α → PMF α) (G : Set α) (ν : PMF α) (t : ℕ) :
    mean ν (visit K G t) = ((law (stopped K Gᶜ) ν t).toOuterMeasure G).toReal := by
  change mean ν (fun x ↦ visit K G t x) = _
  simp_rw [visit_eq_mean_stopped]
  rw [← mean_bind, ← law_bind, PMF.bind_pure, mean_indicator]

lemma visit_eq_zero_of_absorbed (K : α → PMF α) (G A : Set α)
    (hAG : Disjoint A G)
    (hK : ∀ x ∈ A, ∀ y ∈ (K x).support, y ∈ A) (t : ℕ) (x : α) (hx : x ∈ A) :
    visit K G t x = 0 := by
  induction t generalizing x with
  | zero => simp [visit, show x ∉ G from Set.disjoint_left.mp hAG hx]
  | succ t ih =>
    rw [visit, if_neg (Set.disjoint_left.mp hAG hx)]
    apply le_antisymm _ (mean_nonneg _ (visit_nonneg K G t))
    rw [← mean_const (K x) 0]
    exact mean_mono_on_support _ (fun y hy ↦ (ih y (hK x hx y hy)).le)

lemma visit_agrees_on (K L : α → PMF α) (G C : Set α)
    (he : ∀ x ∈ C, K x = L x)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C) (t : ℕ) (x : α) (hx : x ∈ C) :
    visit K G t x = visit L G t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hG : x ∈ G
    · simp [visit, hG]
    · simp only [visit, if_neg hG, ← he x hx]
      exact le_antisymm
        (mean_mono_on_support _ (fun y hy ↦ (ih y (hC x hx y hy)).le))
        (mean_mono_on_support _ (fun y hy ↦ (ih y (hC x hx y hy)).ge))

end
end Lax637351Proofs.FiniteHitting
