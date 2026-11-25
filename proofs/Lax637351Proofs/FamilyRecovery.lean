import Lax637351Proofs.BarrierWindows

namespace Lax637351Proofs.FamilyRecovery

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting
open Lax637351Proofs.FiniteWindows Lax637351Proofs.SparseBarrier Lax637351Proofs.BarrierWindows
open Lax637351Proofs.PairStep Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {α ι : Type*} [Fintype α] [Fintype ι]

lemma visit_mono_event (K : α → PMF α) (E F : Set α) (h : E ⊆ F) (t : ℕ) (x : α) :
    visit K E t x ≤ visit K F t x := by
  induction t generalizing x with
  | zero =>
    by_cases hf : x ∈ F
    · rw [visit_in _ _ _ _ hf]
      exact visit_le_one _ _ _ _
    · have he : x ∉ E := fun hx ↦ hf (h hx)
      simp [visit, hf, he]
  | succ t ih =>
    by_cases hf : x ∈ F
    · rw [visit_in _ _ _ _ hf]
      exact visit_le_one _ _ _ _
    · have he : x ∉ E := fun hx ↦ hf (h hx)
      rw [visit, if_neg he, visit, if_neg hf]
      exact mean_mono _ ih

lemma terminal_mean_le_visit (K : α → PMF α) (E : Set α) (t : ℕ) (x : α) :
    mean (law K (PMF.pure x) t) (fun y ↦ indicator (y ∈ E)) ≤ visit K E t x := by
  have h := terminal_mass_le_visit K Set.univ E t x
  have he : stopped K (Set.univ : Set α) = K := by funext y; simp [stopped]
  simpa only [he] using h

lemma mean_union (p : PMF α) (E F : Set α) :
    mean p (fun x ↦ indicator (x ∈ E ∪ F)) ≤
      mean p (fun x ↦ indicator (x ∈ E)) + mean p (fun x ↦ indicator (x ∈ F)) := by
  rw [← mean_add]
  apply mean_mono
  intro x
  by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [indicator, Set.mem_union, he, hf]

omit [Fintype ι] in
lemma mean_finset_union (p : PMF α) (s : Finset ι) (E : ι → Set α) :
    mean p (fun x ↦ indicator (∃ i ∈ s, x ∈ E i)) ≤
      ∑ i ∈ s, mean p (fun x ↦ indicator (x ∈ E i)) := by
  rw [← mean_sum]
  apply mean_mono
  intro x
  by_cases h : ∃ i ∈ s, x ∈ E i
  · obtain ⟨i, hi, hE⟩ := h
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ s) ↦ indic_nonneg (x ∈ E j)) hi
    rw [show indicator (x ∈ E i) = 1 from if_pos hE] at hsum
    exact (show indicator (∃ j ∈ s, x ∈ E j) ≤ 1 from indic_le_one _).trans hsum
  · rw [indicator, if_neg h]
    exact Finset.sum_nonneg (fun i _ ↦ indic_nonneg _)

lemma one_barrier (K : α → PMF α) (X : α → ℝ) (C : Set α)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C)
    (l u b θ lam r : ℝ) (hl : l ≤ u) (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hθ : lam ≤ θ) (hr : 0 ≤ r)
    (hsmall : ∀ x, l ≤ X x → X x ≤ u → ∀ y ∈ (K x).support, |lam * (X y - X x)| ≤ 1)
    (hdrift : ∀ x, l ≤ X x → X x ≤ u → θ * mean (K x) (fun y ↦ (X y - X x) ^ 2) ≤
      mean (K x) (fun y ↦ X y - X x))
    (hjump : ∀ x ∈ C, ∀ y ∈ (K x).support, |X y - X x| ≤ b)
    (hchange : ∀ x ∈ C, mean (K x) (fun y ↦ indicator (y ≠ x)) ≤ r)
    (t : ℕ) (x : α) (hx : x ∈ C) (hx' : u - b ≤ X x) :
    visit K {y | X y < l} t x ≤ ((t : ℝ) * r + 1) * Real.exp (-lam * (u - b - l)) := by
  have hh := sparse_visit K (fun _ : Unit ↦ X) C hC l u b θ lam 1 r hl hb hlam hθ (by norm_num) hr
    (fun _ ↦ hsmall) (fun _ ↦ hdrift)
    (fun z hz ↦ by
      have h := Finset.card_filter_le (s := (Finset.univ : Finset Unit)) (p := fun _ ↦ X z ≤ u)
      simpa only [Finset.card_univ, Fintype.card_unit, Nat.cast_one, Nat.cast_le] using
        (show ((((Finset.univ : Finset Unit).filter (fun _ ↦ X z ≤ u)).card : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) by exact_mod_cast h))
    (fun z hz w hw _ h ↦ by linarith only [(abs_le.mp (hjump z hz w hw)).1, h])
    hchange t x hx (fun _ ↦ hx')
  simpa only [mul_one, Set.iUnion_const] using hh

omit [Fintype α] in
lemma subset_count (X : ι → α → ℝ) (u : ℝ) (x : α) (s : Finset ι) :
    ((Finset.univ.filter (fun i : s ↦ X i.val x ≤ u)).card : ℝ) ≤
      ((Finset.univ.filter (fun i ↦ X i x ≤ u)).card : ℝ) := by
  let q : Finset s := Finset.univ.filter (fun i : s ↦ X i.val x ≤ u)
  have h : q.image Subtype.val ⊆ Finset.univ.filter (fun i ↦ X i x ≤ u) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have h' := Finset.card_le_card h
  rw [Finset.card_image_of_injective q Subtype.val_injective] at h'
  exact_mod_cast h'

lemma recovery_window (K : α → PMF α) (X : ι → α → ℝ) (C A : Set α)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C)
    (hstop : ∀ x ∉ A, K x = PMF.pure x) (hAC : A ⊆ C)
    (l u b θ lam m r B d ζ : ℝ) (hl : l ≤ u)
    (hb : 0 ≤ b) (hlam : 0 ≤ lam) (hθ : lam ≤ θ) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hd : 0 ≤ d) (hζ : 0 ≤ ζ)
    (hsmall : ∀ i x, l ≤ X i x → X i x ≤ u → ∀ y ∈ (K x).support, |lam * (X i y - X i x)| ≤ 1)
    (hdrift : ∀ i x, l ≤ X i x → X i x ≤ u → θ * mean (K x) (fun y ↦ (X i y - X i x) ^ 2) ≤
      mean (K x) (fun y ↦ X i y - X i x))
    (hcount : ∀ x ∈ C, ((Finset.univ.filter (fun i ↦ X i x ≤ u)).card : ℝ) ≤ m)
    (hjump : ∀ x ∈ C, ∀ y ∈ (K x).support, ∀ i, |X i y - X i x| ≤ b)
    (hchange : ∀ x ∈ C, mean (K x) (fun y ↦ indicator (y ≠ x)) ≤ r)
    (hB : ∀ i x, 0 ≤ X i x ∧ X i x ≤ B)
    (hentry : ∀ i, ∀ x ∈ A, X i x < u → d ≤ mean (K x) (fun y ↦ X i y - X i x))
    (t : ℕ) (ht : 0 < d * (t : ℝ)) (ht' : B ≤ d * (t : ℝ) * ζ) (x : α) (hx : x ∈ C) :
    mean (law K (PMF.pure x) t) (fun y ↦ indicator (y ∈ A ∧ ∃ i, X i y < l)) ≤
      m * ζ + 2 * m * ((t : ℝ) * r + 1) * Real.exp (-lam * (u - b - l)) := by
  let lo : Finset ι := Finset.univ.filter (fun i ↦ X i x ≤ u)
  let hi : Finset ι := Finset.univ \ lo
  let E (i : ι) : Set α := {y | y ∈ A ∧ X i y < l}
  let G (i : ι) : Set α := {y | y ∉ A ∨ u ≤ X i y}
  let β := ((t : ℝ) * r + 1) * Real.exp (-lam * (u - b - l))
  let ν := law K (PMF.pure x) t
  have hβ : 0 ≤ β := by unfold β; positivity
  have hnu (y : α) (hy : y ∈ ν.support) : y ∈ C :=
    law_invariant K (PMF.pure x) C (fun z hz ↦ ((PMF.mem_support_pure_iff _ _).mp hz).symm ▸ hx) hC t y hy
  have hlimit (i : ι) : 1 - visit K (G i) t x ≤ ζ := by
    have h := visit_rate_of_additive_drift K (G i) (X i) B d (hB i) hd (by
      intro y hy
      have hn : ¬(y ∉ A ∨ u ≤ X i y) := hy
      push Not at hn
      exact hentry i y hn.1 hn.2) t x
    exact (mul_le_mul_iff_of_pos_left ht).mp (h.trans ht')
  have heach (i : ι) : mean ν (fun y ↦ indicator (y ∈ E i)) ≤ ζ + β := by
    have hh : ∀ y ∈ G i, visit K (E i) t y ≤ β := by
      intro y hy
      rcases hy with hy | hy
      · have hz := visit_eq_zero_of_absorbed K (E i) Aᶜ
          (by rw [Set.disjoint_left]; exact fun z hz hE ↦ hz hE.1)
          (fun z hz w hw ↦ by rw [hstop z hz, PMF.mem_support_pure_iff] at hw; simpa [hw] using hz) t y hy
        rw [hz]
        exact hβ
      · by_cases hA' : y ∈ A
        · exact (visit_mono_event K (E i) {z | X i z < l} (fun z hz ↦ hz.2) t y).trans
            (one_barrier K (X i) C hC l u b θ lam r hl hb hlam hθ hr (hsmall i) (hdrift i)
              (fun z hz w hw ↦ hjump z hz w hw i) hchange t y (hAC hA') (by linarith only [hy, hb]))
        · have hz := visit_eq_zero_of_absorbed K (E i) Aᶜ
            (by rw [Set.disjoint_left]; exact fun z hz hE ↦ hz hE.1)
            (fun z hz w hw ↦ by rw [hstop z hz, PMF.mem_support_pure_iff] at hw; simpa [hw] using hz) t y hA'
          rw [hz]
          exact hβ
    exact (visit_terminal K (G i) (E i) β hβ t hh x).trans (add_le_add_left (hlimit i) β)
  have hLo : mean ν (fun y ↦ indicator (∃ i ∈ lo, y ∈ E i)) ≤ m * (ζ + β) := by
    apply (mean_finset_union ν lo E).trans
    have h := Finset.sum_le_sum (s := lo) (fun i _ ↦ heach i)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hcount x hx) (add_nonneg hζ hβ))
  have hHi : mean ν (fun y ↦ indicator (∃ i ∈ hi, y ∈ E i)) ≤ m * β := by
    let Y (i : hi) := X i.val
    have he : {y | ∃ i ∈ hi, y ∈ E i} ⊆ ⋃ i : hi, {y | Y i y < l} := by
      intro y hy
      obtain ⟨i, hi', hE⟩ := hy
      exact Set.mem_iUnion.mpr ⟨⟨i, hi'⟩, hE.2⟩
    have hterm := terminal_mean_le_visit K {y | ∃ i ∈ hi, y ∈ E i} t x
    apply hterm.trans ((visit_mono_event K _ _ he t x).trans _)
    have hh := sparse_visit K Y C hC l u b θ lam m r hl hb hlam hθ hm hr
      (fun i ↦ hsmall i.val) (fun i ↦ hdrift i.val)
      (fun z hz ↦ (subset_count X u z hi).trans (hcount z hz))
      (fun z hz w hw i h ↦ by linarith only [(abs_le.mp (hjump z hz w hw i.val)).1, h])
      hchange t x hx (fun i ↦ by
        have h : i.val ∉ lo := (Finset.mem_sdiff.mp i.property).2
        have hp : u < X i.val x := lt_of_not_ge (fun hp ↦ h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
        change u - b ≤ X i.val x
        linarith only [hp, hb])
    exact hh.trans_eq (by unfold β; ring)
  have htotal : {y | y ∈ A ∧ ∃ i, X i y < l} =
      {y | ∃ i ∈ lo, y ∈ E i} ∪ {y | ∃ i ∈ hi, y ∈ E i} := by
    ext y
    constructor
    · rintro ⟨hA, i, hX⟩
      by_cases h : i ∈ lo
      · exact Or.inl ⟨i, h, hA, hX⟩
      · exact Or.inr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩, hA, hX⟩
    · rintro (⟨i, _, hA, hX⟩ | ⟨i, _, hA, hX⟩)
      · exact ⟨hA, i, hX⟩
      · exact ⟨hA, i, hX⟩
  change mean ν (fun y ↦ indicator (y ∈ {z | z ∈ A ∧ ∃ i, X i z < l})) ≤ _
  rw [htotal]
  have h := mean_union ν {y | ∃ i ∈ lo, y ∈ E i} {y | ∃ i ∈ hi, y ∈ E i}
  rw [show 2 * m * ((t : ℝ) * r + 1) * Real.exp (-lam * (u - b - l)) = 2 * m * β by unfold β; ring]
  exact h.trans ((add_le_add hLo hHi).trans_eq (by ring))

end
end Lax637351Proofs.FamilyRecovery
