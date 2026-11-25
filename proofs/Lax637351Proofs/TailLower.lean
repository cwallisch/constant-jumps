import Lax637351Proofs.RuntimeTransfer
import Lax637351Proofs.FiniteHitting
import Mathlib.Algebra.Order.Floor.Semiring

namespace Lax637351Proofs.TailLower

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting
open Lax637351Proofs.RuntimeTransfer
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [Fintype α]

lemma visit_absorbing (K : α → PMF α) (G : Set α)
    (habs : ∀ x ∈ G, ∀ y ∈ (K x).support, y ∈ G) (t : ℕ) (x : α) :
    visit K G t x = ((law K (PMF.pure x) t).toOuterMeasure G).toReal := by
  induction t generalizing x with
  | zero =>
    rw [law_zero, PMF.toOuterMeasure_pure_apply, visit]
    by_cases h : x ∈ G
    · simp only [if_pos h, ENNReal.toReal_one]
    · simp only [if_neg h, ENNReal.toReal_zero]
  | succ t ih =>
    by_cases hx : x ∈ G
    · rw [visit, if_pos hx, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr ?_, ENNReal.toReal_one]
      apply law_invariant _ _ _ _ habs
      intro y hy
      exact ((PMF.mem_support_pure_iff _ _).mp hy).symm ▸ hx
    · rw [visit, if_neg hx, law_first_step, ← mean_indicator, mean_bind]
      have hh (y : α) : visit K G t y =
          mean (law K (PMF.pure y) t) (fun z ↦ if z ∈ G then 1 else 0) := by
        rw [mean_indicator]
        exact ih y
      change mean (K x) (fun y ↦ visit K G t y) = _
      simp only [hh]

lemma tail_from_affine (K : α → PMF α) (G : Set α) (x : α)
    (habs : ∀ x ∈ G, ∀ y ∈ (K x).support, y ∈ G)
    (a s c : ℝ) (ha : 0 < a) (hs : 0 ≤ s) (hcs : s + c ≤ 1 / 2)
    (h : ∀ t : ℕ, visit K G t x ≤ (t : ℝ) * a + c) :
    ENNReal.ofReal (s / (2 * a)) ≤ tailSum K Gᶜ (PMF.pure x) := by
  let H := ⌊s / a⌋₊ + 1
  have hm (t : ℕ) (ht : t ∈ Finset.range H) :
      (1 / 2 : ℝ) ≤ ((law K (PMF.pure x) t).toOuterMeasure Gᶜ).toReal := by
    have ht' : t ≤ ⌊s / a⌋₊ := by have := Finset.mem_range.mp ht; omega
    have ht'' : (t : ℝ) ≤ s / a :=
      (by exact_mod_cast ht' : (t : ℝ) ≤ (⌊s / a⌋₊ : ℕ)).trans (Nat.floor_le (by positivity))
    have ha' := mul_le_mul_of_nonneg_right ht'' ha.le
    have hnorm : s / a * a = s := by field_simp
    rw [hnorm] at ha'
    have hvisit := (h t).trans ((add_le_add_left ha' c).trans hcs)
    rw [visit_absorbing K G habs] at hvisit
    let ν := law K (PMF.pure x) t
    have hle := event_add_compl ν G
    have hne := fun S : Set α ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one ν S)
    have hh := congrArg ENNReal.toReal hle
    rw [ENNReal.toReal_add (hne G) (hne Gᶜ), ENNReal.toReal_one] at hh
    change _ ≤ (ν.toOuterMeasure Gᶜ).toReal
    change (ν.toOuterMeasure G).toReal ≤ _ at hvisit
    linarith
  have hmass (t : ℕ) (ht : t ∈ Finset.range H) :
      ENNReal.ofReal (1 / 2) ≤ (law K (PMF.pure x) t).toOuterMeasure Gᶜ := by
    have hn := ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one (law K (PMF.pure x) t) Gᶜ)
    rw [← ENNReal.ofReal_toReal hn]
    exact ENNReal.ofReal_le_ofReal (hm t ht)
  have hH : s / a ≤ (H : ℝ) := by
    have hh := Nat.lt_floor_add_one (s / a)
    dsimp [H]
    push_cast
    exact hh.le
  have hscale : s / (2 * a) ≤ (H : ℝ) * (1 / 2) := by
    have hh := mul_le_mul_of_nonneg_right hH (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply le_trans _ hh
    ring_nf
    exact le_rfl
  calc
    _ ≤ ENNReal.ofReal ((H : ℝ) * (1 / 2)) := ENNReal.ofReal_le_ofReal hscale
    _ = ∑ _t ∈ Finset.range H, ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      simp [nsmul_eq_mul]
    _ ≤ ∑ t ∈ Finset.range H, (law K (PMF.pure x) t).toOuterMeasure Gᶜ :=
      Finset.sum_le_sum hmass
    _ ≤ _ := ENNReal.sum_le_tsum _

lemma tail_from_linear (K : α → PMF α) (G : Set α) (x : α)
    (habs : ∀ x ∈ G, ∀ y ∈ (K x).support, y ∈ G)
    (a : ℝ) (ha : 0 < a) (h : ∀ t : ℕ, visit K G t x ≤ (t : ℝ) * a) :
    ENNReal.ofReal (1 / (4 * a)) ≤ tailSum K Gᶜ (PMF.pure x) := by
  rw [show (1 : ℝ) / (4 * a) = (1 / 2) / (2 * a) by ring]
  exact tail_from_affine K G x habs a (1 / 2) 0 ha
    (by norm_num) (by norm_num) (by simpa using h)

end
end Lax637351Proofs.TailLower
