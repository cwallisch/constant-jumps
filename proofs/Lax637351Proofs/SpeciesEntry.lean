import Lax637351Proofs.SpeciesProtection

namespace Lax637351Proofs.SpeciesEntry

open Lax637351.Algorithm
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteWindows Lax637351Proofs.FiniteHitting
open Lax637351Proofs.SparseBarrier Lax637351Proofs.PairStep
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauPairs
open Lax637351Proofs.SpeciesDrift Lax637351Proofs.SpeciesCap Lax637351Proofs.SpeciesWindow
open Lax637351Proofs.SpeciesProtection Lax637351Proofs.OffspringEstimates
open OffspringEstimates.Genotypes OffspringEstimates.PopulationRatio OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma exit_implies_visit {α : Type*} [Fintype α] (K : α → PMF α) (A G : Set α)
    (h : ∀ x ∈ A, ∀ y ∈ (K x).support, y ∉ A → y ∈ G) (t : ℕ) (x : α) (hx : x ∈ A) :
    visit K Aᶜ t x ≤ visit K G t x := by
  induction t generalizing x with
  | zero =>
    rw [visit, if_neg (show x ∉ Aᶜ from fun h ↦ h hx)]
    exact visit_nonneg _ _ _ _
  | succ t ih =>
    by_cases hg : x ∈ G
    · rw [visit_in _ _ _ _ hg]
      exact visit_le_one _ _ _ _
    · rw [visit, if_neg (show x ∉ Aᶜ from fun h ↦ h hx), visit, if_neg hg]
      apply mean_mono_on_support
      intro y hy
      by_cases ha : y ∈ A
      · exact ih y ha
      · rw [visit_in _ _ _ _ (h x hx y hy ha)]
        exact visit_le_one _ _ _ _

lemma threshold_excludes_other (hk : 0 < k) (hkn : k ≤ n) (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (B A : Genotype n k) (hBA : B ≠ A)
    (h : clippedScore B P ≤ 4 * level k * (μ : ℕ))
    (Q : Population n μ) (hQ : Q ∈ (auxiliary k p ar P).support) :
    4 * level k * (μ : ℕ) ≤ clippedScore A Q := by
  have hB := low_has_many B P hP h
  have hshift := (abs_le.mp (one_step_count hk hkn p ar P hP B Q hQ)).1
  have hcounts := count_disjoint B A hBA Q
  have hm : (5 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hμ
  have hw : 0 ≤ floorWeight k := by unfold floorWeight; positivity
  have hA : (7 / 10 : ℝ) * (μ : ℕ) ≤ ((μ : ℕ) : ℝ) - count (toString A) Q := by
    linarith only [hB, hshift, hcounts, hm]
  have hr := (mul_le_mul_of_nonneg_left hA hw).trans
    (clipped_range A Q (auxiliary_preserves_plateau hk hkn p ar P hP Q hQ)).1
  apply le_trans _ hr
  unfold level
  nlinarith only [mul_nonneg hw (show (0 : ℝ) ≤ (μ : ℕ) by positivity)]

lemma species_entry_tail (hc : EntryBounds.Conditions n k (1 / 2)) (hμ : (5 : ℕ) ≤ μ)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (t : ℕ) :
    ((k : ℝ) / (256 * n)) * t * (1 - visit (auxiliary k p ar)
      {Q | plateau (k := k) Q ∧ strong k Q} t P) ≤ 3 * (μ : ℕ) := by
  let K := auxiliary k p ar (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | plateau (k := k) Q ∧ strong k Q}
  let g := (k : ℝ) / (256 * n)
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hk : 0 < k := hc.jump_pos
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  change g * t * (1 - visit K G t P) ≤ _
  by_cases hG : P ∈ G
  · rw [visit_in _ _ _ _ hG, sub_self, mul_zero]
    positivity
  · have hstr : ¬ strong k P := fun h ↦ hG ⟨hP, h⟩
    obtain ⟨B, hB⟩ : ∃ B : Genotype n k, clippedScore B P < 4 * level k * (μ : ℕ) := by
      simpa only [strong, not_forall, not_le] using hstr
    let A : Set (Population n μ) := {Q | plateau (k := k) Q ∧ clippedScore B Q < 4 * level k * (μ : ℕ)}
    let V (Q : Population n μ) := max 0 (3 * ((μ : ℕ) : ℝ) - clippedScore B Q)
    have hV (Q : Population n μ) (hQ : plateau (k := k) Q) : V Q = 3 * (μ : ℕ) - clippedScore B Q := by
      unfold V
      apply max_eq_right
      have h := (clipped_range B Q hQ).2
      linarith only [h, count_nonneg (toString B) Q, show (0 : ℝ) ≤ (μ : ℕ) by positivity]
    have hdrift (Q : Population n μ) (hQ : Q ∈ A) : mean (K Q) V ≤ V Q - g := by
      have hd := clipped_entry hc hμ p hp ar Q hQ.1 B hQ.2.le
      have he : mean (K Q) V = mean (K Q) (fun R ↦ 3 * ((μ : ℕ) : ℝ) - clippedScore B R) := by
        apply le_antisymm <;> apply mean_mono_on_support <;> intro R hR
        · exact (hV R (auxiliary_preserves_plateau hk hkn p ar Q hQ.1 R hR)).le
        · exact (hV R (auxiliary_preserves_plateau hk hkn p ar Q hQ.1 R hR)).ge
      rw [he, mean_sub, mean_const, hV Q hQ.1]
      rw [mean_sub, mean_const] at hd
      change g ≤ mean (K Q) (clippedScore B) - clippedScore B Q at hd
      linarith only [hd]
    have hA : P ∈ A := ⟨hP, hB⟩
    have hv := active_window K A V g hg hdrift t P
    rw [active_mass_compl] at hv
    have hvisit := exit_implies_visit K A G (fun Q hQ R hR hRA ↦ by
      have hplateau := auxiliary_preserves_plateau hk hkn p ar Q hQ.1 R hR
      refine ⟨hplateau, fun C ↦ ?_⟩
      by_cases he : C = B
      · subst C
        by_contra! hh
        exact hRA ⟨hplateau, hh⟩
      · exact threshold_excludes_other hk hkn hμ p ar Q hQ.1 B C (Ne.symm he) hQ.2.le R hR) t P hA
    have ht := mul_le_mul_of_nonneg_left (sub_le_sub_left hvisit 1)
      (show 0 ≤ g * t from mul_nonneg hg (by positivity))
    have hV₀ := mean_nonneg (f := V) (law (stopped K A) (PMF.pure P) t) (fun _ ↦ le_max_left _ _)
    rw [hV P hP] at hv
    linarith only [ht, hv, hV₀, clipped_nonneg B P]

end
end Lax637351Proofs.SpeciesEntry
