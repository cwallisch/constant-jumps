import Lax637351Proofs.SpeciesWindow

namespace Lax637351Proofs.SpeciesProtection

open Lax637351.Algorithm
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteWindows Lax637351Proofs.FiniteHitting
open Lax637351Proofs.SparseBarrier Lax637351Proofs.PairStep
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauPairs
open Lax637351Proofs.SpeciesDrift Lax637351Proofs.SpeciesCap Lax637351Proofs.SpeciesWindow Lax637351Proofs.PlateauChanges
open Lax637351Proofs.OffspringEstimates
open OffspringEstimates.Genotypes OffspringEstimates.PopulationRatio OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma count_disjoint (A B : Genotype n k) (hAB : A ≠ B) (P : Population n μ) :
    count (toString A) P + count (toString B) P ≤ (μ : ℕ) := by
  have he : toString A ≠ toString B := fun h ↦ hAB (toString_injective h)
  have h (i : Fin μ) : PopulationRatio.indicator (toString A) (P i) +
      PopulationRatio.indicator (toString B) (P i) ≤ 1 := by
    by_cases ha : P i = toString A <;> by_cases hb : P i = toString B
    · exact (he (ha.symm.trans hb)).elim
    all_goals simp [PopulationRatio.indicator, ha, hb, hAB, Ne.symm hAB]
  unfold count Deletion.total
  rw [← Finset.sum_add_distrib]
  exact (Finset.sum_le_sum (fun i _ ↦ h i)).trans_eq (by simp [nsmul_eq_mul])

lemma at_most_one (P : Population n μ) (hP : plateau (k := k) P) :
    ((Finset.univ.filter (fun B : Genotype n k ↦ clippedScore B P ≤ 2 * level k * (μ : ℕ))).card : ℝ) ≤ 1 := by
  rw [← Nat.cast_one (R := ℝ), Nat.cast_le]
  rw [Finset.card_le_one]
  intro A hA B hB
  by_contra he
  have hsum := count_disjoint A B he P
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have h₀ : 0 ≤ level k * (μ : ℕ) := mul_nonneg (level_pos k).le hμ.le
  have h₁ := low_has_many A P hP (by have h := (Finset.mem_filter.mp hA).2; linarith only [h, h₀])
  have h₂ := low_has_many B P hP (by have h := (Finset.mem_filter.mp hB).2; linarith only [h, h₀])
  linarith only [hsum, h₁, h₂, hμ]

lemma changeBound_ge_p (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool) :
    p ≤ changeBound n k p ar := by
  cases ar
  · exact hp.2
  · exact le_add_of_nonneg_right (by positivity)

lemma change_bound (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (ar : Bool) (P : Population n μ) (hP : plateau (k := k) P) :
    mean (auxiliary k p ar P) (fun Q ↦ indicator (Q ≠ P)) ≤ changeBound n k p ar := by
  cases ar
  · exact (mean_mono _ (fun _ ↦ indic_le_one _)).trans_eq (mean_const _ 1)
  · exact mean_change hk hkn hn p hp P hP

def speciesSlope (n k : ℕ) (p : ℝ) (ar : Bool) : ℝ :=
  p * strictAmount k / (64 * changeBound n k p ar)

set_option maxHeartbeats 350000 in
lemma species_protection (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (hs : strong k P) (t : ℕ) :
    visit (auxiliary k p ar) {Q | ¬safe k Q} t P ≤
      ((t : ℝ) * changeBound n k p ar + 1) *
        Real.exp (-speciesSlope n k p ar * (level k * (μ : ℕ) - 8)) := by
  let C : Set (Population n μ) := {Q | plateau (k := k) Q}
  let L := auxiliary k p ar (n := n) (μ := μ)
  let K := stopped L C
  let h := level k * ((μ : ℕ) : ℝ)
  let r := changeBound n k p ar
  let θ := speciesSlope n k p ar
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  have hk : 0 < k := hc.jump_pos
  have hC (X : Population n μ) (hX : X ∈ C) (Y : Population n μ) (hY : Y ∈ (L X).support) : Y ∈ C :=
    auxiliary_preserves_plateau hk hkn p ar X hX Y hY
  have hr' : p ≤ r := changeBound_ge_p (n := n) (k := k) p ⟨hp.1.le, hp.2⟩ ar
  have hr : 0 < r := hp.1.trans_le hr'
  have hθ : 0 ≤ θ := div_nonneg (mul_nonneg hp.1.le (strictAmount_pos k).le) (by positivity)
  have hθ' : θ * 8 ≤ 1 := by
    unfold θ speciesSlope
    have hh : p * strictAmount k ≤ r := (mul_le_of_le_one_right hp.1.le (strictAmount_le_one k)).trans hr'
    rw [div_mul_eq_mul_div, div_le_one (by positivity : 0 < 64 * r)]
    linarith only [hh, hr]
  have hnon : 0 ≤ h := mul_nonneg (level_pos k).le (by positivity)
  have hb (Q : Population n μ) (hQ : Q ∈ C) : K Q = L Q := by simp [K, stopped, hQ]
  let E : Set (Population n μ) := ⋃ B : Genotype n k, {Q | clippedScore B Q < h}
  have hbad : {Q : Population n μ | ¬safe k Q} = E := by
    ext Q
    simp only [safe, Set.mem_ofPred_eq, not_forall, not_le, Set.mem_iUnion, h, E]
  have htrans : visit L E t P = visit K E t P :=
    visit_agrees_on L K E C (fun Q hQ ↦ (hb Q hQ).symm) hC t P hP
  have hstay (Q : Population n μ) (hQ : Q ∈ C) (Y : Population n μ) (hY : Y ∈ (K Q).support) :
      Y ∈ C := by
    rw [hb Q hQ] at hY
    exact hC Q hQ Y hY
  have hsmall : ∀ (B : Genotype n k) (Q : Population n μ), h ≤ clippedScore B Q →
      clippedScore B Q ≤ 2 * h → ∀ Y ∈ (K Q).support, |θ * (clippedScore B Y - clippedScore B Q)| ≤ 1 := by
    intro B Q h₁ h₂ Y hY
    by_cases hQ : Q ∈ C
    · rw [hb Q hQ] at hY
      rw [abs_mul, abs_of_nonneg hθ]
      exact (mul_le_mul_of_nonneg_left (clipped_step hk hkn p ar Q hQ B Y hY) hθ).trans hθ'
    · have he : K Q = PMF.pure Q := by simp [K, stopped, hQ]
      rw [he, PMF.mem_support_pure_iff] at hY
      subst Y
      simp
  have hdrift : ∀ (B : Genotype n k) (Q : Population n μ), h ≤ clippedScore B Q →
      clippedScore B Q ≤ 2 * h → θ * mean (K Q) (fun Y ↦ (clippedScore B Y - clippedScore B Q) ^ 2) ≤
      mean (K Q) (fun Y ↦ clippedScore B Y - clippedScore B Q) := by
    intro B Q h₁ h₂
    by_cases hQ : Q ∈ C
    · rw [hb Q hQ]
      have hm := unchanged_second_moment L (clippedScore B) 8 (by norm_num) Q
        (clipped_step hk hkn p ar Q hQ B)
      have hmr := change_bound hk hkn hc.dimension_two p ⟨hp.1.le, hp.2⟩ ar Q hQ
      have hmul := mul_le_mul_of_nonneg_left
        (hm.trans (mul_le_mul_of_nonneg_left hmr (sq_nonneg _))) hθ
      have hu : clippedScore B Q ≤ 4 * level k * (μ : ℕ) := by
        rw [mul_assoc (4 : ℝ) (level k)]
        change clippedScore B Q ≤ 4 * h
        linarith only [h₂, hnon]
      have hh := clipped_strict hc herror hμ p ⟨hp.1.le, hp.2⟩ ar Q hQ B h₁ hu
      apply hmul.trans _
      have he : θ * (8 ^ 2 * r) = p * strictAmount k := by
        unfold θ speciesSlope
        change p * strictAmount k / (64 * r) * _ = _
        field_simp
        ring
      rw [he]
      exact hh
    · rw [show K Q = PMF.pure Q by simp [K, stopped, hQ], mean_pure, mean_pure]
      simp
  have hjump : ∀ Q ∈ C, ∀ Y ∈ (K Q).support, ∀ (B : Genotype n k),
      2 * h < clippedScore B Q → 2 * h - 8 ≤ clippedScore B Y := by
    intro Q hQ Y hY B hQ'
    rw [hb Q hQ] at hY
    have ht := (abs_le.mp (clipped_step hk hkn p ar Q hQ B Y hY)).1
    linarith only [ht, hQ']
  have hchange : ∀ Q ∈ C, mean (K Q) (fun Y ↦ PairStep.indicator (Y ≠ Q)) ≤ r := by
    intro Q hQ
    rw [hb Q hQ]
    exact change_bound hk hkn hc.dimension_two p ⟨hp.1.le, hp.2⟩ ar Q hQ

  have hcount (Q : Population n μ) (hQ : Q ∈ C) :
      ((Finset.univ.filter (fun B : Genotype n k ↦ clippedScore B Q ≤ 2 * h)).card : ℝ) ≤ 1 := by
    have he : 2 * h = 2 * level k * (μ : ℕ) := by dsimp [h]; ring
    rw [he]
    exact at_most_one Q hQ
  have hinit (B : Genotype n k) : 2 * h - 8 ≤ clippedScore B P := by
    have hh : 4 * h ≤ clippedScore B P := by simpa only [h, mul_assoc] using hs B
    linarith only [hh, hnon]
  have hbound : visit K E t P ≤ ((t : ℝ) * r + 1) * 1 * Real.exp (-θ * (2 * h - 8 - h)) :=
    sparse_visit K (fun B : Genotype n k ↦ clippedScore B) C hstay h (2 * h) 8 θ θ 1 r
      (by linarith only [hnon]) (by norm_num) hθ le_rfl (by norm_num) hr.le
      hsmall hdrift hcount hjump hchange t P hP hinit
  have he : 2 * h - 8 - h = h - 8 := by ring
  rw [he, mul_one] at hbound
  change visit L {Q | ¬safe k Q} t P ≤ ((t : ℝ) * r + 1) * Real.exp (-θ * (h - 8))
  rwa [hbad, htrans]

end
end Lax637351Proofs.SpeciesProtection
