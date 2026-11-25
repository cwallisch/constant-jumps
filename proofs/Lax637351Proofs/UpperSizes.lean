import Lax637351Proofs.ColumnParameters

namespace Lax637351Proofs.UpperSizes

open Filter
open Lax637351Proofs.OffspringEstimates
open Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnSlot
open Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.ResidentCap Lax637351Proofs.SpeciesWindow Lax637351Proofs.SpeciesCap
open scoped Classical

noncomputable section

def approximationConstant (k : ℕ) : ℝ :=
  (129 / 100 : ℝ) * (4 * (k : ℝ) + 3 * ((k : ℝ) + 2) * (4 * (k : ℝ) + 1))

def quadraticConstant (k : ℕ) : ℝ := Real.exp (-1) * ((1 / 2 : ℝ) * (4 : ℝ)⁻¹ ^ k / 100)

lemma ratio_eventually (D b : ℝ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, D / (n : ℝ) ≤ b := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (D / b))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans (hN.le.trans hn'))
  rw [div_le_iff₀ hn₀, mul_comm b, ← div_le_iff₀ hb]
  exact (le_max_right _ _).trans (hN.le.trans hn')

lemma approximation_eq (n k : ℕ) :
    (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k = approximationConstant k / n := by
  unfold PlateauKernelApproximation.approximationError approximationConstant
  ring

lemma dimension_eventually (k : ℕ) (hk : 2 ≤ k) (a : Settings k) :
    ∀ᶠ n : ℕ in atTop, Dimension k n a ∧ EntryBounds.Conditions n k (1 / 2) ∧
      (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k := by
  let A := approximationConstant k
  let Q := quadraticConstant k
  let F := (128 : ℝ) * (k : ℝ) ^ 2 * 3 ^ k
  have hQ : 0 < Q := by unfold Q quadraticConstant; positivity
  have hR : 0 < bandGain k (residentLevel k) := by
    have h := (gap_pos k).2.1
    unfold bandGain floorWeight
    positivity
  have hF : 0 < ShadowGaps.delta k * residentGap k / 2 :=
    div_pos (mul_pos (ShadowGaps.delta_pos (by omega)) (gap_pos k).2.2) (by norm_num)
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  filter_upwards [eventually_ge_atTop (4 * k), ratio_eventually (A + 5 / 4) _ hR,
    ratio_eventually ((a.T : ℕ) * (512 * (3 : ℝ) ^ k * (k : ℝ) ^ 2)) 1 (by norm_num),
    ratio_eventually F 1 (by norm_num), ratio_eventually (F * (1 + (3 : ℝ) ^ k)) _ hF,
    ratio_eventually (2 * ((k : ℝ) / 16)) Q hQ,
    ratio_eventually (8 * A ^ 2) (Q * ((k : ℝ) / 16)) (by positivity),
    ratio_eventually 1 ((1 / 2 : ℝ) * (k : ℝ) / 32) (by positivity),
    ratio_eventually A _ (strictAmount_pos k)] with n hn hR' hT hF₁ hF₂ hQ₁ hQ₂ hM hA
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₂ : 2 ≤ n := by omega
  refine ⟨⟨hn, hn₂, ?_, ?_, ?_, ?_⟩, ⟨by omega, hn₂, hn, by norm_num, by norm_num, ?_, ?_, ?_⟩, ?_⟩
  · unfold dimensionError
    rw [approximation_eq]
    convert hR' using 1
    unfold A
    ring
  · unfold ReproductiveAdmissibility.error
    convert hT using 1
    ring
  · convert hF₁ using 1
    unfold F
    ring
  · convert hF₂ using 1
    unfold F
    ring
  · change _ ≤ Q
    convert hQ₁ using 1
    ring
  · rw [approximation_eq]
    change 8 * (A / (n : ℝ)) ^ 2 ≤ Q * ((k : ℝ) / (16 * n))
    have h := div_le_div_of_nonneg_right hQ₂ hn'.le
    convert h using 1 <;> first | rfl | ring
  · have h := div_le_div_of_nonneg_right hM hn'.le
    convert h using 1 <;> first | rfl | ring
  · rw [approximation_eq]
    exact hA

lemma eps_le_reciprocal (μ : ℕ+) : eps μ ≤ 1 / ((μ : ℕ) : ℝ) := by
  have h : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  unfold eps
  apply one_div_le_one_div_of_le h
  linarith

lemma population_exists (k : ℕ) (a : Settings k) (_hk : 2 ≤ k) :
    ∃ M : ℕ, ∀ μ : ℕ+, M ≤ (μ : ℕ) → PopulationSize k a μ := by
  let T : ℝ := (a.T : ℕ)
  let R := remainderLimit T
  let A := Real.exp (-2 * T) / 4
  have hT : 0 < T := by unfold T; exact_mod_cast a.T.pos
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  have hA : 0 < A := by unfold A; positivity
  have h := show ∀ᶠ m : ℕ in atTop, ∀ μ : ℕ+, (μ : ℕ) = m → PopulationSize k a μ by
    filter_upwards [ratio_eventually 1 (1 / 8) (by norm_num),
      ratio_eventually 16 _ (gap_pos k).2.1,
      ratio_eventually (2 * T * Real.exp (2 * T)) 1 (by norm_num),
      ratio_eventually (48 * R * T) 1 (by norm_num),
      ratio_eventually (4 * R) (1 / (16 * T)) (by positivity),
      ratio_eventually (4 * R) (entryRate k T) (entryRate_pos _ _),
      ratio_eventually (4 * R * (k : ℝ)) (A / 256) (by positivity)] with m h₁ h₂ h₃ h₄ h₅ h₆ h₇
    intro μ hm
    have he := eps_le_reciprocal μ
    rw [← hm] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
    refine ⟨he.trans h₁, ?_, ?_, ?_, h₅, h₆, ?_⟩
    · exact (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 16)).trans (by convert h₂ using 1 <;> first | rfl | ring)
    · change 2 * eps μ * T * Real.exp (2 * T) ≤ 1
      calc
        _ = (2 * T * Real.exp (2 * T)) * eps μ := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left he (by positivity)).trans (by convert h₃ using 1 <;> first | rfl | ring)
    · change 48 * R * eps μ * T ≤ 1
      calc
        _ = (48 * R * T) * eps μ := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left he (by positivity)).trans (by convert h₄ using 1 <;> first | rfl | ring)
    · convert h₇ using 1
      ring
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  exact ⟨M, fun μ hμ ↦ hM _ hμ μ rfl⟩

end
end Lax637351Proofs.UpperSizes
