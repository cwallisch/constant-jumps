import Lax637351Proofs.ColumnApplied
import Lax637351Proofs.FamilyRecovery
import Lax637351Proofs.Endgame

namespace Lax637351Proofs.ColumnBands

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.ColumnSlot Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnApplied
open Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ColumnMutationDrift Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.ColumnReplacement Lax637351Proofs.ColumnCrossDrift
open Lax637351Proofs.SpeciesWindow Lax637351Proofs.SpeciesProtection
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauChanges
open Lax637351Proofs.FamilyRecovery Lax637351Proofs.SparseBarrier
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def potential (a : Settings k) (i : Fin n) (P : Population n μ) : ℝ :=
  populationPotential k i (a.horizon μ) P

def jumpBound (a : Settings k) : ℝ := 2 * Real.exp (3 * (a.T : ℕ))

def slopeConstant (a : Settings k) : ℝ :=
  min (1 / jumpBound a) (a.frequencyLevel / (8 * (a.T : ℕ) * (jumpBound a) ^ 2))

def columnSlope (a : Settings k) (n : ℕ) (p : ℝ) (ar : Bool) : ℝ :=
  slopeConstant a * p / changeBound n k p ar

def height (a : Settings k) (μ : ℕ+) : ℝ := a.columnLevel * (μ : ℕ)

def active (k : ℕ) : Set (Population n μ) := {Q | plateau (k := k) Q ∧ safe k Q}

def stabilization (a : Settings k) (P : Population n μ) : Prop := ∀ i, 2 * height a μ ≤ potential a i P

lemma potential_total_bounds (a : Settings k) (i : Fin n) (P : Population n μ) :
    0 ≤ potential a i P ∧ potential a i P ≤ Real.exp (2 * (a.T : ℕ)) * (μ : ℕ) := by
  by_cases h : plateau (k := k) P
  · have hl := population_bounds i (a.horizon μ) (horizon_pos a μ) (a.T : ℕ) (time_horizon a μ).le P h
    have hv := frequency_valid k P i
    change 0 ≤ populationPotential k i (a.horizon μ) P ∧ _
    exact ⟨(by have := hv.1; positivity : 0 ≤ Real.exp (-2 * (a.T : ℕ)) * (μ : ℕ) * frequency k i P).trans hl.1,
      hl.2.trans (mul_le_of_le_one_right (by positivity) hv.2)⟩
  · simp [potential, populationPotential, h]
    positivity

lemma potential_low_frequency (a : Settings k) (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P)
    (h : potential a i P ≤ 4 * height a μ) : frequency k i P ≤ a.cutoff := by
  have hl := (population_bounds i (a.horizon μ) (horizon_pos a μ) (a.T : ℕ) (time_horizon a μ).le P hP).1
  have h' := hl.trans h
  unfold height Settings.columnLevel at h'
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have ht := mul_pos (Real.exp_pos (-2 * (a.T : ℕ))) hm
  have he : Real.exp (-2 * (a.T : ℕ)) * (μ : ℕ) * frequency k i P ≤
      Real.exp (-2 * (a.T : ℕ)) * (μ : ℕ) * (a.cutoff / 2) := by
    nlinarith only [h']
  have hj := (mul_le_mul_iff_of_pos_left ht).mp he
  linarith only [hj, a.cutoff_pos]

lemma potential_high_frequency (a : Settings k) (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P)
    (h : height a μ ≤ potential a i P) : a.frequencyLevel ≤ frequency k i P := by
  have hu := h.trans (population_bounds i (a.horizon μ) (horizon_pos a μ) (a.T : ℕ) (time_horizon a μ).le P hP).2
  unfold Settings.frequencyLevel
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  apply (mul_le_mul_iff_of_pos_right hm).mp
  unfold height at hu
  nlinarith only [hu]

lemma potential_conditioned_drift (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (P : Population n μ) (hP : plateau (k := k) P) (hS : safe k P) (i : Fin n)
    (h : potential a i P ≤ 4 * height a μ) :
    p * frequency k i P / (8 * (a.T : ℕ)) + entryRate k (a.T : ℕ) / n ≤
      mean (auxiliary k p ar P) (fun Q ↦ potential a i Q - potential a i P) := by
  let f := frequency k i P
  have hf := potential_low_frequency a i P hP h
  have h₁ : 0 ≤ 24 * ((a.T : ℕ) : ℝ) * Real.exp (6 * (a.T : ℕ)) := by positivity
  have h₂ : 0 ≤ Real.exp (-2 * (a.T : ℕ)) / 2 + 2 * responseLimit (a.T : ℕ) := by
    unfold responseLimit
    positivity
  have h₃ : 0 ≤ 6 * responseLimit (a.T : ℕ) := by unfold responseLimit; positivity
  have h₃' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf h₃) (show 0 ≤ (k : ℝ) by positivity)
  have hg := empirical_prediction_gain hk a hn hm i P hP hS hf
  exact column_increment hn.two (by have := hn.four; omega) (by omega) i (a.horizon μ) (horizon_pos a μ)
    (a.T : ℕ) (time_horizon a μ) p hp ar P hP (hf.trans a.cutoff_half)
    ((mul_le_mul_of_nonneg_left hf h₁).trans a.cutoff_response₁)
    ((mul_le_mul_of_nonneg_left hf h₂).trans a.cutoff_response₂)
    (h₃'.trans a.cutoff_mutation) hm.deterministic hm.cross_linear hm.cross_entry hm.mutation hcopy hg

lemma remainingZeros_sum (P : Population n μ) (hP : plateau (k := k) P) :
    (∑ i : Fin n, (1 - frequency k i P)) = (k : ℝ) := by
  simp_rw [← resident_frequency k P]
  rw [← mean_sum]
  have h (u : Fin μ) : (∑ i : Fin n, indicator (P u i = 0)) = (k : ℝ) := by
    have he := hP u
    have h' := congrArg (fun a : ℕ ↦ (a : ℝ)) he
    simp only [zeros, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h'
    rw [← h']
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P u i = 0 <;> simp [indicator, hi]
  simp_rw [h, mean_const]

lemma finite_candidates (a : Settings k) (P : Population n μ) (hP : plateau (k := k) P) (u : ℝ)
    (hu : u ≤ 4 * height a μ) :
    ((Finset.univ.filter (fun i : Fin n ↦ potential a i P ≤ u)).card : ℝ) ≤ 2 * k := by
  let s := Finset.univ.filter (fun i : Fin n ↦ potential a i P ≤ u)
  have hsmall (i : Fin n) (hi : i ∈ s) : (1 : ℝ) / 2 ≤ 1 - frequency k i P := by
    have h := potential_low_frequency a i P hP ((Finset.mem_filter.mp hi).2.trans hu)
    linarith only [h, a.cutoff_half]
  have hsum := (Finset.sum_le_sum hsmall).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ ↦
      sub_nonneg.mpr (frequency_valid k P i).2))
  rw [remainingZeros_sum P hP, Finset.sum_const, nsmul_eq_mul] at hsum
  change (s.card : ℝ) ≤ 2 * k
  linarith only [hsum]

lemma slope_pos (a : Settings k) : 0 < slopeConstant a := by
  have hf := (settings_levels a).2.1
  have ht : (0 : ℝ) < (a.T : ℕ) := by exact_mod_cast a.T.pos
  unfold slopeConstant jumpBound
  positivity

lemma jump_pos (a : Settings k) : 0 < jumpBound a := by unfold jumpBound; positivity

end
end Lax637351Proofs.ColumnBands
