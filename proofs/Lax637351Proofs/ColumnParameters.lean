import Lax637351Proofs.ColumnDriftBound
import Lax637351Proofs.SpeciesProtection

namespace Lax637351Proofs.ColumnParameters

open Lax637351.Algorithm
open Lax637351Proofs.OffspringEstimates
open Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnSlot
open Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ResidentCap
open Lax637351Proofs.SpeciesCap Lax637351Proofs.PlateauChanges
open scoped Classical ENNReal

noncomputable section

def initialGap (k : ℕ) : ℝ := 2 / 5 * level k

def residentLevel (k : ℕ) : ℝ := floorWeight k * initialGap k / 16

def residentGap (k : ℕ) : ℝ := 2 / 5 * residentLevel k

def bonus (k : ℕ) : ℝ := ShadowGaps.delta k * residentGap k / (4 * (3 : ℝ) ^ k)

lemma gap_pos (k : ℕ) : 0 < initialGap k ∧ 0 < residentLevel k ∧ 0 < residentGap k := by
  have h := level_pos k
  simp only [initialGap, residentLevel, residentGap, floorWeight]
  refine ⟨?_, ?_, ?_⟩ <;> positivity

lemma gap_bound (k : ℕ) : initialGap k ≤ 1 / 10 ∧ residentLevel k ≤ floorWeight k / 16 ∧ residentLevel k ≤ 1 / 100 := by
  have h := level_small k
  have hp : 0 ≤ floorWeight k := by unfold floorWeight; positivity
  have hq : floorWeight k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hu : initialGap k ≤ 1 / 10 := by unfold initialGap; linarith only [h]
  have hv : 0 ≤ initialGap k := (gap_pos k).1.le
  refine ⟨hu, ?_, ?_⟩
  · unfold residentLevel
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_of_le_one_right hp (by linarith)
  · unfold residentLevel
    have hh := mul_le_mul hq hu hv (by norm_num : (0 : ℝ) ≤ 1)
    linarith only [hh]

lemma bonus_pos (k : ℕ) (hk : 1 ≤ k) : 0 < bonus k := by
  unfold bonus
  exact div_pos (mul_pos (ShadowGaps.delta_pos hk) (gap_pos k).2.2) (by positivity)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Settings (k : ℕ) where
  T : ℕ+
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_half : cutoff ≤ 1 / 2
  cutoff_gap : cutoff ≤ initialGap k / 2
  cutoff_remainder : 4 * remainderLimit (T : ℕ) * cutoff ≤ 1
  cutoff_response₁ : 24 * (T : ℕ) * Real.exp (6 * (T : ℕ)) * cutoff ≤ Real.exp (-2 * (T : ℕ)) / 2
  cutoff_response₂ : (Real.exp (-2 * (T : ℕ)) / 2 + 2 * responseLimit (T : ℕ)) * cutoff ≤ Real.exp (-2 * (T : ℕ)) / 4
  cutoff_mutation : 6 * responseLimit (T : ℕ) * cutoff * (k : ℝ) ≤ (Real.exp (-2 * (T : ℕ)) / 4) / 256
  gain : (8 : ℝ) * 3 ^ k ≤ 1 + (T : ℕ) * bonus k

def Settings.horizon {k : ℕ} (a : Settings k) (μ : ℕ+) : ℕ := (μ.val + 1) * a.T.val
def Settings.columnLevel {k : ℕ} (a : Settings k) : ℝ := a.cutoff * Real.exp (-2 * (a.T : ℕ)) / 8
def Settings.frequencyLevel {k : ℕ} (a : Settings k) : ℝ := a.columnLevel / Real.exp (2 * (a.T : ℕ))

lemma time_horizon {k : ℕ} (a : Settings k) (μ : ℕ+) :
    eps μ * a.horizon μ = (a.T : ℕ) := by
  have h : 0 < ((μ : ℕ) : ℝ) + 1 := by positivity
  unfold Settings.horizon eps
  push_cast
  field_simp

lemma horizon_pos {k : ℕ} (a : Settings k) (μ : ℕ+) : 0 < a.horizon μ := by
  unfold Settings.horizon
  exact Nat.mul_pos (by omega) a.T.pos

lemma settings_levels {k : ℕ} (a : Settings k) : 0 < a.columnLevel ∧ 0 < a.frequencyLevel ∧ a.frequencyLevel ≤ 1 := by
  have h₁ := Real.exp_pos (-2 * ((a.T : ℕ) : ℝ))
  have h₂ := Real.exp_pos (2 * ((a.T : ℕ) : ℝ))
  have h₃ : Real.exp (-2 * ((a.T : ℕ) : ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have h : (0 : ℝ) ≤ (a.T : ℕ) := Nat.cast_nonneg _; linarith only [h])
  have h₄ : 1 ≤ Real.exp (2 * ((a.T : ℕ) : ℝ)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hC := a.cutoff_pos
  refine ⟨by unfold Settings.columnLevel; positivity, by unfold Settings.frequencyLevel Settings.columnLevel; positivity, ?_⟩
  unfold Settings.frequencyLevel Settings.columnLevel
  apply (div_le_one h₂).mpr
  have h := mul_le_of_le_one_right hC.le h₃
  linarith only [h, h₄, a.cutoff_half]

lemma settings_exists (k : ℕ) (hk : 2 ≤ k) : Nonempty (Settings k) := by
  have hbonus := bonus_pos k (by omega)
  obtain ⟨T, hT⟩ := exists_nat_gt ((8 : ℝ) * 3 ^ k / bonus k)
  let m : ℕ+ := ⟨T + 1, by omega⟩
  let t : ℝ := (m : ℕ)
  let a := Real.exp (-2 * t)
  let u := responseLimit t
  let r := remainderLimit t
  have ht : 0 < t := by unfold t; exact_mod_cast m.pos
  have ha : 0 < a := Real.exp_pos _
  have hu : 0 < u := Real.exp_pos _
  have hr : 0 ≤ r := by unfold r remainderLimit normLimit; positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let f := min (1 / 2 : ℝ) (min (initialGap k / 2)
    (min (1 / (4 * r + 1)) (min ((a / 2) / (24 * t * Real.exp (6 * t) + 1))
      (min ((a / 4) / (a / 2 + 2 * u + 1)) (((a / 4) / 256) / (6 * u * (k : ℝ) + 1))))))
  have hf : 0 < f := by
    have h := (gap_pos k).1
    unfold f
    positivity
  have hf₀ : f ≤ 1 / 2 := min_le_left _ _
  have hf₁ : f ≤ initialGap k / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hf₂ : f ≤ 1 / (4 * r + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hf₃ : f ≤ (a / 2) / (24 * t * Real.exp (6 * t) + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hf₄ : f ≤ (a / 4) / (a / 2 + 2 * u + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hf₅ : f ≤ ((a / 4) / 256) / (6 * u * (k : ℝ) + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have h₂ := (le_div_iff₀ (show 0 < 4 * r + 1 by positivity)).mp hf₂
  have h₃ := (le_div_iff₀ (show 0 < 24 * t * Real.exp (6 * t) + 1 by positivity)).mp hf₃
  have h₄ := (le_div_iff₀ (show 0 < a / 2 + 2 * u + 1 by positivity)).mp hf₄
  have h₅ := (le_div_iff₀ (show 0 < 6 * u * (k : ℝ) + 1 by positivity)).mp hf₅
  have hg := (div_lt_iff₀ hbonus).mp hT
  have hT' : (T : ℝ) ≤ t := by unfold t m; exact_mod_cast Nat.le_succ T
  refine ⟨⟨m, f, hf, hf₀, hf₁, ?_, ?_, ?_, ?_, ?_⟩⟩
  · change 4 * r * f ≤ 1
    nlinarith only [h₂, hf]
  · change 24 * t * Real.exp (6 * t) * f ≤ a / 2
    nlinarith only [h₃, hf]
  · change (a / 2 + 2 * u) * f ≤ a / 4
    nlinarith only [h₄, hf]
  · change 6 * u * f * (k : ℝ) ≤ (a / 4) / 256
    nlinarith only [h₅, hf]
  · exact hg.le.trans (by nlinarith only [mul_le_mul_of_nonneg_right hT' hbonus.le])

structure Dimension (k n : ℕ) (a : Settings k) : Prop where
  four : 4 * k ≤ n
  two : 2 ≤ n
  resident : dimensionError n k ≤ bandGain k (residentLevel k)
  reproductive : (a.T : ℕ) * ReproductiveAdmissibility.error n k ≤ 1
  fertility_one : (128 * (k : ℝ) ^ 2 / n) * (3 : ℝ) ^ k ≤ 1
  fertility : (128 * (k : ℝ) ^ 2 / n) * (3 : ℝ) ^ k * (1 + (3 : ℝ) ^ k) ≤
    ShadowGaps.delta k * residentGap k / 2

structure PopulationSize (k : ℕ) (a : Settings k) (μ : ℕ+) : Prop where
  eps_eight : eps μ ≤ 1 / 8
  resident : 16 * eps μ ≤ residentLevel k
  perturbation : 2 * eps μ * (a.T : ℕ) * Real.exp (2 * (a.T : ℕ)) ≤ 1
  deterministic : 48 * remainderLimit (a.T : ℕ) * eps μ * (a.T : ℕ) ≤ 1
  cross_linear : (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) ≤ 1 / (16 * (a.T : ℕ))
  cross_entry : (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) ≤ entryRate k (a.T : ℕ)
  mutation : (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * (k : ℝ) ≤
    (Real.exp (-2 * (a.T : ℕ)) / 4) / 256

end
end Lax637351Proofs.ColumnParameters
