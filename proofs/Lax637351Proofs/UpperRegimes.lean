import Lax637351Proofs.UpperRuntime
import Lax637351Proofs.UpperSizes
import Lax637351Proofs.UpperTails

namespace Lax637351Proofs.UpperRegimes

open Lax637351.Algorithm Lax637351.Runtime
open Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.PlateauChanges Lax637351Proofs.SpeciesWindow
open Lax637351Proofs.ArrivalProgress Lax637351Proofs.UpperSizes
open Lax637351Proofs.UpperWindows Lax637351Proofs.UpperTails Lax637351Proofs.UpperRuntime
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def populationConstant (a : Settings k) (M : ℕ) : ℝ :=
  max (max 5 M) (max (max (k : ℝ) (populationFloor a))
    (max (96 * (a.T : ℕ) * remainderLimit (a.T : ℕ)) (3 / (decay a / 4))))

def dimensionConstant (a : Settings k) : ℝ :=
  max (max (Real.exp 1) (k : ℝ))
    (max ((plateauTimeConstant a + 1) / failureTolerance a)
      ((2 * plateauTimeConstant a / (decay a / 4) + 2) / failureTolerance a))

lemma population_constants (a : Settings k) (M : ℕ) :
    let C := populationConstant a M
    5 ≤ C ∧ (M : ℝ) ≤ C ∧ (k : ℝ) ≤ C ∧ populationFloor a ≤ C ∧
      96 * (a.T : ℕ) * remainderLimit (a.T : ℕ) ≤ C ∧ 3 / (decay a / 4) ≤ C := by
  unfold populationConstant
  exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

lemma dimension_constants (a : Settings k) :
    let N := dimensionConstant a
    Real.exp 1 ≤ N ∧ (k : ℝ) ≤ N ∧
      (plateauTimeConstant a + 1) / failureTolerance a ≤ N ∧
      ((2 * plateauTimeConstant a / (decay a / 4) + 1) + 1) / failureTolerance a ≤ N := by
  unfold dimensionConstant
  refine ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  simpa only [add_assoc, one_add_one_eq_two] using
    (le_max_right ((plateauTimeConstant a + 1) / failureTolerance a) _).trans (le_max_right _ _)

lemma log_ge_one {x : ℝ} (h : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  have hh := Real.log_le_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at hh

lemma dimension_threshold (k : ℕ) (hk : 2 ≤ k) (a : Settings k) :
    ∃ N : ℕ, dimensionConstant a ≤ (N : ℝ) ∧
      ∀ n ≥ N, Dimension k n a ∧ Lax637351Proofs.OffspringEstimates.EntryBounds.Conditions n k (1 / 2) ∧
        (129 / 100 : ℝ) * Lax637351Proofs.OffspringEstimates.PlateauKernelApproximation.approximationError n k ≤ strictAmount k := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (dimension_eventually k hk a)
  obtain ⟨N', hN'⟩ := exists_nat_gt (dimensionConstant a)
  refine ⟨max N N', hN'.le.trans (by exact_mod_cast le_max_right N N'), ?_⟩
  exact fun n hn ↦ hN _ ((le_max_left _ _).trans hn)

lemma vanilla_params (a : Settings k) (hk : 2 ≤ k) (M : ℕ) (n : ℕ) (μ : ℕ+) (p : ℝ)
    (hn : dimensionConstant a ≤ (n : ℝ)) (hμn : (μ : ℕ) ≤ n)
    (hp : 0 < p ∧ p ≤ 1) (hP : populationConstant a M * Real.log n / p ≤ ((μ : ℕ) : ℝ)) :
    let m : ℝ := (μ : ℕ)
    5 ≤ (μ : ℕ) ∧ M ≤ (μ : ℕ) ∧ 1 ≤ (n : ℝ) * p ∧
      Real.log ((n : ℝ) * effective false p) ≤ m ∧
      3 * (4 * remainderLimit (a.T : ℕ) / m) * copyRate n p false ≤ p / (8 * (a.T : ℕ)) ∧
      p + (k : ℝ) / n + copyRate n p false / m ≤ 3 * p ∧ populationFloor a ≤ m ∧
      (plateauTimeConstant a * m * n * changeBound n k p false + 1) *
        Real.exp (-decay a * m * p / changeBound n k p false) ≤ failureTolerance a := by
  let C := populationConstant a M
  let m : ℝ := (μ : ℕ)
  let T : ℝ := (a.T : ℕ)
  let R := remainderLimit T
  have hC := population_constants a M
  have hN := dimension_constants a
  have hlog := log_ge_one (hN.1.trans hn)
  have hn' : 1 ≤ (n : ℝ) := by linarith only [hN.1.trans hn, Real.add_one_le_exp (1 : ℝ)]
  have hn₀ : (0 : ℝ) < n := by linarith only [hn']
  have hm₀ : 0 < m := by unfold m; exact_mod_cast μ.pos
  have hT : 0 < T := by unfold T; exact_mod_cast a.T.pos
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  have hC₀ : 0 < C := by linarith only [hC.1]
  have hpC : C * Real.log n ≤ m * p := (div_le_iff₀ hp.1).mp hP
  have hCm : C ≤ m * p := (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hC₀.le : C ≤ C * Real.log n).trans hpC
  have hm' : C ≤ m := hCm.trans (mul_le_of_le_one_right hm₀.le hp.2)
  have hmn : (m : ℝ) ≤ n := by unfold m; exact_mod_cast hμn
  have hk' : (k : ℝ) ≤ (n : ℝ) * p := hC.2.2.1.trans (hCm.trans (mul_le_mul_of_nonneg_right hmn hp.1.le))
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkp : (k : ℝ) / n ≤ p := (div_le_iff₀ hn₀).mpr (by simpa [mul_comm] using hk')
  have hmp : (1 : ℝ) ≤ m * p := (by norm_num : (1 : ℝ) ≤ 5).trans (hC.1.trans hCm)
  have hc := copyRate_le_one n p ⟨hp.1.le, hp.2⟩ false
  have hc' : copyRate n p false / m ≤ p := (div_le_iff₀ hm₀).mpr (hc.trans (by simpa [mul_comm] using hmp))
  have hcopy : 3 * (4 * R / m) * copyRate n p false ≤ p / (8 * T) := by
    have hg : 96 * T * R ≤ m * p := hC.2.2.2.2.1.trans hCm
    have hb := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3 * (4 * R / m) by positivity)
    apply hb.trans
    rw [mul_one, le_div_iff₀ (show 0 < 8 * T by positivity),
      show 3 * (4 * R / m) * (8 * T) = (96 * T * R) / m by ring]
    exact (div_le_iff₀ hm₀).mpr (hg.trans_eq (mul_comm m p))
  have hlog' : Real.log ((n : ℝ) * effective false p) ≤ m := by
    simp only [effective, Bool.false_eq_true, if_false, mul_one]
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith only [hC.1]) (Real.log_nonneg hn')
    linarith only [h, hpC, mul_le_of_le_one_right hm₀.le hp.2]
  have hdecay := (plateau_constants a hk).2.2.2.2
  have hsmall : 3 / decay a ≤ C := (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hdecay])).trans hC.2.2.2.2.2
  have hfive : (5 : ℕ) ≤ (μ : ℕ) :=
    Nat.cast_le.mp (show ((5 : ℕ) : ℝ) ≤ ((μ : ℕ) : ℝ) from hC.1.trans hm')
  have hM : M ≤ (μ : ℕ) :=
    Nat.cast_le.mp (show (M : ℝ) ≤ ((μ : ℕ) : ℝ) from hC.2.1.trans hm')
  exact ⟨hfive, hM,
    hk₁.trans hk', hlog', hcopy, by linarith only [hkp, hc'], hC.2.2.2.1.trans hm',
    vanilla_tail a hk n μ p C hn' hμn hsmall hpC (hN.2.2.1.trans hn)⟩

lemma avoidance_params (a : Settings k) (hk : 2 ≤ k) (M : ℕ) (n : ℕ) (μ : ℕ+) (p : ℝ)
    (hn : 0 < n) (hp : 0 < p ∧ p ≤ 1) (hD : dimensionConstant a ≤ (n : ℝ) * p)
    (hP : populationConstant a M * Real.log ((n : ℝ) * p) ≤ ((μ : ℕ) : ℝ)) :
    let m : ℝ := (μ : ℕ)
    5 ≤ (μ : ℕ) ∧ M ≤ (μ : ℕ) ∧ 1 ≤ (n : ℝ) * p ∧
      Real.log ((n : ℝ) * effective true p) ≤ m ∧
      3 * (4 * remainderLimit (a.T : ℕ) / m) * copyRate n p true ≤ p / (8 * (a.T : ℕ)) ∧
      p + (k : ℝ) / n + copyRate n p true / m ≤ 3 * p ∧ populationFloor a ≤ m ∧
      (plateauTimeConstant a * m * n * changeBound n k p true + 1) *
        Real.exp (-decay a * m * p / changeBound n k p true) ≤ failureTolerance a := by
  let C := populationConstant a M
  let m : ℝ := (μ : ℕ)
  let x := (n : ℝ) * p
  have hC := population_constants a M
  have hN := dimension_constants a
  have hlog := log_ge_one (hN.1.trans hD)
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hx₁ : 1 ≤ x := by linarith only [hN.1.trans hD, Real.add_one_le_exp (1 : ℝ)]
  have hC₀ : 0 ≤ C := by linarith only [hC.1]
  have hCm : C ≤ m := (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hC₀ : C ≤ C * Real.log x).trans hP
  have hkp : (k : ℝ) / n ≤ p := (div_le_iff₀ hn₀).mpr (by simpa [mul_comm] using hN.2.1.trans hD)
  have hlog' : Real.log ((n : ℝ) * effective true p) ≤ m := by
    change Real.log x ≤ m
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith only [hC.1]) (Real.log_nonneg hx₁)
    rw [one_mul] at hh
    exact hh.trans hP
  have hfive : (5 : ℕ) ≤ (μ : ℕ) :=
    Nat.cast_le.mp (show ((5 : ℕ) : ℝ) ≤ ((μ : ℕ) : ℝ) from hC.1.trans hCm)
  have hM : M ≤ (μ : ℕ) :=
    Nat.cast_le.mp (show (M : ℝ) ≤ ((μ : ℕ) : ℝ) from hC.2.1.trans hCm)
  refine ⟨hfive, hM, hx₁, hlog', ?_, ?_,
    hC.2.2.2.1.trans hCm, avoidance_tail a hk n μ p C hp.1 hkp hx₁ hC.2.2.2.2.2 hP (hN.2.2.2.trans hD)⟩
  · have hT : (0 : ℝ) ≤ (a.T : ℕ) := by positivity
    simp only [copyRate, if_true, mul_zero]
    exact div_nonneg hp.1.le (by positivity)
  · simp only [copyRate, if_true, zero_div, add_zero]
    linarith only [hkp, hp.1]

end
end Lax637351Proofs.UpperRegimes
