import Lax637351.Theorem2iii
import Lax637351Proofs.ArrivalTime
import Lax637351Proofs.RareSuccess

namespace Lax637351Proofs.Theorem2iii

open Lax637351.Algorithm Lax637351.Runtime Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.RuntimeBridge
open Lax637351Proofs.PlateauPairs (plateau)
open Lax637351Proofs.ArrivalTime Lax637351Proofs.RareSuccess Lax637351Proofs.CrossoverSuccess
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def arrivalWindow (n : ℕ) (μ : ℕ+) : ℕ :=
  ⌈2 * ((μ : ℕ) * (64 * n * (1 + Real.log n)) : ℝ)⌉₊

lemma arrivalWindow_pos (hn : 2 ≤ n) : 0 < arrivalWindow n μ := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)
  unfold arrivalWindow
  apply Nat.ceil_pos.mpr
  positivity

lemma overall_window (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hμ : 2 ≤ μ) (B p : ℝ)
    (hB : 0 < B) (hp : 0 < p ∧ p ≤ 1 / 2) (hpB : p ≤ B / n)
    (hsize : 4 * (B + k) ≤ ((μ : ℕ) : ℝ) * n)
    (ν : PMF (Population n μ)) :
    scoreLower B k / 4 ≤ mean (law (step (jump k) p true) ν
      (arrivalWindow n μ + plateauWindow k n μ p)) success := by
  let K := step (jump k) p true (n := n) (μ := μ)
  let V := arrivalWindow n μ
  let W := plateauWindow k n μ p
  let q := scoreLower B k
  let A : Set (Population n μ) := {P | arriving k P}
  let ν' := law K ν V
  have hV' : (0 : ℝ) < V := by exact_mod_cast arrivalWindow_pos (by omega : 2 ≤ n) (μ := μ)
  have htail : (ν'.toOuterMeasure A).toReal ≤ 1 / 2 := by
    have ht := arrival_tail hk (by omega : 2 * k ≤ n) p ⟨hp.1.le, hp.2⟩ true ν V
    have hbound : 2 * ((μ : ℕ) * (64 * n * (1 + Real.log n)) : ℝ) ≤ V := Nat.le_ceil _
    change (V : ℝ) * (ν'.toOuterMeasure A).toReal ≤ _ at ht
    nlinarith
  have hlower (P : Population n μ) :
      q / 2 * (1 - (if P ∈ A then 1 else 0)) ≤ mean (law K (PMF.pure P) W) success := by
    by_cases hP : P ∈ A
    · simpa only [if_pos hP, sub_self, mul_zero] using mean_nonneg _ success_nonneg
    · have hP' : ¬ missing P ∨ plateau (k := k) P := by
        by_cases h : missing P
        · exact Or.inr (by by_contra! hp'; exact hP ⟨h, hp'⟩)
        · exact Or.inl h
      have hs := plateau_window_success hk hn hμ B p hB hp hpB hsize (PMF.pure P)
        (fun Q hQ ↦ ((PMF.mem_support_pure_iff _ _).mp hQ).symm ▸ hP')
      simpa only [if_neg hP, sub_zero, mul_one] using hs
  have hs := mean_mono ν' hlower
  rw [mean_mul, mean_sub, mean_const, mean_indicator, ← mean_bind] at hs
  change q / 4 ≤ mean (law K ν (V + W)) success
  rw [law_add]
  have hmul := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ 1 - (ν'.toOuterMeasure A).toReal by linarith)
    (show 0 ≤ q / 2 by dsimp [q]; positivity [scoreLower_pos B k])
  nlinarith

lemma overall_window_cost (hn : 2 ≤ n) (hμ : 2 ≤ μ) {p : ℝ} (hp : 0 < p ∧ p ≤ 1) :
    ((arrivalWindow n μ + plateauWindow k n μ p : ℕ) : ℝ) ≤
      (128 * (1 + (Real.log 2)⁻¹) + k * (Real.log 2)⁻¹) *
        ((μ : ℕ) * n * Real.log n) + ((crossRate k)⁻¹ + 2) * (1 / p) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hμ' : (2 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hμ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
  have hlogn : 0 < Real.log n := hlog2.trans_le hlog
  have hcoef : 1 ≤ (Real.log 2)⁻¹ * Real.log n := by
    calc
      (1 : ℝ) = (Real.log 2)⁻¹ * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hA := Nat.ceil_lt_add_one
    (a := 2 * ((μ : ℕ) * (64 * n * (1 + Real.log n)) : ℝ)) (by positivity)
  have hW := Nat.ceil_lt_add_one (a := 1 / (p * crossRate k))
    (one_div_nonneg.mpr (mul_nonneg hp.1.le (crossRate_pos k).le))
  have hW' : ((⌈1 / (p * crossRate k)⌉₊ : ℕ) : ℝ) <
      (1 / p) * (crossRate k)⁻¹ + 1 := by
    simpa only [div_eq_mul_inv, mul_inv, mul_assoc] using hW
  have hp' : 1 ≤ 1 / p := (le_div_iff₀ hp.1).mpr (by simpa using hp.2)
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ ((μ : ℕ) : ℝ) * n by positivity)
  unfold plateauWindow arrivalWindow
  push_cast
  nlinarith only [hA, hW', hp', hmul,
    mul_le_mul_of_nonneg_left hmul (show 0 ≤ (k : ℝ) by positivity)]

/--
---
conclusion: Lax637351.Theorem2iii.bound
---
-/
theorem bound :
    ∀ k : ℕ, 2 ≤ k →
    ∀ B : ℝ, 0 < B →
      ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → p_c ≤ B / n →
        ∀ μ : ℕ+, 2 ≤ μ →
          expectedOptimizationTime n k μ p_c (avoidReplications := true) ≤
            ENNReal.ofReal (D * (μ * n * Real.log n + 1 / p_c)) := by
  intro k hk B hB
  let q := scoreLower B k
  have hq : 0 < q := scoreLower_pos B k
  have hq' : q ≤ 1 := scoreLower_le_one hB k
  let D₀ := 128 * (1 + (Real.log 2)⁻¹) + (k : ℝ) * (Real.log 2)⁻¹ + ((crossRate k)⁻¹ + 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity [crossRate_pos k]
  refine ⟨D₀ * (4 / q), by positivity, max (4 * k) ⌈4 * (B + k)⌉₊, ?_⟩
  intro n hn p hpos hle hpB μ hμ
  have hn₀ : 4 * k ≤ n := (le_max_left _ _).trans hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnB : 4 * (B + k) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hμ' : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hsize : 4 * (B + k) ≤ ((μ : ℕ) : ℝ) * n :=
    hnB.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ' hn'.le)
  have hp₀ : p ≤ 1 / 2 := hpB.trans ((div_le_iff₀ hn').mpr (by
    have hk' : (0 : ℝ) ≤ k := by positivity
    linarith))
  let L := arrivalWindow n μ + plateauWindow k n μ p
  let r := 1 - ENNReal.ofReal (q / 4)
  have hL : 0 < L := Nat.add_pos_left (arrivalWindow_pos (by omega : 2 ≤ n)) _
  have hq4 : ENNReal.ofReal (q / 4) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hblock (P : Population n μ) (_ : missing P) :
      (law (step (jump k) p true) (PMF.pure P) L).toOuterMeasure {Q | missing Q} ≤ r := by
    have hh := overall_window hk hn₀ hμ B p hB ⟨hpos, hp₀⟩ hpB hsize (PMF.pure P)
    rw [mean_success_compl] at hh
    have hρ := ne_top_of_le_ne_top ENNReal.one_ne_top
      (event_le_one (law (step (jump k) p true) (PMF.pure P) L) {Q | missing Q})
    unfold r
    rw [← ENNReal.ofReal_toReal hρ, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by positivity : 0 ≤ q / 4)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hr : (1 - r)⁻¹ = ENNReal.ofReal (4 / q) := by
    unfold r
    rw [ENNReal.sub_sub_cancel (by simp) hq4, ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < q / 4)]
    congr 1
    field_simp
  apply (expectedOptimizationTime_le_of_block n k μ p true (by omega) L hL r hblock).trans
  rw [hr, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  have hcost := overall_window_cost (k := k) (by omega : 2 ≤ n) hμ ⟨hpos, hle⟩
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hD : (L : ℝ) ≤ D₀ * ((μ : ℕ) * n * Real.log n + 1 / p) := by
    apply hcost.trans
    dsimp [D₀]
    nlinarith [mul_nonneg (show 0 ≤ ((crossRate k)⁻¹ + 2) by positivity [crossRate_pos k])
        (show 0 ≤ ((μ : ℕ) : ℝ) * n * Real.log n by positivity),
      mul_nonneg (show 0 ≤ 128 * (1 + (Real.log 2)⁻¹) + (k : ℝ) * (Real.log 2)⁻¹ by positivity)
        (show 0 ≤ 1 / p by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hD (show 0 ≤ 4 / q by positivity)
  calc
    (L : ℝ) * (4 / q) ≤ D₀ * ((μ : ℕ) * n * Real.log n + 1 / p) * (4 / q) := hmul
    _ = _ := by ring

end
end Lax637351Proofs.Theorem2iii
