import Lax637351Proofs.UpperWindows
import Lax637351Proofs.ArrivalBound
import Lax637351Proofs.RareSuccess

namespace Lax637351Proofs.UpperRuntime

open Lax637351.Algorithm Lax637351.Runtime Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteWindows Lax637351Proofs.RuntimeBridge
open Lax637351Proofs.PlateauPairs (plateau)
open Lax637351Proofs.ArrivalTime Lax637351Proofs.ArrivalCross Lax637351Proofs.ArrivalProgress
open Lax637351Proofs.ArrivalBound Lax637351Proofs.RareSuccess Lax637351Proofs.CrossoverSuccess
open Lax637351Proofs.OffspringEstimates
open Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnBands Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.SpeciesWindow Lax637351Proofs.PlateauChanges Lax637351Proofs.UpperWindows
open Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def arrivalBudget (n k : ℕ) (μ : ℕ+) (p : ℝ) (ar : Bool) : ℝ :=
  128 * (k : ℝ) * (μ : ℕ) + (ordinaryChance k)⁻¹ *
    ((n : ℝ) * (1 + Real.log n) + (μ : ℕ) * n * (5 + Real.log (1 / effective ar p)))

def arrivalConstant (k : ℕ) : ℝ := 128 * (k : ℝ) + 7 * (ordinaryChance k)⁻¹

lemma arrivalConstant_pos (k : ℕ) : 0 < arrivalConstant k := by
  have hc := ordinaryChance_pos k
  unfold arrivalConstant
  positivity

def runtimeConstant (a : Settings k) : ℝ :=
  (2 * arrivalConstant k + 1 + plateauTimeConstant a) * (16 / plateauChance a)

lemma runtimeConstant_pos (a : Settings k) (hk : 2 ≤ k) : 0 < runtimeConstant a := by
  have h := (plateau_constants a hk).2.1
  have hq := (plateau_constants a hk).2.2.1
  have hC := arrivalConstant_pos k
  unfold runtimeConstant
  positivity

lemma startup_budget (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hlog : Real.log ((n : ℝ) * effective ar p) ≤ ((μ : ℕ) : ℝ)) :
    arrivalBudget n k μ p ar ≤ arrivalConstant k * ((μ : ℕ) : ℝ) * n *
      Real.log (Real.exp 1 / effective ar p) := by
  let r := effective ar p
  let m : ℝ := (μ : ℕ)
  let c := Real.log (1 / r)
  let ℓ := Real.log (Real.exp 1 / r)
  have hr := effective_valid p hp ar
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith only [hn']
  have hm : 1 ≤ m := by unfold m; exact_mod_cast μ.pos
  have hc : 0 ≤ c := Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by simpa using hr.2))
  have he : ℓ = 1 + c := by
    unfold ℓ c
    rw [Real.log_div (Real.exp_pos _).ne' hr.1.ne', Real.log_div (by norm_num) hr.1.ne', Real.log_exp, Real.log_one]
    ring
  have hlog' : Real.log (n : ℝ) ≤ m + c := by
    rw [Real.log_mul hn₀.ne' hr.1.ne'] at hlog
    unfold c
    rw [Real.log_div (by norm_num) hr.1.ne', Real.log_one]
    linarith only [hlog]
  have hℓ : 1 ≤ ℓ := by linarith only [he, hc]
  have hterm : 1 + Real.log (n : ℝ) ≤ 2 * m * ℓ := by
    have hmc := mul_nonneg (show 0 ≤ m - 1 by linarith only [hm]) hc
    nlinarith only [hm, hc, he, hlog', hmc]
  have hterm' : 5 + c ≤ 5 * ℓ := by linarith only [he, hc]
  have hA := mul_le_mul_of_nonneg_left hterm hn₀.le
  have hB := mul_le_mul_of_nonneg_left hterm' (show 0 ≤ m * n by positivity)
  have hC := mul_le_mul_of_nonneg_right (mul_le_mul hn' hℓ (by norm_num : (0 : ℝ) ≤ 1) hn₀.le)
    (show 0 ≤ 128 * (k : ℝ) * m by positivity)
  have hD := mul_le_mul_of_nonneg_left (add_le_add hA hB) (inv_nonneg.mpr (ordinaryChance_pos k).le)
  change 128 * (k : ℝ) * m + (ordinaryChance k)⁻¹ * ((n : ℝ) * (1 + Real.log n) + m * n * (5 + c)) ≤
    arrivalConstant k * m * n * ℓ
  unfold arrivalConstant
  linarith only [hC, hD]

lemma overall_window (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool) (hnp : 1 ≤ (n : ℝ) * effective ar p)
    (t : ℕ) (ht : 0 < t) (hbudget : arrivalBudget n k μ p ar ≤ (t : ℝ) / 2)
    (hplateau : ∀ P : Population n μ, plateau (k := k) P →
      plateauChance a / 8 ≤ 1 - ((law (step (jump k) p ar) (PMF.pure P) (blockTime a μ n p)).toOuterMeasure
        {Q | missing Q}).toReal)
    (ν : PMF (Population n μ)) :
    plateauChance a / 16 ≤ mean (law (step (jump k) p ar) ν (t + blockTime a μ n p)) success := by
  let K := step (jump k) p ar (n := n) (μ := μ)
  let W := blockTime a μ n p
  let q := plateauChance a
  let A : Set (Population n μ) := {P | arriving k P}
  let ν' := law K ν t
  have hq := (plateau_constants a hk).2.2.1
  have hq' : q ≤ 1 / 2 := min_le_left _ _
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hb := arrival_tail_sharp hk (by have := hn.four; omega) p hp ar hnp ν t
  have htail : (ν'.toOuterMeasure A).toReal ≤ 1 / 2 := by
    change (t : ℝ) * (ν'.toOuterMeasure A).toReal ≤ arrivalBudget n k μ p ar at hb
    exact (mul_le_mul_iff_of_pos_left ht').mp (hb.trans (hbudget.trans_eq (by ring)))
  have hpoint (P : Population n μ) :
      q / 8 * (1 - indicator (P ∈ A)) ≤ mean (law K (PMF.pure P) W) success := by
    by_cases hP : P ∈ A
    · rw [indicator, if_pos hP, sub_self, mul_zero]
      exact mean_nonneg _ success_nonneg
    · rw [indicator, if_neg hP, sub_zero, mul_one, mean_success_compl]
      by_cases hm : missing P
      · exact hplateau P (by by_contra hP'; exact hP ⟨hm, hP'⟩)
      · have he : (law K (PMF.pure P) W).toOuterMeasure {Q | missing Q} = 0 :=
          event_law_eq_zero K {Q | missing Q} (step_missing_eq_zero (by omega : 0 < k) p ar) W P hm
        rw [he, ENNReal.toReal_zero, sub_zero]
        linarith only [hq']
  have hh := mean_mono ν' hpoint
  rw [mean_mul, mean_sub, mean_const, mean_event, ← mean_bind] at hh
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (ν'.toOuterMeasure A).toReal := by linarith only [htail]
  have h := (mul_le_mul_of_nonneg_left hhalf (show 0 ≤ q / 8 by positivity)).trans hh
  rw [show q / 8 * (1 / 2 : ℝ) = q / 16 by ring] at h
  change q / 16 ≤ mean (law K ν (t + W)) success
  rwa [law_add]

lemma runtime_upper (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hnp : 1 ≤ (n : ℝ) * p) (hlog : Real.log ((n : ℝ) * effective ar p) ≤ ((μ : ℕ) : ℝ))
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ 3 * p)
    (hfloor : populationFloor a ≤ ((μ : ℕ) : ℝ))
    (htail : let r := changeBound n k p ar
      (plateauTimeConstant a * ((μ : ℕ) : ℝ) * n * r + 1) *
        Real.exp (-decay a * (μ : ℕ) * p / r) ≤ failureTolerance a) :
    expectedOptimizationTime n k μ p ar ≤
      ENNReal.ofReal (runtimeConstant a * ((μ : ℕ) : ℝ) * n * Real.log (Real.exp 1 / effective ar p)) := by
  let q := plateauChance a
  let ℓ := Real.log (Real.exp 1 / effective ar p)
  let c := arrivalConstant k
  let t := countTime (2 * c * ℓ) μ n
  let W := blockTime a μ n p
  let L := t + W
  let r := 1 - ENNReal.ofReal (q / 16)
  let K := step (jump k) p ar (n := n) (μ := μ)
  have hq : 0 < q := (plateau_constants a hk).2.2.1
  have hq' : q ≤ 1 / 2 := min_le_left _ _
  have hc' : 0 < c := arrivalConstant_pos k
  have hMμ : (6 : ℝ) ≤ ((μ : ℕ) : ℝ) + 1 := by
    have h : (5 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hμ
    linarith only [h]
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hn.two; omega)
  have hμ₀ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hr' := effective_valid p hp ar
  have hℓ : 1 ≤ ℓ := by
    unfold ℓ
    rw [Real.log_div (Real.exp_pos _).ne' hr'.1.ne', Real.log_exp]
    linarith only [Real.log_nonpos hr'.1.le hr'.2]
  have hℓ₀ : 0 < ℓ := by linarith only [hℓ]
  have ht₀ := countTime_lower (2 * c * ℓ) μ n
  have ht : 0 < t := by
    have hh : (0 : ℝ) < t := (show 0 < (2 * c * ℓ) * ((μ : ℕ) : ℝ) * n by positivity).trans_le ht₀
    exact_mod_cast hh
  have hL : 0 < L := Nat.add_pos_left ht _
  have hnr : 1 ≤ (n : ℝ) * effective ar p := by
    cases ar
    · simpa [effective] using (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by have := hn.two; omega))
    · simpa [effective] using hnp
  have hbudget := startup_budget (k := k) (by have := hn.two; omega) p hp ar hlog
  have hbudget' : arrivalBudget n k μ p ar ≤ (t : ℝ) / 2 := by
    change _ ≤ c * ((μ : ℕ) : ℝ) * n * ℓ at hbudget
    change (2 * c * ℓ) * ((μ : ℕ) : ℝ) * n ≤ (t : ℝ) at ht₀
    linarith only [hbudget, ht₀]
  have hplateau := plateau_block hk a hn hm hc herror hμ p hp ar hnp hcopy hLoss hfloor htail
  have hblock (P : Population n μ) (_ : missing P) :
      (law K (PMF.pure P) L).toOuterMeasure {Q | missing Q} ≤ r := by
    have hh := overall_window hk a hn p hp ar hnr t ht hbudget' hplateau (PMF.pure P)
    rw [mean_success_compl] at hh
    have hρ := ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one (law K (PMF.pure P) L) {Q | missing Q})
    unfold r
    rw [← ENNReal.ofReal_toReal hρ, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by positivity : 0 ≤ q / 16)]
    apply ENNReal.ofReal_le_ofReal
    change q / 16 ≤ 1 - ((law K (PMF.pure P) L).toOuterMeasure {Q | missing Q}).toReal at hh
    linarith only [hh]
  have hq₁ : ENNReal.ofReal (q / 16) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hq'])
  have hinv : (1 - r)⁻¹ = ENNReal.ofReal (16 / q) := by
    unfold r
    rw [ENNReal.sub_sub_cancel (by simp) hq₁, ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < q / 16)]
    congr 1
    field_simp
  apply (expectedOptimizationTime_le_of_block n k μ p ar (by omega) L hL r hblock).trans
  rw [hinv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  have ht' := countTime_upper (2 * c * ℓ) (by positivity) μ (by have := hn.two; omega : 1 ≤ n)
  have hW := windows_bound a hk (by have := hn.two; omega) p hp hnp hMμ
  have hbound : (L : ℝ) ≤ (2 * c + 1 + plateauTimeConstant a) * ((μ : ℕ) : ℝ) * n * ℓ := by
    have hℓ' := mul_le_mul_of_nonneg_left hℓ
      (show 0 ≤ (1 + plateauTimeConstant a) * ((μ : ℕ) : ℝ) * n by
        have hg := (plateau_constants a hk).2.1
        positivity)
    change (t : ℝ) ≤ (2 * c * ℓ + 1) * ((μ : ℕ) : ℝ) * n at ht'
    change ((t + W : ℕ) : ℝ) ≤ _
    push_cast
    linarith only [ht', hW, hℓ']
  have h := mul_le_mul_of_nonneg_right hbound (show 0 ≤ 16 / q by positivity)
  unfold runtimeConstant
  change (L : ℝ) * (16 / q) ≤ ((2 * c + 1 + plateauTimeConstant a) * (16 / q)) * ((μ : ℕ) : ℝ) * n * ℓ
  exact h.trans_eq (by ring)

end
end Lax637351Proofs.UpperRuntime
