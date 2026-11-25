import Lax637351Proofs.Independent
import Lax637351Proofs.Barrier
import Lax637351Proofs.PairStep

namespace Lax637351Proofs.SparseDeviation

open Lax637351Proofs.Independent Lax637351Proofs.Barrier
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)]

def countScore (G : ∀ i, β i → Prop) (x : ∀ i, β i) : ℝ :=
  ∑ i, indicator (G i (x i))

def countMean (p : ∀ i, PMF (β i)) (G : ∀ i, β i → Prop) : ℝ :=
  ∑ i, mean (p i) (fun z ↦ indicator (G i z))

lemma centered_mgf (p : ∀ i, PMF (β i)) (G : ∀ i, β i → Prop) {lam : ℝ}
    (hlam : |lam| ≤ 1) :
    mean (product p) (fun x ↦ Real.exp (lam * (countScore G x - countMean p G))) ≤
      Real.exp (countMean p G * lam ^ 2) := by
  let m (i : ι) := mean (p i) (fun z ↦ indicator (G i z))
  have hm (i : ι) : 0 ≤ m i := mean_nonneg _ (fun _ ↦ indic_nonneg _)
  have hsplit (i : ι) (a : β i) :
      Real.exp (lam * indicator (G i a)) = 1 + (Real.exp lam - 1) * indicator (G i a) := by
    by_cases h : G i a <;> simp [indicator, h]
  have hbound (i : ι) :
      mean (p i) (fun a ↦ Real.exp (lam * indicator (G i a))) ≤ Real.exp ((lam + lam ^ 2) * m i) := by
    simp_rw [hsplit, mean_add, mean_const, mean_mul]
    change 1 + (Real.exp lam - 1) * m i ≤ _
    calc
      _ ≤ Real.exp ((Real.exp lam - 1) * m i) := by
        simpa only [add_comm] using Real.add_one_le_exp ((Real.exp lam - 1) * m i)
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right (exp_quadratic hlam) (hm i)
        nlinarith only [hh]
  have hfactor (x : ∀ i, β i) :
      Real.exp (lam * (countScore G x - countMean p G)) =
        Real.exp (-lam * countMean p G) * ∏ i, Real.exp (lam * indicator (G i (x i))) := by
    rw [← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_add]
    unfold countScore
    congr 1
    ring
  simp_rw [hfactor]
  rw [mean_mul, mean_product p (fun i a ↦ Real.exp (lam * indicator (G i a)))]
  apply le_trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ ↦ mean_nonneg _ (fun _ ↦ (Real.exp_pos _).le))
      (fun i _ ↦ hbound i)) (Real.exp_pos _).le) _
  rw [← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by change -lam * countMean p G + (lam + lam ^ 2) * countMean p G ≤ _; nlinarith)

lemma lower_deviation (p : ∀ i, PMF (β i)) (G : ∀ i, β i → Prop)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) (a : ℝ) :
    (product p).toOuterMeasure {x | countScore G x ≤ countMean p G - a} ≤
      ENNReal.ofReal (Real.exp (countMean p G * lam ^ 2 - lam * a)) := by
  have hh := event_markov (product p) (fun x ↦ Real.exp (-lam * (countScore G x - countMean p G)))
    (fun _ ↦ (Real.exp_pos _).le) {x | countScore G x ≤ countMean p G - a}
    (Real.exp (lam * a)) (Real.exp_pos _)
    (fun x hx ↦ Real.exp_le_exp.mpr (by
      have hh : countScore G x ≤ countMean p G - a := hx
      have h := mul_le_mul_of_nonneg_left (show a ≤ countMean p G - countScore G x by linarith) hlam
      nlinarith))
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_sub]
  have h := centered_mgf p G (lam := -lam) (by rwa [abs_neg, abs_of_nonneg hlam])
  rw [neg_sq] at h
  exact div_le_div_of_nonneg_right h (Real.exp_pos _).le

end
end Lax637351Proofs.SparseDeviation
