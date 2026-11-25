import Lax637351Proofs.RegenerationBounds
import Lax637351Proofs.FiniteHitting

namespace Lax637351Proofs.Charge

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.Regeneration Lax637351Proofs.RegenerationBounds
open scoped Classical ENNReal

noncomputable section

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

def marginal (J : Kernel α ι) (x : α) : PMF α := (J x).map Prod.snd

omit [DecidableEq ι] in
lemma span_sum (J : Kernel α ι) (R : Set α) (t : ℕ) (x : α) :
    span J R t x = ∑ j ∈ Finset.range t, (1 - visit (marginal J) R j x) := by
  induction t generalizing x with
  | zero => simp [span]
  | succ t ih =>
    by_cases hx : x ∈ R
    · rw [span, if_pos hx]
      simp only [visit_in (marginal J) R _ x hx, sub_self, Finset.sum_const_zero]
    · rw [span, if_neg hx, Finset.sum_range_succ', visit, if_neg hx, sub_zero]
      simp_rw [ih, mean_sum, visit, if_neg hx]
      rw [add_comm (1 : ℝ)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [mean_sub, mean_const, marginal, mean_map]

omit [DecidableEq ι] in
lemma span_le_of_block (J : Kernel α ι) (R : Set α) (L : ℕ) (hL : 0 < L)
    (q : ℝ) (hq : 0 < q) (hq' : q ≤ 1)
    (hvisit : ∀ x, q ≤ visit (marginal J) R L x) (t : ℕ) (x : α) :
    span J R t x ≤ (L : ℝ) / q := by
  let K := marginal J
  let S := stopped K Rᶜ
  let C := Rᶜ
  have habs (y : α) (hy : y ∉ C) : (S y).toOuterMeasure C = 0 := by
    change (stopped K C y).toOuterMeasure C = 0
    rw [stopped, if_neg hy, PMF.toOuterMeasure_pure_apply, if_neg hy]
  have hqE : ENNReal.ofReal q ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq'
  have hcompl (s : ℕ) (y : α) :
      (1 - visit K R s y) = ((law S (PMF.pure y) s).toOuterMeasure C).toReal := by
    rw [visit_eq_mean_stopped, mean_indicator]
    let p := law S (PMF.pure y) s
    have hh := event_add_compl p R
    have hf : p.toOuterMeasure R ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one p R)
    have hg : p.toOuterMeasure C ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one p C)
    have hh' := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_add hf hg, ENNReal.toReal_one] at hh'
    change 1 - (p.toOuterMeasure R).toReal = (p.toOuterMeasure C).toReal
    linarith
  have hblock (y : α) (_ : y ∈ C) :
      (law S (PMF.pure y) L).toOuterMeasure C ≤ 1 - ENNReal.ofReal q := by
    have h := hvisit y
    have hh := hcompl L y
    have hf : (law S (PMF.pure y) L).toOuterMeasure C ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _)
    rw [← ENNReal.ofReal_toReal hf, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ hq.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hh := runtime_le_of_block S (PMF.pure x) C habs L hL _ hblock
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hqE, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ))] at hh
  have heq (j : ℕ) (hj : j ∈ Finset.range t) : (law S (PMF.pure x) j).toOuterMeasure C ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _)
  have hf := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((ENNReal.sum_le_tsum (Finset.range t)).trans hh)
  rw [span_sum]
  change (∑ j ∈ Finset.range t, (1 - visit K R j x)) ≤ _
  simp_rw [hcompl]
  rw [ENNReal.toReal_sum heq, ENNReal.toReal_ofReal (by positivity), ← div_eq_mul_inv] at hf
  exact hf

lemma stopped_success_le_capture (J : Kernel α ι) (R G : Set α) (intact : Finset ι → α → Prop)
    (hgoal : ∀ x ∈ G, ∀ D, intact D x → D = ∅)
    (hcarry : ∀ x v, v ∈ (J x).support → ∀ D, intact D x → intact (D \ v.1) v.2)
    (t : ℕ) (D : Finset ι) (x : α) (hx : intact D x) :
    visit (stopped (marginal J) Rᶜ) G t x ≤ capture J R t D x := by
  induction t generalizing D x with
  | zero =>
    by_cases hG : x ∈ G
    · rw [hgoal x hG D hx, capture_empty, visit_in _ _ _ _ hG]
    · rw [visit, if_neg hG]
      exact capture_nonneg _ _ _ _ _
  | succ t ih =>
    by_cases hG : x ∈ G
    · rw [hgoal x hG D hx, capture_empty, visit_in _ _ _ _ hG]
    · rw [visit, if_neg hG]
      by_cases hR : x ∈ R
      · simp only [stopped, Set.mem_compl_iff, hR, not_true_eq_false,
          if_false, mean_pure]
        have hh : visit (stopped (marginal J) Rᶜ) G t x = 0 := by
          apply visit_eq_zero_of_absorbed (A := {x})
          · simp [hG]
          · intro y hy z hz
            have hy' : y = x := Set.mem_singleton_iff.mp hy
            subst y
            simp [stopped, hR] at hz
            exact hz
          · simp
        rw [hh]
        exact capture_nonneg _ _ _ _ _
      · by_cases hD : D = ∅
        · rw [hD, capture_empty]
          apply (mean_mono _ fun y ↦ visit_le_one _ _ _ y).trans_eq (mean_const _ 1)
        · rw [capture, if_neg hD, if_neg hR, stopped, if_pos (show x ∈ Rᶜ from hR), marginal, mean_map]
          exact mean_mono_on_support _ (fun v hv ↦ ih _ _ (hcarry x v hv D hx))

lemma visit_le_charges (K : α → PMF α) (G R C : Set α) (a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ x ∈ C, ∀ y ∈ (K x).support, y ∈ C)
    (ha' : ∀ x ∈ C, x ∈ R → x ∉ G → ∀ t,
      mean (K x) (visit (stopped K Rᶜ) G t) ≤ a)
    (t : ℕ) (x : α) (hx : x ∈ C) :
    visit K G t x ≤ (t : ℝ) * a + visit (stopped K Rᶜ) G t x := by
  induction t generalizing x with
  | zero => simp [visit]
  | succ t ih =>
    by_cases hG : x ∈ G
    · simp only [visit_in _ _ _ _ hG]
      exact le_add_of_nonneg_left (by positivity)
    · rw [visit, if_neg hG]
      have hh := mean_mono_on_support (K x) (fun y hy ↦ ih y (hC x hx y hy))
      rw [mean_add, mean_const] at hh
      apply hh.trans
      push_cast
      by_cases hR : x ∈ R
      · have he := ha' x hx hR hG t
        have hn := visit_nonneg (stopped K Rᶜ) G (t + 1) x
        nlinarith
      · rw [visit, if_neg hG, stopped, if_pos (show x ∈ Rᶜ from hR)]
        linarith

end
end Lax637351Proofs.Charge
