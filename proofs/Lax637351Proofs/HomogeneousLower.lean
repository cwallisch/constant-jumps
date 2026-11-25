import Lax637351Proofs.PlateauRegeneration
import Lax637351Proofs.TailLower
import Lax637351Proofs.PlateauEntry
import Lax637351Proofs.UniformEntry

namespace Lax637351Proofs.HomogeneousLower

open Lax637351.Algorithm Lax637351.Runtime Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open Lax637351Proofs.Charge Lax637351Proofs.RegenerationBounds Lax637351Proofs.PlateauRegeneration
open Lax637351Proofs.CopyingExponential Lax637351Proofs.Ordinary Lax637351Proofs.PlateauPairs
open Lax637351Proofs.TailLower Lax637351Proofs.RuntimeTransfer Lax637351Proofs.RuntimeBridge
open Lax637351Proofs.PlateauEntry Lax637351Proofs.UniformEntry Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def chargeRate (k n : ℕ) (μ : ℕ+) (p : ℝ) : ℝ :=
  hitBound (resetBudget μ p) (1 / (n : ℝ)) k / resetBudget μ p

lemma chargeRate_pos {p : ℝ} (hn : 0 < n) (hp : 0 < p) : 0 < chargeRate k n μ p := by
  have ht : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  unfold chargeRate hitBound resetBudget
  positivity

lemma homogeneous_lower (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (hp' : (k + 1 : ℝ) / n ≤ p)
    (P : Population n μ) (hP : homogeneousPlateau k P) :
    ENNReal.ofReal (1 / (4 * chargeRate k n μ p)) ≤
      tailSum (step (jump k) p true) {Q | missing Q} (PMF.pure P) := by
  let K := step (jump k) p true (n := n) (μ := μ)
  let a := chargeRate k n μ p
  let C : Set (Population n μ) := {P | ¬ missing P ∨ plateau (k := k) P}
  have hC (P : Population n μ) (hP : P ∈ C) (Q : Population n μ) (hQ : Q ∈ (K P).support) :
      Q ∈ C := by
    rcases hP with hopt | hpl
    · exact Or.inl (step_preserves_optimum (by omega : 0 < k) p true hopt hQ)
    · by_cases h : missing Q
      · exact Or.inr (step_preserves_plateau_or_optimum (by omega : 0 < k)
          (by omega : k ≤ n) p true hpl hQ h)
      · exact Or.inl h
  have ha : 0 < a := chargeRate_pos (k := k) (n := n) (μ := μ) (by omega) hp.1
  have hcharge (x : Population n μ) (hx : x ∈ C) (hr : x ∈ resets k) (ht : x ∉ target)
      (t : ℕ) : mean (K x) (visit (stopped K (resets k)ᶜ) target t) ≤ a := by
    have hm : missing x := not_not.mp ht
    have hpl : plateau (k := k) x := hx.resolve_left (not_not_intro hm)
    have hhom : homogeneous x := hr.resolve_left (not_not_intro hpl)
    exact reset_charge hk hkn hμ p hp hp' x ⟨hpl, hhom⟩ t
  have hlin (t : ℕ) : visit K target t P ≤ (t : ℝ) * a := by
    have ht := visit_le_charges K target (resets k) C a ha.le hC hcharge t P (Or.inr hP.1)
    have hz := stopped_at_plateau_reset (k := k) p P (Or.inr hP.2)
      (ordinary_missing (by omega : 0 < k) (fun j ↦ (hP.1 j).ge)) t
    rw [hz, add_zero] at ht
    exact ht
  have habs : ∀ x ∈ (target : Set (Population n μ)), ∀ y ∈ (K x).support, y ∈ target :=
    fun x hx y hy ↦ step_preserves_optimum (by omega : 0 < k) p true hx hy
  have hset : (target : Set (Population n μ))ᶜ = {Q | missing Q} := by
    ext Q
    simp [target]
  simpa only [hset] using tail_from_linear K target P habs a ha hlin

lemma from_uniform_lower (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (hp' : (k + 1 : ℝ) / n ≤ p)
    (hinit : (1 / 2 : ℝ) ≤ mean (PMF.uniformOfFintype (Population n μ))
      (fun P ↦ indicator (ordinary k P))) :
    ENNReal.ofReal (Real.exp (-16 * ((μ : ℕ) : ℝ)) / (32 * chargeRate k n μ p)) ≤
      expectedOptimizationTime n k μ p true := by
  let K := step (jump k) p true (n := n) (μ := μ)
  let ν := PMF.uniformOfFintype (Population n μ)
  let G : Set (Population n μ) := {Q | homogeneousPlateau k Q}
  let E : Set (Population n μ) := {Q | plateauEntry k Q}
  let q := Real.exp (-16 * ((μ : ℕ) : ℝ))
  let a := chargeRate k n μ p
  have hq : 0 < q := Real.exp_pos _
  have hq' : q ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith [show (0 : ℝ) ≤ (μ : ℕ) by positivity]
  have ha : 0 < a := chargeRate_pos (k := k) (n := n) (μ := μ) (by omega) hp.1
  obtain ⟨t, ht⟩ := uniform_entry_window (μ := μ) (by omega : 0 < k)
    (by omega : k ≤ n) (by omega : 2 ≤ n) p ⟨hp.1.le, hp.2⟩
  have ht' (P : Population n μ) (hP : ordinary k P) : q / 4 ≤ visit K G (t + resetWindow μ p) P := by
    have hh := visit_lower_through K E G (resetWindow μ p) q hq.le hq'
      (fun Q hQ ↦ reset_window_lower (by omega : 0 < k) (by omega : k ≤ n) (by omega : 2 ≤ n)
        hμ p hp hp' Q hQ.1 hQ.2) t P
    simpa only [div_eq_mul_inv, one_mul] using
      (mul_le_mul_of_nonneg_left (ht P hP) hq.le).trans hh
  let L := t + resetWindow μ p
  have hmass_pt (P : Population n μ) : (q / 4) * indicator (ordinary k P) ≤ visit K G L P := by
    by_cases hP : ordinary k P
    · simpa only [indicator, if_pos hP, mul_one] using ht' P hP
    · simpa only [indicator, if_neg hP, mul_zero] using visit_nonneg K G L P
  have hh := mean_mono ν hmass_pt
  rw [mean_mul, mean_visit_eq] at hh
  have hq8 : q / 8 ≤ ((law (stopped K Gᶜ) ν L).toOuterMeasure G).toReal := by
    have ht := mul_le_mul_of_nonneg_left hinit (show 0 ≤ q / 4 by positivity)
    linarith
  have hmass : ENNReal.ofReal (q / 8) ≤ (law (stopped K Gᶜ) ν L).toOuterMeasure G := by
    have hne := ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one (law (stopped K Gᶜ) ν L) G)
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal hq8
  have hr := tailSum_ge_from_hit K {Q | missing Q} G ν (ENNReal.ofReal (1 / (4 * a)))
    (fun Q hQ ↦ homogeneous_lower hk hkn hμ p hp hp' Q hQ) L
  rw [expectedOptimizationTime_eq]
  change ENNReal.ofReal (q / (32 * a)) ≤ tailSum K {Q | missing Q} ν
  have hx := mul_le_mul' hmass (le_refl (ENNReal.ofReal (1 / (4 * a))))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q / 8)] at hx
  rw [show q / 8 * (1 / (4 * a)) = q / (32 * a) by ring] at hx
  exact hx.trans hr

end
end Lax637351Proofs.HomogeneousLower
