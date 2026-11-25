import Lax637351Proofs.ColumnBands

namespace Lax637351Proofs.ColumnBarriers

open Lax637351.Algorithm
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting
open Lax637351Proofs.FiniteWindows Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.ColumnSlot Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnBands
open Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ColumnMutationDrift Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.ColumnReplacement Lax637351Proofs.ColumnCrossDrift
open Lax637351Proofs.SpeciesWindow Lax637351Proofs.SpeciesProtection
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauChanges
open Lax637351Proofs.FamilyRecovery Lax637351Proofs.SparseBarrier Lax637351Proofs.Endgame
open Lax637351Proofs.BarrierWindows Lax637351Proofs.SubsetPairs Lax637351Proofs.Transitions
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def columnChain (k : ℕ) (p : ℝ) (ar : Bool) (P : Population n μ) : PMF (Population n μ) :=
  stopped (auxiliary k p ar) (active k) P

lemma height_pos (a : Settings k) (μ : ℕ+) : 0 < height a μ := by
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  exact mul_pos (settings_levels a).1 hm

lemma protected_invariant (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (Q : Population n μ)
    (hQ : Q ∈ (columnChain k p ar P).support) : plateau (k := k) Q := by
  by_cases h : P ∈ active k
  · rw [columnChain, stopped, if_pos h] at hQ
    exact auxiliary_preserves_plateau hk hkn p ar P hP Q hQ
  · rw [columnChain, stopped, if_neg h, PMF.mem_support_pure_iff] at hQ
    exact hQ.symm ▸ hP

lemma protected_jump (hk : 0 < k) (hkn : k ≤ n) (a : Settings k) (p : ℝ) (ar : Bool)
    (P : Population n μ) (Q : Population n μ) (hQ : Q ∈ (columnChain k p ar P).support) (i : Fin n) :
    |potential a i Q - potential a i P| ≤ jumpBound a := by
  by_cases h : P ∈ active k
  · rw [columnChain, stopped, if_pos h] at hQ
    exact column_step_bound hk hkn i _ (horizon_pos a μ) _ (time_horizon a μ).le p ar P h.1 Q hQ
  · rw [columnChain, stopped, if_neg h, PMF.mem_support_pure_iff] at hQ
    simpa [hQ] using (jump_pos a).le

lemma protected_change (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (ar : Bool) (P : Population n μ) :
    mean (columnChain k p ar P) (fun Q ↦ indicator (Q ≠ P)) ≤ changeBound n k p ar := by
  by_cases h : P ∈ active k
  · rw [columnChain, stopped, if_pos h]
    exact change_bound hk hkn hn p hp ar P h.1
  · rw [columnChain, stopped, if_neg h, mean_pure]
    simpa only [indicator, if_neg (not_not.mpr rfl)] using hp.1.trans (changeBound_ge_p (n := n) (k := k) p hp ar)

lemma slope_range (a : Settings k) (n : ℕ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool) :
    0 ≤ columnSlope a n p ar ∧ columnSlope a n p ar * jumpBound a ≤ 1 := by
  have h := changeBound_ge_p (n := n) (k := k) p ⟨hp.1.le, hp.2⟩ ar
  have hr := hp.1.trans_le h
  have hB := jump_pos a
  have hS := slope_pos a
  unfold columnSlope
  constructor
  · exact div_nonneg (mul_nonneg hS.le hp.1.le) hr.le
  · have hbound : slopeConstant a * jumpBound a ≤ 1 :=
      (le_div_iff₀ hB).mp (min_le_left _ _)
    rw [div_mul_eq_mul_div, div_le_one hr]
    have h' := mul_le_mul_of_nonneg_right hbound hp.1.le
    linarith only [h', h]

lemma protected_moment (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hμ : PopulationSize k a μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (P : Population n μ) (i : Fin n) (hl : height a μ ≤ potential a i P) (hu : potential a i P ≤ 4 * height a μ) :
    columnSlope a n p ar * mean (columnChain k p ar P) (fun Q ↦ (potential a i Q - potential a i P) ^ 2) ≤
      mean (columnChain k p ar P) (fun Q ↦ potential a i Q - potential a i P) := by
  by_cases hs : P ∈ active k
  · rw [columnChain, stopped, if_pos hs]
    let r := changeBound n k p ar
    let b := jumpBound a
    let lam := columnSlope a n p ar
    have hT : (0 : ℝ) < (a.T : ℕ) := by exact_mod_cast a.T.pos
    have hk' : 0 < k := by omega
    have hkn : k ≤ n := by have := hn.four; omega
    have h₀ : 0 ≤ lam := (slope_range a n p hp ar).1
    have hp' : 0 ≤ p ∧ p ≤ 1 := ⟨hp.1.le, hp.2⟩
    have hr : 0 < r := hp.1.trans_le (changeBound_ge_p (n := n) (k := k) p hp' ar)
    have hb : 0 < b := jump_pos a
    have hm := unchanged_second_moment (auxiliary k p ar) (potential a i) b hb.le P
      (fun Q hQ ↦ column_step_bound hk' hkn i _ (horizon_pos a μ) _ (time_horizon a μ).le p ar P hs.1 Q hQ)
    have hc := change_bound hk' hkn hn.two p hp' ar P hs.1
    have h₂ := mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg b))) h₀
    have hF := potential_high_frequency a i P hs.1 hl
    have hD := potential_conditioned_drift hk a hn hμ p hp' ar hcopy P hs.1 hs.2 i hu
    have hbound : lam * (b ^ 2 * r) ≤ p * a.frequencyLevel / (8 * (a.T : ℕ)) := by
      have he : lam * (b ^ 2 * r) = p * (slopeConstant a * b ^ 2) := by
        unfold lam columnSlope
        change slopeConstant a * p / r * (b ^ 2 * r) = _
        field_simp
      rw [he]
      have h' : slopeConstant a ≤ a.frequencyLevel / (8 * (a.T : ℕ) * b ^ 2) := min_le_right _ _
      have hbnd : slopeConstant a * b ^ 2 ≤ a.frequencyLevel / (8 * (a.T : ℕ)) :=
        (mul_le_mul_of_nonneg_right h' (sq_nonneg b)).trans_eq (by field_simp [hb.ne'])
      exact (mul_le_mul_of_nonneg_left hbnd hp.1.le).trans_eq (by ring)
    have h₁ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF hp.1.le)
      (show 0 ≤ 8 * ((a.T : ℕ) : ℝ) by positivity)
    exact h₂.trans (hbound.trans (h₁.trans ((le_add_of_nonneg_right (div_nonneg (entryRate_pos _ _).le (by positivity))).trans hD)))
  · rw [columnChain, stopped, if_neg hs, mean_pure, mean_pure]
    simp

lemma protected_small (hk : 0 < k) (hkn : k ≤ n) (a : Settings k) (p : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (ar : Bool) (P Q : Population n μ)
    (hQ : Q ∈ (columnChain k p ar P).support) (i : Fin n) :
    |columnSlope a n p ar * (potential a i Q - potential a i P)| ≤ 1 := by
  have h := slope_range a n p hp ar
  rw [abs_mul, abs_of_nonneg h.1]
  exact (mul_le_mul_of_nonneg_left (protected_jump hk hkn a p ar P Q hQ i) h.1).trans h.2

def barrierFactor (a : Settings k) (n : ℕ) (μ : ℕ+) (p : ℝ) (ar : Bool) (t : ℕ) : ℝ :=
  ((t : ℝ) * changeBound n k p ar + 1) *
    Real.exp (-columnSlope a n p ar * (height a μ - jumpBound a))

lemma column_recovery (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (t : ℕ) (ht : 0 < t) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (htime : Real.exp (2 * (a.T : ℕ)) * (μ : ℕ) ≤ entryRate k (a.T : ℕ) / n * t * ζ)
    (P : Population n μ) (hP : plateau (k := k) P) :
    mean (law (columnChain k p ar) (PMF.pure P) t)
      (fun Q ↦ indicator (Q ∈ active k ∧ ¬stabilization a Q)) ≤
      2 * k * ζ + 4 * k * barrierFactor a n μ p ar t := by
  let K : Population n μ → PMF (Population n μ) := columnChain k p ar
  let C : Set (Population n μ) := {Q | plateau (k := k) Q}
  let h := height a μ
  let b := jumpBound a
  let lam := columnSlope a n p ar
  let r := changeBound n k p ar
  let d := entryRate k (a.T : ℕ) / n
  have hH : 0 < h := height_pos a μ
  have hk' : 0 < k := by omega
  have hkn : k ≤ n := by have := hn.four; omega
  have hr : 0 ≤ r := hp.1.le.trans (changeBound_ge_p p ⟨hp.1.le, hp.2⟩ ar)
  have hd : 0 < d := div_pos (entryRate_pos _ _) (by exact_mod_cast (show 0 < n by have := hn.two; omega))
  have hh := recovery_window K (potential a) C (active k) (protected_invariant hk' hkn p ar)
    (fun Q hQ ↦ by change stopped _ _ Q = _; rw [stopped, if_neg hQ]) (fun _ hQ ↦ hQ.1)
    (2 * h) (3 * h) b lam lam (2 * k) r (Real.exp (2 * (a.T : ℕ)) * (μ : ℕ)) d ζ
    (by linarith only [hH]) (jump_pos a).le (slope_range a n p hp ar).1 le_rfl (by positivity) hr hd.le hζ
    (fun i Q _ _ R hR ↦ protected_small hk' hkn a p hp ar Q R hR i)
    (fun i Q hQ hQ' ↦ protected_moment hk a hn hm p hp ar hcopy Q i (by linarith only [hQ, hH])
      (by linarith only [hQ', hH]))
    (fun Q hQ ↦ finite_candidates a Q hQ _ (by linarith only [hH]))
    (fun Q _ R hR i ↦ protected_jump hk' hkn a p ar Q R hR i)
    (fun Q _ ↦ protected_change hk' hkn hn.two p ⟨hp.1.le, hp.2⟩ ar Q)
    (potential_total_bounds a)
    (fun i Q hQ hQ' ↦ by
      change d ≤ mean (stopped (auxiliary k p ar) (active k) Q) _
      rw [stopped, if_pos hQ]
      have hi := potential_conditioned_drift hk a hn hm p ⟨hp.1.le, hp.2⟩ ar hcopy Q hQ.1 hQ.2 i
        (by linarith only [hQ', hH])
      have hf := (frequency_valid k Q i).1
      have hpF : 0 ≤ p * frequency k i Q / (8 * (a.T : ℕ)) :=
        div_nonneg (mul_nonneg hp.1.le hf) (by positivity)
      exact (le_add_of_nonneg_left hpF).trans hi)
    t (mul_pos hd (by exact_mod_cast ht)) htime P hP
  have he : (fun Q : Population n μ ↦ indicator (Q ∈ active k ∧ ¬stabilization a Q)) =
      (fun Q ↦ indicator (Q ∈ active k ∧ ∃ i, potential a i Q < 2 * h)) := by
    funext Q
    congr 1
    simp [stabilization, h, not_forall, not_le]
  rw [he]
  refine hh.trans_eq ?_
  have hex : 3 * h - b - 2 * h = h - b := by ring
  rw [hex]
  unfold barrierFactor
  change 2 * (k : ℝ) * ζ + 2 * (2 * (k : ℝ)) * ((t : ℝ) * r + 1) * Real.exp (-lam * (h - b)) = _
  ring

lemma singleton_avoids (k : ℕ) (i : Fin n) (P : Population n μ) :
    avoidsRate {i} P = frequency k i P := by
  unfold avoidsRate frequency
  congr 1
  funext x
  congr 1
  simp only [avoids, Finset.disjoint_singleton_left, mem_zeros]
  apply propext
  constructor
  · exact bit_eq_one_of_ne_zero _
  · intro h hh
    rw [h] at hh
    exact one_ne_zero hh

lemma column_protection (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (t : ℕ) (P : Population n μ) (hP : plateau (k := k) P) (hS : stabilization a P) :
    visit (columnChain k p ar) {Q | ¬columns a.frequencyLevel Q} t P ≤
      2 * k * barrierFactor a n μ p ar t := by
  let K : Population n μ → PMF (Population n μ) := columnChain k p ar
  let C : Set (Population n μ) := {Q | plateau (k := k) Q}
  let h := height a μ
  let b := jumpBound a
  let lam := columnSlope a n p ar
  let r := changeBound n k p ar
  let E : Set (Population n μ) := ⋃ i, {Q | potential a i Q < h}
  have hH : 0 < h := height_pos a μ
  have hk' : 0 < k := by omega
  have hkn : k ≤ n := by have := hn.four; omega
  have hr : 0 ≤ r := hp.1.le.trans (changeBound_ge_p p ⟨hp.1.le, hp.2⟩ ar)
  apply (visit_mono_on_invariant K C _ E (protected_invariant hk' hkn p ar) ?_ t P hP).trans
  · have hh := sparse_visit K (potential a) C (protected_invariant hk' hkn p ar)
      h (2 * h) b lam lam (2 * k) r (by linarith only [hH]) (jump_pos a).le
      (slope_range a n p hp ar).1 le_rfl (by positivity) hr
      (fun i Q _ _ R hR ↦ protected_small hk' hkn a p hp ar Q R hR i)
      (fun i Q hQ hQ' ↦ protected_moment hk a hn hm p hp ar hcopy Q i hQ (by linarith only [hQ', hH]))
      (fun Q hQ ↦ finite_candidates a Q hQ _ (by linarith only [hH]))
      (fun Q _ R hR i hi ↦
        by linarith only [(abs_le.mp (protected_jump hk' hkn a p ar Q R hR i)).1, hi])
      (fun Q _ ↦ protected_change hk' hkn hn.two p ⟨hp.1.le, hp.2⟩ ar Q)
      t P hP (fun i ↦ by have := hS i; linarith only [this, (jump_pos a).le])
    have hex : 2 * h - b - h = h - b := by ring
    rw [hex] at hh
    exact hh.trans_eq (by unfold barrierFactor; ring)
  · intro Q hQ hQ'
    by_contra hf
    apply hQ'
    intro i
    rw [singleton_avoids k]
    apply potential_high_frequency a i Q hQ
    exact le_of_not_gt (fun hi ↦ hf (Set.mem_iUnion.mpr ⟨i, hi⟩))

end
end Lax637351Proofs.ColumnBarriers
