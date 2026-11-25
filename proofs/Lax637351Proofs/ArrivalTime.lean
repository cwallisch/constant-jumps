import Lax637351Proofs.ArrivalMutation
import Lax637351Proofs.RuntimeBridge
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Lax637351Proofs.ArrivalTime

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs (plateau)
open Lax637351Proofs.ArrivalMutation
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def arriving (k : ℕ) (P : Population n μ) : Prop :=
  missing P ∧ ¬ plateau (k := k) P

def weight (n v : ℕ) : ℝ := 64 * n / ((n - v : ℕ) : ℝ)

def rawCost (k : ℕ) (P : Population n μ) : ℝ :=
  ∑ i, ∑ v ∈ Finset.range n, if fitnessLevel k (P i) ≤ v then weight n v else 0

def cost (k : ℕ) (P : Population n μ) : ℝ :=
  if arriving k P then rawCost k P else 0

lemma weight_nonneg (n v : ℕ) : 0 ≤ weight n v := by unfold weight; positivity

lemma rawCost_nonneg (k : ℕ) (P : Population n μ) : 0 ≤ rawCost k P := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact weight_nonneg _ _
  · exact le_rfl

lemma cost_nonneg (k : ℕ) (P : Population n μ) : 0 ≤ cost k P := by
  unfold cost
  split_ifs
  · exact rawCost_nonneg _ _
  · exact le_rfl

lemma cost_le_raw (k : ℕ) (P : Population n μ) : cost k P ≤ rawCost k P := by
  unfold cost
  split_ifs
  · exact le_rfl
  · exact rawCost_nonneg _ _

lemma rawCost_difference (P Q : Population n μ)
    (hmon : ∀ i, fitnessLevel k (P i) ≤ fitnessLevel k (Q i)) :
    rawCost k P - rawCost k Q = ∑ i, ∑ v ∈ Finset.range n,
      (if fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i) then weight n v else 0) := by
  simp only [rawCost, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  have hle := hmon i
  split_ifs <;> first | rfl | omega | linarith

lemma rawCost_drop (P Q : Population n μ)
    (hmon : ∀ i, fitnessLevel k (P i) ≤ fitnessLevel k (Q i))
    (v : ℕ) (hv : v < n) :
    (if ∃ i, fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i) then weight n v else 0)
      ≤ rawCost k P - rawCost k Q := by
  rw [rawCost_difference P Q hmon]
  have hnonneg (i : Fin μ) (w : ℕ) :
      0 ≤ (if fitnessLevel k (P i) ≤ w ∧ w < fitnessLevel k (Q i) then weight n w else 0) := by
    split_ifs
    · exact weight_nonneg _ _
    · exact le_rfl
  by_cases h : ∃ i, fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i)
  · rw [if_pos h]
    obtain ⟨i, hi⟩ := h
    have ha := Finset.single_le_sum (s := Finset.range n) (fun w _ ↦ hnonneg i w)
      (Finset.mem_range.mpr hv)
    rw [if_pos hi] at ha
    exact ha.trans (Finset.single_le_sum (fun j _ ↦ Finset.sum_nonneg fun w _ ↦ hnonneg j w)
      (Finset.mem_univ i))
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg fun w _ ↦ hnonneg i w)

lemma progress_step (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1 / 2)
    (avoid : Bool) (P : Population n μ) (hP : missing P)
    (u : Fin μ) (v : ℕ) (hv : v < n) (hu : fitnessLevel k (P u) = v)
    (hmin : ∀ i, v ≤ fitnessLevel k (P i)) :
    ((n - v : ℕ) : ℝ) / (64 * n) ≤
      mean (step (jump k) p avoid P) (fun Q ↦
        if ∃ i, fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i) then 1 else 0) := by
  let f (Q : Population n μ) : ℝ :=
    if ∃ i, fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i) then 1 else 0
  have hnonneg (Q : Population n μ) : 0 ≤ f Q := by dsimp [f]; split_ifs <;> norm_num
  have hbranch (j : Fin μ) : ((n - v : ℕ) : ℝ) / (32 * n) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦
        mean (select (jump k) avoid false P (P j) (mutate (P j) m)) f) := by
    apply (mutation_progress hk hkn v hv _ (hP j) (hmin j)).trans
    apply mean_mono
    intro m
    by_cases hm : favorable (k := k) v (P j) m
    · rw [if_pos hm, ← mean_const (select (jump k) avoid false P (P j) (mutate (P j) m)) 1]
      apply mean_mono_on_support
      intro Q hQ
      have hn : ¬ (avoid = true ∧ ¬ false = true ∧ mutate (P j) m = P j) :=
        fun h ↦ hm.1 h.2.2
      rw [select, if_neg hn] at hQ
      have hfbetter : jump k (P u) < jump k (mutate (P j) m) := by
        rw [← fitnessLevel_eq (by omega : k ≤ n), ← fitnessLevel_eq (by omega : k ≤ n), hu]
        exact_mod_cast hm.2
      obtain ⟨d, hD, hd⟩ := insert_strict_improvement (jump k) P _ u hfbetter hQ
      have hd' : fitnessLevel k (P d) ≤ v := by
        rw [← fitnessLevel_eq (by omega : k ≤ n), ← fitnessLevel_eq (by omega : k ≤ n), hu] at hd
        exact_mod_cast hd
      have hdQ : fitnessLevel k (Q d) = fitnessLevel k (mutate (P j) m) := by
        simp [hD]
      simp [f, show ∃ i, fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i) from
        ⟨d, hd', hdQ.symm ▸ hm.2⟩]
    · rw [if_neg hm]
      exact mean_nonneg _ hnonneg
  change _ ≤ mean (step (jump k) p avoid P) f
  rw [mean_step ⟨hp.1, by linarith [hp.2]⟩]
  have hmut := mean_uniform_lower _ _ hbranch
  have hcros : 0 ≤ mean (parents P true) (fun y ↦
      mean (independentBits n (1 / (n : ℝ))) fun m ↦
        mean (select (jump k) avoid true P y (mutate y m)) f) :=
    mean_nonneg _ fun _ ↦ mean_nonneg _ fun _ ↦ mean_nonneg _ hnonneg
  have ht : ((n - v : ℕ) : ℝ) / (64 * n) =
      (1 / 2) * (((n - v : ℕ) : ℝ) / (32 * n)) := by ring
  rw [ht]
  have h₁ := mul_nonneg hp.1 hcros
  have h₂ := mul_le_mul_of_nonneg_left hmut (show 0 ≤ 1 - p by linarith [hp.2])
  have h₃ := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - p by linarith [hp.2])
    (show 0 ≤ (((n - v : ℕ) : ℝ) / (32 * n)) by positivity)
  linarith

lemma arrival_absorbing (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (avoid : Bool)
    (P : Population n μ) (hP : ¬ arriving k P) {Q : Population n μ}
    (hQ : Q ∈ (step (jump k) p avoid P).support) : ¬ arriving k Q := by
  by_cases hmiss : missing P
  · intro h
    exact h.2 (step_preserves_plateau_or_optimum hk hkn p avoid (by
      by_contra hp
      exact hP ⟨hmiss, hp⟩) hQ h.1)
  · exact fun h ↦ step_preserves_optimum hk p avoid hmiss hQ h.1

lemma cost_drift (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1 / 2)
    (avoid : Bool) (P : Population n μ) :
    mean (step (jump k) p avoid P) (cost k) + (if arriving k P then 1 else 0) ≤ cost k P := by
  by_cases hP : arriving k P
  · obtain ⟨u, hu⟩ := Finite.exists_min fun u : Fin μ ↦ fitnessLevel k (P u)
    let v := fitnessLevel k (P u)
    have hlt : v < n := by
      have hv := fitnessLevel_le_of_nonopt (by omega : k ≤ n) (hP.1 u)
      by_contra! h
      have hall (i : Fin μ) : fitnessLevel k (P i) = n := by
        have hhi := hu i
        have hlo := fitnessLevel_le_of_nonopt (by omega : k ≤ n) (hP.1 i)
        change n ≤ fitnessLevel k (P u) at h
        omega
      exact hP.2 (fun i ↦ (fitnessLevel_eq_plateau (by omega : k ≤ n) (hP.1 i)).mp (hall i))
    have hprob := progress_step hk hkn p hp avoid P hP.1 u v hlt rfl hu
    have hstep (Q : Population n μ) (hQ : Q ∈ (step (jump k) p avoid P).support) :
        weight n v * (if ∃ i, fitnessLevel k (P i) ≤ v ∧ v < fitnessLevel k (Q i) then 1 else 0)
          ≤ rawCost k P - cost k Q := by
      have hmon (i : Fin μ) : fitnessLevel k (P i) ≤ fitnessLevel k (Q i) := by
        have hm := step_fitness_mono (jump k) p avoid P hQ i
        rw [← fitnessLevel_eq (by omega : k ≤ n), ← fitnessLevel_eq (by omega : k ≤ n)] at hm
        exact_mod_cast hm
      have hh := (rawCost_drop P Q hmon v hlt).trans
        (sub_le_sub_left (cost_le_raw k Q) (rawCost k P))
      split_ifs at hh ⊢ <;> simpa using hh
    have hm := mean_mono_on_support (step (jump k) p avoid P) hstep
    rw [mean_mul, mean_sub, mean_const] at hm
    have hmul := mul_le_mul_of_nonneg_left hprob (weight_nonneg n v)
    have heq : weight n v * (((n - v : ℕ) : ℝ) / (64 * n)) = 1 := by
      unfold weight
      have hnv : (0 : ℝ) < ((n - v : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - v by omega)
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      field_simp
    rw [heq] at hmul
    rw [if_pos hP, cost, if_pos hP]
    linarith
  · rw [if_neg hP, add_zero, cost, if_neg hP]
    rw [← mean_const (step (jump k) p avoid P) 0]
    apply mean_mono_on_support
    intro Q hQ
    simp [cost, arrival_absorbing (by omega : 0 < k) (by omega : k ≤ n) p avoid P hP hQ]

lemma rawCost_upper (P : Population n μ) : rawCost k P ≤
    (μ : ℕ) * (64 * n * (1 + Real.log n)) := by
  unfold rawCost
  have hs : ∑ v ∈ Finset.range n, weight n v = 64 * n * (harmonic n : ℝ) := by
    rw [← Finset.sum_range_reflect (weight n)]
    have hw (v : ℕ) (hv : v ∈ Finset.range n) :
        weight n (n - 1 - v) = 64 * n * (((v + 1 : ℕ) : ℝ)⁻¹) := by
      unfold weight
      rw [show n - (n - 1 - v) = v + 1 by have := Finset.mem_range.mp hv; omega]
      ring
    rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hc : ∑ v ∈ Finset.range n, weight n v ≤ 64 * n * (1 + Real.log n) := by
    rw [hs]
    exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity)
  calc
    _ ≤ ∑ _i : Fin μ, 64 * (n : ℝ) * (1 + Real.log n) := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans _ hc
      exact Finset.sum_le_sum (fun v _ ↦ by
        split_ifs
        · exact le_rfl
        · exact weight_nonneg _ _)
    _ = _ := by simp [nsmul_eq_mul]

lemma arrival_tail (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1 / 2)
    (avoid : Bool) (ν : PMF (Population n μ)) (s : ℕ) :
    (s : ℝ) * ((law (step (jump k) p avoid) ν s).toOuterMeasure
      {P | arriving k P}).toReal ≤ (μ : ℕ) * (64 * n * (1 + Real.log n)) := by
  let K := step (jump k) p avoid (μ := μ) (n := n)
  let A : Set (Population n μ) := {P | arriving k P}
  let h (t : ℕ) := ((law K ν t).toOuterMeasure A).toReal
  have habs (P : Population n μ) (hP : P ∉ A) : (K P).toOuterMeasure A = 0 :=
    event_zero_of_support _ _ (fun Q hQ ↦ arrival_absorbing (by omega) (by omega) p avoid P hP hQ)
  have hanti : Antitone h := by
    intro a b hab
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _))
      (event_law_antitone K ν A habs hab)
  have hstep (t : ℕ) : mean (law K ν (t + 1)) (cost k) + h t ≤ mean (law K ν t) (cost k) := by
    have hmono := mean_mono (law K ν t) (cost_drift hk hkn p hp avoid)
    rw [mean_add, ← mean_bind] at hmono
    change _ + mean _ (fun P ↦ if P ∈ A then 1 else 0) ≤ _ at hmono
    rw [mean_indicator] at hmono
    exact hmono
  have hsum (t : ℕ) : mean (law K ν t) (cost k) + ∑ u ∈ Finset.range t, h u ≤ mean ν (cost k) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep t]
  have hh : (s : ℝ) * h s ≤ ∑ u ∈ Finset.range s, h u := by
    have hh := Finset.sum_le_sum (s := Finset.range s) (fun u hu ↦
      hanti (Nat.le_of_lt (Finset.mem_range.mp hu)))
    simpa [nsmul_eq_mul] using hh
  have hbound := (mean_mono ν (fun P ↦ (cost_le_raw k P).trans (rawCost_upper P))).trans_eq
    (mean_const ν _)
  have hn' := mean_nonneg (law K ν s) (cost_nonneg k)
  change (s : ℝ) * h s ≤ _
  linarith [hsum s]

end
end Lax637351Proofs.ArrivalTime
