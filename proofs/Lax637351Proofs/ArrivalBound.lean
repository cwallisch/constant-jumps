import Lax637351Proofs.ArrivalCosts
import Lax637351Proofs.FiniteWindows

namespace Lax637351Proofs.ArrivalBound

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift
open Lax637351Proofs.FiniteWindows Lax637351Proofs.FiniteHitting Lax637351Proofs.Sampling
open Lax637351Proofs.ArrivalMutation Lax637351Proofs.ArrivalTime
open Lax637351Proofs.ArrivalCross Lax637351Proofs.ArrivalProgress Lax637351Proofs.ArrivalCosts
open Lax637351Proofs.PlateauPairs (plateau)
open Lax637351Proofs.RankPotential Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def rankWeight (n k : ℕ) (μ : ℕ+) (p : ℝ) (ar : Bool) (v : Fin n) (j : ℕ) : ℝ :=
  (progressRate n k μ p ar v j)⁻¹

lemma effective_valid (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool) :
    0 < effective ar p ∧ effective ar p ≤ 1 := by cases ar <;> simp [effective, hp.1, hp.2]

lemma rate_pos (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool) (v : Fin n) (j : ℕ) :
    0 < progressRate n k μ p ar v j := by
  unfold progressRate
  split_ifs with h
  · norm_num
  · have hq : (0 : ℝ) < ((n - ((v : ℕ) - k) : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - ((v : ℕ) - k) by omega)
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp' := (effective_valid p hp ar).1
    exact mul_pos (ordinaryChance_pos k) (add_pos_of_pos_of_nonneg (div_pos hq hn) (by positivity))

lemma minimum_arriving (hk : k ≤ n) (P : Population n μ) (hP : arriving k P) :
    ∃ u : Fin μ, (fitnessLevel k (P u) < n) ∧ (∀ j, fitnessLevel k (P u) ≤ fitnessLevel k (P j)) := by
  obtain ⟨u, hu⟩ := Finite.exists_min fun u : Fin μ ↦ fitnessLevel k (P u)
  refine ⟨u, ?_, hu⟩
  by_contra! h
  apply hP.2
  intro i
  have hh := fitnessLevel_le_of_nonopt hk (hP.1 i)
  exact (fitnessLevel_eq_plateau hk (hP.1 i)).mp (by have ht := hu i; omega)

lemma arrival_sum_bound (_hkn : k ≤ n) (hn : 0 < n) (p : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (ar : Bool) (hnp : 1 ≤ (n : ℝ) * effective ar p) :
    (∑ v : Fin n, ∑ j ∈ Finset.range (μ : ℕ), rankWeight n k μ p ar v j) ≤
      128 * (k : ℝ) * (μ : ℕ) + (ordinaryChance k)⁻¹ *
        ((n : ℝ) * (1 + Real.log n) + (μ : ℕ) * n * (5 + Real.log (1 / effective ar p))) := by
  let V : Finset (Fin n) := Finset.univ.filter (fun v ↦ (v : ℕ) < k)
  let f (v : Fin n) := ∑ j ∈ Finset.range (μ : ℕ), rankWeight n k μ p ar v j
  let r := effective ar p
  let g (u : ℕ) := ∑ j ∈ Finset.range (μ : ℕ),
    ((((u + 1 : ℕ) : ℝ) / n + r * (j : ℝ) / (μ : ℕ))⁻¹)
  let φ (v : Fin n) := n - ((v : ℕ) - k) - 1
  have hV : V.card ≤ k := by
    have he : V.image Fin.val ⊆ Finset.range k := fun u hu ↦ by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      have := (Finset.mem_filter.mp hv).2
      simpa only [Finset.mem_range] using this
    have hc := Finset.card_le_card he
    rwa [Finset.card_image_of_injective V Fin.val_injective, Finset.card_range] at hc
  have hsmall (v : Fin n) (hv : v ∈ V) : f v = 128 * ((μ : ℕ) : ℝ) := by
    have hv' : (v : ℕ) < k := (Finset.mem_filter.mp hv).2
    simp [f, rankWeight, progressRate, hv', nsmul_eq_mul, mul_comm]
  have hsmall' : ∑ v ∈ V, f v ≤ 128 * (k : ℝ) * (μ : ℕ) := by
    rw [Finset.sum_congr rfl hsmall]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have ht : (V.card : ℝ) ≤ k := by exact_mod_cast hV
    nlinarith only [mul_le_mul_of_nonneg_right ht (show 0 ≤ 128 * ((μ : ℕ) : ℝ) by positivity)]
  have hlarge (v : Fin n) (hv : v ∈ (Finset.univ \ V)) : f v = (ordinaryChance k)⁻¹ * g (φ v) := by
    have hv' : ¬(v : ℕ) < k := by simpa [V] using (Finset.mem_sdiff.mp hv).2
    have hu : φ v + 1 = n - ((v : ℕ) - k) := by
      have h := v.isLt
      dsimp [φ]
      omega
    dsimp only [f, g]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [rankWeight, progressRate, if_neg hv', hu, mul_inv, r]
  have hφ (v : Fin n) (hv : v ∈ (Finset.univ \ V)) : φ v ∈ Finset.range n := by
    rw [Finset.mem_range]
    dsimp [φ]
    omega
  have hinj : Set.InjOn φ (↑(Finset.univ \ V) : Set (Fin n)) := by
    intro a ha b hb ht
    have ha' : k ≤ (a : ℕ) := by simpa [V] using (Finset.mem_sdiff.mp ha).2
    have hb' : k ≤ (b : ℕ) := by simpa [V] using (Finset.mem_sdiff.mp hb).2
    apply Fin.ext
    have ha'' := a.isLt
    have hb'' := b.isLt
    dsimp [φ] at ht
    omega
  have hsum : (∑ v ∈ (Finset.univ \ V), g (φ v)) ≤ ∑ u ∈ Finset.range n, g u := by
    rw [← Finset.sum_image hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact hφ v hv
    · intro u _ _
      unfold g
      apply Finset.sum_nonneg
      intro j _
      apply inv_nonneg.mpr
      have hr := (effective_valid p hp ar).1
      positivity
  have hlarge' := mul_le_mul_of_nonneg_left
    (hsum.trans (grid_bound n μ hn μ.pos r (effective_valid p hp ar) hnp))
    (inv_nonneg.mpr (ordinaryChance_pos k).le)
  rw [Finset.mul_sum, ← Finset.sum_congr rfl hlarge] at hlarge'
  have hpartition := Finset.sum_sdiff (Finset.subset_univ V) (f := f)
  change (∑ v, f v) ≤ _
  rw [← hpartition]
  linarith only [hsmall', hlarge']

lemma arrival_tail_sharp (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (p : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (ar : Bool) (hnp : 1 ≤ (n : ℝ) * effective ar p)
    (ν : PMF (Population n μ)) (t : ℕ) :
    (t : ℝ) * ((law (step (jump k) p ar) ν t).toOuterMeasure {P | arriving k P}).toReal ≤
      128 * (k : ℝ) * (μ : ℕ) + (ordinaryChance k)⁻¹ *
        ((n : ℝ) * (1 + Real.log n) + (μ : ℕ) * n * (5 + Real.log (1 / effective ar p))) := by
  let K := step (jump k) p ar (n := n) (μ := μ)
  let A : Set (Population n μ) := {P | arriving k P}
  let w := rankWeight n k μ p ar
  let counts (v : Fin n) := fitterCount (n := n) (μ := μ) k v
  let V := value (μ : ℕ) w counts
  have hw (v j) : 0 ≤ w v j := inv_nonneg.mpr (rate_pos (k := k) (μ := μ) p hp ar v j).le
  have hV (P : Population n μ) : 0 ≤ V P :=
    Finset.sum_nonneg (fun v _ ↦ tail_nonneg _ _ (hw v) _)
  have hdrift (P : Population n μ) (hP : P ∈ A) : mean (K P) V ≤ V P - 1 := by
    obtain ⟨i, hi, hmin⟩ := minimum_arriving (by omega : k ≤ n) P hP
    let v : Fin n := ⟨fitnessLevel k (P i), hi⟩
    have hprob := improves_count hk hkn p ⟨hp.1.le, hp.2⟩ ar P hP.1 i v rfl hi hmin
    have hCount : counts v P < (μ : ℕ) := by
      unfold counts fitterCount
      have hs : i ∉ Finset.univ.filter (fun j ↦ (v : ℕ) < fitnessLevel k (P j)) := by simp [v]
      have hh := Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
        ⟨i, Finset.mem_univ _, hs⟩)
      simpa only [Finset.card_univ, Fintype.card_fin] using hh
    have hmon (Q : Population n μ) (hQ : Q ∈ (K P).support) (i : Fin n) : counts i P ≤ counts i Q := by
      apply fitter_mono
      intro j
      have h := step_fitness_mono (jump k) p ar P hQ j
      rw [← fitnessLevel_eq (by omega : k ≤ n), ← fitnessLevel_eq (by omega : k ≤ n)] at h
      exact_mod_cast h
    have hh := mean_mono_on_support (K P)
      (fun Q hQ ↦ drop (μ : ℕ) w counts hw P Q (hmon Q hQ) v hCount)
    rw [mean_mul, mean_sub, mean_const] at hh
    have he : (fun Q ↦ indicator (fitterCount k v P < fitterCount k v Q)) =
        (fun Q ↦ if counts v P < counts v Q then (1 : ℝ) else 0) := by
      funext Q
      by_cases h : fitterCount k v P < fitterCount k v Q <;> simp [counts, indicator, h]
    rw [he] at hprob
    have hb := mul_le_mul_of_nonneg_left hprob (hw v (counts v P))
    change (progressRate n k μ p ar v (counts v P))⁻¹ *
        progressRate n k μ p ar v (counts v P) ≤ _ at hb
    rw [inv_mul_cancel₀ (rate_pos (k := k) (μ := μ) p hp ar v (counts v P)).ne'] at hb
    change (1 : ℝ) ≤ w v (counts v P) * mean (K P)
      (fun Q ↦ if counts v P < counts v Q then 1 else 0) at hb
    change _ ≤ V P - mean (K P) V at hh
    linarith only [hh, hb]
  have hmono : Antitone (fun s ↦ ((law (stopped K A) ν s).toOuterMeasure A).toReal) := by
    intro s u hsu
    apply ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _))
    apply event_law_antitone _ _ _ _ hsu
    intro P hP
    rw [stopped, if_neg hP, PMF.toOuterMeasure_pure_apply]
    simp [hP]
  have hsum := stopped_telescoping K A V 1 hdrift ν t
  rw [one_mul] at hsum
  have hs : (t : ℝ) * ((law (stopped K A) ν t).toOuterMeasure A).toReal ≤
      ∑ s ∈ Finset.range t, ((law (stopped K A) ν s).toOuterMeasure A).toReal := by
    have h := Finset.sum_le_sum (s := Finset.range t)
      (fun s hs ↦ hmono (Nat.le_of_lt (Finset.mem_range.mp hs)))
    simpa [nsmul_eq_mul] using h
  have hV' : mean ν V ≤ ∑ v : Fin n, ∑ j ∈ Finset.range (μ : ℕ), w v j := by
    apply le_trans _ (mean_const ν _).le
    apply mean_mono
    intro P
    apply Finset.sum_le_sum
    intro v _
    have h := tail_antitone (μ : ℕ) (w v) (hw v) (Nat.zero_le (counts v P))
    simpa only [tail, Nat.zero_le, if_true] using h
  have he (s : ℕ) : (law (stopped K A) ν s).toOuterMeasure A =
      (law K ν s).toOuterMeasure A := by
    induction s with
    | zero => rfl
    | succ s ih =>
      -- When neither chain can enter the active set from outside, the
      -- restrictions of their laws to active states agree at all times.
      clear ih
      have hr (u : ℕ) (P : Population n μ) (hP : P ∈ A) : law (stopped K A) ν u P = law K ν u P := by
        induction u generalizing P with
        | zero => rfl
        | succ u iu =>
          simp only [law_succ, PMF.bind_apply]
          apply tsum_congr
          intro Q
          by_cases hQ : Q ∈ A
          · rw [stopped, if_pos hQ, iu Q hQ]
          · have hK : K Q P = 0 := by
              by_contra h
              exact arrival_absorbing (by omega) (by omega) p ar Q hQ ((PMF.mem_support_iff _ _).mpr h) hP
            rw [stopped, if_neg hQ, hK, mul_zero, PMF.pure_apply, if_neg (show P ≠ Q from fun h ↦ hQ (h ▸ hP)), mul_zero]
      simp only [PMF.toOuterMeasure_apply]
      apply tsum_congr
      intro P
      by_cases hP : P ∈ A
      · rw [Set.indicator_of_mem hP, Set.indicator_of_mem hP, hr _ P hP]
      · rw [Set.indicator_of_notMem hP, Set.indicator_of_notMem hP]
  have hh := arrival_sum_bound (μ := μ) (by omega : k ≤ n) (by omega) p hp ar hnp
  rw [he] at hs
  linarith only [hs, hsum, hV', hh, mean_nonneg (law (stopped K A) ν t) hV]

end
end Lax637351Proofs.ArrivalBound
