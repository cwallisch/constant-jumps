import Lax637351Proofs.OffspringBridge

namespace Lax637351Proofs.SpeciesDrift

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauChanges Lax637351Proofs.OffspringBridge
open Lax637351Proofs.OffspringEstimates
open OffspringEstimates.Genotypes OffspringEstimates.PopulationRatio OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def score (B : Genotype n k) (P : Population n μ) : ℝ :=
  (μ : ℕ) * ratio (weightFunction B) (toString B) P

def fraction (B : Genotype n k) (P : Population n μ) : ℝ :=
  count (toString B) P / ((μ : ℕ) : ℝ)

def genotypeList (P : Population n μ) (hP : plateau (k := k) P) : Fin μ → Genotype n k :=
  fun i ↦ ofString (P i) (hP i)

lemma realize_list (P : Population n μ) (hP : plateau (k := k) P) :
    realizePopulation (genotypeList P hP) = P := funext (fun _i ↦ toString_ofString _ _)

lemma fraction_eq (B : Genotype n k) (P : Population n μ) (hP : plateau (k := k) P) :
    fraction B P = (EmpiricalKernels.empirical (genotypeList P hP) B).toReal := by
  unfold fraction
  have h := count_empirical (genotypeList P hP) B
  rw [realize_list P hP] at h
  rw [h]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast μ.ne_zero)

lemma centered_of_pos (B : Genotype n k) (P : Population n μ) (hN : 0 < count (toString B) P) :
    slotMean (fun z ↦ weightFunction B z -
      ratio (weightFunction B) (toString B) P * PopulationRatio.indicator (toString B) z) P = 0 := by
  unfold slotMean
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (Deletion.total (weightFunction B) P - (Deletion.total (weightFunction B) P / count (toString B) P) * count (toString B) P) / ((μ : ℕ) : ℝ) = 0
  rw [div_mul_cancel₀ _ hN.ne', sub_self, zero_div]

lemma step_relation (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P)
    (Q : Population n μ) (hQ : Q ∈ (auxiliary k p ar P).support) :
    ∃ z d, Q = Lax637351Proofs.Transitions.replace P z d := by
  obtain ⟨a, _, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp hQ
  rw [rejectSelect_plateau hk hkn ar P hP] at ha
  split_ifs at ha
  · obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    exact ⟨MarkedStep.child a, d, rfl⟩
  · rw [(PMF.mem_support_pure_iff _ _).mp ha]
    exact ⟨MarkedStep.child a, Fin.last _, by simp [Lax637351Proofs.Transitions.replace]⟩

lemma replace_eq_old (P : Population n μ) (z : BitString n) (d : Fin ((μ : ℕ) + 1)) :
    Lax637351Proofs.Transitions.replace P z d = OffspringEstimates.Deletion.replace P z d := by
  rw [Lax637351Proofs.Transitions.replace_eq]
  rfl

lemma ratio_drift (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k)
    (hN : 1 < count (toString B) P) (a : ℝ) (ha : 0 ≤ a)
    (hbirth : a ≤ mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedWeight B) -
      ratio (weightFunction B) (toString B) P *
        mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedClone B)) :
    (1 / 2 : ℝ) * a ≤ mean (auxiliary k p ar P) (fun Q ↦ score B Q - score B P) := by
  let X := count (toString B) P
  let q := ratio (weightFunction B) (toString B) P
  let f (z : BitString n) := weightFunction B z - q * PopulationRatio.indicator (toString B) z
  let K := auxiliary k p ar P
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hX : 0 < X := by change 1 < X at hN; linarith
  have hf : slotMean f P = 0 := centered_of_pos B P hX
  have hA := slot_drift hk hkn p ar P hP f
  rw [show submitRate k p ar P * slotMean f P = 0 by rw [hf, mul_zero], sub_zero, submit_centered p hp ar P hP f hf,
    show f = _ from rfl, accepted_contrast hkn] at hA
  have hm := div_le_div_of_nonneg_right hbirth (show 0 ≤ ((μ : ℕ) + 1 : ℝ) by positivity)
  rw [← hA] at hm
  have hden : (1 / 2 : ℝ) ≤ ((μ : ℕ) : ℝ) ^ 2 / (X * ((μ : ℕ) + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h₁ := mul_le_mul_of_nonneg_right (count_le_size (toString B) P) (show 0 ≤ ((μ : ℕ) + 1 : ℝ) by positivity)
    change X * _ ≤ _ at h₁
    have h₂ : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
    nlinarith only [h₁, mul_le_mul_of_nonneg_left h₂ hμ.le]
  have hstep (Q : Population n μ) (hQ : Q ∈ K.support) :
      (((μ : ℕ) : ℝ) ^ 2 / X) * (slotMean f Q - slotMean f P) ≤ score B Q - score B P := by
    obtain ⟨z, d, he⟩ := step_relation hk hkn p ar P hP Q hQ
    have hh := replace_ratio_lower (weightFunction B) (toString B) (weightFunction_anchor B)
      (weightFunction_bounds B) P z hN d
    rw [← replace_eq_old, ← he] at hh
    have hf' (Y : Population n μ) : slotMean f Y =
        (Deletion.total (weightFunction B) Y - q * count (toString B) Y) / ((μ : ℕ) : ℝ) := by
      simp [slotMean, f, Deletion.total, count, Finset.sum_sub_distrib, Finset.mul_sum]
    have hs := mul_le_mul_of_nonneg_left hh hμ.le
    unfold score
    rw [← mul_sub]
    apply le_trans _ hs
    apply le_of_eq
    rw [hf' Q, hf' P]
    dsimp only [q]
    field_simp
    ring
  have hh := mean_mono_on_support K hstep
  rw [mean_mul] at hh
  have hs := mul_le_mul_of_nonneg_left hm (div_nonneg (sq_nonneg ((μ : ℕ) : ℝ)) hX.le)
  have he := mul_le_mul_of_nonneg_right hden ha
  apply le_trans he
  apply le_trans _ (hs.trans hh)
  apply le_of_eq
  field_simp

lemma birth_contrast (_hkn : k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k) :
    let ν := EmpiricalKernels.empirical (genotypeList P hP)
    let q := ratio (weightFunction B) (toString B) P
    mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedWeight B) -
      q * mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedClone B) =
      p * (EmpiricalKernels.pairMean ν (ActualBirthKernels.weightedBirth B) -
        q * EmpiricalKernels.pairMean ν (ActualBirthKernels.cloneBirth B)) +
      (1 - p) * (mean ν (fun x ↦ ActualBirthKernels.weightedBirth B x x) -
        q * mean ν (fun x ↦ ActualBirthKernels.cloneBirth B x x)) := by
  have h := offspring_contrast (genotypeList P hP) B p hp
  dsimp only at h ⊢
  rw [realize_list P hP, accepted_indicator] at h
  exact h

lemma entry_drift {p0 : ℝ} (hc : EntryBounds.Conditions n k p0)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool) (P : Population n μ)
    (hP : plateau (k := k) P) (B : Genotype n k) (hN : 1 < count (toString B) P)
    (hf : p0 ≤ fraction B P) (hq : ratio (weightFunction B) (toString B) P ≤ 1 / 25) :
    p0 * (k : ℝ) / (128 * n) ≤ mean (auxiliary k p ar P) (fun Q ↦ score B Q - score B P) := by
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  let G := genotypeList P hP
  let ν := EmpiricalKernels.empirical G
  have hν : p0 ≤ (ν B).toReal := (fraction_eq B P hP) ▸ hf
  have hrat : ratio (weightFunction B) (toString B) P =
      Species.cloud B (fun x ↦ (ν x).toReal) / (ν B).toReal := by
    have h := ratio_empirical G B
    rw [show realizePopulation G = P from realize_list P hP] at h
    exact h
  have hbirth := EntryBounds.mixture_entry_lower hc B ν hν (by rwa [← hrat]) p hp
  dsimp only at hbirth
  rw [← hrat] at hbirth
  have hbirth' : p0 * (k : ℝ) / (64 * n) ≤ mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedWeight B) -
      ratio (weightFunction B) (toString B) P * mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedClone B) := by
    rw [birth_contrast hkn p hp P hP B]
    exact hbirth
  have hd := ratio_drift (by have := hc.jump_pos; omega : 0 < k) hkn p hp ar P hP B hN _
    (by have := hc.threshold_pos; positivity) hbirth'
  convert hd using 1; ring

end
end Lax637351Proofs.SpeciesDrift
