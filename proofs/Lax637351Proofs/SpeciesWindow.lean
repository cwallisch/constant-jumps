import Lax637351Proofs.SpeciesCap

namespace Lax637351Proofs.SpeciesWindow

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.SparseBarrier Lax637351Proofs.PairStep
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauPairs
open Lax637351Proofs.SpeciesDrift Lax637351Proofs.SpeciesCap Lax637351Proofs.PlateauChanges
open Lax637351Proofs.OffspringEstimates
open OffspringEstimates.Genotypes OffspringEstimates.PopulationRatio OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def strong (k : ℕ) (P : Population n μ) : Prop :=
  ∀ B : Genotype n k, 4 * level k * (μ : ℕ) ≤ clippedScore B P

def safe (k : ℕ) (P : Population n μ) : Prop :=
  ∀ B : Genotype n k, level k * (μ : ℕ) ≤ clippedScore B P

def strictAmount (k : ℕ) : ℝ :=
  Real.exp (-1) * floorWeight k * level k ^ 2 / 5000

def changeBound (n k : ℕ) (p : ℝ) (ar : Bool) : ℝ := if ar then p + (k : ℝ) / n else 1

lemma strictAmount_pos (k : ℕ) : 0 < strictAmount k := by
  have h := level_pos k
  unfold strictAmount floorWeight
  positivity

lemma strictAmount_le_one (k : ℕ) : strictAmount k ≤ 1 := by
  have h := (Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  rw [Real.exp_zero] at h
  have hw : floorWeight k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hh : level k ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (level_pos k).le (by norm_num : (0 : ℝ) ≤ 1)).mpr (by linarith [level_small k])
  unfold strictAmount
  have hprod := mul_le_one₀ h (by unfold floorWeight; positivity) hw
  have hprod' := mul_le_one₀ hprod (sq_nonneg (level k)) (by simpa using hh)
  linarith

lemma cap_of_safe (P : Population n μ) (hP : plateau (k := k) P) (hs : safe k P) (B : Genotype n k) :
    fraction B P ≤ 1 - 2 / 5 * level k := by
  have h := (hs B).trans (clipped_range B P hP).2
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  unfold fraction
  apply (div_le_iff₀ hm).mpr
  nlinarith only [h]

lemma strict_birth (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k)
    (hq : ratio (weightFunction B) (toString B) P ≤ 1 / 25)
    (hf : (1 / 2 : ℝ) ≤ fraction B P)
    (hl : level k * (μ : ℕ) ≤ clippedScore B P)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    2 * p * strictAmount k ≤ mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedWeight B) -
      ratio (weightFunction B) (toString B) P *
        mean (OffspringEstimates.Sampling.offspring p P) (ActualBirthKernels.acceptedClone B) := by
  let G := genotypeList P hP
  let ν := EmpiricalKernels.empirical G
  let q := ratio (weightFunction B) (toString B) P
  let v := (ν B).toReal
  have hrat : q = Species.cloud B (fun x ↦ (ν x).toReal) / v := by
    have h := ratio_empirical G B
    rwa [show realizePopulation G = P from realize_list P hP] at h
  have hv : fraction B P = v := fraction_eq B P hP
  have hv0 : 0 < v := by linarith only [hf, hv]
  have hq0 : 0 ≤ q := ratio_nonneg _ _ (fun x ↦ (weightFunction_bounds B x).1) P
  have hf' : 1 / 2 ≤ v := hv ▸ hf
  have hV : 2 / 5 * level k ≤ 1 - v := by
    have h := hl.trans (clipped_range B P hP).2
    have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
    have hf : count (toString B) P = (μ : ℕ) * v := by
      have ht := (div_eq_iff hm.ne').mp hv
      linarith only [ht]
    rw [hf] at h
    apply (mul_le_mul_iff_of_pos_right hm).mp
    nlinarith only [h]
  have hQ := SpeciesEnvelope.ideal_quadratic_drift B ν (1 / 2) (by norm_num) (by norm_num)
    hv0 hf' (by rwa [← hrat])
  rw [← hrat] at hQ
  have hcross := ActualBirthKernels.crossed_ratio_lower hc.dimension_two hc.dimension_four_jump B ν q hq0
  have hpow := (sq_le_sq₀ (by have := level_pos k; positivity) (by linarith [hV, level_pos k])).mpr hV
  have hcoef : 0 ≤ Real.exp (-1) * floorWeight k / 200 := by unfold floorWeight; positivity
  have hgain := mul_le_mul_of_nonneg_left hpow hcoef
  have hmain := mul_le_mul_of_nonneg_left hQ (Real.exp_pos (-1)).le
  have herr : 0 ≤ PlateauKernelApproximation.approximationError n k := by
    unfold PlateauKernelApproximation.approximationError
    positivity
  have he := mul_le_mul_of_nonneg_right (show (5 / 4 : ℝ) + q ≤ 129 / 100 by linarith only [hq]) herr
  have hA : 2 * strictAmount k ≤ EmpiricalKernels.pairMean ν (ActualBirthKernels.weightedBirth B) -
      q * EmpiricalKernels.pairMean ν (ActualBirthKernels.cloneBirth B) := by
    unfold strictAmount at *
    change (1 / 2 * floorWeight k / 100) * (1 - v) ^ 2 ≤ _ at hQ
    change Real.exp (-1) * ((1 / 2 * floorWeight k / 100) * (1 - v) ^ 2) ≤ _ at hmain
    change Real.exp (-1) * _ - _ ≤ _ at hcross
    nlinarith only [hgain, hmain, hcross, he, herror, show 0 ≤ Real.exp (-1) * floorWeight k * level k ^ 2 by unfold floorWeight; positivity]
  have hm := EntryBounds.mixture_entry_lower hc B ν hf' (by rwa [← hrat]) 0 (by norm_num)
  dsimp only at hm
  rw [← hrat] at hm
  norm_num only [zero_mul, zero_add, sub_zero, one_mul] at hm
  have hB : 0 ≤ mean ν (fun x ↦ ActualBirthKernels.weightedBirth B x x) -
      q * mean ν (fun x ↦ ActualBirthKernels.cloneBirth B x x) := by
    exact (by positivity : 0 ≤ (1 / 2 : ℝ) * (k : ℝ) / (64 * n)).trans hm
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  rw [birth_contrast hkn p hp P hP B]
  change _ ≤ p * _ + (1 - p) * _
  have h₁ := mul_le_mul_of_nonneg_left hA hp.1
  have h₂ := mul_nonneg (sub_nonneg.mpr hp.2) hB
  nlinarith only [h₁, h₂]

lemma clipped_entry (hc : EntryBounds.Conditions n k (1 / 2)) (hμ : (5 : ℕ) ≤ μ) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool) (P : Population n μ) (hP : plateau (k := k) P)
    (B : Genotype n k) (hupper : clippedScore B P ≤ 4 * level k * (μ : ℕ)) :
    (k : ℝ) / (256 * n) ≤ mean (auxiliary k p ar P) (fun Q ↦ clippedScore B Q - clippedScore B P) := by
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  have hk : 0 < k := hc.jump_pos
  have h := near_anchor hk hkn hμ p ar P hP B hupper
  have hE := entry_drift hc p hp ar P hP B h.1.1 h.1.2.1 h.1.2.2
  have hμR : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have he := clipped_eq B P (by linarith only [(le_div_iff₀ hμR).mp h.1.2.1])
  rw [he]
  have hE' := mean_mono_on_support (auxiliary k p ar P) (fun Q hQ ↦
    show score B Q - score B P ≤ clippedScore B Q - score B P by rw [h.2 Q hQ])
  apply le_trans _ (hE.trans hE')
  exact le_of_eq (by ring)

lemma clipped_strict (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P)
    (B : Genotype n k) (hlower : level k * (μ : ℕ) ≤ clippedScore B P)
    (hupper : clippedScore B P ≤ 4 * level k * (μ : ℕ)) :
    p * strictAmount k ≤ mean (auxiliary k p ar P) (fun Q ↦ clippedScore B Q - clippedScore B P) := by
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  have hk : 0 < k := hc.jump_pos
  have h := near_anchor hk hkn hμ p ar P hP B hupper
  have hbirth := strict_birth hc herror P hP B h.1.2.2 h.1.2.1 hlower p hp
  have hE := ratio_drift hk hkn p hp ar P hP B h.1.1 _
    (mul_nonneg (mul_nonneg (by norm_num) hp.1) (strictAmount_pos k).le) hbirth
  have hμR : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have he := clipped_eq B P (by linarith only [(le_div_iff₀ hμR).mp h.1.2.1])
  rw [he]
  have hE' := mean_mono_on_support (auxiliary k p ar P) (fun Q hQ ↦
    show score B Q - score B P ≤ clippedScore B Q - score B P by rw [h.2 Q hQ])
  apply le_trans _ (hE.trans hE')
  exact le_of_eq (by ring)

end
end Lax637351Proofs.SpeciesWindow
