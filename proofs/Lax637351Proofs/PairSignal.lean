import Lax637351Proofs.CoordinateExtension

namespace Lax637351Proofs.PairSignal

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.FiniteWindows
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.PairAveraging Lax637351Proofs.PlateauKernel Lax637351Proofs.SubsetPairs
open Lax637351Proofs.MarkedStep Lax637351Proofs.CoordinateExtension
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def crossOffspring (P : Population n μ) : PMF (BitString n) :=
  (parents P true).bind fun z ↦ (independentBits n (1 / (n : ℝ))).map (mutate z)

def crossed (k : ℕ) (P : Population n μ) (f : BitString n → ℝ) : ℝ :=
  mean (crossOffspring P) (fun z ↦ indicator ((zeros z).card = k) * f z)

lemma indicator_and (X Y : Prop) : indicator (X ∧ Y) = indicator X * indicator Y := by
  by_cases hx : X <;> by_cases hy : Y <;> simp [indicator, hx, hy]

lemma avoids_singleton (i : Fin n) (x : BitString n) : avoids {i} x ↔ x i = 1 := by
  rw [avoids, Finset.disjoint_singleton_left, mem_zeros]
  exact ⟨bit_eq_one_of_ne_zero _, fun h ↦ by rw [h]; decide⟩

lemma avoidsRate_nonneg (U : Finset (Fin n)) (P : Population n μ) : 0 ≤ avoidsRate U P := by
  rw [avoidsRate, slotMean_eq]
  exact mean_nonneg _ (fun _ ↦ indic_nonneg _)

lemma avoided_after_cross (hn : 2 ≤ n) (hsize : 4 * k ≤ n) (P : Population n μ) (hP : plateau (k := k) P)
    (U : Finset (Fin n)) (hU : U.card ≤ k) (i : Fin n) (hi : i ∈ U) :
    extensionConstant k * avoidsRate (U.erase i) P * avoidsRate {i} P ≤
      crossed k P (fun z ↦ indicator (avoids U z)) := by
  let V := U.erase i
  let F (z : BitString n) := indicator ((zeros z).card = k ∧ avoids U z)
  have hpt (a b : Fin μ) :
      extensionConstant k * (indicator (avoids V (P a)) * indicator ((P b) i = 1)) ≤
        mean (PMF.uniformOfFintype (BitString n)) (fun s ↦
          mean (independentBits n (1 / (n : ℝ))) (fun m ↦ F (mutate (crossover (P a) (P b) s) m))) := by
    by_cases h : avoids V (P a) ∧ (P b) i = 1
    · simp only [indicator, if_pos h.1, if_pos h.2, mul_one]
      exact extension_mating hn hsize U hU i hi (P a) (P b) (hP a) (hP b) h.1 h.2
    · rw [← indicator_and, indicator, if_neg h, mul_zero]
      exact mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ indic_nonneg _))
  have hh := mean_mono (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ab ↦ hpt ab.1 ab.2)
  rw [mean_mul, mean_uniform_pair (fun a b : Fin μ ↦ indicator (avoids V (P a)) * indicator ((P b) i = 1))] at hh
  have he : (fun b : Fin μ ↦ indicator ((P b) i = 1)) = fun b ↦ indicator (avoids {i} (P b)) := by
    funext b
    rw [avoids_singleton]
  have hm : mean (PMF.uniformOfFintype (Fin μ)) (fun b ↦ indicator ((P b) i = 1)) = avoidsRate {i} P := by
    rw [he, avoidsRate, slotMean_eq]
  simp_rw [mean_mul, hm] at hh
  have hswap (a : Fin μ) : indicator (avoids V (P a)) * avoidsRate {i} P =
      avoidsRate {i} P * indicator (avoids V (P a)) := mul_comm _ _
  change extensionConstant k * mean (PMF.uniformOfFintype (Fin μ))
    (fun a ↦ indicator (avoids V (P a)) * avoidsRate {i} P) ≤ _ at hh
  have hm' : mean (PMF.uniformOfFintype (Fin μ)) (fun a ↦ indicator (avoids V (P a))) = avoidsRate V P := by
    rw [avoidsRate, slotMean_eq]
  simp_rw [hswap, mean_mul, hm'] at hh
  unfold crossed crossOffspring
  change _ ≤ mean ((parents P true).bind fun z ↦ (independentBits n (1 / (n : ℝ))).map (mutate z)) _
  simp only [mean_bind, mean_map, ← indicator_and, parents, if_true, Bind.bind, Pure.pure, mean_pure]
  have ht : extensionConstant k * avoidsRate V P * avoidsRate {i} P =
      extensionConstant k * (avoidsRate {i} P * avoidsRate V P) := by ring
  rw [ht]
  exact hh

lemma crossed_lower (hk : 0 < k) (hn : 2 ≤ n) (hsize : 4 * k ≤ n)
    (r : ℕ) (hr : r < k) (P : Population n μ) (hP : plateau (k := k) P)
    (δ : ℝ) (hδ : 0 ≤ δ) (hcol : ∀ i : Fin n, δ ≤ avoidsRate {i} P) :
    (extensionConstant k * δ / k) * subsetScore r P ≤
      crossed k P (partnerMean (choosePair (r + 1)) P) := by
  let C := crossOffspring P
  let c := extensionConstant k * δ
  have hC : 0 ≤ c := mul_nonneg (by unfold extensionConstant; positivity) hδ
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have next_bound (U : Finset (Fin n)) (hU : U.card = r + 1) :
      (c / k) * (∑ i ∈ U, avoidsRate (U.erase i) P) ≤
        crossed k P (fun z ↦ indicator (avoids U z)) := by
    let g := crossed k P (fun z ↦ indicator (avoids U z))
    have hg : 0 ≤ g := mean_nonneg _ (fun z ↦ mul_nonneg (indic_nonneg _) (indic_nonneg _))
    have hpt (i : Fin n) (hi : i ∈ U) : c * avoidsRate (U.erase i) P ≤ g := by
      have h := mul_le_mul_of_nonneg_left (hcol i)
        (show 0 ≤ extensionConstant k * avoidsRate (U.erase i) P from
          mul_nonneg (by unfold extensionConstant; positivity) (avoidsRate_nonneg _ _))
      have hh := avoided_after_cross hn hsize P hP U (by omega) i hi
      change _ ≤ g at hh
      exact (le_of_eq (by dsimp [c]; ring)).trans (h.trans hh)
    have h := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at h
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    have hr' : (U.card : ℝ) ≤ k := by exact_mod_cast (show U.card ≤ k by omega)
    have he : (c / (k : ℝ)) * ∑ i ∈ U, avoidsRate (U.erase i) P = (c * ∑ i ∈ U, avoidsRate (U.erase i) P) / k := by ring
    rw [he]
    apply (div_le_iff₀ hk').mpr
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_right hr' hg])
  have hrow (j : Fin μ) :
      (c / k) * partnerMean (choosePair r) P (P j) ≤
        crossed k P (fun z ↦ choosePair (r + 1) z (P j)) := by
    let S := zeros (P j)
    let g (U : Finset (Fin n)) := avoidsRate U P
    have hS : S.card = k := hP j
    have hx := extend_subsets S r (by omega) g (fun U ↦ avoidsRate_nonneg U P)
    have h := mul_le_mul_of_nonneg_left hx (div_nonneg hC hk'.le)
    have hsum : (c / k) * (∑ U ∈ S.powersetCard (r + 1), ∑ i ∈ U, g (U.erase i)) =
        ∑ U ∈ S.powersetCard (r + 1), (c / k) * (∑ i ∈ U, g (U.erase i)) := Finset.mul_sum ..
    rw [hsum] at h
    have hh := Finset.sum_le_sum (s := S.powersetCard (r + 1))
      (fun U hU ↦ next_bound U (Finset.mem_powersetCard.mp hU).2)
    rw [partnerMean_sum r P hP (P j) (hP j)]
    refine h.trans (hh.trans_eq ?_)
    unfold crossed
    rw [← mean_sum]
    apply le_antisymm <;> apply mean_mono <;> intro z <;> apply le_of_eq
    · by_cases hz : (zeros z).card = k
      · simp only [indicator, if_pos hz, one_mul, choosePair_symm (r + 1) z]
        exact (choosePair_sum _ _ _ ((hP j).trans hz.symm)).symm
      · simp [indicator, hz]
    · by_cases hz : (zeros z).card = k
      · simp only [indicator, if_pos hz, one_mul, choosePair_symm (r + 1) z]
        exact choosePair_sum _ _ _ ((hP j).trans hz.symm)
      · simp [indicator, hz]
  have ht := mean_mono (PMF.uniformOfFintype (Fin μ)) hrow
  rw [mean_mul, ← subsetScore_eq] at ht
  refine ht.trans_eq ?_
  unfold crossed
  rw [mean_swap]
  congr 1
  funext z
  rw [mean_mul, ← partnerMean_eq]

end
end Lax637351Proofs.PairSignal
