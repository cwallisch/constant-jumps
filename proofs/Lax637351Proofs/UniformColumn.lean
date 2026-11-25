import Lax637351Proofs.EntryScales
import Lax637351Proofs.CleanCopyEntry
import Lax637351Proofs.RuntimeBridge

namespace Lax637351Proofs.UniformColumn

open Lax637351.Algorithm Lax637351.Runtime Lax637351Proofs.Transitions
open Lax637351Proofs.EntryScales Lax637351Proofs.BandColumn Lax637351Proofs.FillBand
open Lax637351Proofs.CutoffEntry Lax637351Proofs.CleanCopyEntry Lax637351Proofs.SlopeCharge
open Lax637351Proofs.Ordinary Lax637351Proofs.BestRank
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open Lax637351Proofs.PairStep Lax637351Proofs.SlopeReset Lax637351Proofs.RuntimeTransfer Lax637351Proofs.RuntimeBridge
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma entry_probability (hk : 2 ≤ k) (S : Conditions k n μ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (1 / 16 : ℝ) ≤
      mean (PMF.uniformOfFintype (Population n μ)) (visit (step (jump k) p false)
        {Q | fixedColumn k (cutoff n) Q} (cutoffLength n μ + (fillLength μ + length n))) := by
  let B := cutoff n
  let L := length n
  let d := landingWidth n
  let a := bandLow n μ
  let lc := landingTilt n
  let lt := tapeTilt n
  let w := tapeWidth n
  let T := cutoffLength n μ
  let H := fillLength μ
  let K := step (jump k) p false (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | fixedColumn k B Q}
  let E : Set (Population n μ) := {Q | landing B d Q}
  let V : Set (Population n μ) := {Q | fillBand a B Q}
  let ν := PMF.uniformOfFintype (Population n μ)
  have hn := S.dimension
  have hcut := S.cutoff_le
  have hBk := S.cutoff_ge
  change 4 * (B + 1) ≤ n at hcut
  change 4 * k ≤ B at hBk
  have hkn : k ≤ B ∧ 2 * B ≤ n := by omega
  have hTilt := tilt_bounds n (by omega)
  have hd : 0 ≤ d := by dsimp [d, landingWidth]; positivity
  have ha : (k : ℝ) ≤ a := by
    have h := S.band
    have he : (4 : ℝ) * k ≤ B := by exact_mod_cast hBk
    have hl : (0 : ℝ) ≤ L := by dsimp [L]; positivity
    have hw : 0 ≤ w := by dsimp [w, tapeWidth]; positivity
    have hk' : (0 : ℝ) ≤ k := by positivity
    change (B : ℝ) / 2 < a - L - w at h
    linarith only [h, he, hl, hw, hk']
  have hland (P : Population n μ) (hP : ordinary (B + 1) P) : (1 / 2 : ℝ) ≤ visit K E T P := by
    have hP' : B < bestZeros P := (ordinary_iff_bestZeros P).mp hP
    have hh := landing_window (k := k) (by omega) hn hkn p hp d lc hd hTilt.1.1 hTilt.1.2 P hP'
    have ht := S.land_error
    change _ ≤ visit K E T P at hh
    linarith only [hh, ht]
  have hlower (P : Population n μ) (hP : P ∈ E) : (1 / 4 : ℝ) ≤ visit K G (H + L) P := by
    obtain ⟨hb, i, hi, hu⟩ := hP
    let A := P i
    have hmin : bestZeros P = (zeros A).card := by
      exact best_eq A P ⟨⟨i, rfl⟩, fun j ↦ by
        by_cases hj : j = i
        · exact Or.inl (by rw [hj])
        · exact Or.inr (hi.trans_lt (hu j hj))⟩
    have hcut' : bestZeros P ≤ B := (bestZeros_le P i).trans hi
    by_cases hsmall : p ≤ splitRate n
    · have hlow : (k : ℝ) ≤ (bestZeros P : ℝ) := by
        have hh : 0 ≤ (H : ℝ) * d := mul_nonneg (by positivity) hd
        change (k : ℝ) ≤ (B : ℝ) - ((H : ℝ) + 1) * d at ha
        linarith only [ha, hb, hh]
      have hA : k ≤ (zeros A).card ∧ (zeros A).card ≤ B := ⟨hmin ▸ (by exact_mod_cast hlow), hi⟩
      have ht : uniqueBest A P := ⟨⟨i, rfl⟩, fun j ↦ by
        by_cases h : j = i
        · exact Or.inl (by rw [h])
        · exact Or.inr (hi.trans_lt (hu j h))⟩
      have hclean := clean_copy_window (by omega : 0 < k) (by omega : k ≤ n) hn p hp P A hA ht
      have hq : (H : ℝ) * (p + ((B : ℝ) + 1) / n) ≤ 1 / 4 :=
        (mul_le_mul_of_nonneg_left (add_le_add_left hsmall _) (by positivity : 0 ≤ (H : ℝ))).trans S.clean_error
      have hh : (1 / 4 : ℝ) ≤ visit K G H P := by
        change _ ≤ visit K G H P at hclean
        linarith only [hclean, hq]
      exact hh.trans (visit_monotone K G P (Nat.le_add_right H L))
    · have hfill : (1 / 2 : ℝ) ≤ visit K V H P := by
        have hh := fill_window (k := k) (by omega) hn hkn p hp d lc hd hTilt.1.1 hTilt.1.2 ha P ⟨hb, hcut'⟩
        change _ ≤ visit K V H P at hh
        linarith only [hh, S.fill_error]
      have hprog : columnProgress B μ (splitRate n) * L ≤ columnProgress B μ p * L := by
        unfold columnProgress
        gcongr
        exact le_of_not_ge hsmall
      have hpcol (Q : Population n μ) (hQ : Q ∈ V) : (3 / 4 : ℝ) ≤ visit K G L Q := by
        exact column_window (by omega : 0 < k) hn hBk (by omega) S.far p hp Q a w lt L hTilt.2.1 hTilt.2.2
          (by dsimp [w, tapeWidth]; positivity) hQ S.band S.tape_error
          (S.work.trans (div_le_div_of_nonneg_right hprog (by norm_num))) (S.progress.trans_le hprog)
      have hh := visit_lower_through K V G L (3 / 4) (by norm_num) (by norm_num) hpcol H P
      linarith only [hfill, hh]
  have hpoint (P : Population n μ) :
      (1 / 8 : ℝ) * indicator (ordinary (B + 1) P) ≤ visit K G (T + (H + L)) P := by
    by_cases h : ordinary (B + 1) P
    · have htrans := visit_lower_through K E G (H + L) (1 / 4) (by norm_num) (by norm_num) hlower T P
      rw [indicator, if_pos h, mul_one]
      linarith only [htrans, hland P h]
    · simpa only [indicator, if_neg h, mul_zero] using visit_nonneg K G (T + (H + L)) P
  have hh := mean_mono ν hpoint
  rw [mean_mul] at hh
  linarith only [hh, S.initial]

lemma from_uniform_column (hk : 2 ≤ k) (hμ : 2 ≤ μ) (S : Conditions k n μ)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (M : ℝ) (hM : copyBudget n (cutoff n) μ p ≤ M)
    (hsmall : 2 * Real.exp 1 * (cutoff n : ℝ) ^ 2 * M / n ≤ 1)
    (hslack : 2 * (cutoff n : ℝ) * M / n ≤ 1 / 4) :
    ENNReal.ofReal (1 / (128 * slopeCharge n M k)) ≤ expectedOptimizationTime n k μ p false := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | fixedColumn k (cutoff n) Q}
  let ν := PMF.uniformOfFintype (Population n μ)
  let T := cutoffLength n μ + (fillLength μ + length n)
  let a := slopeCharge n M k
  have hBn := S.cutoff_le
  have hBk := S.cutoff_ge
  have hn := S.dimension
  have hh := entry_probability hk S p hp
  change (_ : ℝ) ≤ mean ν (visit K G T) at hh
  rw [mean_visit_eq] at hh
  have hmass : ENNReal.ofReal (1 / 16) ≤ (law (stopped K Gᶜ) ν T).toOuterMeasure G := by
    have hn := ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one (law (stopped K Gᶜ) ν T) G)
    rw [← ENNReal.ofReal_toReal hn]
    exact ENNReal.ofReal_le_ofReal hh
  have hw := tailSum_ge_from_hit K {Q | missing Q} G ν (ENNReal.ofReal (1 / (8 * a)))
    (fun Q hQ ↦ fixed_column_lower (by omega : 0 < k) (by omega : k ≤ n) hn hμ (cutoff n) p hp M hM hsmall hslack Q hQ) T
  rw [expectedOptimizationTime_eq]
  have hm := mul_le_mul' hmass (le_refl (ENNReal.ofReal (1 / (8 * a))))
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16),
    show (1 / 16 : ℝ) * (1 / (8 * a)) = 1 / (128 * a) by ring] at hm
  exact hm.trans hw

end
end Lax637351Proofs.UniformColumn
