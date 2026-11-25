import Lax637351Proofs.ColumnParameters
import Lax637351Proofs.ColumnMixture

namespace Lax637351Proofs.ColumnApplied

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ColumnMixture Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnSlot
open Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ResidentCap
open Lax637351Proofs.ResidentScore Lax637351Proofs.SpeciesCap Lax637351Proofs.SpeciesWindow
open Lax637351Proofs.PlateauChanges Lax637351Proofs.Auxiliary
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma horizon_perturbation (a : Settings k) (h : PopulationSize k a μ) :
    (eps μ / (1 - eps μ) - eps μ) * a.horizon μ * (1 + eps μ / (1 - eps μ)) ^ a.horizon μ ≤ 1 := by
  let e := eps μ
  let H := a.horizon μ
  let t : ℝ := (a.T : ℕ)
  have he := eps_bounds μ
  have ht : 0 < t := by unfold t; exact_mod_cast a.T.pos
  have he' : 0 < 1 - e := by unfold e; linarith only [he.2]
  have hq : e / (1 - e) ≤ 2 * e := by
    apply (div_le_iff₀ he').mpr
    have hh := mul_nonneg (show 0 ≤ 1 - 2 * e by unfold e; linarith only [he.2]) he.1.le
    nlinarith only [hh]
  have hε : 0 < e := (eps_bounds μ).1
  have hc : 0 ≤ e / (1 - e) := div_nonneg hε.le he'.le
  have hpow : (1 + e / (1 - e)) ^ H ≤ Real.exp (2 * t) := by
    apply (one_le_exp_bound _ H hc).trans
    have hmul := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (α := ℝ) H)
    have hE : e * H = t := time_horizon a μ
    exact Real.exp_le_exp.mpr (by nlinarith only [hmul, hE])
  have heq : e / (1 - e) - e = e ^ 2 / (1 - e) := by field_simp; ring
  have hsmall : (e / (1 - e) - e) * H ≤ 2 * e * t := by
    rw [heq]
    have hrel : e ^ 2 / (1 - e) = e * (e / (1 - e)) := by ring
    rw [hrel]
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hε.le) (Nat.cast_nonneg (α := ℝ) H)
    have hE : e * H = t := time_horizon a μ
    nlinarith only [hm, mul_le_mul_of_nonneg_left hE.le (by positivity : 0 ≤ 2 * e)]
  have Hnon : 0 ≤ (e / (1 - e) - e) * H := by rw [heq]; positivity
  exact (mul_le_mul hsmall hpow (by positivity) (by positivity)).trans h.perturbation

lemma resident_start_cap (a : Settings k) (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P)
    (hs : safe k P) (hf : frequency k i P ≤ a.cutoff) :
    ∀ x ∉ mutants i, residentLevel k ≤ lawScore x (residents i (empiricalWeights P hP)) := by
  let w := empiricalWeights P hP
  let f := ColumnGain.fraction i w
  let q := residents i w
  have hα : 0 < initialGap k := (gap_pos k).1
  have hα' : initialGap k ≤ 1 / 10 := (gap_bound k).1
  have hw := empirical_probability P hP
  have hf₁ : f ≤ initialGap k / 2 := by
    change fraction i (empiricalWeights P hP) ≤ _
    rw [empirical_fraction i P hP]
    exact hf.trans a.cutoff_gap
  have hf₀ : f < 1 := by linarith only [hf₁, hα']
  have hq := residents_probability i w hw hf₀
  have hW : 0 ≤ floorWeight k := by unfold floorWeight; positivity
  intro x hx
  have hxbound : w x ≤ 1 - initialGap k := by
    have h := cap_of_safe P hP hs x
    rw [SpeciesDrift.fraction_eq x P hP] at h
    exact h
  have hq' : q x ≤ 1 - initialGap k / 2 := by
    change (1 - f)⁻¹ * project (mutants i)ᶜ w x ≤ _
    simp only [project, Set.mem_compl_iff, if_pos hx]
    rw [← div_eq_inv_mul, div_le_iff₀ (sub_pos.mpr hf₀)]
    have hh := mul_le_mul_of_nonneg_right hf₁ (show 0 ≤ 1 - initialGap k / 2 by linarith only [hα'])
    have hαf := sq_nonneg (initialGap k / 2)
    nlinarith only [hxbound, hh, hαf]
  have h := (mul_le_mul_of_nonneg_left (show initialGap k / 2 ≤ 1 - q x by linarith only [hq']) hW).trans
    (lawScore_bounds x q hq).1
  apply le_trans _ h
  unfold residentLevel
  nlinarith only [mul_nonneg hW hα.le]

lemma empirical_prediction_gain (hk : 2 ≤ k) (a : Settings k)
    (hn : Dimension k n a) (hm : PopulationSize k a μ)
    (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P) (hs : safe k P)
    (hf : frequency k i P ≤ a.cutoff) :
    3 * frequency k i P ≤ fraction i (predict (replaceKernel i) (eps μ) (a.horizon μ) (empiricalWeights P hP)) := by
  have hT := time_horizon a μ
  have he := eps_bounds μ
  let w := empiricalWeights P hP
  let f := fraction i w
  have hw := empirical_probability P hP
  have hf' : f ≤ a.cutoff := by
    change fraction i (empiricalWeights P hP) ≤ _
    rwa [empirical_fraction i P hP]
  have hflt : f < 1 := by linarith only [hf', a.cutoff_half]
  have hR : 0 ≤ remainderLimit (a.T : ℕ) := by unfold remainderLimit normLimit; positivity
  rw [← empirical_fraction i P hP]
  apply nonlinear_from_response i (eps μ) ⟨he.1.le, by linarith only [he.2]⟩
    (a.horizon μ) (a.T : ℕ) hT.le w hw hflt
    ((mul_le_mul_of_nonneg_left hf' (mul_nonneg (by norm_num) hR)).trans a.cutoff_remainder)
  intro hf₀
  have hπ := residents_probability i w hw hflt
  have hν := rare_probability i w hw hf₀
  have hc := resident_cap hn.four hn.two (residentLevel k) (gap_pos k).2.1
    (gap_bound k).2.1 (gap_bound k).2.2 hn.resident i (eps μ)
    ⟨he.1.le, hm.eps_eight⟩ hm.resident _ hπ (residents_zero i w) (resident_start_cap a i P hP hs hf)
  have hk₀ : 0 < k := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₀.ne'
  have hω : 0 ≤ residentGap (r + 1) := (gap_pos _).2.2.le
  have hE := hn.reproductive
  have hE' : (a.horizon μ : ℝ) * eps μ * ReproductiveAdmissibility.error n (r + 1) ≤ 1 := by
    rw [mul_comm ((a.horizon μ : ℕ) : ℝ), hT]
    exact hE
  have hF : (eps μ) * (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) ≤ 1 := by
    have h := hn.fertility_one
    push_cast at h
    rw [mul_assoc]
    exact mul_le_one₀ (by linarith only [he.2]) (by positivity) h
  have hD := hn.fertility
  push_cast at hD
  have hval := linear_gain (by omega : 1 ≤ r) hn.four i (eps μ) (residentGap (r + 1))
    ⟨he.1.le, by linarith only [he.2]⟩ hω (a.horizon μ) (horizon_perturbation a hm)
    hE' hF hD (residents i w) (rare i w) hπ hν (residents_zero i w) (rare_zero i w) hc
  apply le_trans _ hval
  have hD0 : (0 : ℝ) < 3 ^ (r + 1) := by positivity
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 3 ^ (r + 1))]
  let E := eps μ
  let c := ShadowGaps.delta (r + 1) * residentGap (r + 1)
  let B : ℝ := 3 ^ (r + 1)
  have hC : 0 ≤ c := mul_nonneg (ShadowGaps.delta_pos (by omega)).le hω
  have hp : E * bonus (r + 1) ≤ E * c / (2 * (1 + E) * B) := by
    change E * (c / (4 * B)) ≤ _
    rw [show E * (c / (4 * B)) = E * c / (4 * B) by ring]
    have hq := mul_le_mul_of_nonneg_right (show 2 * (1 + E) ≤ 4 by unfold E; linarith only [he.2]) hD0.le
    have hb : 0 < 2 * (1 + E) * B := by have hε : 0 < E := he.1; have hB : 0 < B := hD0; positivity
    exact div_le_div_of_nonneg_left (mul_nonneg he.1.le hC) hb hq
  have hbonus := bonus_pos (r + 1) (by omega)
  have hbase : 0 ≤ 1 + E * bonus (r + 1) := add_nonneg zero_le_one (mul_nonneg he.1.le hbonus.le)
  have hd : 1 + E * bonus (r + 1) ≤ 1 + E * c / (2 * (1 + E) * B) := by linarith only [hp]
  have hpow := pow_le_pow_left₀ hbase hd (a.horizon μ)
  have hBern := one_add_mul_le_pow (a := E * bonus (r + 1))
    ((by norm_num : (-2 : ℝ) ≤ 0).trans (mul_nonneg he.1.le hbonus.le)) (a.horizon μ)
  have h₀ : (a.horizon μ : ℝ) * (E * bonus (r + 1)) = (a.T : ℕ) * bonus (r + 1) := by
    calc
      _ = (E * (a.horizon μ : ℝ)) * bonus (r + 1) := by ring
      _ = _ := by rw [show E * (a.horizon μ : ℝ) = (a.T : ℕ) from hT]
  rw [h₀] at hBern
  have hg : (4 : ℝ) * (2 * 3 ^ (r + 1)) ≤ 1 + (a.T : ℕ) * bonus (r + 1) := by
    rw [show (4 : ℝ) * (2 * 3 ^ (r + 1)) = 8 * 3 ^ (r + 1) by ring]
    exact a.gain
  exact hg.trans (hBern.trans hpow)

end
end Lax637351Proofs.ColumnApplied
