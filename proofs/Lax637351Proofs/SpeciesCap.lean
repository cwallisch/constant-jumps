import Lax637351Proofs.SpeciesDrift
import Lax637351Proofs.SparseBarrier

namespace Lax637351Proofs.SpeciesCap

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauPairs
open Lax637351Proofs.SpeciesDrift Lax637351Proofs.OffspringBridge Lax637351Proofs.OffspringEstimates
open OffspringEstimates.Genotypes OffspringEstimates.PopulationRatio OffspringEstimates.SpeciesState
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def floorWeight (k : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ k

def level (k : ℕ) : ℝ := floorWeight k / 1000

def clippedScore (B : Genotype n k) (P : Population n μ) : ℝ :=
  ((μ : ℕ) : ℝ) * Deletion.total (weightFunction B) P / max (count (toString B) P) ((μ : ℕ) / 2 : ℝ)

lemma level_pos (k : ℕ) : 0 < level k := by unfold level floorWeight; positivity

lemma level_small (k : ℕ) : level k ≤ 1 / 1000 := by
  unfold level floorWeight
  exact div_le_div_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)

lemma weighted_count_bounds (B : Genotype n k) (P : Population n μ) (hP : plateau (k := k) P) :
    floorWeight k * (((μ : ℕ) : ℝ) - count (toString B) P) ≤ Deletion.total (weightFunction B) P ∧
      Deletion.total (weightFunction B) P ≤ (5 / 4 : ℝ) * (((μ : ℕ) : ℝ) - count (toString B) P) := by
  have he : ((μ : ℕ) : ℝ) - count (toString B) P =
      ∑ i : Fin μ, (1 - PopulationRatio.indicator (toString B) (P i)) := by
    rw [Finset.sum_sub_distrib]
    simp [count, Deletion.total, nsmul_eq_mul]
  rw [he, Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    by_cases hi : P i = toString B
    · simp [hi, PopulationRatio.indicator, weightFunction_anchor]
    · have he : ofString (P i) (hP i) ≠ B := by
        intro h
        exact hi ((toString_ofString _ _).symm.trans (congrArg toString h))
      have hw := Weights.uniform_weight_lower (distance_pos B _ he) (distance_le B (ofString (P i) (hP i)))
      have hiP : (zeros (P i)).card = k := hP i
      rw [← weightFunction_toString, toString_ofString (P i) hiP] at hw
      simpa [PopulationRatio.indicator, hi, floorWeight] using hw
  · apply Finset.sum_le_sum
    intro i _
    by_cases hi : P i = toString B
    · simp [hi, PopulationRatio.indicator, weightFunction_anchor]
    · simpa [PopulationRatio.indicator, hi] using (weightFunction_bounds B (P i)).2

lemma clipped_eq (B : Genotype n k) (P : Population n μ)
    (h : ((μ : ℕ) / 2 : ℝ) ≤ count (toString B) P) :
    clippedScore B P = score B P := by
  simp [clippedScore, score, ratio, max_eq_left h, mul_div_assoc]

lemma clipped_nonneg (B : Genotype n k) (P : Population n μ) : 0 ≤ clippedScore B P := by
  unfold clippedScore
  have hW : 0 ≤ Deletion.total (weightFunction B) P := Finset.sum_nonneg fun i _ ↦ (weightFunction_bounds B (P i)).1
  have hM : 0 ≤ max (count (toString B) P) (((μ : ℕ) : ℝ) / 2) := (count_nonneg _ _).trans (le_max_left _ _)
  exact div_nonneg (mul_nonneg (by positivity) hW) hM

lemma clipped_range (B : Genotype n k) (P : Population n μ) (hP : plateau (k := k) P) :
    floorWeight k * (((μ : ℕ) : ℝ) - count (toString B) P) ≤ clippedScore B P ∧
      clippedScore B P ≤ (5 / 2 : ℝ) * (((μ : ℕ) : ℝ) - count (toString B) P) := by
  let m : ℝ := (μ : ℕ)
  let a := count (toString B) P
  let Z := Deletion.total (weightFunction B) P
  have hm : 0 < m := by dsimp [m]; exact_mod_cast μ.pos
  have hC : a ≤ m := count_le_size _ _
  have hM : 0 < max a (m / 2) := (half_pos hm).trans_le (le_max_right _ _)
  have hM' : max a (m / 2) ≤ m := max_le hC (by linarith)
  have hs : 0 ≤ m - a := sub_nonneg.mpr hC
  have hw : 0 ≤ floorWeight k := by unfold floorWeight; positivity
  have hd := weighted_count_bounds B P hP
  change floorWeight k * (m - a) ≤ m * Z / max a (m / 2) ∧
    m * Z / max a (m / 2) ≤ 5 / 2 * (m - a)
  constructor
  · rw [le_div_iff₀ hM]
    apply (mul_le_mul_of_nonneg_left hM' (mul_nonneg hw hs)).trans
    simpa only [mul_comm _ m] using mul_le_mul_of_nonneg_left hd.1 hm.le
  · rw [div_le_iff₀ hM]
    have hr := mul_le_mul_of_nonneg_left (le_max_right a (m / 2)) (show 0 ≤ (5 / 2 : ℝ) * (m - a) by positivity)
    have hd' := mul_le_mul_of_nonneg_left hd.2 hm.le
    nlinarith only [hd', hr]

lemma one_step_count (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k)
    (Q : Population n μ) (hQ : Q ∈ (auxiliary k p ar P).support) :
    |count (toString B) Q - count (toString B) P| ≤ 1 := by
  obtain ⟨z, d, rfl⟩ := step_relation hk hkn p ar P hP Q hQ
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [Lax637351Proofs.Transitions.replace]
  · simpa [Lax637351Proofs.Transitions.replace] using update_count_abs (toString B) P i z

lemma one_step_total (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k)
    (Q : Population n μ) (hQ : Q ∈ (auxiliary k p ar P).support) :
    |Deletion.total (weightFunction B) Q - Deletion.total (weightFunction B) P| ≤ 5 / 4 := by
  obtain ⟨z, d, rfl⟩ := step_relation hk hkn p ar P hP Q hQ
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [Lax637351Proofs.Transitions.replace]
    norm_num
  · rw [Lax637351Proofs.Transitions.replace, Fin.lastCases_castSucc, Deletion.total_update, abs_le]
    have h := weightFunction_bounds B z
    have h' := weightFunction_bounds B (P i)
    constructor <;> linarith

lemma clipped_step (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k)
    (Q : Population n μ) (hQ : Q ∈ (auxiliary k p ar P).support) :
    |clippedScore B Q - clippedScore B P| ≤ 8 := by
  let m : ℝ := (μ : ℕ)
  let A (P : Population n μ) := max (count (toString B) P) (m / 2)
  let Z (P : Population n μ) := Deletion.total (weightFunction B) P
  have hm : 0 < m := by dsimp [m]; exact_mod_cast μ.pos
  have hA (Y : Population n μ) : m / 2 ≤ A Y := le_max_right _ _
  have hA' (Y : Population n μ) : 0 < A Y := (half_pos hm).trans_le (hA Y)
  have hAc : |A Q - A P| ≤ 1 := by
    rw [abs_le]
    have h := abs_le.mp (one_step_count hk hkn p ar P hP B Q hQ)
    constructor
    · have hh : A P ≤ A Q + 1 := by
        apply max_le
        · linarith only [h.1, le_max_left (count (toString B) Q) (m / 2)]
        · linarith only [hA Q]
      linarith
    · have hh : A Q ≤ A P + 1 := by
        apply max_le
        · linarith only [h.2, le_max_left (count (toString B) P) (m / 2)]
        · linarith only [hA P]
      linarith
  have hZ : 0 ≤ Z P := Finset.sum_nonneg (fun i _ ↦ (weightFunction_bounds B (P i)).1)
  have hZ' : Z P ≤ (5 / 4) * m := by
    have h := (weighted_count_bounds B P hP).2
    change Z P ≤ _ at h
    linarith only [h, count_nonneg (toString B) P]
  change |m * Z Q / A Q - m * Z P / A P| ≤ _
  rw [show m * Z Q / A Q - m * Z P / A P =
      m / A Q * (Z Q - Z P) + (m / A Q * (Z P / A P)) * (A P - A Q) by
    field_simp [(hA' _).ne']; ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hm.le (hA' Q).le),
    abs_of_nonneg (mul_nonneg (div_nonneg hm.le (hA' Q).le) (div_nonneg hZ (hA' P).le)), abs_sub_comm (A P)]
  have h₂ : m / A Q ≤ 2 := (div_le_iff₀ (hA' Q)).mpr (by linarith only [hA Q])
  have h₃ : Z P / A P ≤ 5 / 2 := (div_le_iff₀ (hA' P)).mpr (by linarith only [hA P, hZ'])
  have hfirst := mul_le_mul h₂ (one_step_total hk hkn p ar P hP B Q hQ)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hprod := mul_le_mul h₂ h₃ (div_nonneg hZ (hA' P).le) (by norm_num : (0 : ℝ) ≤ 2)
  have hsecond := mul_le_mul hprod hAc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * (5 / 2))
  linarith only [hfirst, hsecond]

lemma low_has_many (B : Genotype n k) (P : Population n μ) (hP : plateau (k := k) P)
    (h : clippedScore B P ≤ 4 * level k * (μ : ℕ)) :
    (9 / 10 : ℝ) * (μ : ℕ) ≤ count (toString B) P := by
  have hd := (clipped_range B P hP).1.trans h
  unfold level at hd
  have hw : 0 < floorWeight k := by unfold floorWeight; positivity
  have hh : floorWeight k * (((μ : ℕ) : ℝ) - count (toString B) P) ≤
      floorWeight k * (4 / 1000 * (μ : ℕ)) := by
    exact hd.trans_eq (by ring)
  have hh' := (mul_le_mul_iff_of_pos_left hw).mp hh
  have hm : (0 : ℝ) ≤ (μ : ℕ) := by positivity
  linarith only [hh', hm]

lemma near_anchor (hk : 0 < k) (hkn : k ≤ n) (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (B : Genotype n k)
    (h : clippedScore B P ≤ 4 * level k * (μ : ℕ)) :
    (1 < count (toString B) P ∧ (1 / 2 : ℝ) ≤ fraction B P ∧
      ratio (weightFunction B) (toString B) P ≤ 1 / 25) ∧
      ∀ Q ∈ (auxiliary k p ar P).support, clippedScore B Q = score B Q := by
  have hm : (5 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hμ
  have hμR : (0 : ℝ) < (μ : ℕ) := by linarith
  have hcount := low_has_many B P hP h
  have hclip := clipped_eq B P (by linarith)
  have hrat : ratio (weightFunction B) (toString B) P ≤ 1 / 25 := by
    rw [hclip, score] at h
    have hh := mul_le_mul_of_nonneg_right (level_small k) hμR.le
    nlinarith only [h, hh, mul_pos hμR (show 0 < (1 / 25 - 4 / 1000 : ℝ) by norm_num),
      (mul_le_mul_iff_of_pos_left hμR).mp (show
        (μ : ℕ) * ratio (weightFunction B) (toString B) P ≤ (μ : ℕ) * (4 * level k) by linarith only [h])]
  refine ⟨⟨by linarith, ?_, hrat⟩, ?_⟩
  · unfold fraction
    exact (le_div_iff₀ hμR).mpr (by linarith)
  · intro Q hQ
    apply clipped_eq
    have hh := (abs_le.mp (one_step_count hk hkn p ar P hP B Q hQ)).1
    linarith

end
end Lax637351Proofs.SpeciesCap
