import Lax637351Proofs.CopyingWindow

namespace Lax637351Proofs.CopyingExponential

open Lax637351.Algorithm Lax637351Proofs.CopyingWindow
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open Lax637351Proofs.Ordinary Lax637351Proofs.CopyingModel
open scoped Classical ENNReal

noncomputable section

lemma factorial_lower (r : ℕ) : ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
  have hr : (0 : ℝ) < r.factorial := by exact_mod_cast r.factorial_pos
  have h := (div_le_iff₀ hr).mp (Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r)
  rw [div_pow, ← Real.exp_nat_mul, mul_one]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h)

lemma ratio_product (m : ℕ) (hm : 2 ≤ m) :
    (1 / (3 * Real.exp 1)) ^ (m - 1) ≤
      ∏ j ∈ Finset.Ico 1 m, (j : ℝ) / ((m : ℝ) + 1) := by
  let r := m - 1
  have hr : r + 1 = m := Nat.sub_add_cancel (by omega)
  have h₁ : (∏ j ∈ Finset.Ico 1 m, (j : ℝ)) = (r.factorial : ℝ) := by
    rw [← Nat.cast_prod]
    conv_lhs => rw [← hr]
    rw [Finset.prod_Ico_id_eq_factorial]
  have hc : (Finset.Ico 1 m).card = r := Nat.card_Ico 1 m
  have hf := factorial_lower r
  rw [Finset.prod_div_distrib, Finset.prod_const, hc, h₁]
  have hle : (1 / (3 * Real.exp 1)) ≤ ((r : ℝ) / Real.exp 1) / ((m : ℝ) + 1) := by
    have hm' : (m : ℝ) + 1 ≤ 3 * (r : ℝ) := by
      have hNat : m + 1 ≤ 3 * r := by dsimp [r]; omega
      exact_mod_cast hNat
    have hE := Real.exp_pos 1
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hE).mpr
    nlinarith [mul_le_mul_of_nonneg_right hm' hE.le]
  apply (pow_le_pow_left₀ (by positivity) hle r).trans
  rw [div_pow]
  exact div_le_div_of_nonneg_right hf (by positivity)

lemma complete_product (m : ℕ) (hm : 2 ≤ m) :
    Real.exp (-16 * (m : ℝ)) ≤ ∏ j ∈ Finset.Ico 1 m, stageFactor m j := by
  let r := m - 1
  let f (i : ℕ) := (i : ℝ) / ((m : ℝ) + 1)
  let P := ∏ j ∈ Finset.Ico 1 m, f j
  let q := 1 / (3 * Real.exp 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hP : q ^ r ≤ P := ratio_product m hm
  have hP' : 0 ≤ P := (pow_nonneg hq _).trans hP
  have hfac (i : ℕ) (hi : i ∈ Finset.Ico 1 m) :
      (1 / 128) * f i ^ 2 * f (m - i) ≤ stageFactor m i := by
    have hil := (Finset.mem_Ico.mp hi).2
    have hi' : (i : ℝ) ≤ m := by exact_mod_cast hil.le
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    unfold stageFactor
    dsimp [f]
    rw [Nat.cast_sub hil.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity) _ 2
    exact div_le_div_of_nonneg_left (by positivity) hm' (by linarith)
  have hc := Nat.card_Ico 1 m
  have hreflect : (∏ j ∈ Finset.Ico 1 m, f (m - j)) = P := by
    rw [Finset.prod_Ico_reflect f 1 (show m ≤ m + 1 by omega)]
    simp [P]
  have hbase : Real.exp (-16) ≤ (1 / 128) * q ^ 3 := by
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have hh := (Real.add_one_lt_exp (x := 1) (by norm_num)).le
      norm_num at hh ⊢
      exact hh
    have hE : (3456 : ℝ) ≤ Real.exp 13 := by
      calc
        _ ≤ (2 : ℝ) ^ 13 := by norm_num
        _ ≤ Real.exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) he2 _
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    have heq : Real.exp (-16) * ((Real.exp 1) ^ 3) = (Real.exp 13)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      norm_num
    have hInv : (Real.exp 13)⁻¹ ≤ (3456 : ℝ)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3456) hE
    apply (le_of_mul_le_mul_right _ (show 0 < Real.exp 1 ^ 3 by positivity))
    rw [heq]
    have hqeq : (1 : ℝ) / 128 * q ^ 3 * Real.exp 1 ^ 3 = 3456⁻¹ := by
      dsimp [q]
      field_simp
      norm_num
    rw [hqeq]
    exact hInv
  calc
    Real.exp (-16 * (m : ℝ)) ≤ Real.exp ((r : ℝ) * (-16)) := by
      apply Real.exp_le_exp.mpr
      have hr : (r : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
      linarith
    _ = (Real.exp (-16)) ^ r := Real.exp_nat_mul _ _
    _ ≤ ((1 / 128) * q ^ 3) ^ r := pow_le_pow_left₀ (by positivity) hbase _
    _ = (1 / 128 : ℝ) ^ r * (q ^ r) ^ 3 := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3]
    _ ≤ (1 / 128 : ℝ) ^ r * P ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hq _) hP _) (by positivity)
    _ = ∏ i ∈ Finset.Ico 1 m, (1 / 128) * f i ^ 2 * f (m - i) := by
      have hp2 : (∏ i ∈ Finset.Ico 1 m, f i ^ 2) = P ^ 2 := by
        dsimp only [P]
        rw [Finset.prod_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hc, hp2, hreflect]
      change (1 / 128 : ℝ) ^ r * P ^ 3 = (1 / 128 : ℝ) ^ r * P ^ 2 * P
      ring
    _ ≤ _ := Finset.prod_le_prod (fun i _ ↦ by dsimp [f]; positivity) hfac

variable {n k : ℕ} {μ : ℕ+}

def resetWindow (μ : ℕ+) (p : ℝ) : ℕ := (μ : ℕ) * stageLength p

lemma reset_window_lower (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (hp' : (k + 1 : ℝ) / n ≤ p)
    (P : Population n μ) (hP : ordinary k P) (hpl : hasPlateau k P) :
    Real.exp (-16 * ((μ : ℕ) : ℝ)) ≤
      visit (Lax637351.Algorithm.step (jump k) p true) {Q | homogeneousPlateau k Q}
        (resetWindow μ p) P := by
  let K := Lax637351.Algorithm.step (jump k) p true (n := n) (μ := μ)
  obtain ⟨i, hi⟩ := hpl
  let A := P i
  let s := copyCount A P
  have hs : s ≤ (μ : ℕ) := copyCount_le _ _
  have hs' : 1 ≤ s := Finset.card_pos.mpr ⟨i, (mem_copies _ _ _).mpr rfl⟩
  let r := (μ : ℕ) - s
  have hr : r ≤ (μ : ℕ) := Nat.sub_le _ _
  have hcount : copyCount A P = (μ : ℕ) - r := (Nat.sub_sub_self hs).symm
  have hh := copying_product hk hkn hn p hp hp' A hi r hr P hP hcount
  rw [← hcount] at hh
  have hpSub : Finset.Ico s (μ : ℕ) ⊆ Finset.Ico 1 (μ : ℕ) := by
    intro j hj
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Ico.mp hj
    exact Finset.mem_Ico.mpr ⟨hs'.trans hj₁, hj₂⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one hpSub
    (fun j hj ↦ stageFactor_nonneg (Finset.mem_Ico.mp hj).2.le)
    (fun j hj _ ↦ stageFactor_le_one (Finset.mem_Ico.mp hj).2)
  have hq := (complete_product (μ : ℕ) (by exact_mod_cast hμ)).trans (hprod.trans hh)
  have hG : ∀ Q ∈ ({Q | copyCount A Q = (μ : ℕ)} : Set (Population n μ)),
      homogeneousPlateau k Q := by
    intro Q hQ
    have hall := (copyCount_full_iff A Q).mp hQ
    refine ⟨fun j ↦ ?_, fun j ↦ (hall j).trans (hall 0).symm⟩
    simpa [hall j] using hi
  have hf := visit_lower_through K {Q | copyCount A Q = (μ : ℕ)}
    {Q | homogeneousPlateau k Q} 0 1 (by norm_num) le_rfl
    (fun Q hQ ↦ (visit_in K _ _ _ (hG Q hQ)).ge) (r * stageLength p) P
  simp only [one_mul, add_zero] at hf
  exact hq.trans (hf.trans (visit_monotone K _ _ (Nat.mul_le_mul_right _ hr)))

end
end Lax637351Proofs.CopyingExponential
