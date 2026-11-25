import Lax637351Proofs.Regeneration
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Basic

namespace Lax637351Proofs.RegenerationBounds

open Lax637351Proofs.Regeneration Lax637351Proofs.FiniteDrift
open scoped Classical ENNReal

noncomputable section

variable {ι : Type*} [DecidableEq ι]

def hitBound (b ρ : ℝ) (d : ℕ) : ℝ := (d.factorial : ℝ) * (2 * b * ρ) ^ d

lemma hitBound_nonneg {b ρ : ℝ} (hb : 1 ≤ b) (hρ : 0 ≤ ρ) (d : ℕ) :
    0 ≤ hitBound b ρ d := by unfold hitBound; positivity

lemma grouped_coefficient (b ρ : ℝ) (D : Finset ι) :
    hitCoefficient ρ (hitBound b ρ) D =
      ∑ j ∈ Finset.range (D.card + 1),
        if j = 0 then 0 else (D.card.choose j : ℝ) * (ρ ^ j * hitBound b ρ (D.card - j)) := by
  unfold hitCoefficient nonemptySubsets
  have heq : D.powerset.erase ∅ = D.powerset.filter (fun J ↦ J.card ≠ 0) := by
    ext J
    simp [Finset.card_eq_zero, and_comm]
  rw [heq, Finset.sum_filter]
  have hf : ∀ J ∈ D.powerset,
      (if J.card ≠ 0 then ρ ^ J.card * hitBound b ρ (D \ J).card else 0) =
      (if J.card = 0 then 0 else ρ ^ J.card * hitBound b ρ (D.card - J.card)) := by
    intro J hJ
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ)]
    by_cases h : J.card = 0 <;> simp [h]
  rw [Finset.sum_congr rfl hf]
  let f (j : ℕ) := if j = 0 then 0 else ρ ^ j * hitBound b ρ (D.card - j)
  change (∑ J ∈ D.powerset, f J.card) = _
  rw [Finset.sum_powerset_apply_card f]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0 <;> simp [f, hj, nsmul_eq_mul]

lemma coefficient_le {b ρ : ℝ} (hb : 1 ≤ b) (hρ : 0 ≤ ρ) (D : Finset ι) :
    hitCoefficient ρ (hitBound b ρ) D ≤ hitBound b ρ D.card / b := by
  let d := D.card
  let W := hitBound b ρ d
  have hW : 0 ≤ W := hitBound_nonneg hb hρ d
  have hb' : 0 < b := by linarith
  have hterm (j : ℕ) (hpos : 0 < j) (hle : j ≤ d) :
      b * ((d.choose j : ℝ) * (ρ ^ j * hitBound b ρ (d - j))) ≤
        W * (1 / 2 : ℝ) ^ j := by
    have hc : (d.choose j : ℝ) * ((d - j).factorial : ℝ) ≤ (d.factorial : ℝ) := by
      have hh : d.choose j * (d - j).factorial * j.factorial = d.factorial := by
        simpa only [Nat.mul_assoc, Nat.mul_comm ((d - j).factorial)] using
          Nat.choose_mul_factorial_mul_factorial hle
      have hi := Nat.le_mul_of_pos_right (n := d.choose j * (d - j).factorial)
        (Nat.factorial_pos j)
      rw [hh] at hi
      exact_mod_cast hi
    have hp : b ≤ b ^ j := by
      simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ j by omega)
    have hmul := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤
      b * ρ ^ j * (2 * b * ρ) ^ (d - j))
    have hpow := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (pow_nonneg hρ j))
      (by positivity : 0 ≤ (d.factorial : ℝ) * (2 * b * ρ) ^ (d - j))
    calc
      _ ≤ b * ρ ^ j * (2 * b * ρ) ^ (d - j) * (d.factorial : ℝ) := by
        unfold hitBound
        nlinarith only [hmul]
      _ ≤ ((d.factorial : ℝ) * (2 * b * ρ) ^ (d - j)) * (b ^ j * ρ ^ j) := by
        nlinarith only [hpow]
      _ = _ := by
        change _ = ((d.factorial : ℝ) * (2 * b * ρ) ^ d) * (1 / 2 : ℝ) ^ j
        rw [show (2 * b * ρ) ^ d = (2 * b * ρ) ^ (d - j) * (2 * b * ρ) ^ j by
          rw [← pow_add, Nat.sub_add_cancel hle]]
        have heq : (2 * b * ρ) ^ j * (1 / 2 : ℝ) ^ j = b ^ j * ρ ^ j := by
          rw [← mul_pow, show 2 * b * ρ * (1 / 2) = b * ρ by ring, mul_pow]
        rw [← heq]
        ring
  have hgeom (m : ℕ) : (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (j + 1)) ≤ 1 := by
    calc
      _ ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) :=
        Summable.sum_le_tsum _ (fun _ _ ↦ by positivity)
          (summable_geometric_two.mul_left (1 / 2 : ℝ) |>.congr fun _ ↦ by rw [pow_succ'])
      _ = 1 := by
        simp_rw [pow_succ']
        rw [tsum_mul_left, tsum_geometric_two]
        norm_num
  apply (le_div_iff₀ hb').mpr
  rw [mul_comm, grouped_coefficient, Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum (g := fun j ↦ if j = 0 then 0 else W * (1 / 2 : ℝ) ^ j) ?_) _
  · intro j hj
    by_cases hj' : j = 0
    · simp [hj']
    · simp only [if_neg hj']
      exact hterm j (Nat.pos_of_ne_zero hj') (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  · rw [Finset.sum_range_succ']
    simp only [if_true, add_zero, Nat.succ_ne_zero, if_false, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hgeom d) hW).trans_eq (mul_one W)

variable {α : Type*} [Fintype α] [Fintype ι]

lemma capture_le (K : Kernel α ι) (R : Set α) (b ρ : ℝ) (hb : 1 ≤ b) (hρ : 0 ≤ ρ)
    (hmask : ∀ x J, mean (K x) (fun v ↦ if J ⊆ v.1 then 1 else 0) ≤ ρ ^ J.card)
    (htime : ∀ t x, span K R t x ≤ b) (D : Finset ι) (t : ℕ) (x : α) :
    capture K R t D x ≤ hitBound b ρ D.card := by
  revert t x
  induction D using Finset.strongInduction with
  | H D ih =>
    intro t x
    by_cases hD : D = ∅
    · simp [hD, hitBound]
    · let C := hitBound b ρ D.card / b
      have hc : 0 ≤ C := div_nonneg (hitBound_nonneg hb hρ _) (by linarith)
      have hf (J : Finset ι) (hJ : J ∈ nonemptySubsets D) :
          ∀ s y, capture K R s (D \ J) y ≤ hitBound b ρ (D \ J).card := by
        apply ih
        obtain ⟨hne, hsub⟩ := mem_nonemptySubsets.mp hJ
        exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun heq ↦
          hne (Finset.disjoint_iff_inter_eq_empty.mp (sdiff_eq_left.mp heq) ▸
            (Finset.inter_eq_right.mpr hsub).symm)⟩
      have hh := capture_le_span K R ρ (hitBound b ρ) (hitBound_nonneg hb hρ)
        D hD hmask hf C hc (coefficient_le hb hρ D) t x
      apply hh.trans ((mul_le_mul_of_nonneg_left (htime t x) hc).trans_eq ?_)
      dsimp [C]
      field_simp

end
end Lax637351Proofs.RegenerationBounds
