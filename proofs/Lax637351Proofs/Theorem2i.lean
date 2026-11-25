import Lax637351.Theorem2i
import Lax637351Proofs.HomogeneousLower

namespace Lax637351Proofs.Theorem2i

open Lax637351.Algorithm Lax637351.Runtime
open Lax637351Proofs.RegenerationBounds Lax637351Proofs.PlateauRegeneration
open Lax637351Proofs.HomogeneousLower Lax637351Proofs.UniformEntry
open scoped Classical ENNReal

noncomputable section

def scale (k : ℕ) : ℝ := 32 * (k.factorial : ℝ) * 2 ^ k

lemma scale_ge_one (k : ℕ) : 1 ≤ scale k := by
  have hf : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  unfold scale
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 32 * (k.factorial : ℝ) by positivity)]

lemma charge_factorization (k : ℕ) {n : ℕ} (hn : 0 < n) (μ : ℕ+) {p : ℝ} (hp : 0 < p) :
    (((n : ℝ) * p) ^ k / (scale k * p)) * Real.exp (-(17 * ((μ : ℕ) : ℝ) * k)) ≤
        Real.exp (-16 * ((μ : ℕ) : ℝ)) / (32 * chargeRate k n μ p) := by
  let m : ℝ := (μ : ℕ)
  let q := Real.exp (-16 * m)
  let B := Real.exp (17 * m)
  let x : ℝ := (n : ℝ) * p
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < x := mul_pos hnr hp
  have hq : 0 < q := Real.exp_pos _
  have hB : 0 < B := Real.exp_pos _
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hsc : 0 < scale k := lt_of_lt_of_le zero_lt_one (scale_ge_one k)
  have he : 1 ≤ q * B := by
    dsimp [q, B]
    rw [← Real.exp_add]
    have hm : 0 ≤ m := by dsimp [m]; positivity
    exact Real.one_le_exp (by linarith)
  have hpow : (B ^ k)⁻¹ = Real.exp (-(17 * m * (k : ℝ))) := by
    dsimp [B]
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  change (x ^ k / (scale k * p)) * Real.exp (-(17 * m * k)) ≤ q / (32 * chargeRate k n μ p)
  have heq : q / (32 * chargeRate k n μ p) = (x ^ k / (scale k * p)) * ((q * B) * (B ^ k)⁻¹) := by
    unfold chargeRate resetBudget hitBound scale
    dsimp only [x, B, m]
    simp only [mul_pow, div_pow, one_pow]
    field_simp
  rw [heq, ← hpow]
  exact mul_le_mul_of_nonneg_left ((one_mul _).symm.le.trans
    (mul_le_mul_of_nonneg_right he (by positivity))) (by positivity)

lemma absorb_pop_loss {k : ℕ} {η x p m : ℝ} (_hη : 0 < η) (hx : 1 ≤ x) (hp : 0 < p)
    (h₁ : 17 * (k : ℝ) * m ≤ η / 2 * Real.log x)
    (h₂ : scale k ≤ Real.exp (η / 2 * Real.log x)) :
    x ^ ((k : ℝ) - η) / p ≤
      (x ^ k / (scale k * p)) * Real.exp (-(17 * m * k)) := by
  have hx' : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs : 0 < scale k := lt_of_lt_of_le zero_lt_one (scale_ge_one k)
  let u := η / 2 * Real.log x
  have he : Real.exp (-u) ≤ Real.exp (-(17 * m * (k : ℝ))) := by
    apply Real.exp_le_exp.mpr
    dsimp [u]
    nlinarith only [h₁]
  have hpow : x ^ ((k : ℝ) - η) = x ^ k * (Real.exp (-u) / Real.exp u) := by
    rw [Real.rpow_def_of_pos hx', ← Real.exp_sub,
      ← Real.rpow_natCast, Real.rpow_def_of_pos hx', ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  rw [hpow]
  calc
    _ = (x ^ k / p) * (Real.exp (-u) / Real.exp u) := by ring
    _ ≤ (x ^ k / p) * (Real.exp (-u) / scale k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hs h₂
    _ = (x ^ k / (scale k * p)) * Real.exp (-u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

/--
---
conclusion: Lax637351.Theorem2i.bound
---
-/
theorem bound :
    ∀ k : ℕ, 2 ≤ k →
    ∀ η : ℝ, 0 < η →
      ∃ ε : ℝ, 0 < ε ∧
      ∃ N : ℕ,
        ∀ n ≥ N,
        ∀ p_c : ℝ, 0 < p_c → p_c ≤ 1 → (N : ℝ) / n ≤ p_c →
        ∀ μ : ℕ+, 2 ≤ μ → μ ≤ ε * Real.log (n * p_c) →
          expectedOptimizationTime n k μ p_c (avoidReplications := true) ≥
            ENNReal.ofReal ((n * p_c) ^ ((k : ℝ) - η) / p_c) := by
  intro k hk η hη
  let C := 17 * (k : ℝ)
  let ε := min 1 (η / (2 * C))
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε' : ε ≤ 1 := min_le_left _ _
  have hεC : C * ε ≤ η / 2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right 1 (η / (2 * C))) hC.le
    apply hh.trans_eq
    field_simp
  obtain ⟨Ni, hNi⟩ := initial_ordinary_eventually k
  let Nr := ⌈Real.exp (Real.log (scale k) / (η / 2))⌉₊
  let N := max (2 * k + 1) (max Ni Nr)
  refine ⟨ε, hε, N, ?_⟩
  intro n hn p hpos hle hnp μ hμ hpop
  let x : ℝ := (n : ℝ) * p
  let m : ℝ := (μ : ℕ)
  have hn₀ : 2 * k + 1 ≤ n := (le_max_left _ _).trans hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hxN : (N : ℝ) ≤ x := (div_le_iff₀ hn').mp hnp |>.trans_eq (mul_comm p n)
  have hN : 2 * k + 1 ≤ N := le_max_left _ _
  have hkN : k + 1 ≤ N := by omega
  have hx1 : 1 ≤ x := (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N).trans hxN
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hp' : (k + 1 : ℝ) / n ≤ p := by
    apply le_trans _ hnp
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkN) hn'.le
  have hlog0 := Real.log_nonneg hx1
  have hlogn : Real.log x ≤ n := by
    have hxn : x ≤ n := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hn'.le
    linarith [Real.log_le_sub_one_of_pos hx]
  have hμn : (μ : ℕ) ≤ n := by
    have hh := hpop.trans ((mul_le_of_le_one_left hlog0 hε').trans hlogn)
    exact_mod_cast hh
  have hNi' : Ni ≤ n := ((le_max_left Ni Nr).trans (le_max_right (2 * k + 1) _)).trans hn
  have hlo := from_uniform_lower hk (by omega : 2 * k ≤ n) hμ p ⟨hpos, hle⟩ hp' (hNi n hNi' μ hμn)
  have h₁ : 17 * (k : ℝ) * m ≤ η / 2 * Real.log x := by
    have h := mul_le_mul_of_nonneg_left hpop hC.le
    have hl := mul_le_mul_of_nonneg_right hεC hlog0
    exact h.trans (by simpa only [mul_assoc] using hl)
  have hsc : 0 < scale k := lt_of_lt_of_le zero_lt_one (scale_ge_one k)
  have h₂ : scale k ≤ Real.exp (η / 2 * Real.log x) := by
    have hNr : Nr ≤ N := (le_max_right Ni Nr).trans (le_max_right (2 * k + 1) _)
    have hR : Real.exp (Real.log (scale k) / (η / 2)) ≤ x :=
      (Nat.le_ceil _).trans ((by exact_mod_cast hNr : (Nr : ℝ) ≤ N).trans hxN)
    have hl := (Real.le_log_iff_exp_le hx).mpr hR
    rw [← Real.exp_log hsc, Real.exp_le_exp]
    simpa only [mul_comm (η / 2)] using (div_le_iff₀ (by positivity : 0 < η / 2)).mp hl
  apply le_trans _ hlo
  apply ENNReal.ofReal_le_ofReal
  exact (absorb_pop_loss hη hx1 hpos h₁ h₂).trans (charge_factorization k (by omega) μ hpos)

end
end Lax637351Proofs.Theorem2i
