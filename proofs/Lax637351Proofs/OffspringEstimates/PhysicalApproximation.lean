import Lax637351Proofs.OffspringEstimates.BitProduct
import Lax637351Proofs.OffspringEstimates.MaskCounts
import Lax637351Proofs.OffspringEstimates.BinomialApproximation
import Lax637351Proofs.OffspringEstimates.Profiles

namespace Lax637351Proofs.OffspringEstimates.PhysicalApproximation

open Lax637351Proofs.OffspringEstimates.Algorithm Lax637351Proofs.OffspringEstimates.BitProduct Lax637351Proofs.OffspringEstimates.MaskCounts
open Lax637351Proofs.OffspringEstimates.BinomialApproximation Lax637351Proofs.OffspringEstimates.Profiles
open scoped BigOperators Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma truncated_error_sum {n N k : ℕ} (hn : 2 ≤ n) (hN : N ≤ n) (hk : k ≤ N) :
    (∑ w ∈ Finset.range (k + 1), |binomialTerm n N w - Real.exp (-1) / (w.factorial : ℝ)|) ≤
      3 * ((k : ℝ) + 2) * (((n - N + k : ℕ) : ℝ) + 1) / n := by
  let R : ℝ := ((k : ℝ) + 2) * (((n - N + k : ℕ) : ℝ) + 1) / n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hterm : ∀ w ∈ Finset.range (k + 1),
      |binomialTerm n N w - Real.exp (-1) / (w.factorial : ℝ)| ≤ R * (1 / (w.factorial : ℝ)) := by
    intro w hw
    have hwk : w ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
    have happrox := binomial_poisson_error hn hN (hwk.trans hk)
    have h1 : (w : ℝ) + 2 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hwk 2
    have h2 : (((n - N + w : ℕ) : ℝ) + 1) ≤ (((n - N + k : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left hwk (n - N)) 1
    have hprod := mul_le_mul h1 h2 (by positivity : 0 ≤ (((n - N + w : ℕ) : ℝ) + 1))
      (by positivity : 0 ≤ (k : ℝ) + 2)
    have hle := div_le_div_of_nonneg_right hprod
      (by positivity : 0 ≤ (n : ℝ) * (w.factorial : ℝ))
    have heq : ((k : ℝ) + 2) * (((n - N + k : ℕ) : ℝ) + 1) /
        ((n : ℝ) * (w.factorial : ℝ)) = R * (1 / (w.factorial : ℝ)) := by
      dsimp [R]
      field_simp
    exact happrox.trans (hle.trans_eq heq)
  calc
    _ ≤ ∑ w ∈ Finset.range (k + 1), R * (1 / (w.factorial : ℝ)) := Finset.sum_le_sum hterm
    _ = R * (∑ w ∈ Finset.range (k + 1), (1 : ℝ) / (w.factorial : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ R * 3 := mul_le_mul_of_nonneg_left (factorial_inverse_sum_le k) hR
    _ = _ := by dsimp [R]; ring

end
end Lax637351Proofs.OffspringEstimates.PhysicalApproximation
