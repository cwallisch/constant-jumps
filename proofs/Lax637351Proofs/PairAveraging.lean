import Lax637351Proofs.PlateauPairs

namespace Lax637351Proofs.PairAveraging

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {n : ℕ} {μ : ℕ+}

def pairSum (f : BitString n → BitString n → ℝ) (P Q : Population n μ) : ℝ :=
  ∑ i, ∑ j, f (P i) (Q j)

def pairMean (f : BitString n → BitString n → ℝ) (P : Population n μ) : ℝ :=
  pairSum f P P / (((μ : ℕ) : ℝ) ^ 2)

def partnerMean (f : BitString n → BitString n → ℝ) (P : Population n μ) (z : BitString n) : ℝ :=
  (∑ i, f z (P i)) / ((μ : ℕ) : ℝ)

lemma sum_update {α : Type*} (P : Fin μ → α) (i : Fin μ) (z : α) (f : α → ℝ) :
    (∑ j, f (Function.update P i z j)) - ∑ j, f (P j) = f z - f (P i) := by
  have h₁ := Finset.sum_erase_add Finset.univ (fun j ↦ f (P j)) (Finset.mem_univ i)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j ↦ f (Function.update P i z j)) (Finset.mem_univ i)
  have h₃ : (∑ j ∈ Finset.univ.erase i, f (Function.update P i z j)) =
      ∑ j ∈ Finset.univ.erase i, f (P j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h₃, Function.update_self] at h₂
  linarith

lemma pairSum_left (f : BitString n → BitString n → ℝ) (P Q : Population n μ) (d : Fin μ)
    (z : BitString n) :
    pairSum f (Function.update P d z) Q - pairSum f P Q =
      ∑ i, (f z (Q i) - f (P d) (Q i)) := by
  have hh := sum_update P d z (fun x ↦ ∑ j, f x (Q j))
  simpa only [pairSum, Finset.sum_sub_distrib] using hh

lemma pairSum_swap (f : BitString n → BitString n → ℝ) (hsym : ∀ x y, f x y = f y x)
    (P Q : Population n μ) : pairSum f P Q = pairSum f Q P := by
  unfold pairSum
  rw [Finset.sum_comm]
  simp_rw [hsym (P _) (Q _)]

lemma pairSum_update (f : BitString n → BitString n → ℝ)
    (hsym : ∀ x y, f x y = f y x) (hdiag : ∀ x, f x x = 0)
    (P : Population n μ) (d : Fin μ) (z : BitString n) :
    pairSum f (Function.update P d z) (Function.update P d z) - pairSum f P P =
      2 * ((∑ i, f z (P i)) - (∑ i, f (P d) (P i)) - f z (P d)) := by
  let Q := Function.update P d z
  have hl := pairSum_left f P P d z
  have hr := pairSum_left f P Q d z
  rw [pairSum_swap f hsym P Q] at hr
  have hx := sum_update P d z (f z)
  have hy := sum_update P d z (f (P d))
  simp only [hdiag, hsym (P d) z] at hx hy
  rw [Finset.sum_sub_distrib] at hl hr
  linarith

lemma pair_replace_delta (f : BitString n → BitString n → ℝ)
    (hsym : ∀ x y, f x y = f y x) (hdiag : ∀ x, f x x = 0)
    (P : Population n μ) (z : BitString n) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (fun d ↦ pairMean f (replace P z d) - pairMean f P) =
      (2 / ((μ : ℕ) + 1 : ℝ)) *
        ((1 - (1 / ((μ : ℕ) : ℝ))) * partnerMean f P z - pairMean f P) := by
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  rw [mean_uniform, Fin.sum_univ_castSucc]
  simp only [replace, Fin.lastCases_last, Fin.lastCases_castSucc, sub_self, add_zero,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hsum :
      (∑ i, (pairMean f (Function.update P i z) - pairMean f P)) =
        (2 / (((μ : ℕ) : ℝ) ^ 2)) *
          ((((μ : ℕ) : ℝ) - 1) * (∑ i, f z (P i)) - pairSum f P P) := by
    have heq (i : Fin μ) : pairMean f (Function.update P i z) - pairMean f P =
        (2 / (((μ : ℕ) : ℝ) ^ 2)) *
          ((∑ j, f z (P j)) - (∑ j, f (P i) (P j)) - f z (P i)) := by
      unfold pairMean
      rw [← sub_div, pairSum_update f hsym hdiag]
      ring
    simp_rw [heq]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pairSum]
    ring
  rw [hsum]
  unfold partnerMean pairMean
  have hD : (0 : ℝ) < (μ : ℕ) + 1 := by linarith
  field_simp

end
end Lax637351Proofs.PairAveraging
