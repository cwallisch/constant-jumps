import Lax637351Proofs.PairStep

namespace Lax637351Proofs.RareDrift

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def retain (B : ℝ) (k n : ℕ) (μ : ℕ+) : ℝ :=
  1 - 2 * (B + k) / ((μ : ℕ) * n)

def advance (n : ℕ) (μ : ℕ+) : ℝ := 1 / (64 * (μ : ℕ) * n)

def parentAverage (j : Fin μ) (r : ℕ) (P : Population n μ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin μ)) (fun u ↦ if u ≠ j then indicator (pairGood u j r P) else 0)

lemma oneStep_pair (hk : 2 ≤ k) (hn : 4 * k ≤ n) (B p : ℝ)
    (hB : 0 < B) (hp : 0 ≤ p ∧ p ≤ 1 / 2) (hpB : p ≤ B / n)
    (P : Population n μ) (hP : ¬ missing P ∨ plateau (k := k) P)
    (i j : Fin μ) (hij : i ≠ j) (r : ℕ) (hr : r < k) :
    retain B k n μ * indicator (pairGood i j (r + 1) P) +
      advance n μ * parentAverage j r P ≤
        mean (step (jump k) p true P) (fun Q ↦ indicator (pairGood i j (r + 1) Q)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hμ : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hμ' : (0 : ℝ) < (μ : ℕ) := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  let D : ℝ := (μ : ℕ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let A := indicator (pairGood i j (r + 1) P)
  let E := parentAverage j r P
  have hA : 0 ≤ A := indic_nonneg _
  have hE : 0 ≤ E := by
    apply mean_nonneg
    intro u
    split_ifs
    · exact indic_nonneg _
    · exact le_rfl
  have ht : advance n μ ≤ (1 - p) / (16 * (n : ℝ) * D) := by
    unfold advance
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - p by linarith [hp.2])
      (show 0 ≤ 64 * ((μ : ℕ) : ℝ) * n by positivity)
    dsimp [D]
    nlinarith [mul_nonneg (show 0 ≤ ((μ : ℕ) : ℝ) - 1 by linarith) hn'.le]
  rcases hP with hsucc | hplat
  · have hA' : A = 1 := by simp [A, pairGood, indicator, hsucc]
    have hE' : E ≤ 1 := by
      apply (mean_mono _ ?_).trans_eq (mean_const _ 1)
      intro u
      split_ifs
      · exact indic_le_one _
      · norm_num
    have hh : advance n μ ≤ 2 * (B + k) / ((μ : ℕ) * n : ℝ) := by
      unfold advance
      have h₀ : (0 : ℝ) < (μ : ℕ) * n := by positivity
      rw [show 64 * ((μ : ℕ) : ℝ) * n = 64 * (((μ : ℕ) : ℝ) * n) by ring, div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right (by linarith) h₀.le
    have hm : mean (step (jump k) p true P) (fun Q ↦ indicator (pairGood i j (r + 1) Q)) = 1 := by
      apply mean_supported_const
      intro Q hQ
      have hQQ := step_preserves_optimum (show 0 < k by omega) p true hsucc hQ
      simp [pairGood, indicator, hQQ]
    change retain B k n μ * A + advance n μ * E ≤ _
    rw [hm, hA', mul_one, retain]
    have hb := mul_le_mul_of_nonneg_left hE' (show 0 ≤ advance n μ by unfold advance; positivity)
    linarith
  · by_cases hmiss : missing P
    · have hc (y m : BitString n) :=
        crossover_pair_lower (show 0 < k by omega) (show k ≤ n by omega)
          P hmiss hplat i j hij (r + 1) y m
      have hC := (mean_const (parents P true) ((1 - 2 / D) * A)).symm.le.trans
        (mean_mono _ (fun y ↦ (mean_const (Lax637351.Algorithm.independentBits n (1 / (n : ℝ)))
          ((1 - 2 / D) * A)).symm.le.trans (mean_mono _ (hc y))))
      have hM := mean_mono (PMF.uniformOfFintype (Fin μ)) (fun u ↦
        mutation_pair_lower (show 0 < k by omega) hn P hmiss hplat i j u hij r hr)
      change mean _ (fun u ↦ (1 - 2 / D * ((k : ℝ) / n)) * A +
          (if u ≠ j then indicator (pairGood u j r P) else 0) / (16 * n * D)) ≤ _ at hM
      have heq : (fun u : Fin μ ↦ (1 - 2 / D * ((k : ℝ) / n)) * A +
          (if u ≠ j then indicator (pairGood u j r P) else 0) / (16 * n * D)) =
          (fun u : Fin μ ↦ (1 - 2 / D * ((k : ℝ) / n)) * A +
            (16 * (n : ℝ) * D)⁻¹ * (if u ≠ j then indicator (pairGood u j r P) else 0)) := by
        funext u
        simp only [div_eq_mul_inv, mul_comm]
      rw [heq] at hM
      rw [mean_add, mean_const, mean_mul] at hM
      change _ + (16 * (n : ℝ) * D)⁻¹ * E ≤ _ at hM
      rw [mean_step ⟨hp.1, by linarith [hp.2]⟩]
      have hsum := add_le_add (mul_le_mul_of_nonneg_left hC hp.1)
        (mul_le_mul_of_nonneg_left hM (show 0 ≤ 1 - p by linarith [hp.2]))
      apply le_trans _ hsum
      have hd : (2 / D) ≤ 2 / ((μ : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hμ'
        simp [D]
      have hinner : p + (1 - p) * ((k : ℝ) / n) ≤ (B + k) / n := by
        have hh := mul_nonneg hp.1 (show 0 ≤ (k : ℝ) / n by positivity)
        rw [add_div]
        nlinarith
      have hcoeff : (2 / D) * (p + (1 - p) * ((k : ℝ) / n)) ≤
          2 * (B + k) / ((μ : ℕ) * n : ℝ) := by
        calc
          _ ≤ (2 / D) * ((B + k) / n) := mul_le_mul_of_nonneg_left hinner (by positivity)
          _ ≤ (2 / ((μ : ℕ) : ℝ)) * ((B + k) / n) :=
            mul_le_mul_of_nonneg_right hd (by positivity)
          _ = _ := by ring
      have hret : retain B k n μ ≤
          p * (1 - 2 / D) + (1 - p) * (1 - 2 / D * ((k : ℝ) / n)) := by
        unfold retain
        nlinarith only [hcoeff]
      have hf := mul_le_mul_of_nonneg_right hret hA
      have hE' := mul_le_mul_of_nonneg_right ht hE
      change retain B k n μ * A + advance n μ * E ≤ _
      simp only [div_eq_mul_inv] at hE'
      nlinarith only [hf, hE']
    · have hsucc : ¬ missing P := hmiss
      exfalso
      obtain ⟨u, hu⟩ : ∃ u, P u = optimum n := by simpa [missing] using hsucc
      have hh := hplat u
      rw [hu, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hh
      omega

end
end Lax637351Proofs.RareDrift
