import Lax637351Proofs.ColumnMutationDrift

namespace Lax637351Proofs.ColumnDriftBound

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.PlateauPairs
open Lax637351Proofs.ColumnSlot Lax637351Proofs.ColumnEvents Lax637351Proofs.ColumnReplacement
open Lax637351Proofs.ColumnCrossDrift Lax637351Proofs.ColumnMutationDrift Lax637351Proofs.PlateauChanges
open Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnEmpirical
open Lax637351Proofs.PredictionNorm Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnGain
open Lax637351Proofs.Auxiliary Lax637351Proofs.PairSignal Lax637351Proofs.PlateauKernel
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def entryRate (k : ℕ) (T : ℝ) : ℝ := (Real.exp (-2 * T) / 4) * immigrationRate k / 16

lemma entryRate_pos (k : ℕ) (T : ℝ) : 0 < entryRate k T :=
  div_pos (mul_pos (div_pos (Real.exp_pos _) (by norm_num)) (immigrationRate_pos k)) (by norm_num)

lemma immigrationRate_small (k : ℕ) : immigrationRate k ≤ 1 / 16 := by
  unfold immigrationRate
  have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := 2 * k)
  linarith only [h]

lemma column_increment (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (hk : 0 < k) (i : Fin n)
    (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H = T)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P)
    (hf : frequency k i P ≤ 1 / 2)
    (hf₁ : 24 * T * Real.exp (6 * T) * frequency k i P ≤ Real.exp (-2 * T) / 2)
    (hf₂ : (Real.exp (-2 * T) / 2 + 2 * responseLimit T) * frequency k i P ≤ Real.exp (-2 * T) / 4)
    (hf₃ : 6 * responseLimit T * frequency k i P * (k : ℝ) ≤ (Real.exp (-2 * T) / 4) / 256)
    (hsmall : 48 * remainderLimit T * eps μ * T ≤ 1)
    (hR₁ : (4 * remainderLimit T / ((μ : ℕ) : ℝ)) ≤ 1 / (16 * T))
    (hR₂ : (4 * remainderLimit T / ((μ : ℕ) : ℝ)) ≤ entryRate k T)
    (hR₃ : (4 * remainderLimit T / ((μ : ℕ) : ℝ)) * (k : ℝ) ≤ (Real.exp (-2 * T) / 4) / 256)
    (hcopy : 3 * (4 * remainderLimit T / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * T))
    (hg : 3 * frequency k i P ≤ fraction i (predict (replaceKernel i) (eps μ) H (empiricalWeights P hP))) :
    p * frequency k i P / (8 * T) + entryRate k T / n ≤ mean (auxiliary k p ar P)
      (fun Q ↦ populationPotential k i H Q - populationPotential k i H P) := by
  let f := frequency k i P
  let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
  let A := Real.exp (-2 * T) / 4
  let b := immigrationRate k
  let L := entryRate k T
  let C := coeff μ
  let W := replaceMean k i H P
  have hT' : 0 < T := hT ▸ mul_pos (eps_bounds μ).1 (by exact_mod_cast hH)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hf0 : 0 ≤ f := (frequency_valid k P i).1
  have hA : 0 ≤ A := by unfold A; positivity
  have hb : 0 ≤ b := (immigrationRate_pos k).le
  have hL : 0 ≤ L := (entryRate_pos k T).le
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (coeff_bounds μ).1
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  have hC₁ : (1 / 2 : ℝ) ≤ C := (coeff_bounds μ).1
  change f ≤ 1 / 2 at hf
  have hx := crossover_drift_lower hn hkn i H hH T hT hsmall P hP (by linarith only [hf]) hf₁ hf₂ hg
  dsimp only at hx
  change C * (f / T + A * (b / n) * (1 - f) ^ 2) - R * (4 * f + 1 / n) ≤ crossed k P W at hx
  have hm := changed_mutation_drift hn hkn i H hH T hT.le P hP (by linarith only [hf]) hf₁ hf₂
  dsimp only at hm
  change C * A * (1 - f) / (16 * n) - (6 * responseLimit T * f + R) * (k : ℝ) / n ≤ changedMutation k P W at hm
  have hc := neutral_copy_drift i H hH T hT.le P hP
  change -R * (3 * f) ≤ slotMean W P at hc
  have hx' : f / (4 * T) + L / n ≤ crossed k P W := by
    have hq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith only [hf])).mpr
      (show (1 / 2 : ℝ) ≤ 1 - f by linarith only [hf])
    have ha := mul_le_mul_of_nonneg_left hq (mul_nonneg hA (div_nonneg hb hn'.le))
    have hfeed : 4 * L / n ≤ A * (b / n) * (1 - f) ^ 2 := by
      have he : 4 * L / n = A * (b / n) * (1 / 2) ^ 2 := by
        change 4 * (A * b / 16) / n = _
        ring
      rw [he]
      exact ha
    have hfeed' := mul_le_mul_of_nonneg_left (add_le_add_left hfeed (f / T)) hC
    have hpos : 0 ≤ f / T + 4 * L / n := by positivity
    have hcoef := mul_le_mul_of_nonneg_right hC₁ hpos
    change R ≤ 1 / (16 * T) at hR₁
    change R ≤ L at hR₂
    have hloss := add_le_add (mul_le_mul_of_nonneg_right hR₁ (show 0 ≤ 4 * f by positivity))
      (mul_le_mul_of_nonneg_right hR₂ (show 0 ≤ 1 / (n : ℝ) by positivity))
    have hEq : (1 : ℝ) / (16 * T) * (4 * f) + L * (1 / (n : ℝ)) = f / (4 * T) + L / n := by ring
    nlinarith only [hx, hfeed', hcoef, hloss, hEq, show (1 / 2 : ℝ) * (f / T + 4 * L / n) = 2 * (f / (4 * T)) + 2 * (L / n) by ring]
  have hm' : L / n ≤ changedMutation k P W := by
    have hgain := mul_le_mul hC₁ (show (1 / 2 : ℝ) ≤ 1 - f by linarith only [hf])
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hC
    have hgain' := mul_le_mul_of_nonneg_right hgain (div_nonneg hA (by positivity : 0 ≤ 16 * (n : ℝ)))
    change (6 * responseLimit T * f) * (k : ℝ) ≤ A / 256 at hf₃
    change R * (k : ℝ) ≤ A / 256 at hR₃
    have hloss := div_le_div_of_nonneg_right (add_le_add hf₃ hR₃) hn'.le
    have hk' := mul_le_mul_of_nonneg_left (immigrationRate_small k) hA
    have hL' : L ≤ A / 256 := by change A * b / 16 ≤ A / 256; nlinarith only [hk']
    have hb' := div_le_div_of_nonneg_right hL' hn'.le
    have halve : A / 256 / n ≤ A / 128 / n :=
      div_le_div_of_nonneg_right (by linarith only [hA]) hn'.le
    calc
      L / n ≤ A / 128 / n := hb'.trans halve
      _ = (1 / 2 : ℝ) * (1 / 2) * (A / (16 * n)) - (A / 256 + A / 256) / n := by ring
      _ ≤ C * (1 - f) * (A / (16 * n)) - (6 * responseLimit T * f * k + R * k) / n :=
        sub_le_sub hgain' hloss
      _ ≤ changedMutation k P W := by
        exact (show _ = C * A * (1 - f) / (16 * n) - (6 * responseLimit T * f + R) * (k : ℝ) / n by ring).le.trans hm
  rw [aux_mean_proposal hk (by omega : k ≤ n) p hp ar P hP i H]
  have qnon := copyRate_nonneg n p hp.2 ar
  have h₁ := mul_le_mul_of_nonneg_left hx' hp.1
  have h₂ := mul_le_mul_of_nonneg_left hm' (sub_nonneg.mpr hp.2)
  have h₃ := mul_le_mul_of_nonneg_left hc qnon
  change 3 * R * copyRate n p ar ≤ p / (8 * T) at hcopy
  have h₄ := mul_le_mul_of_nonneg_right hcopy hf0
  change p * f / (8 * T) + L / n ≤ p * crossed k P W + (1 - p) * changedMutation k P W + copyRate n p ar * slotMean W P
  have h₅ : -(p / (8 * T) * f) ≤ copyRate n p ar * (-R * (3 * f)) :=
    (neg_le_neg h₄).trans_eq (by ring)
  calc
    _ = p * (f / (4 * T) + L / n) + (1 - p) * (L / n) + -(p / (8 * T) * f) := by ring
    _ ≤ _ := add_le_add (add_le_add h₁ h₂) (h₅.trans h₃)

end
end Lax637351Proofs.ColumnDriftBound
