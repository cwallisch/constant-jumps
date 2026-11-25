import Lax637351Proofs.ColumnCrossDrift

namespace Lax637351Proofs.ColumnMutationDrift

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnSlot
open Lax637351Proofs.PlateauKernel Lax637351Proofs.ColumnEvents Lax637351Proofs.ColumnReplacement
open Lax637351Proofs.ColumnContrast Lax637351Proofs.ColumnCrossDrift Lax637351Proofs.PlateauChanges
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

lemma frequency_valid (k : ℕ) (P : Population n μ) (i : Fin n) :
    0 ≤ frequency k i P ∧ frequency k i P ≤ 1 := by
  rw [← mutation_frequency k P i]
  exact ⟨mean_nonneg _ (fun _ ↦ indic_nonneg _),
    (mean_mono _ (fun _ ↦ indic_le_one _)).trans_eq (mean_const _ 1)⟩

lemma neutral_copy_drift (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) :
    -(4 * remainderLimit T / ((μ : ℕ) : ℝ)) * (3 * frequency k i P) ≤
      slotMean (replaceMean k i H P) P := by
  let f := frequency k i P
  let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
  let g := ColumnEmpirical.rawGradient (ColumnEmpirical.responseMap i (eps μ) H (ColumnEmpirical.empiricalWeights P hP))
  let ν := PMF.uniformOfFintype (Fin μ)
  have h (u : Fin μ) :
      coeff μ * (g (P u) - slotMean g P) - R * (2 * f + indicator (P u i = 1)) ≤ replaceMean k i H P (P u) :=
    (replaceMean_lower i H hH T hT P hP (P u) (hP u)).2
  have hh := mean_mono ν h
  rw [mean_sub, mean_mul, mean_sub, mean_const, ← slotMean_eq, sub_self, mul_zero,
    mean_mul, mean_add, mean_const, mutation_frequency, zero_sub] at hh
  rw [slotMean_eq]
  change -R * (3 * f) ≤ _
  change -(R * (2 * f + f)) ≤ _ at hh
  nlinarith only [hh]

def mutateMean (P : Population n μ) (g : BitString n → BitString n → ℝ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin μ)) fun u ↦ mean (independentBits n (1 / (n : ℝ))) fun m ↦
    g (P u) (mutate (P u) m)

lemma mutateMean_mono (P : Population n μ) (g h : BitString n → BitString n → ℝ)
    (hg : ∀ u : Fin μ, ∀ z, g (P u) z ≤ h (P u) z) :
    mutateMean P g ≤ mutateMean P h :=
  mean_mono _ (fun u ↦ mean_mono _ (fun m ↦ hg u (mutate (P u) m)))

lemma mutateMean_sub (P : Population n μ) (g h : BitString n → BitString n → ℝ) :
    mutateMean P (fun x z ↦ g x z - h x z) = mutateMean P g - mutateMean P h := by
  unfold mutateMean
  simp_rw [mean_sub]

lemma mutateMean_mul (P : Population n μ) (a : ℝ) (g : BitString n → BitString n → ℝ) :
    mutateMean P (fun x z ↦ a * g x z) = a * mutateMean P g := by
  unfold mutateMean
  simp_rw [mean_mul]

def changed (k : ℕ) (x z : BitString n) : Prop := (zeros z).card = k ∧ z ≠ x

lemma mutant_changed_upper (hn : 2 ≤ n) (i : Fin n) (P : Population n μ) (hP : plateau (k := k) P) :
    mutateMean P (fun x z ↦ indicator (x i = 1) * indicator (changed k x z)) ≤
      frequency k i P * ((k : ℝ) / n) := by
  unfold mutateMean
  simp_rw [mean_mul]
  have h := mean_mono (PMF.uniformOfFintype (Fin μ)) (fun u ↦
    mul_le_mul_of_nonneg_left (changed_mutation_row hn (P u) (hP u)) (indic_nonneg (P u i = 1)))
  simp_rw [mul_comm _ ((k : ℝ) / n)] at h
  rw [mean_mul, mutation_frequency] at h
  rwa [mul_comm]

lemma mutation_immigrant_lower (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (i : Fin n)
    (P : Population n μ) (hP : plateau (k := k) P) :
    (1 - frequency k i P) / (16 * n) ≤ mutateMean P (fun x z ↦ indicator (x i = 0 ∧ immigrant k i z)) := by
  unfold mutateMean
  have h (u : Fin μ) : (1 / (16 * (n : ℝ))) * indicator (P u i = 0) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (P u i = 0 ∧ immigrant k i (mutate (P u) m))) := by
    by_cases he : P u i = 0
    · have hh (m : BitString n) :
          (P u i = 0 ∧ immigrant k i (mutate (P u) m)) = immigrant k i (mutate (P u) m) :=
        propext ⟨And.right, And.intro he⟩
      rw [show indicator (P u i = 0) = 1 from if_pos he, mul_one]
      simp_rw [hh]
      exact mutation_immigrant hn hkn i (P u) (hP u) he
    · simp [indicator, he, mean_const]
  have hh := mean_mono (PMF.uniformOfFintype (Fin μ)) h
  rw [mean_mul, resident_frequency k P i] at hh
  convert hh using 1
  ring

lemma changed_mutation_drift (hn : 2 ≤ n) (hkn : 2 * k ≤ n) (i : Fin n) (H : ℕ) (hH : 0 < H)
    (T : ℝ) (hT : eps μ * H ≤ T) (P : Population n μ) (hP : plateau (k := k) P)
    (hf : frequency k i P < 1)
    (hf₁ : 24 * T * Real.exp (6 * T) * frequency k i P ≤ Real.exp (-2 * T) / 2)
    (hf₂ : (Real.exp (-2 * T) / 2 + 2 * responseLimit T) * frequency k i P ≤ Real.exp (-2 * T) / 4) :
    let f := frequency k i P
    let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
    coeff μ * (Real.exp (-2 * T) / 4) * (1 - f) / (16 * n) -
      (6 * responseLimit T * f + R) * (k : ℝ) / n ≤ changedMutation k P (replaceMean k i H P) := by
  let f := frequency k i P
  let A := Real.exp (-2 * T) / 4
  let B := responseLimit T
  let C := coeff μ
  let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
  let W := replaceMean k i H P
  let J := rawContrast k i H P hP
  let I (x z : BitString n) := indicator (x i = 0 ∧ immigrant k i z)
  let F (x z : BitString n) := indicator (changed k x z)
  let M (x z : BitString n) := indicator (x i = 1) * F x z
  have hT₀ := (mul_nonneg (eps_bounds μ).1.le (Nat.cast_nonneg H)).trans hT
  have hf0 : 0 ≤ f := (frequency_valid k P i).1
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (coeff_bounds μ).1
  have hA : 0 ≤ A := by unfold A; positivity
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  have hlocal (u : Fin μ) (z : BitString n) :
      C * (A * I (P u) z - 4 * B * f * F (P u) z - 2 * B * M (P u) z) - R * F (P u) z ≤
        F (P u) z * W z := by
    by_cases hc : changed k (P u) z
    · have hz := hc.1
      have hW := (replaceMean_lower i H hH T hT P hP z hz).1
      change C * J z - R ≤ W z at hW
      have hj : A * I (P u) z - 4 * B * f - 2 * B * indicator (P u i = 1) ≤ J z := by
        by_cases hU : P u i = 0
        · by_cases hZ : z i = 0
          · have h := contrast_resident_lower i H hH T hT P hP z hz hZ
            simpa only [I, immigrant, indicator, hU, hZ, Fin.zero_ne_one, and_false,
              if_false, mul_zero, zero_sub, sub_zero] using h
          · have h1 : z i = 1 := bit_eq_one_of_ne_zero _ hZ
            have hh : I (P u) z = 1 := if_pos ⟨hU, hz, h1⟩
            rw [hh, mul_one, show indicator (P u i = 1) = 0 by simp [indicator, hU], mul_zero, sub_zero]
            have h := contrast_immigrant_lower hn i H hH T hT P hP z hz h1 hf hf₁ hf₂
            exact (sub_le_self _ (mul_nonneg (mul_nonneg (by norm_num) hB) hf0)).trans h
        · have h1 : P u i = 1 := bit_eq_one_of_ne_zero _ hU
          rw [show I (P u) z = 0 from if_neg (fun h ↦ hU h.1), mul_zero,
            show indicator (P u i = 1) = 1 from if_pos h1, mul_one]
          have h := contrast_lower i H hH T hT P hP z hz
          linarith only [h, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hB) hf0]
      have he : F (P u) z = 1 := if_pos hc
      simp only [M, he, mul_one, one_mul]
      exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hj hC) _).trans hW
    · have hI : I (P u) z = 0 := by
        apply if_neg
        rintro ⟨hU, hZ, hbit⟩
        exact hc ⟨hZ, fun he ↦ Fin.zero_ne_one ((congrFun he i).trans hU |>.symm.trans hbit)⟩
      simp [M, show F (P u) z = 0 from if_neg hc, hI]
  have hm := mutateMean_mono P
    (fun x z ↦ C * (A * I x z - 4 * B * f * F x z - 2 * B * M x z) - R * F x z)
    (fun x z ↦ F x z * W z) hlocal
  rw [mutateMean_sub, mutateMean_mul, mutateMean_sub, mutateMean_sub, mutateMean_mul,
    mutateMean_mul, mutateMean_mul, mutateMean_mul] at hm
  have hW : mutateMean P (fun x z ↦ F x z * W z) = changedMutation k P W := rfl
  rw [hW] at hm
  have hI := mutation_immigrant_lower hn hkn i P hP
  have hM := mutant_changed_upper hn i P hP
  have hF : mutateMean P F ≤ (k : ℝ) / n :=
    (mean_mono (PMF.uniformOfFintype (Fin μ)) (fun u ↦ changed_mutation_row hn (P u) (hP u))).trans_eq
      (mean_const _ _)
  change (1 - f) / (16 * n) ≤ mutateMean P I at hI
  change mutateMean P M ≤ f * ((k : ℝ) / n) at hM
  have h₁ := mul_le_mul_of_nonneg_left hI (mul_nonneg hC hA)
  have h₂ := mul_le_mul_of_nonneg_left hF (mul_nonneg (mul_nonneg hC (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hB)) hf0)
  have h₃ := mul_le_mul_of_nonneg_left hM (mul_nonneg (mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 2)) hB)
  have h₄ := mul_le_mul_of_nonneg_left hF hR
  have h₅ := mul_le_mul_of_nonneg_right (coeff_bounds μ).2
    (show 0 ≤ 6 * B * f * ((k : ℝ) / n) from mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hf0) (by positivity))
  change C * (6 * B * f * ((k : ℝ) / n)) ≤ _ at h₅
  change C * A * (1 - f) / (16 * n) - (6 * B * f + R) * (k : ℝ) / n ≤ changedMutation k P W
  have ht := (add_le_add (add_le_add h₂ h₃) h₄).trans
    (show C * (4 * B) * f * ((k : ℝ) / n) + C * 2 * B * (f * ((k : ℝ) / n)) + R * ((k : ℝ) / n) ≤
      (6 * B * f + R) * (k : ℝ) / n from by
        calc
          _ = C * (6 * B * f * ((k : ℝ) / n)) + R * ((k : ℝ) / n) := by ring
          _ ≤ _ := (add_le_add_left h₅ (R * ((k : ℝ) / n))).trans_eq (by ring))
  calc
    _ = C * A * ((1 - f) / (16 * n)) - (6 * B * f + R) * (k : ℝ) / n := by ring
    _ ≤ C * A * mutateMean P I -
        (C * (4 * B) * f * mutateMean P F + C * 2 * B * mutateMean P M + R * mutateMean P F) :=
      sub_le_sub h₁ ht
    _ ≤ _ := (by
      rw [show C * A * mutateMean P I -
        (C * (4 * B) * f * mutateMean P F + C * 2 * B * mutateMean P M + R * mutateMean P F) =
        C * (A * mutateMean P I - 4 * B * f * mutateMean P F - 2 * B * mutateMean P M) - R * mutateMean P F by ring]
      exact hm)

end
end Lax637351Proofs.ColumnMutationDrift
