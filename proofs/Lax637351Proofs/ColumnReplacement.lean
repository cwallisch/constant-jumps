import Lax637351Proofs.ColumnSlot

namespace Lax637351Proofs.ColumnReplacement

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnGain
open Lax637351Proofs.ColumnPrediction Lax637351Proofs.ColumnNormBounds Lax637351Proofs.ColumnAverages
open Lax637351Proofs.ColumnEmpirical Lax637351Proofs.ColumnGradient Lax637351Proofs.ColumnSlot
open Lax637351Proofs.PlateauKernel Lax637351Proofs.Auxiliary
open Lax637351Proofs.SpeciesDrift (genotypeList step_relation)
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def rawContrast (k : ℕ) (i : Fin n) (H : ℕ) (P : Population n μ) (hP : plateau (k := k) P)
    (z : BitString n) : ℝ :=
  let g := rawGradient (responseMap i (eps μ) H (empiricalWeights P hP))
  g z - slotMean g P

def replaceMean (k : ℕ) (i : Fin n) (H : ℕ) (P : Population n μ) (z : BitString n) : ℝ :=
  mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (fun d ↦
    populationPotential k i H (replace P z d) - populationPotential k i H P)

lemma update_plateau (P : Population n μ) (hP : plateau (k := k) P)
    (z : BitString n) (hz : (zeros z).card = k) (d : Fin μ) :
    plateau (k := k) (Function.update P d z) := by
  intro j
  by_cases h : j = d
  · subst j
    simpa only [Function.update_self] using hz
  · simpa only [Function.update_of_ne h] using hP j

lemma gradient_replacement (k : ℕ) (i : Fin n) (H : ℕ) (P : Population n μ) (hP : plateau (k := k) P)
    (z : BitString n) (hz : (zeros z).card = k) (d : Fin μ) :
    let g := rawGradient (responseMap i (eps μ) H (empiricalWeights P hP))
    meanResponse i (eps μ) H (empiricalWeights P hP) (atom (ofString z hz) - atom (genotypeList P hP d)) =
      ((μ : ℕ) : ℝ) * (slotMean g (Function.update P d z) - slotMean g P) := by
  let w := empiricalWeights P hP
  let Q := Function.update P d z
  let hQ := update_plateau P hP z hz d
  have h := empirical_delta_gradient i (eps μ) H P Q hP hQ
  rw [empirical_replace P hP z hz d hQ, meanResponse_smul] at h
  have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  dsimp only
  dsimp only [Q] at h
  rw [← h]
  field_simp

lemma replaceMean_lower (i : Fin n) (H : ℕ) (hH : 0 < H) (T : ℝ) (hT : eps μ * H ≤ T)
    (P : Population n μ) (hP : plateau (k := k) P) (z : BitString n) (hz : (zeros z).card = k) :
    let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
    let J := coeff μ * rawContrast k i H P hP z
    J - R ≤ replaceMean k i H P z ∧
      J - R * (2 * frequency k i P + indicator (z i = 1)) ≤ replaceMean k i H P z := by
  let R := 4 * remainderLimit T / ((μ : ℕ) : ℝ)
  let G := populationPotential (μ := μ) k i H
  let w := empiricalWeights P hP
  let f := frequency k i P
  let g := rawGradient (responseMap i (eps μ) H w)
  let ν := PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))
  let L (d : Fin ((μ : ℕ) + 1)) := ((μ : ℕ) : ℝ) * (slotMean g (replace P z d) - slotMean g P)
  let Δ (d : Fin ((μ : ℕ) + 1)) := G (replace P z d) - G P
  let D (d : Fin ((μ : ℕ) + 1)) : ℝ := Fin.lastCases 0 (fun u ↦ indicator (P u i = 1)) d
  have hT₀ := (mul_nonneg (eps_bounds μ).1.le (Nat.cast_nonneg H)).trans hT
  have hR : 0 ≤ R := by unfold R remainderLimit normLimit; positivity
  have hf : 0 ≤ f := by unfold f; rw [← empirical_fraction i P hP]; exact (fraction_bounds i w (empirical_probability P hP)).1
  have hpoint (d : Fin ((μ : ℕ) + 1)) :
      L d - R ≤ Δ d ∧ L d - R * (f + D d + indicator (z i = 1)) ≤ Δ d := by
    refine Fin.lastCases ?_ (fun u ↦ ?_) d
    · have hr : 0 ≤ R * (f + D (Fin.last (μ : ℕ)) + indicator (z i = 1)) := by
        unfold D
        rw [Fin.lastCases_last]
        exact mul_nonneg hR (add_nonneg (add_nonneg hf (le_refl 0)) (indic_nonneg _))
      simp only [L, Δ, replace, Fin.lastCases_last, sub_self, mul_zero, zero_sub]
      exact ⟨neg_nonpos.mpr hR, neg_nonpos.mpr hr⟩
    · let Q := Function.update P u z
      let hQ := update_plateau P hP z hz u
      have he := replacement_error i H hH T hT P hP z hz u hQ
      have hg := gradient_replacement k i H P hP z hz u
      dsimp only at he hg
      rw [hg, empirical_fraction i P hP] at he
      have hA := (abs_le.mp he.1).1
      change L u.castSucc - R ≤ Δ u.castSucc ∧ _
      constructor
      · simp only [L, Δ, replace, Fin.lastCases_castSucc]
        linarith only [hA]
      · by_cases hz0 : z i = 0 <;> by_cases hu : P u i = 0
        · have hh := (abs_le.mp (he.2 hz0 hu)).1
          simp only [L, Δ, D, replace, Fin.lastCases_castSucc, indicator, hz0, hu, Fin.zero_ne_one,
            if_false, add_zero]
          nlinarith only [hh]
        all_goals
          have hir : R ≤ R * (f + D u.castSucc + indicator (z i = 1)) := by
            simp only [D, Fin.lastCases_castSucc]
            have hf' : 1 ≤ f + indicator (P u i = 1) + indicator (z i = 1) := by
              first
              | rw [show indicator (P u i = 1) = 1 from if_pos (bit_eq_one_of_ne_zero _ hu)]
                linarith only [hf, indic_nonneg (z i = 1)]
              | rw [show indicator (z i = 1) = 1 from if_pos (bit_eq_one_of_ne_zero _ hz0)]
                linarith only [hf, indic_nonneg (P u i = 1)]
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hf' hR
          simp only [L, Δ, replace, Fin.lastCases_castSucc] at *
          linarith only [hA, hir]
  have hL : mean ν L = coeff μ * rawContrast k i H P hP z := by
    unfold L ν
    rw [mean_mul, slot_replace_delta, coeff, rawContrast, eps]
    change ((μ : ℕ) : ℝ) * ((g z - slotMean g P) / ((μ : ℕ) + 1)) =
      ((μ : ℕ) : ℝ) * (1 / ((μ : ℕ) + 1 : ℝ)) * (g z - slotMean g P)
    ring
  have hD : mean ν D ≤ f := by
    unfold ν D f frequency slotMean
    rw [mean_uniform, Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, add_zero, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    have hM : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
    rw [mul_comm, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left _ hM (by linarith)
    exact Finset.sum_nonneg (fun _ _ ↦ indic_nonneg _)
  constructor
  · have h := mean_mono ν (fun d ↦ (hpoint d).1)
    rwa [mean_sub, mean_const, hL] at h
  · have h := mean_mono ν (fun d ↦ (hpoint d).2)
    rw [mean_sub, hL, mean_mul, mean_add, mean_add, mean_const, mean_const] at h
    have hd := mul_le_mul_of_nonneg_left hD hR
    change _ ≤ mean ν Δ
    nlinarith only [h, hd]

lemma column_step_bound (hk : 0 < k) (hkn : k ≤ n) (i : Fin n) (H : ℕ) (hH : 0 < H)
    (T : ℝ) (hT : eps μ * H ≤ T) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (Q : Population n μ)
    (hQ : Q ∈ (auxiliary k p ar P).support) :
    |populationPotential k i H Q - populationPotential k i H P| ≤ 2 * Real.exp (3 * T) := by
  obtain ⟨z, d, he⟩ := step_relation hk hkn p ar P hP Q hQ
  subst Q
  revert hQ
  refine Fin.lastCases ?_ (fun j ↦ ?_) d
  · intro hQ
    simp [replace, (Real.exp_pos _).le]
  · intro hQ
    have hpl := auxiliary_preserves_plateau hk hkn p ar P hP _ hQ
    simp only [replace, Fin.lastCases_castSucc] at hpl ⊢
    have hz : (zeros z).card = k := by have h := hpl j; rwa [Function.update_self] at h
    rw [populationPotential, dif_pos hpl, populationPotential, dif_pos hP, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (μ : ℕ))]
    let w := empiricalWeights P hP
    let v := empiricalWeights (Function.update P j z) hpl
    have he := eps_bounds μ
    have hh := meanPotential_lipschitz i (eps μ) ⟨he.1.le, by linarith [he.2]⟩ H hH T hT
      w v (empirical_probability P hP) (empirical_probability _ hpl)
    have hδ : variation (v - w) ≤ 2 / ((μ : ℕ) : ℝ) := by
      unfold v w
      rw [empirical_replace P hP z hz j hpl, variation_smul, abs_of_nonneg (by positivity)]
      have h := mul_le_mul_of_nonneg_left (variation_atom_diff (ofString z hz) (genotypeList P hP j))
        (show 0 ≤ 1 / ((μ : ℕ) : ℝ) by positivity)
      exact h.trans_eq (by ring)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le)
    apply (mul_le_mul_of_nonneg_left hh' (by positivity : (0 : ℝ) ≤ (μ : ℕ))).trans_eq
    have hm : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
    field_simp

end
end Lax637351Proofs.ColumnReplacement
