import Lax637351Proofs.TapeConcentration
import Lax637351Proofs.BestRank

namespace Lax637351Proofs.Descent

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.TapeDraw Lax637351Proofs.TapeRun Lax637351Proofs.Independent
open Lax637351Proofs.Mutation Lax637351Proofs.SparseDeviation Lax637351Proofs.TapeConcentration
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.FiniteChain Lax637351Proofs.MarkedStep Lax637351Proofs.BestRank
open Lax637351Proofs.OffspringProduct
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def childBit (c : Fin 2 × Fin 2) (x y : Fin 2) : Fin 2 :=
  let b := if c.1 = 1 then x else y
  if c.2 = 1 then 1 - b else b

lemma mean_childBit (hn : 2 ≤ n) (x y : Fin 2) :
    mean (coordinateLaw n) (fun c ↦ zeroBit (childBit c x y)) =
      (1 / (n : ℝ)) + (1 - 2 / (n : ℝ)) * ((zeroBit x + zeroBit y) / 2) := by
  let a : Index (⟨2, by decide⟩ : ℕ+) := (true, ⟨0, by decide⟩, ⟨1, by decide⟩)
  let v : Fin 2 → Fin 2 := Fin.cases x (fun _ ↦ y)
  exact mean_bitProposal hn a v

lemma pairMutation_product (hn : 2 ≤ n) (x y : BitString n) :
    pairMutation x y (1 / (n : ℝ)) =
      (product (fun _ : Fin n ↦ coordinateLaw n)).map (fun c j ↦ childBit (c j) (x j) (y j)) := by
  rw [product_map (fun _ : Fin n ↦ coordinateLaw n) (fun j c ↦ childBit c (x j) (y j))]
  ext w
  rw [pairMutation_apply _ _ _ _ (rate_valid hn), product_apply]
  apply Finset.prod_congr rfl
  intro j _
  have h := site_probability_sum (x j) (y j) (w j) (1 / (n : ℝ)) (rate_valid hn)
  rw [← h, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [coordinateLaw_apply]
  by_cases he : (w j) = childBit (b, f) (x j) (y j)
  · simp [he, childBit]
  · have hd : childBit (b, f) (x j) (y j) ≠ w j := Ne.symm he
    simp only [childBit] at he hd
    simp only [childBit, if_neg he, if_neg hd, mul_zero]

lemma proposal_tail_pair (hn : 2 ≤ n) (x y : BitString n) (r d lam : ℝ)
    (hr : r ≤ (n : ℝ) / 2) (hx : r ≤ ((zeros x).card : ℝ)) (hy : r ≤ ((zeros y).card : ℝ))
    (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    mean (pairMutation x y (1 / (n : ℝ))) (fun z ↦ indicator (((zeros z).card : ℝ) < r - d)) ≤
      Real.exp (r * lam ^ 2 - lam * d) := by
  let C := product (fun _ : Fin n ↦ coordinateLaw n)
  let G (j : Fin n) (c : Fin 2 × Fin 2) := childBit c (x j) (y j) = 0
  let g := countMean (fun _ : Fin n ↦ coordinateLaw n) G
  have hg : r ≤ g := by
    have he : g = 1 + (1 - 2 / (n : ℝ)) * ((((zeros x).card : ℝ) + ((zeros y).card : ℝ)) / 2) := by
      change (∑ j : Fin n, mean (coordinateLaw n) (fun c ↦ zeroBit (childBit c (x j) (y j)))) = _
      simp_rw [mean_childBit hn]
      have hs : (∑ i : Fin n, (zeroBit (x i) + zeroBit (y i)) / 2) =
          (((zeros x).card : ℝ) + ((zeros y).card : ℝ)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← zero_count_as_score, ← zero_count_as_score]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [he]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnn : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hcoef : 0 ≤ 1 - 2 / (n : ℝ) := sub_nonneg.mpr ((div_le_one hn').mpr hnn)
    have ha := mul_le_mul_of_nonneg_left (show r ≤ (((zeros x).card : ℝ) + ((zeros y).card : ℝ)) / 2 by linarith)
      hcoef
    have hb := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 / (n : ℝ) by positivity)
    have hv : (2 / (n : ℝ)) * (n / 2) = 1 := by field_simp
    rw [hv] at hb
    nlinarith only [ha, hb]
  have hscore (v : Fin n → Fin 2 × Fin 2) :
      ((zeros (fun j ↦ childBit (v j) (x j) (y j))).card : ℝ) = countScore G v := by
    rw [zero_count_as_score]
    rfl
  rw [pairMutation_product hn, mean_map]
  simp_rw [hscore]
  let E := {v | countScore G v ≤ g - (g - r + d)}
  have hpt (v : Fin n → Fin 2 × Fin 2) :
      indicator (countScore G v < r - d) ≤ (if v ∈ E then 1 else 0) := by
    by_cases h : countScore G v < r - d
    · have he : v ∈ E := by dsimp [E]; linarith
      simp [indicator, h, if_pos he]
    · rw [indicator, if_neg h]
      split_ifs <;> norm_num
  change mean C (fun v ↦ indicator (countScore G v < r - d)) ≤ _
  apply (mean_mono C hpt).trans
  rw [mean_indicator]
  have hdev := lower_deviation (fun _ : Fin n ↦ coordinateLaw n) G hl hl' (g - r + d)
  change C.toOuterMeasure E ≤ _ at hdev
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdev
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  change g * lam ^ 2 - lam * (g - r + d) ≤ r * lam ^ 2 - lam * d
  have hL := mul_nonneg hl (sub_nonneg.mpr hl')
  have hM := mul_nonneg (sub_nonneg.mpr hg) hL
  nlinarith only [hM]

lemma mean_draws_pairs {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (f : BitString n → ℝ) :
    mean (draws p P) (fun d ↦ f (child d)) =
      p * mean (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ij ↦
        mean (pairMutation (P ij.1) (P ij.2) (1 / (n : ℝ))) f) +
      (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        mean (pairMutation (P i) (P i) (1 / (n : ℝ))) f) := by
  rw [mean_draws hp]
  simp only [parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure, child]
  have h (i : Fin μ) (m : BitString n) : crossover (P i) (P i) m = P i := by
    funext j
    simp [crossover]
  simp only [pairMutation, mean_bind, mean_pure, h, mean_const]

lemma one_step_drop (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool) (P : Population n μ)
    (r d lam : ℝ) (hr : r ≤ (n : ℝ) / 2) (hP : r ≤ (bestZeros P : ℝ))
    (hd : 0 ≤ d) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    mean (step (jump k) p ar P) (fun Q ↦ indicator ((bestZeros Q : ℝ) < r - d)) ≤
      Real.exp (r * lam ^ 2 - lam * d) := by
  let f (z : BitString n) := indicator (((zeros z).card : ℝ) < r - d)
  let c := Real.exp (r * lam ^ 2 - lam * d)
  have hpj (i : Fin μ) : r ≤ ((zeros (P i)).card : ℝ) :=
    hP.trans (by exact_mod_cast bestZeros_le P i)
  have hpt (v : Draw n × Population n μ) (hv : v ∈ (stepMarked (jump k) p ar P).support) :
      indicator ((bestZeros v.2 : ℝ) < r - d) ≤ f (child v.1) := by
    by_cases h : (bestZeros v.2 : ℝ) < r - d
    · obtain ⟨i, hi⟩ := bestZeros_attains v.2
      have hz : v.2 i = child v.1 := by
        obtain ⟨z, _, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
        obtain ⟨Q, hQ, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
        have hs : Q i ≠ P i := by
          intro he
          rw [← hi] at h
          change ((zeros (Q i)).card : ℝ) < r - d at h
          rw [he] at h
          linarith only [hpj i, hd, h]
        unfold select at hQ
        split_ifs at hQ
        · exact (hs (congrFun ((PMF.mem_support_pure_iff _ _).mp hQ) i)).elim
        · obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ
          revert hs
          refine Fin.lastCases ?_ (fun j ↦ ?_) d
          · simp [replace]
          · by_cases hij : i = j
            · simp [replace, hij]
            · simp [replace, Function.update_of_ne hij]
      have ht : ((zeros (child v.1)).card : ℝ) < r - d := by rwa [← hz, hi]
      simp [f, indicator, h, ht]
    · rw [indicator, if_neg h]
      exact indic_nonneg _
  rw [← stepMarked_population (jump k) p ar P, mean_map]
  apply (mean_mono_on_support _ hpt).trans
  rw [← mean_map _ Prod.fst (fun u ↦ f (child u)), stepMarked_draws, mean_draws_pairs hp]
  have hc (i j : Fin μ) : mean (pairMutation (P i) (P j) (1 / (n : ℝ))) f ≤ c :=
    proposal_tail_pair hn (P i) (P j) r d lam hr (hpj i) (hpj j) hl hl'
  have h₁ := mean_mono (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ij ↦ hc ij.1 ij.2)
  have h₂ := mean_mono (PMF.uniformOfFintype (Fin μ)) (fun i ↦ hc i i)
  rw [mean_const] at h₁ h₂
  exact (add_le_add (mul_le_mul_of_nonneg_left h₁ hp.1)
    (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hp.2))).trans_eq (by dsimp [c]; ring)

end
end Lax637351Proofs.Descent
