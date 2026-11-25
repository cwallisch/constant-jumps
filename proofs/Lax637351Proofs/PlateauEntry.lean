import Lax637351Proofs.CopyingModel
import Lax637351Proofs.FiniteRace

namespace Lax637351Proofs.PlateauEntry

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.MarkedStep Lax637351Proofs.Ordinary Lax637351Proofs.OffspringProduct
open Lax637351Proofs.CopyingModel Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open Filter
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma mean_pairMutation (x y : BitString n) (r : ℝ) (f : BitString n → ℝ) :
    mean (pairMutation x y r) f =
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
        mean (independentBits n r) fun f' ↦ f (mutate (crossover x y m) f')) := by
  simp [pairMutation, mean_bind, mean_pure]

lemma mean_pairMutation_self (x : BitString n) (r : ℝ) (f : BitString n → ℝ) :
    mean (pairMutation x x r) f = mean (independentBits n r) (fun m ↦ f (mutate x m)) := by
  rw [pairMutation_self, mean_map]

lemma mean_child {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (f : BitString n → ℝ) :
    mean (draws p P) (fun d ↦ f (child d)) =
      p * mean (PMF.uniformOfFintype (Fin μ × Fin μ))
        (fun ij ↦ mean (pairMutation (P ij.1) (P ij.2) (1 / n)) f) +
      (1 - p) * mean (PMF.uniformOfFintype (Fin μ))
        (fun i ↦ mean (pairMutation (P i) (P i) (1 / n)) f) := by
  simp only [mean_draws hp, child, parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
  simp_rw [mean_pairMutation_self, mean_pairMutation]

lemma proposal_hazard (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ordinary k P) :
    (1 / (n : ℝ)) ^ n ≤ mean (draws p P) (fun d ↦ indicator (child d = optimum n)) ∧
    mean (draws p P) (fun d ↦ indicator (child d = optimum n)) ≤
      mean (draws p P) (fun d ↦ indicator ((zeros (child d)).card = k)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := rate_valid hn
  have hr' : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn'
  have hlow (i j : Fin μ) :
      (1 / (n : ℝ)) ^ n ≤ mean (pairMutation (P i) (P j) (1 / n))
        (fun z ↦ indicator (z = optimum n)) := by
    let ν := pairMutation (P i) (P j) (1 / n)
    have he := mean_indicator ν ({optimum n} : Set (BitString n))
    change mean ν (fun z ↦ indicator (z = optimum n)) = _ at he
    rw [he, PMF.toOuterMeasure_apply_singleton]
    have hh := ENNReal.toReal_mono (ν.apply_ne_top _) (pairMutation_optimum_lower (P i) (P j) hn)
    simpa only [ENNReal.toReal_ofReal (pow_nonneg hr.1 _)] using hh
  have hle (i j : Fin μ) :
      mean (pairMutation (P i) (P j) (1 / n)) (fun z ↦ indicator (z = optimum n)) ≤
        mean (pairMutation (P i) (P j) (1 / n)) (fun z ↦ indicator ((zeros z).card = k)) := by
    let ν := pairMutation (P i) (P j) (1 / n)
    let A : Set (BitString n) := {z | (zeros z).card = k}
    have he := mean_indicator ν ({optimum n} : Set (BitString n))
    have hh := mean_indicator ν A
    change mean ν (fun z ↦ indicator (z = optimum n)) = _ at he
    change mean ν (fun z ↦ indicator ((zeros z).card = k)) = _ at hh
    rw [he, hh, PMF.toOuterMeasure_apply_singleton]
    apply ENNReal.toReal_mono
      (ne_top_of_le_ne_top ENNReal.one_ne_top (FiniteChain.event_le_one ν A))
    exact pairMutation_plateau_ge_optimum (P i) (P j) (hP i) ⟨hr.1, hr'⟩
  have hlo := mean_uniform_lower (α := Fin μ × Fin μ) _ _ (fun ij ↦ hlow ij.1 ij.2)
  have hlo' := mean_uniform_lower (α := Fin μ) _ _ (fun i ↦ hlow i i)
  have hh := mean_mono (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ij ↦ hle ij.1 ij.2)
  have hh' := mean_mono (PMF.uniformOfFintype (Fin μ)) (fun i ↦ hle i i)
  constructor
  · rw [mean_child hp P (fun z ↦ indicator (z = optimum n))]
    have ha := mul_le_mul_of_nonneg_left hlo hp.1
    have hb := mul_le_mul_of_nonneg_left hlo' (sub_nonneg.mpr hp.2)
    linarith
  · rw [mean_child hp P (fun z ↦ indicator (z = optimum n)),
      mean_child hp P (fun z ↦ indicator ((zeros z).card = k))]
    exact add_le_add (mul_le_mul_of_nonneg_left hh hp.1)
      (mul_le_mul_of_nonneg_left hh' (sub_nonneg.mpr hp.2))

def plateauEntry (k : ℕ) (P : Population n μ) : Prop := ordinary k P ∧ hasPlateau k P

lemma select_bad_law (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (cross : Bool) (y z : BitString n) (hy : cross = false → y ≠ optimum n) :
    mean (select (jump k) true cross P y z) (fun Q ↦ indicator (¬ missing Q)) =
      indicator (z = optimum n) := by
  have hmiss := ordinary_missing hk hP
  by_cases hz : z = optimum n
  · rw [hz, show indicator (optimum n = optimum n) = 1 by simp [indicator]]
    have hdiscard : ¬ (true = true ∧ ¬ cross = true ∧ optimum n = y) := by
      rintro ⟨_, hc, hy'⟩
      exact hy (Bool.eq_false_of_not_eq_true hc) hy'.symm
    rw [select, if_neg hdiscard]
    apply mean_supported_const
    intro Q hQ
    obtain ⟨d, rfl, _⟩ := insert_strict_improvement (jump k) P _
      (0 : Fin μ) (jump_lt_optimum hk _ (hmiss 0)) hQ
    have hQ' : ¬ missing (Function.update P d (optimum n)) :=
      fun h ↦ h d (Function.update_self d (optimum n) P)
    simp [indicator, hQ']
  · rw [show indicator (z = optimum n) = 0 by simp [indicator, hz]]
    apply mean_supported_const
    intro Q hQ
    have hQQ := ordinary_missing hk (invariant_next hk hkn hP cross y z hz hQ)
    simp [indicator, hQQ]

lemma select_good_lower (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (hN : ¬ hasPlateau k P) (cross : Bool) (y z : BitString n)
    (hy : cross = false → (zeros y).card ≠ k) :
    indicator ((zeros z).card = k) ≤
      mean (select (jump k) true cross P y z) (fun Q ↦ indicator (plateauEntry k Q)) := by
  by_cases hz : (zeros z).card = k
  · have hdiscard : ¬ (true = true ∧ ¬ cross = true ∧ z = y) := by
      rintro ⟨_, hc, he⟩
      exact hy (Bool.eq_false_of_not_eq_true hc) (he ▸ hz)
    have hnopt : z ≠ optimum n := by
      intro hh
      rw [hh, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hz
      omega
    rw [indicator, if_pos hz, ← mean_const (select (jump k) true cross P y z) 1]
    apply mean_mono_on_support
    intro Q hQ
    have hQord := invariant_next hk hkn hP cross y z hnopt hQ
    rw [select, if_neg hdiscard] at hQ
    have hbetter : jump k (P 0) < jump k z := by
      rw [jump_plateau hkn z hz]
      exact jump_lt_plateau hk hkn _ (ordinary_missing hk hP 0) (fun h ↦ hN ⟨0, h⟩)
    obtain ⟨d, rfl, _⟩ := insert_strict_improvement (jump k) P z 0 hbetter hQ
    have hpl : hasPlateau k (Function.update P d z) :=
      ⟨d, by simpa using hz⟩
    simp [indicator, show plateauEntry k (Function.update P d z) from ⟨hQord, hpl⟩]
  · simp only [indicator, if_neg hz]
    exact mean_nonneg _ (fun _ ↦ by split_ifs <;> norm_num)

lemma entry_hazard (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ordinary k P) (hN : ¬ hasPlateau k P) :
    (1 / (n : ℝ)) ^ n ≤ mean (step (jump k) p true P) (fun Q ↦ indicator (¬ missing Q)) ∧
    mean (step (jump k) p true P) (fun Q ↦ indicator (¬ missing Q)) ≤
      mean (step (jump k) p true P) (fun Q ↦ indicator (plateauEntry k Q)) := by
  obtain ⟨hpos, hcomp⟩ := proposal_hazard (k := k) hn p hp P hP
  have hbad : mean (step (jump k) p true P) (fun Q ↦ indicator (¬ missing Q)) =
      mean (draws p P) (fun d ↦ indicator (child d = optimum n)) := by
    rw [mean_step hp, mean_draws hp]
    simp only [child]
    have h₁ (y m : BitString n) :=
      select_bad_law hk hkn P hP true y (mutate y m) (by simp)
    have h₂ (i : Fin μ) (m : BitString n) :=
      select_bad_law hk hkn P hP false (P i) (mutate (P i) m)
        (fun _ ↦ ordinary_missing hk hP i)
    simp only [h₁, h₂]
  have hgood : mean (draws p P) (fun d ↦ indicator ((zeros (child d)).card = k)) ≤
      mean (step (jump k) p true P) (fun Q ↦ indicator (plateauEntry k Q)) := by
    rw [mean_step hp, mean_draws hp]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ hp.1
      apply mean_mono
      intro y
      apply mean_mono
      intro m
      exact select_good_lower hk hkn P hP hN true y (mutate y m) (by simp)
    · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hp.2)
      apply mean_mono
      intro i
      apply mean_mono
      intro m
      exact select_good_lower hk hkn P hP hN false (P i) (mutate (P i) m) (fun _ h ↦ hN ⟨i, h⟩)
  rw [hbad]
  exact ⟨hpos, hcomp.trans hgood⟩

lemma uniform_entry_window (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∃ t : ℕ, ∀ P : Population n μ, ordinary k P →
      (1 / 4 : ℝ) ≤ visit (step (jump k) p true) {Q | plateauEntry k Q} t P := by
  let K := step (jump k) p true (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | plateauEntry k Q}
  let B : Set (Population n μ) := {Q | ¬ missing Q}
  let I : Set (Population n μ) := {Q | ordinary k Q ∧ ¬ hasPlateau k Q}
  let δ := (1 / (n : ℝ)) ^ n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1 := pow_le_one₀ (rate_valid hn).1 (rate_valid hn).2
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hδ')
    (show 1 - δ < 1 by linarith)
  have he := (tendsto_order.mp ht).2 (1 / 2 : ℝ) (by norm_num)
  obtain ⟨t, ht'⟩ := he.exists
  refine ⟨t, fun P hP ↦ ?_⟩
  by_cases hpl : hasPlateau k P
  · have hPg : P ∈ G := ⟨hP, hpl⟩
    change _ ≤ visit K G t P
    rw [visit_in K G _ _ hPg]
    norm_num
  · have hGB : Disjoint G B :=
      Set.disjoint_left.mpr (fun x hx hX ↦ hX (ordinary_missing hk hx.1))
    have hGI : Disjoint G I :=
      Set.disjoint_left.mpr (fun x hx hX ↦ hX.2 hx.2)
    have hBI : Disjoint B I :=
      Set.disjoint_left.mpr (fun x hx hX ↦ hx (ordinary_missing hk hX.1))
    have hsupp (x : Population n μ) (hx : x ∈ I) (y : Population n μ) (hy : y ∈ (K x).support) :
        y ∈ G ∪ B ∪ I := by
      by_cases h : missing y
      · have ho := ordinary_preserved hkn p true hx.1 hy h
        by_cases hG : hasPlateau k y
        · exact Or.inl (Or.inl ⟨ho, hG⟩)
        · exact Or.inr ⟨ho, hG⟩
      · exact Or.inl (Or.inr h)
    have hh := visit_race K G B I hGB hGI hBI δ hδ.le hδ' hsupp
      (fun x hx ↦ (entry_hazard hk hkn hn p hp x hx.1 hx.2).2)
      (fun x hx ↦ (entry_hazard hk hkn hn p hp x hx.1 hx.2).1)
      t P ⟨hP, hpl⟩
    have hlow : (1 / 4 : ℝ) ≤ raceBound δ t := by unfold raceBound; linarith
    exact hlow.trans hh

end
end Lax637351Proofs.PlateauEntry
