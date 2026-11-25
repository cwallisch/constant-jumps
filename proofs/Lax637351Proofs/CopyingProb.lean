import Lax637351Proofs.CopyingModel

namespace Lax637351Proofs.CopyingProb

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.MarkedStep Lax637351Proofs.Ordinary Lax637351Proofs.CopyingModel
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def idle (k : ℕ) (d : Draw n) : Prop := d.1 = false ∧ ¬ dangerous k d.2.1 d.2.2

def grow (k : ℕ) (A : BitString n) (P : Population n μ) (v : Draw n × Population n μ) : Prop :=
  v.1.1 = true ∧ ordinary k v.2 ∧ copyCount A v.2 = copyCount A P + 1

lemma idle_support (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (A : BitString n)
    (hA : (zeros A).card = k) (P : Population n μ) (hP : ordinary k P)
    (v : Draw n × Population n μ) (hv : v ∈ (stepMarked (jump k) p true P).support)
    (hi : idle k v.1) : ordinary k v.2 ∧ copyCount A v.2 = copyCount A P := by
  rcases (PMF.mem_support_bind_iff _ _ _).mp hv with ⟨d, hd, hv⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨Q, hQ, rfl⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp hd with ⟨cross, _, hd⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp hd with ⟨y, hy, hd⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hd with ⟨m, _, rfl⟩
  have hcross : cross = false := hi.1
  subst cross
  have hy' : y ∈ ((PMF.uniformOfFintype (Fin μ)).map P).support := by simpa [parents] using hy
  rcases (PMF.mem_support_map_iff _ _ _).mp hy' with ⟨i, _, rfl⟩
  have hi' : ¬ dangerous k (P i) m := hi.2
  have hnz : mutate (P i) m ≠ optimum n := by
    intro he
    have hn : mutate (P i) m ≠ P i := he.symm ▸ Ne.symm (ordinary_missing hk hP i)
    have hz : (zeros (mutate (P i) m)).card ≤ k := by
      simp [he, (zeros_eq_empty_iff (optimum n)).mpr rfl]
    exact hi' ⟨hn, hz⟩
  exact ⟨invariant_next hk hkn hP false (P i) _ hnz hQ, copyCount_wait hk hkn P A hA i m hi' Q hQ⟩

lemma idle_probability (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hp' : (k + 1 : ℝ) / n ≤ p) (P : Population n μ) (hP : ordinary k P) :
    1 - min 1 (2 * p) ≤ mean (stepMarked (jump k) p true P) (fun v ↦ indicator (idle k v.1)) := by
  by_cases h2 : 1 ≤ 2 * p
  · rw [min_eq_left h2, sub_self]
    exact mean_nonneg _ (fun _ ↦ indic_nonneg _)
  · rw [min_eq_right (le_of_not_ge h2), ← mean_map _ Prod.fst (fun d ↦ indicator (idle k d)),
      stepMarked_draws, mean_draws hp]
    have hnot (i : Fin μ) :
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (idle k (false, P i, m))) =
          1 - mean (independentBits n (1 / (n : ℝ)))
            (fun m ↦ indicator (dangerous k (P i) m)) := by
      have heq : (fun m : BitString n ↦ indicator (idle k (false, P i, m))) =
          fun m ↦ 1 - indicator (dangerous k (P i) m) := by
        funext m
        by_cases h : dangerous k (P i) m <;> simp [idle, indicator, h]
      rw [heq, mean_sub, mean_const]
    have hlow : 1 - p ≤ mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (idle k (false, P i, m)))) := by
      apply mean_uniform_lower
      intro i
      rw [hnot]
      exact sub_le_sub_left ((danger_bound hn (P i) (hP i)).trans hp') 1
    have hh := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hp.2)
    have heq (y m : BitString n) : indicator (idle k (true, y, m)) = 0 := by simp [indicator, idle]
    simp only [heq, mean_const, mul_zero, zero_add]
    nlinarith only [hh, sq_nonneg p]

lemma replace_copy_fraction (P : Population n μ) (A : BitString n) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
      (fun d ↦ indicator (∃ u : Fin μ, d = u.castSucc ∧ P u ≠ A)) =
      ((μ : ℕ) - copyCount A P : ℝ) / ((μ : ℕ) + 1 : ℝ) := by
  rw [mean_uniform, Fin.sum_univ_castSucc]
  have hl : indicator (∃ u : Fin μ, Fin.last (μ : ℕ) = u.castSucc ∧ P u ≠ A) = 0 := by
    apply if_neg
    rintro ⟨i, hi, _⟩
    have ht := congrArg Fin.val hi
    simp at ht
    have hi' := i.isLt
    omega
  have hh (i : Fin μ) :
      indicator (∃ u : Fin μ, i.castSucc = u.castSucc ∧ P u ≠ A) = 1 - indicator (P i = A) := by
    have h : (∃ u : Fin μ, i.castSucc = u.castSucc ∧ P u ≠ A) ↔ P i ≠ A := by
      constructor
      · rintro ⟨u, h, hne⟩
        exact (Fin.castSucc_injective _ h).symm ▸ hne
      · exact fun h ↦ ⟨i, rfl, h⟩
    by_cases hi : P i = A <;> simp [indicator, hi]
  simp only [hl, hh, add_zero, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, mul_one]
  have hcount : (∑ i : Fin μ, indicator (P i = A)) = (copyCount A P : ℝ) := by
    simp only [copyCount, copies, Finset.card_filter, Nat.cast_sum, indicator,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : P i = A <;> simp [h]
  rw [hcount, div_eq_inv_mul]

lemma best_clone_deletion (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : k ≤ (zeros A).card)
    (hbest : ∀ i, jump k (P i) ≤ jump k A) :
    ((μ : ℕ) - copyCount A P : ℝ) / ((μ : ℕ) + 1 : ℝ) ≤
      mean (Transitions.insert (jump k) P A)
        (fun Q ↦ indicator (ordinary k Q ∧ copyCount A Q = copyCount A P + 1)) := by
  have hA' : A ≠ optimum n := by
    intro h
    rw [h, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hA
    omega
  have hs : select (jump k) true true P A A = Transitions.insert (jump k) P A := by simp [select]
  have hord (Q : Population n μ) (hQ : Q ∈ (Transitions.insert (jump k) P A).support) :
      ordinary k Q := invariant_next hk hkn hP true A A hA' (hs.symm ▸ hQ)
  by_cases hpl : ∀ i, jump k (P i) = jump k A
  · have he := insert_eq_uniform (jump k) P A hpl
    rw [he, mean_map, ← replace_copy_fraction P A]
    apply mean_mono
    intro d
    by_cases h : ∃ u : Fin μ, d = u.castSucc ∧ P u ≠ A
    · obtain ⟨u, rfl, hne⟩ := h
      have hP' : ordinary k (Function.update P u A) := by
        intro i
        by_cases hi : i = u
        · subst i
          simpa using hA
        · simpa only [Function.update_of_ne hi] using hP i
      have hd : ordinary k (replace P A u.castSucc) ∧
          copyCount A (replace P A u.castSucc) = copyCount A P + 1 := by
        simpa [replace, copyCount_update A P u hne] using hP'
      simp [indicator, hne, hd]
    · simpa only [indicator, if_neg h] using
        indic_nonneg (ordinary k (replace P A d) ∧ copyCount A (replace P A d) = copyCount A P + 1)
  · obtain ⟨u, hu⟩ := not_forall.mp hpl
    have hu' : jump k (P u) < jump k A := lt_of_le_of_ne (hbest u) hu
    have hmean : mean (Transitions.insert (jump k) P A)
        (fun Q ↦ indicator (ordinary k Q ∧ copyCount A Q = copyCount A P + 1)) = 1 := by
      apply mean_supported_const
      intro Q hQ
      have ha := hord Q hQ
      obtain ⟨d, rfl, hd⟩ := insert_strict_improvement (jump k) P A u hu' hQ
      have hne : P d ≠ A := fun h ↦ (not_lt_of_ge (h ▸ hd)) hu'
      simp [indicator, ha, copyCount_update A P d hne]
    rw [hmean]
    apply (div_le_one (by positivity)).mpr
    have hc : (0 : ℝ) ≤ copyCount A P := by positivity
    linarith

def goodRate (m i : ℕ) (p : ℝ) : ℝ := (p / 8) * ((i : ℝ) / m) ^ 2 * ((m : ℝ) - i) / (m + 1)

lemma goodRate_nonneg {m i : ℕ} (hi : i ≤ m) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ goodRate m i p := by
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi
  unfold goodRate
  positivity

lemma grow_best_probability (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : k ≤ (zeros A).card) (hbest : ∀ i, jump k (P i) ≤ jump k A)
    (avoid : Bool) :
    goodRate μ (copyCount A P) p ≤
      mean (stepMarked (jump k) p avoid P) (fun v ↦ indicator (grow k A P v)) := by
  let c : ℝ := ((μ : ℕ) - copyCount A P : ℝ) / ((μ : ℕ) + 1 : ℝ)
  have hc : 0 ≤ c := by
    have hh : (copyCount A P : ℝ) ≤ (μ : ℕ) := by exact_mod_cast copyCount_le A P
    dsimp [c]
    positivity
  let f (Q : Population n μ) :=
    indicator (ordinary k Q ∧ copyCount A Q = copyCount A P + 1)
  have hfalse (i : Fin μ) (m : BitString n) (Q : Population n μ) :
      indicator (grow k A P ((false, P i, m), Q)) = 0 := by simp [indicator, grow]
  have htrue (y m : BitString n) (Q : Population n μ) :
      indicator (grow k A P ((true, y, m), Q)) = f Q := by simp [indicator, grow, f]
  have heq := mean_marked hp (jump k) avoid P (fun d Q ↦ indicator (grow k A P (d, Q)))
  simp only [hfalse, htrue, mean_const, mul_zero, add_zero] at heq
  rw [heq]
  have hpair (ij : Fin μ × Fin μ) :
      (1 / 8) * c * (indicator (P ij.1 = A) * indicator (P ij.2 = A)) ≤
        mean (PMF.uniformOfFintype (BitString n)) (fun mask' ↦
          mean (independentBits n (1 / (n : ℝ))) (fun m ↦
            let y := crossover (P ij.1) (P ij.2) mask'
            mean (select (jump k) avoid true P y (mutate y m)) f)) := by
    by_cases h₁ : P ij.1 = A
    · by_cases h₂ : P ij.2 = A
      · simp only [indicator, if_pos h₁, if_pos h₂, mul_one]
        apply mean_uniform_lower
        intro mask'
        have hcross : crossover (P ij.1) (P ij.2) mask' = A := by
          funext j
          simp [crossover, h₁, h₂]
        simp only [hcross]
        have hbase := mean_single_lower (independentBits n (1 / (n : ℝ)))
          (fun m ↦ mean (select (jump k) avoid true P A (mutate A m)) f)
          (fun m ↦ mean_nonneg _ (fun Q ↦ indic_nonneg _)) (mask ∅)
        have hmut : mutate A (mask ∅) = A := by funext j; simp [mutate, mask]
        rw [hmut] at hbase
        have hzero : (1 / 8 : ℝ) ≤ (independentBits n (1 / (n : ℝ)) (mask ∅)).toReal := by
          simpa using weight_lower hn (∅ : Finset (Fin n))
        have hh := best_clone_deletion hk hkn P hP A hA hbest
        have hSelect (z : BitString n) : select (jump k) avoid true P A z = Transitions.insert (jump k) P z := by simp [select]
        simp only [hSelect] at hbase ⊢
        exact (mul_le_mul hzero hh hc ENNReal.toReal_nonneg).trans hbase
      · simp only [indicator, if_neg h₂, mul_zero]
        exact mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ indic_nonneg _)))
    · simp only [indicator, if_neg h₁, zero_mul, mul_zero]
      exact mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ mean_nonneg _ (fun _ ↦ indic_nonneg _)))
  have hm := mean_mono (PMF.uniformOfFintype (Fin μ × Fin μ)) hpair
  rw [mean_mul, mean_uniform_pair (fun i j : Fin μ ↦ indicator (P i = A) * indicator (P j = A))] at hm
  simp_rw [mean_mul, uniform_copyRate] at hm
  have heq' : (fun i : Fin μ ↦ indicator (P i = A) * ((copyCount A P : ℝ) / (μ : ℕ))) =
      fun i ↦ ((copyCount A P : ℝ) / (μ : ℕ)) * indicator (P i = A) := by
    funext i
    ring
  rw [heq', mean_mul, uniform_copyRate] at hm
  have hh := mul_le_mul_of_nonneg_left hm hp.1
  simp only [parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
  apply le_trans _ hh
  unfold goodRate
  dsimp [c]
  ring_nf
  exact le_rfl

lemma grow_probability (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : (zeros A).card = k) :
    goodRate μ (copyCount A P) p ≤
      mean (stepMarked (jump k) p true P) (fun v ↦ indicator (grow k A P v)) :=
  grow_best_probability hk hkn hn p hp P hP A hA.ge (fun i ↦ by
    rw [jump_plateau hkn A hA, jump_of_many_zeros hkn _ (hP i)]
    exact_mod_cast (show k + (n - (zeros (P i)).card) ≤ n by have := hP i; omega)) true

end
end Lax637351Proofs.CopyingProb
