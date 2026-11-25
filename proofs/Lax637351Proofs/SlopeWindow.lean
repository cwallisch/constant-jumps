import Lax637351Proofs.SlopeCopy
import Lax637351Proofs.FiniteWindows
import Lax637351Proofs.MaskKernel

namespace Lax637351Proofs.SlopeWindow

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.Ordinary Lax637351Proofs.BestRank Lax637351Proofs.SlopeCopy
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.MarkedStep
open Lax637351Proofs.PairAveraging
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def safe (k : ℕ) (x : BitString n) : Prop :=
  k ≤ (zeros x).card ∨ x = optimum n

lemma safe_fit (hkn : k ≤ n) (x : BitString n) (hx : safe k x) :
    jump k x = (k + (n - (zeros x).card) : ℕ) := by
  rcases hx with hx | rfl
  · exact jump_of_many_zeros hkn x hx
  · rw [jump_optimum, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty, Nat.sub_zero]

lemma safe_iff (_hk : 0 < k) (hkn : k ≤ n) (x : BitString n) :
    safe k x ↔ (k : ℝ) ≤ jump k x := by
  constructor
  · intro hx
    rw [safe_fit hkn x hx]
    exact_mod_cast Nat.le_add_right _ _
  · intro hf
    by_cases hx : x = optimum n
    · exact Or.inr hx
    · exact Or.inl (large_fitness_ordinary hkn x hx hf)

lemma safe_zero_order (hkn : k ≤ n) {x y : BitString n} (hx : safe k x) (hy : safe k y)
    (hxy : jump k x ≤ jump k y) : (zeros y).card ≤ (zeros x).card := by
  rw [safe_fit hkn _ hx, safe_fit hkn _ hy, Nat.cast_le] at hxy
  have h₁ := Finset.card_le_univ (zeros x)
  have h₂ := Finset.card_le_univ (zeros y)
  simp only [Fintype.card_fin] at h₁ h₂
  omega

lemma safe_step (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool) (P : Population n μ)
    (hP : ∀ i, safe k (P i)) (Q : Population n μ) (hQ : Q ∈ (step (jump k) p ar P).support) :
    ∀ i, safe k (Q i) ∧ (zeros (Q i)).card ≤ (zeros (P i)).card := by
  intro i
  have hfit := step_fitness_mono _ _ _ _ hQ i
  have hsafe := (safe_iff hk hkn _).mpr (((safe_iff hk hkn _).mp (hP i)).trans hfit)
  exact ⟨hsafe, safe_zero_order hkn (hP i) hsafe hfit⟩

lemma safe_insert (hk : 0 < k) (hkn : k ≤ n) (P : Population n μ)
    (hP : ∀ i, safe k (P i)) (z : BitString n) (Q : Population n μ)
    (hQ : Q ∈ (Transitions.insert (jump k) P z).support) :
    ∀ i, safe k (Q i) ∧ (zeros (Q i)).card ≤ (zeros (P i)).card := by
  intro i
  have hfit := insert_fitness_mono _ _ _ hQ i
  have hsafe := (safe_iff hk hkn _).mpr (((safe_iff hk hkn _).mp (hP i)).trans hfit)
  exact ⟨hsafe, safe_zero_order hkn (hP i) hsafe hfit⟩

lemma improved_site (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (z : BitString n) (hz : k ≤ (zeros z).card) (u : Fin μ) (hbetter : (zeros z).card < (zeros (P u)).card)
    (Q : Population n μ) (hQ : Q ∈ (Transitions.insert (jump k) P z).support) :
    ∃ d, Q = Function.update P d z ∧ (zeros (P u)).card ≤ (zeros (P d)).card := by
  have ht : jump k (P u) < jump k z := by
    exact lt_of_not_ge (fun h ↦ (not_le_of_gt hbetter) ((slope_order hkn hz (hP u)).mp h))
  obtain ⟨d, hd, hF⟩ := insert_strict_improvement _ _ _ u ht hQ
  exact ⟨d, hd, (slope_order hkn (hP d) (hP u)).mp hF⟩

lemma step_one_slot (p : ℝ) (ar : Bool) (P Q : Population n μ)
    (hQ : Q ∈ (step (jump k) p ar P).support) :
    ∃ z : BitString n, ∃ d : Fin ((μ : ℕ) + 1), Q = replace P z d := by
  rw [← stepMarked_population] at hQ
  obtain ⟨v, hv, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ
  obtain ⟨e, _, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
  obtain ⟨X, hX, hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
  have hXQ : X = Q := (congrArg Prod.snd hxe).trans he
  unfold select at hX
  split_ifs at hX
  · exact ⟨child e, Fin.last _, hXQ.symm.trans (by simpa [replace] using (PMF.mem_support_pure_iff _ _).mp hX)⟩
  · obtain ⟨d, _, h⟩ := (PMF.mem_support_map_iff _ _ _).mp hX
    exact ⟨child e, d, hXQ.symm.trans h.symm⟩

lemma same_parent_lower (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (i : Fin μ)
    (f : Population n μ → ℝ) (hf : ∀ Q, 0 ≤ f Q) (b : ℝ) (hb : 0 ≤ b)
    (h : b ≤ mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      mean (Transitions.insert (jump k) P (mutate (P i) m)) f)) :
    b / ((μ : ℕ) : ℝ) ^ 2 ≤ mean (step (jump k) p false P) f := by
  let m : ℝ := (μ : ℕ)
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (Nat.succ_le_of_lt μ.pos)
  have hp' : 0 < m := by linarith
  let F (x : BitString n) := mean (independentBits n (1 / (n : ℝ))) (fun q ↦
    mean (Transitions.insert (jump k) P (mutate x q)) f)
  have hF (x : BitString n) : 0 ≤ F x := mean_nonneg _ (fun _ ↦ mean_nonneg _ hf)
  rw [mean_unmarked hp]
  change b / m ^ 2 ≤ p * mean (parents P true) F +
       (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun j ↦ F (P j))
  have hmut : b / m ^ 2 ≤ mean (PMF.uniformOfFintype (Fin μ)) (fun j ↦ F (P j)) := by
    have hs := mean_single_lower (PMF.uniformOfFintype (Fin μ)) (fun j ↦ F (P j)) (fun j ↦ hF (P j)) i
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_fin] at hs
    change m⁻¹ * F (P i) ≤ _ at hs
    apply le_trans _ hs
    calc
      _ ≤ m⁻¹ * b := by
        rw [mul_comm, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hb hp' (by nlinarith only [hm, mul_nonneg (sub_nonneg.mpr hm) hp'.le])
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp'.le)
  have hcross : b / m ^ 2 ≤ mean (parents P true) F := by
    simp only [parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
    have hs := mean_single_lower (PMF.uniformOfFintype (Fin μ × Fin μ))
      (fun ij ↦ mean (PMF.uniformOfFintype (BitString n)) (fun s ↦ F (crossover (P ij.1) (P ij.2) s)))
      (fun ij ↦ mean_nonneg _ (fun s ↦ hF _)) (i, i)
    have hc (s : BitString n) : crossover (P i) (P i) s = P i := by funext j; simp [crossover]
    simp only [hc, mean_const, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hs
    apply le_trans _ hs
    rw [div_eq_inv_mul, pow_two]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hs := add_le_add (mul_le_mul_of_nonneg_left hcross hp.1)
    (mul_le_mul_of_nonneg_left hmut (sub_nonneg.mpr hp.2))
  apply le_trans _ hs
  exact le_of_eq (by ring)

lemma mutation_choice_lower (hn : 2 ≤ n) (P : Population n μ) (i : Fin μ)
    (F : Population n μ → ℝ) (hF : ∀ Q, 0 ≤ F Q)
    (S : Finset (Fin n)) (b : ℝ) (hb : 0 ≤ b)
    (h : b ≤ mean (Transitions.insert (jump k) P (mutate (P i) (mask S))) F) :
    ((1 / (n : ℝ)) ^ S.card / 8) * b ≤ mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      mean (Transitions.insert (jump k) P (mutate (P i) m)) F) := by
  apply le_trans _ (mean_single_lower _ _ (fun m ↦ mean_nonneg _ hF) (mask S))
  exact mul_le_mul (by simpa only [div_eq_mul_inv, one_div, one_mul] using weight_lower hn S) h hb ENNReal.toReal_nonneg

end
end Lax637351Proofs.SlopeWindow
