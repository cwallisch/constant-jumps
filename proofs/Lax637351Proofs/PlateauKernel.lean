import Lax637351Proofs.Auxiliary
import Lax637351Proofs.PairAveraging

namespace Lax637351Proofs.PlateauKernel

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.MarkedStep
open Lax637351Proofs.Auxiliary Lax637351Proofs.PairAveraging
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def submitted (k : ℕ) (ar : Bool) (d : Draw n) : Prop :=
  (zeros (child d)).card = k ∧ ¬ discarded ar d

lemma rejectSelect_plateau (hk : 0 < k) (hkn : k ≤ n) (ar : Bool) (P : Population n μ)
    (hp : plateau (k := k) P) (d : Draw n) :
    rejectSelect k ar P d = if submitted k ar d then
      (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))).map (replace P (child d))
      else PMF.pure P := by
  by_cases hs : submitted k ar d
  · have ho : child d ≠ optimum n := by
      intro h
      have hh := hs.1
      rw [h, (zeros_eq_empty_iff _).mpr rfl, Finset.card_empty] at hh
      omega
    have hd : ¬ (ar = true ∧ ¬d.1 = true ∧ child d = d.2.1) := hs.2
    rw [if_pos hs, rejectSelect, if_neg ho, select, if_neg hd]
    exact insert_eq_uniform (jump k) P _ (fun i ↦
      (jump_plateau hkn _ (hp i)).trans (jump_plateau hkn _ hs.1).symm)
  · rw [if_neg hs, rejectSelect]
    split_ifs with hz
    · rfl
    · unfold select
      split_ifs with hd
      · rfl
      · have hZ : (zeros (child d)).card ≠ k := fun he ↦ hs ⟨he, hd⟩
        have hw (i : Fin μ) : jump k (child d) < jump k (P i) := by
          rw [jump_plateau hkn _ (hp i)]
          exact jump_lt_plateau hk hkn _ hz hZ
        have hh := map_constant_on_support (Transitions.insert (jump k) P (child d))
          (fun Q ↦ Q) P (fun Q hQ ↦ insert_support_of_worse _ _ _ hw hQ)
        exact (PMF.map_id _).symm.trans hh

lemma auxiliary_preserves_plateau (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hp : plateau (k := k) P)
    (Q : Population n μ) (hQ : Q ∈ (auxiliary k p ar P).support) :
    plateau (k := k) Q := by
  obtain ⟨d, _, hQ⟩ := (PMF.mem_support_bind_iff _ _ _).mp hQ
  rw [rejectSelect_plateau hk hkn ar P hp] at hQ
  split_ifs at hQ with hs
  · rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨i, _, rfl⟩
    refine Fin.lastCases ?_ (fun u ↦ ?_) i
    · simpa only [replace, Fin.lastCases_last] using hp
    · intro j
      by_cases hj : j = u
      · subst j
        simpa only [replace, Fin.lastCases_castSucc, Function.update_self] using hs.1
      · simpa only [replace, Fin.lastCases_castSucc, Function.update_of_ne hj] using hp j
  · rw [(PMF.mem_support_pure_iff _ _).mp hQ]
    exact hp

def submitRate (k : ℕ) (p : ℝ) (ar : Bool) (P : Population n μ) : ℝ :=
  mean (draws p P) (fun d ↦ indicator (submitted k ar d))

def submitMean (k : ℕ) (p : ℝ) (ar : Bool) (P : Population n μ) (f : BitString n → ℝ) : ℝ :=
  mean (draws p P) (fun d ↦ indicator (submitted k ar d) * f (child d))

lemma pair_drift (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hp : plateau (k := k) P) (f : BitString n → BitString n → ℝ)
    (hsym : ∀ x y, f x y = f y x) (hdiag : ∀ x, f x x = 0) :
    mean (auxiliary k p ar P) (fun Q ↦ pairMean f Q - pairMean f P) =
      (2 / ((μ : ℕ) + 1 : ℝ)) *
        ((1 - (1 / ((μ : ℕ) : ℝ))) * submitMean k p ar P (partnerMean f P) -
          submitRate k p ar P * pairMean f P) := by
  rw [auxiliary, mean_bind]
  have heq (d : Draw n) :
      mean (rejectSelect k ar P d) (fun Q ↦ pairMean f Q - pairMean f P) =
        (2 / ((μ : ℕ) + 1 : ℝ)) *
          ((1 - (1 / ((μ : ℕ) : ℝ))) *
              (indicator (submitted k ar d) * partnerMean f P (child d)) -
            pairMean f P * indicator (submitted k ar d)) := by
    rw [rejectSelect_plateau hk hkn ar P hp]
    by_cases h : submitted k ar d
    · rw [if_pos h, mean_map, pair_replace_delta f hsym hdiag]
      simp only [indicator, if_pos h, one_mul, mul_one]
    · simp only [mean_pure, sub_self, indicator, if_neg h, zero_mul, mul_zero]
  simp_rw [heq]
  rw [mean_mul, mean_sub, mean_mul, mean_mul]
  simp only [submitRate, submitMean, mul_comm (pairMean f P)]

def slotMean (f : BitString n → ℝ) (P : Population n μ) : ℝ :=
  (∑ i, f (P i)) / ((μ : ℕ) : ℝ)

lemma slotMean_eq (f : BitString n → ℝ) (P : Population n μ) :
    slotMean f P = mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ f (P i)) := by
  simp [slotMean, mean_uniform, div_eq_inv_mul]

lemma slot_replace_delta (f : BitString n → ℝ) (P : Population n μ) (z : BitString n) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))) (fun d ↦ slotMean f (replace P z d) - slotMean f P) =
      (f z - slotMean f P) / ((μ : ℕ) + 1 : ℝ) := by
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  rw [mean_uniform, Fin.sum_univ_castSucc]
  simp only [replace, Fin.lastCases_last, Fin.lastCases_castSucc, sub_self, add_zero,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one, slotMean, ← sub_div]
  simp_rw [sum_update P _ z f, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (0 : ℝ) < (μ : ℕ) + 1 := by linarith
  field_simp

lemma slot_drift (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (P : Population n μ) (hp : plateau (k := k) P) (f : BitString n → ℝ) :
    mean (auxiliary k p ar P) (fun Q ↦ slotMean f Q - slotMean f P) =
      (submitMean k p ar P f - submitRate k p ar P * slotMean f P) / ((μ : ℕ) + 1 : ℝ) := by
  rw [auxiliary, mean_bind]
  have heq (d : Draw n) :
      mean (rejectSelect k ar P d) (fun Q ↦ slotMean f Q - slotMean f P) =
        ((indicator (submitted k ar d) * f (child d)) -
          slotMean f P * indicator (submitted k ar d)) *
          (((μ : ℕ) : ℝ) + 1)⁻¹ := by
    rw [rejectSelect_plateau hk hkn ar P hp]
    by_cases h : submitted k ar d
    · rw [if_pos h, mean_map, slot_replace_delta]
      simp only [div_eq_mul_inv, indicator, if_pos h, one_mul, mul_one]
    · simp only [mean_pure, sub_self, indicator, if_neg h, zero_mul, mul_zero]
  simp_rw [heq]
  have hr : (fun d : Draw n ↦
      (indicator (submitted k ar d) * f (child d) - slotMean f P * indicator (submitted k ar d)) *
        (((μ : ℕ) : ℝ) + 1)⁻¹) =
      fun d ↦ (((μ : ℕ) : ℝ) + 1)⁻¹ *
        (indicator (submitted k ar d) * f (child d) - slotMean f P * indicator (submitted k ar d)) := by
    funext d
    ring
  rw [hr, mean_mul, mean_sub, mean_mul]
  simp only [submitRate, submitMean, div_eq_inv_mul, mul_comm (slotMean f P)]

end
end Lax637351Proofs.PlateauKernel
