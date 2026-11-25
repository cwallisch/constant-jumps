import Lax637351Proofs.FiniteDrift
import Lax637351Proofs.Transitions
import Mathlib.Tactic.FieldSimp

namespace Lax637351Proofs.Sampling

open Lax637351.Algorithm
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Transitions
open scoped Classical ENNReal

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_map (p : PMF α) (g : α → β) (f : β → ℝ) :
    mean (p.map g) f = mean p (fun x ↦ f (g x)) := by
  rw [← PMF.bind_pure_comp, mean_bind]
  simp only [Function.comp_apply, mean_pure]

lemma mean_uniform [Nonempty α] (f : α → ℝ) :
    mean (PMF.uniformOfFintype α) f = (Fintype.card α : ℝ)⁻¹ * ∑ x, f x := by
  unfold mean
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact (Finset.mul_sum _ _ _).symm

lemma mean_uniform_lower [Nonempty α] (f : α → ℝ) (c : ℝ) (h : ∀ x, c ≤ f x) :
    c ≤ mean (PMF.uniformOfFintype α) f :=
  (mean_const _ c).symm.le.trans (mean_mono _ h)

lemma mean_uniform_pair [Nonempty α] [Nonempty β] (f : α → β → ℝ) :
    mean (PMF.uniformOfFintype (α × β)) (fun x ↦ f x.1 x.2) =
      mean (PMF.uniformOfFintype α) (fun a ↦ mean (PMF.uniformOfFintype β) (f a)) := by
  simp only [mean_uniform, Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type]
  rw [← Finset.mul_sum, ← mul_assoc]

omit [Fintype β] in
lemma mean_single_lower (p : PMF α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (x : α) :
    (p x).toReal * f x ≤ mean p f :=
  Finset.single_le_sum (fun y _ ↦ mul_nonneg ENNReal.toReal_nonneg (hf y)) (Finset.mem_univ x)

lemma injective_sum_le_indicator (p : PMF β) (e : α → β) (he : Function.Injective e)
    (P : β → Prop) [DecidablePred P] (hP : ∀ a, P (e a)) :
    (∑ a, (p (e a)).toReal) ≤ mean p (fun b ↦ if P b then 1 else 0) := by
  classical
  have himage : (∑ a, (p (e a)).toReal) =
      ∑ b ∈ Finset.univ.image e, (p b).toReal := by
    rw [Finset.sum_image (fun a _ b _ h ↦ he h)]
  rw [himage]
  unfold mean
  calc
    _ = ∑ b ∈ Finset.univ.image e, (p b).toReal * (if P b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
      simp only [if_pos (hP a), mul_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ ↦ by split_ifs <;> positivity)

lemma coin_true {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) : coin p true = ENNReal.ofReal p := by
  simp [coin, hp]

lemma coin_false {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) : coin p false = ENNReal.ofReal (1 - p) := by
  simp [coin, hp]

lemma mean_swap (p : PMF α) (q : PMF β) (f : α → β → ℝ) :
    mean p (fun x ↦ mean q (f x)) = mean q (fun y ↦ mean p (fun x ↦ f x y)) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype β] in
lemma mean_uniform_exclude [Nonempty α] [DecidableEq α] (i : α) (c : ℝ) :
    mean (PMF.uniformOfFintype α) (fun j ↦ if j ≠ i then c else 0) =
      (1 - (Fintype.card α : ℝ)⁻¹) * c := by
  classical
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hh (j : α) : (if j ≠ i then c else 0) = c - (if j = i then c else 0) := by
    by_cases h : j = i <;> simp [h]
  simp only [hh, mean_uniform, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

omit [Fintype β] in
lemma mean_sum {ι : Type*} (p : PMF α) (S : Finset ι) (f : ι → α → ℝ) :
    mean p (fun x ↦ ∑ i ∈ S, f i x) = ∑ i ∈ S, mean p (f i) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype β] in
lemma uniform_avoid_two [Nonempty α] (i j : α) (hne : i ≠ j) (c d : ℝ) :
    mean (PMF.uniformOfFintype α) (fun x ↦ if x = i then d else if x = j then 0 else c) =
      (1 - 2 / (Fintype.card α : ℝ)) * c + d / (Fintype.card α : ℝ) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hs : (∑ x : α, if x = i then d else if x = j then 0 else c) =
      (Fintype.card α : ℝ) * c + (d - c) + (0 - c) := by
    have he (x : α) : (if x = i then d else if x = j then 0 else c) =
        c + (if x = i then d - c else 0) + (if x = j then 0 - c else 0) := by
      by_cases hxi : x = i <;> by_cases hxj : x = j <;>
        simp_all
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mean_uniform, hs]
  field_simp
  ring

lemma mean_coin {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (f : Bool → ℝ) :
    mean (coin p) f = p * f true + (1 - p) * f false := by
  unfold mean
  rw [Fintype.sum_bool]
  simp [coin_true hp, coin_false hp, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]

lemma mean_step {n : ℕ} {μ : ℕ+} {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (fitness : BitString n → ℝ) (avoid : Bool) (P : Population n μ)
    (f : Population n μ → ℝ) :
    mean (step fitness p avoid P) f =
      p * mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
          fun m ↦ mean (select fitness avoid true P y (mutate y m)) f) +
      (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun u ↦
        mean (independentBits n (1 / (n : ℝ))) fun m ↦
          mean (select fitness avoid false P (P u) (mutate (P u) m)) f) := by
  simp only [step_eq, mean_bind, mean_coin hp, parents, Bool.false_eq_true, if_false, mean_map]

end
end Lax637351Proofs.Sampling
