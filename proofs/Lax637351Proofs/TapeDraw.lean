import Lax637351Proofs.Auxiliary
import Lax637351Proofs.Independent
import Lax637351Proofs.CrossoverSuccess

namespace Lax637351Proofs.TapeDraw

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.MarkedStep Lax637351Proofs.Auxiliary
open Lax637351Proofs.Independent Lax637351Proofs.CrossoverSuccess
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {n : ℕ} {μ : ℕ+}

abbrev Index (μ : ℕ+) := Bool × (Fin μ × Fin μ)
abbrev Masks (n : ℕ) := BitString n × BitString n
abbrev Innovation (n : ℕ) (μ : ℕ+) := Index μ × Masks n

def indexLaw (μ : ℕ+) (p : ℝ) : PMF (Index μ) :=
  (coin p).bind fun c ↦ (PMF.uniformOfFintype (Fin μ × Fin μ)).map (fun ij ↦ (c, ij))

def maskLaw (n : ℕ) : PMF (Masks n) :=
  (PMF.uniformOfFintype (BitString n)).bind fun m ↦
    (independentBits n (1 / (n : ℝ))).map fun f ↦ (m, f)

def innovationLaw (n : ℕ) (μ : ℕ+) (p : ℝ) : PMF (Innovation n μ) :=
  (indexLaw μ p).bind fun i ↦ (maskLaw n).map fun m ↦ (i, m)

def beforeMutation (P : Population n μ) (s : Innovation n μ) : BitString n :=
  if s.1.1 then crossover (P s.1.2.1) (P s.1.2.2) s.2.1 else P s.1.2.1

def asDraw (P : Population n μ) (s : Innovation n μ) : Draw n :=
  (s.1.1, beforeMutation P s, s.2.2)

lemma uniform_fst (α β : Type*) [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  apply PMF.ext
  intro a
  let u := PMF.uniformOfFintype (α × β)
  let v := PMF.uniformOfFintype α
  apply (ENNReal.toReal_eq_toReal_iff' ((u.map Prod.fst).apply_ne_top a) (v.apply_ne_top a)).mp
  let f (x : α) : ℝ := if x = a then 1 else 0
  have he (p : PMF α) : mean p f = (p a).toReal := by
    unfold mean
    simp only [f, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]
  change ((u.map Prod.fst) a).toReal = (v a).toReal
  rw [← he, ← he, mean_map]
  have h := mean_uniform_pair (fun x : α ↦ fun _ : β ↦ f x)
  simpa only [mean_const] using h

lemma innovation_draws (n : ℕ) (μ : ℕ+) (p : ℝ) (P : Population n μ) :
    (innovationLaw n μ p).map (asDraw P) = draws p P := by
  simp only [innovationLaw, indexLaw, maskLaw, draws, PMF.map_bind, PMF.bind_map, PMF.map_comp, PMF.bind_bind,
    Function.comp_def, asDraw, beforeMutation]
  congr 1
  funext b
  cases b
  · simp only [Bool.false_eq_true, if_false, parents]
    have heq (ij : Fin μ × Fin μ) :
        ((PMF.uniformOfFintype (BitString n)).bind fun _ ↦
          (independentBits n (1 / (n : ℝ))).map (fun f ↦ (false, P ij.1, f))) =
            (independentBits n (1 / (n : ℝ))).map (fun f ↦ (false, P ij.1, f)) :=
      PMF.bind_const _ _
    simp only [heq]
    have hf := PMF.bind_map (PMF.uniformOfFintype (Fin μ × Fin μ)) Prod.fst
      (fun i ↦ (independentBits n (1 / (n : ℝ))).map (fun f ↦ (false, P i, f)))
    rw [uniform_fst] at hf
    rw [PMF.bind_map]
    exact hf.symm
  · simp only [if_true, parents, Bind.bind, Pure.pure, PMF.bind_bind, PMF.pure_bind]

lemma step_innovations (k : ℕ) (p : ℝ) (ar : Bool) (P : Population n μ) :
    step (jump k) p ar P = (innovationLaw n μ p).bind (fun s ↦
      let d := asDraw P s
      select (jump k) ar d.1 P d.2.1 (child d)) := by
  rw [step_draw_factor, ← innovation_draws, PMF.bind_map]
  rfl

def bitCoin (p : ℝ) : PMF (Fin 2) :=
  (coin p).map (fun b ↦ if b then 1 else 0)

lemma bitCoin_apply (p : ℝ) (b : Fin 2) : bitCoin p b = coin p (b = 1) := by
  simp only [bitCoin, PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  fin_cases b <;> simp

def coordinateLaw (n : ℕ) : PMF (Fin 2 × Fin 2) :=
  (bitCoin (1 / 2)).bind fun b ↦ (bitCoin (1 / (n : ℝ))).map fun f ↦ (b, f)

def rearrange {n : ℕ} (m : Fin n → Fin 2 × Fin 2) : Masks n :=
  (fun j ↦ (m j).1, fun j ↦ (m j).2)

lemma bind_pair_apply {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (q : PMF β)
    (x : α) (y : β) :
    (p.bind fun a ↦ q.map fun b ↦ (a, b)) (x, y) = p x * q y := by
  simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype, Prod.mk.injEq]
  have hh (a : α) : (∑ b, if x = a ∧ y = b then q b else 0) =
      if x = a then q y else 0 := by
    by_cases h : x = a
    · simp only [h, true_and, if_true, Finset.sum_ite_eq, Finset.mem_univ]
    · simp [h]
  simp only [hh, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma coordinateLaw_apply (n : ℕ) (x : Fin 2 × Fin 2) :
    coordinateLaw n x = coin (1 / 2) (x.1 = 1) * coin (1 / (n : ℝ)) (x.2 = 1) := by
  rcases x with ⟨b, f⟩
  rw [coordinateLaw, bind_pair_apply, bitCoin_apply, bitCoin_apply]

lemma maskLaw_apply (n : ℕ) (x : Masks n) :
    maskLaw n x = (∏ j, coin (1 / 2) (x.1 j = 1)) * ∏ j, coin (1 / (n : ℝ)) (x.2 j = 1) := by
  rcases x with ⟨m, f⟩
  rw [maskLaw, ← fair_bits_uniform, bind_pair_apply,
    OffspringProduct.independentBits_apply, OffspringProduct.independentBits_apply]

lemma innovationLaw_apply (n : ℕ) (μ : ℕ+) (p : ℝ) (x : Innovation n μ) :
    innovationLaw n μ p x = indexLaw μ p x.1 *
      (∏ j, coordinateLaw n (x.2.1 j, x.2.2 j)) := by
  rcases x with ⟨i, m, f⟩
  rw [innovationLaw, bind_pair_apply, maskLaw_apply]
  simp_rw [coordinateLaw_apply, Finset.prod_mul_distrib]

end
end Lax637351Proofs.TapeDraw
