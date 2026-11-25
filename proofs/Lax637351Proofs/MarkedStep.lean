import Lax637351Proofs.Mutation

namespace Lax637351Proofs.MarkedStep

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open scoped Classical ENNReal

noncomputable section

variable {n : ℕ} {μ : ℕ+}

abbrev Draw (n : ℕ) := Bool × BitString n × BitString n

def child (d : Draw n) : BitString n := mutate d.2.1 d.2.2

def discarded (avoid : Bool) (d : Draw n) : Prop :=
  avoid ∧ ¬ d.1 ∧ child d = d.2.1

def draws (p : ℝ) (P : Population n μ) : PMF (Draw n) :=
  (coin p).bind fun cross ↦ (parents P cross).bind fun y ↦
    (independentBits n (1 / (n : ℝ))).map fun m ↦ (cross, y, m)

def stepMarked (fitness : BitString n → ℝ) (p : ℝ) (avoid : Bool) (P : Population n μ) :
    PMF (Draw n × Population n μ) :=
  (draws p P).bind fun d ↦ (select fitness avoid d.1 P d.2.1 (child d)).map fun Q ↦ (d, Q)

lemma stepMarked_population (fitness : BitString n → ℝ) (p : ℝ) (avoid : Bool) (P : Population n μ) :
    (stepMarked fitness p avoid P).map Prod.snd = step fitness p avoid P := by
  simp only [stepMarked, draws, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind,
    PMF.bind_map, step_eq, child]
  have hm (q : PMF (Population n μ)) : q.map (fun Q ↦ Q) = q := PMF.map_id q
  simp only [hm]

lemma stepMarked_draws (fitness : BitString n → ℝ) (p : ℝ) (avoid : Bool) (P : Population n μ) :
    (stepMarked fitness p avoid P).map Prod.fst = draws p P := by
  have hm (q : PMF (Population n μ)) (d : Draw n) :
      q.map (fun _ ↦ d) = PMF.pure d := PMF.map_const q d
  simp only [stepMarked, PMF.map_bind, PMF.map_comp, Function.comp_def, hm,
    PMF.bind_pure]

lemma mean_draws {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (f : Draw n → ℝ) :
    mean (draws p P) f =
      p * mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
          (fun m ↦ f (true, y, m))) +
      (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦ f (false, P i, m))) := by
  simp only [draws, mean_bind, mean_coin hp, parents, Bool.false_eq_true, if_false, mean_map]

lemma mean_marked {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (fitness : BitString n → ℝ) (avoid : Bool)
    (P : Population n μ) (f : Draw n → Population n μ → ℝ) :
    mean (stepMarked fitness p avoid P) (fun d ↦ f d.1 d.2) =
      p * mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
        (fun m ↦ mean (select fitness avoid true P y (mutate y m)) (f (true, y, m)))) +
      (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        mean (independentBits n (1 / (n : ℝ)))
          (fun m ↦ mean (select fitness avoid false P (P i) (mutate (P i) m)) (f (false, P i, m)))) := by
  simp only [stepMarked, mean_bind, mean_map, mean_draws hp, child]

lemma mask_marginal (p : ℝ) (P : Population n μ) :
    (draws p P).map (fun d ↦ d.2.2) = independentBits n (1 / (n : ℝ)) := by
  have hm (q : PMF (BitString n)) : q.map (fun m ↦ m) = q := PMF.map_id q
  simp only [draws, PMF.map_bind, PMF.map_comp, Function.comp_def, hm, PMF.bind_const]

end
end Lax637351Proofs.MarkedStep
