import Lax637351Proofs.TapeDraw
import Lax637351Proofs.SparseDeviation
import Lax637351Proofs.FiniteHitting

namespace Lax637351Proofs.TapeRun

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.TapeDraw Lax637351Proofs.Independent Lax637351Proofs.MarkedStep
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteHitting
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {α β : Type*} {n L : ℕ} {μ : ℕ+}

lemma product_succ [Fintype β] (p : PMF β) (L : ℕ) :
    product (fun _ : Fin (L + 1) ↦ p) =
      p.bind (fun a ↦ (product (fun _ : Fin L ↦ p)).map (Fin.cons a)) := by
  let e := Fin.consEquiv (fun _ : Fin (L + 1) ↦ β)
  let q := product (fun _ : Fin L ↦ p)
  let r := p.bind fun a ↦ q.map (fun u ↦ (a, u))
  have he : r.map e = p.bind (fun a ↦ q.map (Fin.cons a)) := by
    simp only [r, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rfl
  rw [← he]
  ext u
  have hr : (r.map e) u = r (e.symm u) := by
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (e.symm u)]
    · simp
    · intro x _ hx
      have h : u ≠ e x := fun hh ↦ hx (e.injective (hh.symm.trans (e.apply_symm_apply u).symm))
      simp [h]
    · simp
  rw [hr, show e.symm u = (u 0, Fin.tail u) by rfl]
  dsimp only [r, q]
  rw [bind_pair_apply, product_apply, Fin.prod_univ_succ, product_apply]
  rfl

def realize (f : α → β → PMF α) : (L : ℕ) → (Fin L → β) → α → PMF α
  | 0, _, x => PMF.pure x
  | L + 1, u, x => (f x (u 0)).bind fun y ↦ realize f L (Fin.tail u) y

lemma mixture [Fintype β] (p : PMF β) (f : α → β → PMF α) (L : ℕ) (x : α) :
    (product (fun _ : Fin L ↦ p)).bind (fun u ↦ realize f L u x) =
      law (fun y ↦ p.bind (f y)) (PMF.pure x) L := by
  induction L generalizing x with
  | zero => simp [realize, law_zero, PMF.bind_const]
  | succ L ih =>
    rw [product_succ, law_first_step]
    simp only [realize, PMF.bind_bind, PMF.bind_map, Function.comp_def, Fin.cons_zero, Fin.tail_cons]
    congr 1
    funext a
    rw [PMF.bind_comm (product (fun _ : Fin L ↦ p)) (f x a)]
    simp_rw [ih]

abbrev Schedule (L : ℕ) (μ : ℕ+) := Fin L → Fin ((μ : ℕ) + 1)

def innovation (a : Index μ) (u : Fin n → Fin 2 × Fin 2) : Innovation n μ :=
  (a, rearrange u)

def assemble (a : Fin L → Index μ) (u : Fin n → Fin L → Fin 2 × Fin 2) : Fin L → Innovation n μ :=
  fun t ↦ innovation (a t) (fun j ↦ u j t)

lemma factor_tapes (n : ℕ) (μ : ℕ+) (p : ℝ) (L : ℕ) :
    product (fun _ : Fin L ↦ innovationLaw n μ p) =
      (product (fun _ : Fin L ↦ indexLaw μ p)).bind fun a ↦
        (product (fun _ : Fin n ↦ product (fun _ : Fin L ↦ coordinateLaw n))).map (assemble a) := by
  let I := product (fun _ : Fin L ↦ indexLaw μ p)
  let M := product (fun _ : Fin n ↦ product (fun _ : Fin L ↦ coordinateLaw n))
  let e : ((Fin L → Index μ) × (Fin n → Fin L → Fin 2 × Fin 2)) ≃ (Fin L → Innovation n μ) :=
    ⟨fun x ↦ assemble x.1 x.2, fun x ↦ (fun t ↦ (x t).1, fun j t ↦ ((x t).2.1 j, (x t).2.2 j)),
      fun x ↦ by rcases x with ⟨a, v⟩; rfl, fun x ↦ by funext t; rfl⟩
  let F := I.bind fun a ↦ M.map (fun u ↦ (a, u))
  have he : F.map e = I.bind fun a ↦ M.map (assemble a) := by
    simp only [F, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rfl
  change _ = I.bind (fun a ↦ M.map (assemble a))
  rw [← he]
  ext x
  have hr : (F.map e) x = F (e.symm x) := by
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (e.symm x)]
    · simp
    · intro j _ hj
      have h : x ≠ e j := fun hh ↦ hj (e.injective (hh.symm.trans (e.apply_symm_apply x).symm))
      simp [h]
    · simp
  rw [hr, show e.symm x = (fun t ↦ (x t).1, fun j t ↦ ((x t).2.1 j, (x t).2.2 j)) by rfl]
  dsimp only [F]
  rw [bind_pair_apply]
  simp only [I, M, product_apply, innovationLaw_apply, Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_comm

def scheduled : (L : ℕ) → (Fin L → Innovation n μ) → Schedule L μ → Population n μ → Population n μ
  | 0, _, _, P => P
  | L + 1, u, d, P =>
    scheduled L (Fin.tail u) (Fin.tail d) (replace P (child (asDraw P (u 0))) (d 0))

def oneUpdate (k : ℕ) (active : Set (Population n μ)) (P : Population n μ)
    (u : Innovation n μ) : PMF (Population n μ) :=
  if P ∈ active then Transitions.insert (jump k) P (child (asDraw P u)) else PMF.pure P

lemma mixture_step (k : ℕ) (p : ℝ) (A : Set (Population n μ)) (P : Population n μ) :
    (innovationLaw n μ p).bind (oneUpdate k A P) = stopped (step (jump k) p false) A P := by
  by_cases h : P ∈ A
  · rw [stopped, if_pos h, step_innovations]
    congr 1
    funext u
    simp [oneUpdate, h, select]
  · rw [stopped, if_neg h, show oneUpdate k A P = fun _ ↦ PMF.pure P by funext u; simp [oneUpdate, h], PMF.bind_const]

lemma realized_schedule (k : ℕ) (A : Set (Population n μ)) (L : ℕ) (u : Fin L → Innovation n μ)
    (P Q : Population n μ) (hQ : Q ∈ (realize (oneUpdate k A) L u P).support) :
    ∃ d : Schedule L μ, Q = scheduled L u d P := by
  induction L generalizing P Q with
  | zero =>
    refine ⟨fun i ↦ i.elim0, ?_⟩
    exact (PMF.mem_support_pure_iff _ _).mp hQ
  | succ L ih =>
    rw [realize] at hQ
    obtain ⟨P', hP', hQ⟩ := (PMF.mem_support_bind_iff _ _ _).mp hQ
    obtain ⟨d, hD⟩ := ih (Fin.tail u) P' Q hQ
    have he : ∃ a : Fin ((μ : ℕ) + 1), P' = replace P (child (asDraw P (u 0))) a := by
      by_cases h : P ∈ A
      · rw [oneUpdate, if_pos h] at hP'
        obtain ⟨a, _, ha⟩ := (PMF.mem_support_map_iff _ _ _).mp hP'
        exact ⟨a, ha.symm⟩
      · rw [oneUpdate, if_neg h] at hP'
        exact ⟨Fin.last _, by simpa [replace] using (PMF.mem_support_pure_iff _ _).mp hP'⟩
    obtain ⟨a, rfl⟩ := he
    refine ⟨Fin.cons a d, ?_⟩
    simpa only [scheduled, Fin.cons_zero, Fin.tail_cons] using hD

def bitProposal (a : Index μ) (m : Fin 2 × Fin 2) (v : Fin μ → Fin 2) : Fin 2 :=
  let b := if a.1 then (if m.1 = 1 then v a.2.1 else v a.2.2) else v a.2.1
  if m.2 = 1 then 1 - b else b

def bitUpdate (a : Index μ) (m : Fin 2 × Fin 2) (d : Fin ((μ : ℕ) + 1))
    (v : Fin μ → Fin 2) : Fin μ → Fin 2 :=
  Fin.lastCases v (fun i ↦ Function.update v i (bitProposal a m v)) d

def runColumn : (L : ℕ) → (Fin L → Index μ) → (Fin L → Fin 2 × Fin 2) →
    Schedule L μ → (Fin μ → Fin 2) → (Fin μ → Fin 2)
  | 0, _, _, _, v => v
  | L + 1, a, u, d, v =>
    runColumn L (Fin.tail a) (Fin.tail u) (Fin.tail d) (bitUpdate (a 0) (u 0) (d 0) v)

lemma column_separates (L : ℕ) (a : Fin L → Index μ) (u : Fin n → Fin L → Fin 2 × Fin 2)
    (d : Schedule L μ) (P : Population n μ) (j : Fin n) :
    (fun i ↦ scheduled L (assemble a u) d P i j) =
      runColumn L a (u j) d (fun i ↦ P i j) := by
  induction L generalizing P with
  | zero => rfl
  | succ L ih =>
    simp only [scheduled, runColumn]
    have hT : Fin.tail (assemble a u) = assemble (Fin.tail a) (fun j ↦ Fin.tail (u j)) := rfl
    rw [hT, ih]
    congr 1
    refine Fin.lastCases ?_ (fun i ↦ ?_) (d 0)
    · simp [replace, bitUpdate]
    · funext v
      by_cases hv : v = i
      · subst v
        simp only [replace, bitUpdate, Fin.lastCases_castSucc, Function.update_self]
        unfold child asDraw beforeMutation assemble innovation rearrange bitProposal
        cases hb : (a 0).1 <;> by_cases hm : (u j 0).1 = 1 <;>
          simp [hm, mutate, crossover]
      · simp [replace, bitUpdate, Function.update_of_ne hv]

end
end Lax637351Proofs.TapeRun
