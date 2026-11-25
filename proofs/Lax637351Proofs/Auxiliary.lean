import Lax637351Proofs.Ordinary
import Lax637351Proofs.MaskKernel
import Lax637351Proofs.RuntimeBridge

namespace Lax637351Proofs.Auxiliary

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs Lax637351Proofs.MarkedStep Lax637351Proofs.Ordinary
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def rejectSelect (k : ℕ) (ar : Bool) (P : Population n μ) (d : Draw n) :
    PMF (Population n μ) :=
  if child d = optimum n then PMF.pure P
  else select (jump k) ar d.1 P d.2.1 (child d)

def auxiliary (k : ℕ) (p : ℝ) (ar : Bool) (P : Population n μ) : PMF (Population n μ) :=
  (draws p P).bind (rejectSelect k ar P)

def tagged (k : ℕ) (p : ℝ) (ar : Bool) (s : Bool × Population n μ) :
    PMF (Bool × Population n μ) :=
  (draws p s.2).bind fun d ↦ (rejectSelect k ar s.2 d).map (fun Q ↦ (s.1 || decide (child d = optimum n), Q))

def alive (P : Population n μ) : Option (Population n μ) :=
  if missing P then some P else none

def taggedAlive (s : Bool × Population n μ) : Option (Population n μ) :=
  if s.1 then none else some s.2

lemma map_constant_on_support {α β : Type*} (ν : PMF α) (f : α → β) (b : β)
    (h : ∀ x ∈ ν.support, f x = b) :
    ν.map f = PMF.pure b := by
  have hh : (ν.map f).support ⊆ ({b} : Set β) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    exact h x hx
  have hmass := (PMF.toOuterMeasure_apply_eq_one_iff (ν.map f) ({b} : Set β)).mpr hh
  rw [PMF.toOuterMeasure_apply_singleton] at hmass
  apply PMF.ext
  intro b'
  by_cases he : b' = b
  · subst b'
    simpa only [PMF.pure_apply_self] using hmass
  · have hh' : b' ∉ (ν.map f).support := fun h' ↦ he (hh h')
    rw [PMF.pure_apply_of_ne _ _ he]
    by_contra hn
    exact hh' ((PMF.mem_support_iff _ _).mpr hn)

lemma step_draw_factor (k : ℕ) (p : ℝ) (ar : Bool) (P : Population n μ) :
    step (jump k) p ar P =
      (draws p P).bind (fun d ↦ select (jump k) ar d.1 P d.2.1 (child d)) := by
  simp [step_eq, draws, child, PMF.bind_bind, PMF.bind_map, Function.comp_def]

lemma select_preserves_missing {P Q : Population n μ} (hP : missing P) (ar cross : Bool)
    (y z : BitString n) (hz : z ≠ optimum n)
    (hQ : Q ∈ (select (jump k) ar cross P y z).support) : missing Q := by
  intro i
  unfold select at hQ
  split_ifs at hQ
  · rw [(PMF.mem_support_pure_iff _ _).mp hQ]
    exact hP i
  · rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨d, _, rfl⟩
    refine Fin.lastCases ?_ (fun u ↦ ?_) d
    · simpa [replace] using hP i
    · by_cases hu : i = u
      · simpa [replace, hu] using hz
      · simpa only [replace, Fin.lastCases_castSucc, Function.update_of_ne hu] using hP i

lemma select_opt_of_draw (hk : 0 < k) {p : ℝ} {ar : Bool} {P : Population n μ}
    (hP : missing P) (d : Draw n) (hd : d ∈ (draws p P).support)
    (hz : child d = optimum n) (Q : Population n μ)
    (hQ : Q ∈ (select (jump k) ar d.1 P d.2.1 (child d)).support) : ¬ missing Q := by
  have hn : ¬ (ar = true ∧ ¬d.1 = true ∧ child d = d.2.1) := by
    rintro ⟨_, hb, he⟩
    have hfalse : d.1 = false := Bool.eq_false_of_not_eq_true hb
    have hy := MaskKernel.chosen_draw_parent hd
    rw [hfalse] at hy
    have hh : d.2.1 ∈ ((PMF.uniformOfFintype (Fin μ)).map P).support := by simpa [parents] using hy
    obtain ⟨i, _, hi⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    exact hP i (hi.trans (he.symm.trans hz))
  rw [select, if_neg hn, hz] at hQ
  obtain ⟨i, rfl, _⟩ := insert_strict_improvement (jump k) P (optimum n) (0 : Fin μ)
    (jump_lt_optimum hk _ (hP 0)) hQ
  exact fun h ↦ h i (Function.update_self i (optimum n) P)

lemma bind_congr_support {α β : Type*} (ν : PMF α) (f g : α → PMF β)
    (h : ∀ x ∈ ν.support, f x = g x) : ν.bind f = ν.bind g := by
  apply PMF.ext
  intro b
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ ν.support
  · rw [h x hx]
  · have he : ν x = 0 := (PMF.mem_support_iff _ _).not.mp hx |> not_not.mp
    simp [he]

lemma select_map_alive (hk : 0 < k) {p : ℝ} (ar : Bool) {P : Population n μ}
    (hP : missing P) (d : Draw n) (hd : d ∈ (draws p P).support) :
    (select (jump k) ar d.1 P d.2.1 (child d)).map alive =
      (rejectSelect k ar P d).map (fun Q ↦ taggedAlive (decide (child d = optimum n), Q)) := by
  by_cases hz : child d = optimum n
  · have he := map_constant_on_support (select (jump k) ar d.1 P d.2.1 (child d)) alive none
      (fun Q hQ ↦ by simp [alive, select_opt_of_draw hk hP d hd hz Q hQ])
    rw [he, rejectSelect, if_pos hz, PMF.pure_map]
    simp [taggedAlive, hz]
  · rw [rejectSelect, if_neg hz]
    simp only [taggedAlive, hz, decide_false, Bool.false_eq_true, if_false]
    have h (Q : Population n μ) (hQ : Q ∈ (select (jump k) ar d.1 P d.2.1 (child d)).support) :
        alive Q = some Q := by simp [alive, select_preserves_missing hP ar d.1 d.2.1 _ hz hQ]
    simp only [PMF.map, Function.comp_def]
    exact bind_congr_support _ _ _ (fun Q hQ ↦ congrArg PMF.pure (h Q hQ))

lemma tagged_marginal (k : ℕ) (p : ℝ) (ar : Bool) (s : Bool × Population n μ) :
    (tagged k p ar s).map Prod.snd = auxiliary k p ar s.2 := by
  have hm (q : PMF (Population n μ)) : q.map (fun x ↦ x) = q := PMF.map_id q
  simp only [tagged, auxiliary, PMF.map_bind, PMF.map_comp, Function.comp_def, hm]

lemma rejectSelect_missing (k : ℕ) (ar : Bool) (P : Population n μ) (hP : missing P)
    (d : Draw n) (Q : Population n μ) (hQ : Q ∈ (rejectSelect k ar P d).support) : missing Q := by
  unfold rejectSelect at hQ
  split_ifs at hQ with h
  · rw [(PMF.mem_support_pure_iff _ _).mp hQ]
    exact hP
  · exact select_preserves_missing hP ar d.1 d.2.1 (child d) h hQ

lemma tagged_missing (k : ℕ) (p : ℝ) (ar : Bool) (s : Bool × Population n μ)
    (hs : missing s.2) (v : Bool × Population n μ) (hv : v ∈ (tagged k p ar s).support) : missing v.2 := by
  rcases (PMF.mem_support_bind_iff _ _ _).mp hv with ⟨d, _, hv⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨Q, hQ, rfl⟩
  exact rejectSelect_missing k ar s.2 hs d Q hQ

def killed (k : ℕ) (p : ℝ) (ar : Bool) : Option (Population n μ) → PMF (Option (Population n μ))
  | none => PMF.pure none
  | some P => (step (jump k) p ar P).map alive

lemma physical_killed (hk : 0 < k) (p : ℝ) (ar : Bool) (P : Population n μ) :
    (step (jump k) p ar P).map alive = killed k p ar (alive P) := by
  by_cases hP : missing P
  · rw [alive, if_pos hP, killed]
  · rw [show alive P = none by simp [alive, hP], killed]
    apply map_constant_on_support
    intro Q hQ
    have h := step_preserves_optimum hk p ar hP hQ
    simp [alive, h]

lemma tagged_killed (hk : 0 < k) (p : ℝ) (ar : Bool) (s : Bool × Population n μ) (hs : missing s.2) :
    (tagged k p ar s).map taggedAlive = killed k p ar (taggedAlive s) := by
  rcases s with ⟨b, P⟩
  cases b
  · simp only [taggedAlive, Bool.false_eq_true, if_false, killed, tagged, PMF.map_bind,
      PMF.map_comp, Function.comp_def, Bool.false_or]
    rw [step_draw_factor, PMF.map_bind]
    exact bind_congr_support _ _ _ (fun d hd ↦ (select_map_alive hk ar hs d hd).symm)
  · simp only [taggedAlive, if_true, killed, tagged, PMF.map_bind, PMF.map_comp,
      Function.comp_def, Bool.true_or]
    have h (d : Draw n) : ((rejectSelect k ar P d).map (fun _ ↦ none : Population n μ → Option (Population n μ))) =
        PMF.pure none := PMF.map_const _ _
    simp only [h, PMF.bind_const]

lemma law_map_of_support {α β : Type*} (K : α → PMF α) (L : β → PMF β)
    (f : α → β) (ν : PMF α) (I : Set α) (hν : ∀ x ∈ ν.support, x ∈ I)
    (hK : ∀ x ∈ I, ∀ y ∈ (K x).support, y ∈ I)
    (h : ∀ x ∈ I, (K x).map f = L (f x)) (t : ℕ) :
    (law K ν t).map f = law L (ν.map f) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [law_succ, law_succ, PMF.map_bind, ← ih, PMF.bind_map]
    exact bind_congr_support _ _ _ (fun x hx ↦ h x (law_invariant K ν I hν hK t x hx))

lemma tagged_population_law (k : ℕ) (p : ℝ) (ar : Bool) (ν : PMF (Bool × Population n μ)) (t : ℕ) :
    (law (tagged k p ar) ν t).map Prod.snd = law (auxiliary k p ar) (ν.map Prod.snd) t :=
  law_map_of_support (tagged k p ar) (auxiliary k p ar) Prod.snd ν Set.univ
    (by simp) (by simp) (fun s _ ↦ tagged_marginal k p ar s) t

lemma marked_failure_probability (hk : 0 < k) (p : ℝ) (ar : Bool)
    (ν : PMF (Population n μ)) (hν : ∀ P ∈ ν.support, missing P) (t : ℕ) :
    (law (step (jump k) p ar) ν t).toOuterMeasure {P | missing P} =
      (law (tagged k p ar) (ν.map (fun P ↦ (false, P))) t).toOuterMeasure {s | s.1 = false} := by
  let ν' := ν.map (fun P ↦ (false, P))
  have hν' : ∀ s ∈ ν'.support, missing s.2 := by
    intro s hs
    obtain ⟨P, hP, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
    exact hν P hP
  have h₁ := law_map_of_support (step (jump k) p ar) (killed k p ar) alive ν Set.univ (by simp) (by simp)
    (fun P _ ↦ physical_killed hk p ar P) t
  have h₂ := law_map_of_support (tagged k p ar) (killed k p ar) taggedAlive ν' {s | missing s.2} hν'
    (fun s hs v hv ↦ tagged_missing k p ar s hs v hv) (fun s hs ↦ tagged_killed hk p ar s hs) t
  have h₀ : ν.map alive = ν'.map taggedAlive := by
    rw [PMF.map_comp]
    simp only [PMF.map, Function.comp_def, taggedAlive, Bool.false_eq_true, if_false]
    exact bind_congr_support _ _ _ (fun P hP ↦ by simp [alive, hν P hP])
  rw [h₀, ← h₂] at h₁
  have hh := congrArg (fun q : PMF (Option (Population n μ)) ↦ q.toOuterMeasure {x | x ≠ none}) h₁
  simp only [PMF.toOuterMeasure_map_apply] at hh
  have he : alive ⁻¹' {x : Option (Population n μ) | x ≠ none} = {P | missing P} := by
    ext P
    by_cases h : missing P <;> simp [alive, h]
  have hf : taggedAlive ⁻¹' {x : Option (Population n μ) | x ≠ none} = {s | s.1 = false} := by
    ext s
    cases hb : s.1 <;> simp [taggedAlive, hb]
  simpa only [he, hf] using hh

end
end Lax637351Proofs.Auxiliary
