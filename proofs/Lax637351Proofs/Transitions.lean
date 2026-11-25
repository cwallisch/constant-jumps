import Lax637351.Algorithm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Lax637351Proofs.Transitions

open Lax637351.Algorithm
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def zeros (x : BitString n) : Finset (Fin n) := Finset.univ.filter fun j ↦ x j = 0

@[simp] lemma mem_zeros (x : BitString n) (j : Fin n) : j ∈ zeros x ↔ x j = 0 := by
  simp [zeros]

lemma bit_eq_one_of_ne_zero (b : Fin 2) (hb : b ≠ 0) : b = 1 := by
  fin_cases b <;> simp_all

lemma ones_add_card_zeros (x : BitString n) : ones x + (zeros x).card = n := by
  rw [ones, zeros, Finset.card_filter, ← Finset.sum_add_distrib]
  have h (j : Fin n) : (x j : ℕ) + (if x j = 0 then 1 else 0) = 1 := by
    generalize x j = b
    fin_cases b <;> decide
  simp [h]

lemma zeros_eq_empty_iff (x : BitString n) : zeros x = ∅ ↔ x = optimum n := by
  constructor
  · intro h
    funext j
    apply bit_eq_one_of_ne_zero
    intro hz
    have hm := (mem_zeros x j).mpr hz
    simp [h] at hm
  · rintro rfl
    ext j
    simp [optimum]

lemma ones_optimum : ones (optimum n) = n := by simp [ones, optimum]

lemma ones_eq_n_iff (x : BitString n) : ones x = n ↔ x = optimum n := by
  rw [← zeros_eq_empty_iff, ← Finset.card_eq_zero]
  have := ones_add_card_zeros x
  omega

lemma jump_optimum : jump k (optimum n) = (k + n : ℕ) := by simp [jump, ones_optimum]

lemma jump_lt_optimum (hk : 0 < k) (x : BitString n) (hx : x ≠ optimum n) :
    jump k x < jump k (optimum n) := by
  have h := ones_add_card_zeros x
  have hne := mt (ones_eq_n_iff x).mp hx
  rw [jump_optimum, jump]
  split_ifs
  · exact_mod_cast (by omega : k + ones x < k + n)
  · exact_mod_cast (by omega : n - ones x < k + n)

lemma jump_of_many_zeros (hkn : k ≤ n) (x : BitString n) (hx : k ≤ (zeros x).card) :
    jump k x = (k + (n - (zeros x).card) : ℕ) := by
  have := ones_add_card_zeros x
  rw [jump, if_pos (Or.inl (by omega))]
  exact_mod_cast (by omega : k + ones x = k + (n - (zeros x).card))

lemma jump_of_few_zeros (hkn : k ≤ n) (x : BitString n)
    (hpos : 0 < (zeros x).card) (hx : (zeros x).card < k) :
    jump k x = (zeros x).card := by
  have := ones_add_card_zeros x
  rw [jump, if_neg (by omega)]
  exact_mod_cast (by omega : n - ones x = (zeros x).card)

lemma jump_plateau (hk : k ≤ n) (x : BitString n) (hx : (zeros x).card = k) :
    jump k x = n := by
  have := ones_add_card_zeros x
  rw [jump, if_pos (Or.inl (by omega))]
  exact_mod_cast (by omega : k + ones x = n)

lemma jump_lt_plateau (_hk : 0 < k) (hkn : k ≤ n) (x : BitString n)
    (hx : x ≠ optimum n) (hplat : (zeros x).card ≠ k) : jump k x < n := by
  have := ones_add_card_zeros x
  have hne := mt (ones_eq_n_iff x).mp hx
  unfold jump
  split_ifs with h
  · exact_mod_cast (by omega : k + ones x < n)
  · exact_mod_cast (by omega : n - ones x < n)

def replace (P : Population n μ) (z : BitString n)
    (d : Fin ((μ : ℕ) + 1)) : Population n μ :=
  Fin.lastCases P (fun i ↦ Function.update P i z) d

def insert (fitness : BitString n → ℝ) (P : Population n μ) (z : BitString n) :
    PMF (Population n μ) :=
  (deletionIndex fitness (Fin.lastCases z P)).map (replace P z)

def parents (P : Population n μ) (cross : Bool) : PMF (BitString n) :=
  if cross then do
    let (u, v) ← PMF.uniformOfFintype (Fin μ × Fin μ)
    let mask ← PMF.uniformOfFintype (BitString n)
    pure (crossover (P u) (P v) mask)
  else (PMF.uniformOfFintype (Fin μ)).map P

def select (fitness : BitString n → ℝ) (avoid cross : Bool) (P : Population n μ)
    (y z : BitString n) : PMF (Population n μ) :=
  if avoid ∧ ¬ cross ∧ z = y then PMF.pure P else insert fitness P z

lemma replace_eq (P : Population n μ) (z : BitString n) (d : Fin ((μ : ℕ) + 1)) :
    replace P z d = if h : d.val < (μ : ℕ) then Function.update P ⟨d.val, h⟩ z else P := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [replace]
  · simp [replace, i.isLt]

lemma step_eq (fitness : BitString n → ℝ) (p : ℝ) (avoid : Bool) (P : Population n μ) :
    step fitness p avoid P = (coin p).bind fun cross ↦ (parents P cross).bind fun y ↦
      (independentBits n (1 / (n : ℝ))).bind fun m ↦ select fitness avoid cross P y (mutate y m) := by
  simp only [step, parents, select, insert, PMF.map, Bind.bind, Pure.pure]
  congr 1
  funext cross
  cases cross <;> simp [PMF.bind_bind, replace_eq, Function.comp_def]

lemma deletion_min_lastCases (fitness : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) (d : Fin ((μ : ℕ) + 1))
    (hd : d ∈ (deletionIndex (μ := μ) fitness (Fin.lastCases z P)).support)
    (j : Fin ((μ : ℕ) + 1)) :
    fitness (Fin.lastCases z P d) ≤ fitness (Fin.lastCases z P j) := by
  have hh : ∀ j : Fin ((μ : ℕ) + 1),
      fitness (Fin.lastCases z P d) ≤ fitness (Fin.lastCases z P j) := by
    simpa only [deletionIndex, PMF.mem_support_uniformOfFinset_iff,
      Finset.mem_filter, Finset.mem_univ, true_and] using hd
  exact hh j

lemma deletion_uniform (fitness : BitString n → ℝ) (Q : Fin ((μ : ℕ) + 1) → BitString n)
    (v : ℝ) (hQ : ∀ j, fitness (Q j) = v) :
    deletionIndex fitness Q = PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)) := by
  simp [deletionIndex, hQ, PMF.uniformOfFintype]

lemma replace_fitness_mono (fitness : BitString n → ℝ) (P : Population n μ) (z : BitString n)
    (d : Fin ((μ : ℕ) + 1)) (hd : d ∈ (deletionIndex (μ := μ) fitness (Fin.lastCases z P)).support) :
    ∀ u, fitness (P u) ≤ fitness (replace P z d u) := by
  intro u
  rw [replace_eq]
  split_ifs with hold
  · let i : Fin μ := ⟨d.val, hold⟩
    change fitness (P u) ≤ fitness (Function.update P i z u)
    by_cases hu : u = i
    · subst u
      rw [Function.update_self]
      have hdi : d = i.castSucc := Fin.ext rfl
      have hz := deletion_min_lastCases fitness P z d hd (Fin.last (μ : ℕ))
      simpa only [hdi, Fin.lastCases_castSucc, Fin.lastCases_last] using hz
    · rw [Function.update_of_ne hu]
  · exact le_rfl

lemma insert_fitness_mono (fitness : BitString n → ℝ) (P : Population n μ) (z : BitString n)
    {Q : Population n μ} (hQ : Q ∈ (insert fitness P z).support) :
    ∀ u, fitness (P u) ≤ fitness (Q u) := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨d, hd, rfl⟩
  exact replace_fitness_mono fitness P z d hd

lemma select_fitness_mono (fitness : BitString n → ℝ) (avoid cross : Bool) (P : Population n μ)
    (y z : BitString n) {Q : Population n μ} (hQ : Q ∈ (select fitness avoid cross P y z).support) :
    ∀ u, fitness (P u) ≤ fitness (Q u) := by
  unfold select at hQ
  split_ifs at hQ
  · rw [(PMF.mem_support_pure_iff _ _).mp hQ]
    exact fun _ ↦ le_rfl
  · exact insert_fitness_mono fitness P z hQ

lemma insert_strict_improvement (fitness : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) (u : Fin μ) (hu : fitness (P u) < fitness z)
    {Q : Population n μ} (hQ : Q ∈ (insert fitness P z).support) :
    ∃ d : Fin μ, Q = Function.update P d z ∧ fitness (P d) ≤ fitness (P u) := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨d, hd, rfl⟩
  revert hd
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · intro hd
    have hmin := deletion_min_lastCases fitness P z _ hd u.castSucc
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hmin
    exact (not_lt_of_ge hmin hu).elim
  · intro hd
    have hmin := deletion_min_lastCases fitness P z _ hd u.castSucc
    simp only [Fin.lastCases_castSucc] at hmin
    exact ⟨i, by simp [replace], hmin⟩

lemma insert_support_of_worse (fitness : BitString n → ℝ) (P : Population n μ)
    (z : BitString n) (hz : ∀ i, fitness z < fitness (P i))
    {Q : Population n μ} (hQ : Q ∈ (insert fitness P z).support) : Q = P := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨d, hd, rfl⟩
  revert hd
  refine Fin.lastCases ?_ (fun i ↦ ?_) d
  · simp [replace]
  · intro hd
    have hmin := deletion_min_lastCases fitness P z _ hd (Fin.last (μ : ℕ))
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hmin
    exact (not_lt_of_ge hmin (hz i)).elim

lemma insert_eq_uniform (fitness : BitString n → ℝ) (P : Population n μ) (z : BitString n)
    (hfit : ∀ i, fitness (P i) = fitness z) :
    insert fitness P z = (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1))).map (replace P z) := by
  unfold insert
  rw [deletion_uniform (μ := μ) fitness _ (fitness z)]
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · simpa only [Fin.lastCases_castSucc] using hfit j

lemma step_fitness_mono (fitness : BitString n → ℝ) (p : ℝ) (avoid : Bool) (P : Population n μ)
    {Q : Population n μ} (hQ : Q ∈ (step fitness p avoid P).support) :
    ∀ u, fitness (P u) ≤ fitness (Q u) := by
  rw [step_eq] at hQ
  rcases (PMF.mem_support_bind_iff _ _ _).mp hQ with ⟨cross, _, hQ⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp hQ with ⟨y, _, hQ⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp hQ with ⟨m, _, hQ⟩
  exact select_fitness_mono fitness avoid cross P y (mutate y m) hQ

def missing (P : Population n μ) : Prop := ∀ i, P i ≠ optimum n

lemma step_preserves_optimum (hk : 0 < k) (p : ℝ) (avoid : Bool) {P Q : Population n μ}
    (hP : ¬ missing P) (hQ : Q ∈ (step (jump k) p avoid P).support) : ¬ missing Q := by
  obtain ⟨i, hi⟩ : ∃ i, P i = optimum n := by simpa [missing] using hP
  intro h
  have hm := step_fitness_mono (jump k) p avoid P hQ i
  exact (not_lt_of_ge (hi ▸ hm)) (jump_lt_optimum hk (Q i) (h i))

lemma step_preserves_plateau_or_optimum (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (avoid : Bool)
    {P Q : Population n μ} (hP : ∀ u, (zeros (P u)).card = k)
    (hQ : Q ∈ (step (jump k) p avoid P).support) (hmiss : missing Q) :
    ∀ u, (zeros (Q u)).card = k := by
  intro u
  by_contra hn
  have hm := step_fitness_mono (jump k) p avoid P hQ u
  rw [jump_plateau hkn (P u) (hP u)] at hm
  exact (not_lt_of_ge hm) (jump_lt_plateau hk hkn (Q u) (hmiss u) hn)

end
end Lax637351Proofs.Transitions
