import Lax637351Proofs.Sampling
import Lax637351Proofs.ElementaryBounds

namespace Lax637351Proofs.Mutation

open Lax637351.Algorithm
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Transitions
open scoped Classical ENNReal

noncomputable section

variable {n : ℕ}

def mask (S : Finset (Fin n)) : BitString n := fun i ↦ if i ∈ S then 1 else 0

@[simp] lemma mask_eq_one (S : Finset (Fin n)) (j : Fin n) : mask S j = 1 ↔ j ∈ S := by
  by_cases h : j ∈ S <;> simp [mask, h]

lemma mask_injective : Function.Injective (mask (n := n)) := by
  intro S T h
  ext j
  rw [← mask_eq_one, ← mask_eq_one, h]

lemma weight (S : Finset (Fin n)) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) :
    (independentBits n p (mask S)).toReal = p ^ S.card * (1 - p) ^ (n - S.card) := by
  simp only [independentBits, PMF.ofFintype_apply, ENNReal.toReal_prod]
  rw [← Finset.prod_compl_mul_prod S]
  have h₀ : ∀ j ∈ Sᶜ, (coin p (mask S j = 1)).toReal = 1 - p := by
    intro j hj
    have hn := Finset.mem_compl.mp hj
    simp [mask, hn, coin_false hp, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
  have h₁ : ∀ j ∈ S, (coin p (mask S j = 1)).toReal = p := by
    intro j hj
    simp [mask, hj, coin_true hp, ENNReal.toReal_ofReal hp.1]
  rw [Finset.prod_congr rfl h₀, Finset.prod_congr rfl h₁, Finset.prod_const,
    Finset.prod_const, Finset.card_compl, Fintype.card_fin, mul_comm]

lemma rate_valid (hn : 2 ≤ n) : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

lemma weight_lower (hn : 2 ≤ n) (S : Finset (Fin n)) :
    (1 / (n : ℝ)) ^ S.card * (1 / 8) ≤ (independentBits n (1 / (n : ℝ)) (mask S)).toReal := by
  have hp := rate_valid hn
  rw [weight S hp]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp.1 _)
  exact (ElementaryBounds.no_mutation_lower n hn).trans <|
    pow_le_pow_of_le_one (sub_nonneg.mpr hp.2) (sub_le_self _ hp.1) (Nat.sub_le _ _)

lemma zero_set_flip (x : BitString n) (S : Finset (Fin n)) :
    zeros (mutate x (mask S)) = (zeros x \ S) ∪ (S \ zeros x) := by
  ext j
  have hb (b : Fin 2) : 1 - b = 0 ↔ b ≠ 0 := by
    fin_cases b <;> decide
  by_cases h : j ∈ S <;> simp [mutate, mask, h, hb]

lemma mask_zeros_compl (m : BitString n) : mask (zeros m)ᶜ = m := by
  funext j
  by_cases h : m j = 0
  · simp [mask, h]
  · have h' := bit_eq_one_of_ne_zero _ h
    simp [mask, h']

lemma equal_card_no_hit (x m : BitString n)
    (h : ¬ ∃ j ∈ zeros x, m j = 1)
    (hcard : (zeros (mutate x m)).card = (zeros x).card) :
    mutate x m = x := by
  let S := (zeros m)ᶜ
  have hdis : Disjoint (zeros x) S := by
    apply Finset.disjoint_left.mpr
    intro j hj hS
    have hm := bit_eq_one_of_ne_zero (m j) (by simpa [S] using hS)
    exact h ⟨j, hj, hm⟩
  have hnew : zeros (mutate x m) = zeros x ∪ S := by
    conv_lhs => rw [← mask_zeros_compl m]
    rw [zero_set_flip, hdis.sdiff_eq_left, hdis.symm.sdiff_eq_left]
  rw [hnew, Finset.card_union_of_disjoint hdis] at hcard
  have hempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
  conv_lhs => rw [← mask_zeros_compl m]
  change mutate x (mask S) = x
  funext j
  simp [hempty, mutate, mask]

lemma mutate_mask_ne (x : BitString n) {S : Finset (Fin n)} (hS : S.Nonempty) :
    mutate x (mask S) ≠ x := by
  obtain ⟨j, hj⟩ := hS
  intro heq
  have h := congrFun heq j
  simp only [mutate, (mask_eq_one S j).mpr hj, if_true] at h
  generalize x j = b at h
  fin_cases b <;> norm_num at h

lemma flip_zero_card (x : BitString n) {j : Fin n} (hj : j ∈ zeros x) :
    (zeros (mutate x (mask {j}))).card = (zeros x).card - 1 := by
  have he : ({j} : Finset (Fin n)) \ zeros x = ∅ := by
    ext i
    by_cases h : i = j <;> simp [h, hj]
  rw [zero_set_flip, Finset.sdiff_singleton_eq_erase, he,
    Finset.union_empty, Finset.card_erase_of_mem hj]

lemma flip_one_card (x : BitString n) {j : Fin n} (hj : j ∉ zeros x) :
    (zeros (mutate x (mask {j}))).card = (zeros x).card + 1 := by
  have he : ({j} : Finset (Fin n)) \ zeros x = {j} := by
    ext i
    by_cases h : i = j <;> simp [h, hj]
  rw [zero_set_flip, Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hj,
    he, Finset.union_singleton, Finset.card_insert_of_notMem hj]

lemma swap_zero_set (x : BitString n) {a b : Fin n} (ha : a ∈ zeros x) (hb : b ∉ zeros x) :
    zeros (mutate x (mask {a, b})) = {b} ∪ (zeros x).erase a := by
  rw [zero_set_flip]
  ext j
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase]
  by_cases hja : j = a
  · subst j
    simp [ha, show a ≠ b from fun h ↦ hb (h ▸ ha)]
  · by_cases hjb : j = b
    · subst j
      simp [hb]
    · simp [hja, hjb]

lemma single_mask_event (hn : 2 ≤ n) (S : Finset (Fin n)) (G : BitString n → Prop)
    (hG : ∀ j ∈ S, G (mask {j})) :
    (S.card : ℝ) / (8 * n) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ if G m then 1 else 0) := by
  let e (j : S) := mask {j.val}
  have he : Function.Injective e := by
    intro i j h
    simpa [e, Finset.singleton_inj] using mask_injective h
  have hsmall (j : S) : 1 / (8 * (n : ℝ)) ≤
      (independentBits n (1 / (n : ℝ)) (e j)).toReal := by
    simpa [e, div_eq_mul_inv, mul_inv, mul_comm] using weight_lower hn {j.val}
  calc
    _ = ∑ _j : S, 1 / (8 * (n : ℝ)) := by
      simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ ∑ j : S, (independentBits n (1 / (n : ℝ)) (e j)).toReal :=
      Finset.sum_le_sum fun j _ ↦ hsmall j
    _ ≤ _ := injective_sum_le_indicator _ e he G (fun j ↦ hG j j.property)

lemma swap_mask_event (hn : 2 ≤ n) (a : Fin n) (S : Finset (Fin n)) (ha : a ∉ S)
    (G : BitString n → Prop) (hG : ∀ j ∈ S, G (mask {a, j})) :
    (S.card : ℝ) / (8 * (n : ℝ) ^ 2) ≤
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦ if G m then 1 else 0) := by
  let e (j : S) := mask {a, j.val}
  have hne (j : S) : a ≠ j.val := fun h ↦ ha (h ▸ j.property)
  have he : Function.Injective e := by
    intro i j h
    have heq : ({a, i.val} : Finset (Fin n)) = {a, j.val} := mask_injective h
    have hi : i.val ∈ ({a, j.val} : Finset (Fin n)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact Subtype.ext (by simpa [Ne.symm (hne i)] using hi)
  have hsmall (j : S) : 1 / (8 * (n : ℝ) ^ 2) ≤
      (independentBits n (1 / (n : ℝ)) (e j)).toReal := by
    have hcard : ({a, j.val} : Finset (Fin n)).card = 2 := by simp [hne j]
    simpa [e, hcard, div_eq_mul_inv, mul_inv, mul_comm, inv_pow] using
      weight_lower hn ({a, j.val} : Finset (Fin n))
  calc
    _ = ∑ _j : S, 1 / (8 * (n : ℝ) ^ 2) := by
      simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ ∑ j : S, (independentBits n (1 / (n : ℝ)) (e j)).toReal :=
      Finset.sum_le_sum fun j _ ↦ hsmall j
    _ ≤ _ := injective_sum_le_indicator _ e he G (fun j ↦ hG j j.property)

lemma mask_coord_mean {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (j : Fin n) :
    mean (independentBits n p) (fun m ↦ if m j = 1 then 1 else 0) = p := by
  let v (i : Fin n) (b : Fin 2) : ℝ :=
    (coin p (b = 1)).toReal * if i = j then if b = 1 then 1 else 0 else 1
  have hprod (m : BitString n) :
      (∏ i, v i (m i)) = (independentBits n p m).toReal *
        (if m j = 1 then 1 else 0) := by
    simp only [v, Finset.prod_mul_distrib, independentBits, PMF.ofFintype_apply,
      ENNReal.toReal_prod]
    congr 1
    simp
  unfold mean
  simp_rw [← hprod]
  rw [← Fintype.prod_sum]
  have hsum (i : Fin n) : (∑ b, v i b) = if i = j then p else 1 := by
    rw [Fin.sum_univ_two]
    by_cases h : i = j <;>
      simp [v, h, coin_true hp, coin_false hp, ENNReal.toReal_ofReal hp.1,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]
  simp [hsum]

lemma mask_hit_upper (hn : 2 ≤ n) (S : Finset (Fin n)) :
    mean (independentBits n (1 / (n : ℝ)))
      (fun m ↦ if ∃ j ∈ S, m j = 1 then 1 else 0) ≤ (S.card : ℝ) / n := by
  apply (mean_mono _ (g := fun m ↦ ∑ j ∈ S, if m j = 1 then 1 else 0) ?_).trans_eq
  · rw [mean_sum]
    simp_rw [mask_coord_mean (rate_valid hn)]
    simp [nsmul_eq_mul, div_eq_mul_inv]
  · intro m
    by_cases h : ∃ j ∈ S, m j = 1
    · obtain ⟨j, hj, hjm⟩ := h
      rw [if_pos ⟨j, hj, hjm⟩]
      simpa only [if_pos hjm] using
        (Finset.single_le_sum (s := S) (f := fun i ↦ if m i = 1 then (1 : ℝ) else 0)
          (fun i _ ↦ by split_ifs <;> norm_num) hj)
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun i _ ↦ by split_ifs <;> norm_num)

end
end Lax637351Proofs.Mutation
