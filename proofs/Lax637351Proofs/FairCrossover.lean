import Lax637351Proofs.FairWalk
import Lax637351Proofs.TapeRun
import Mathlib.Logic.Equiv.Sum

namespace Lax637351Proofs.FairCrossover

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.Independent Lax637351Proofs.TapeRun Lax637351Proofs.TapeDraw
open Lax637351Proofs.FairWalk
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {α β : Type*}

lemma uniform_map_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext y
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (e.symm y)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro x _ hx
    have hn : y ≠ e x := fun hh ↦ hx (e.injective (hh.symm.trans (e.apply_symm_apply y).symm))
    simp [hn]
  · simp

lemma uniform_restrict [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β] (S : Finset α) :
    (PMF.uniformOfFintype (α → β)).map (fun f (j : S) ↦ f j) = PMF.uniformOfFintype (S → β) := by
  let e := ((Equiv.sumCompl (· ∈ S)).symm.arrowCongr (Equiv.refl β)).trans
    (Equiv.sumArrowEquivProdArrow {j // j ∈ S} {j // j ∉ S} β)
  have he : (fun f (j : S) ↦ f j) = Prod.fst ∘ e := rfl
  rw [he, ← PMF.map_comp, uniform_map_equiv e, uniform_fst]

lemma fair_uniform : coin (1 / 2) = PMF.uniformOfFintype Bool := by
  have h : (0 : ℝ) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ 1 := by norm_num
  ext b
  cases b <;> norm_num [coin_true h, coin_false h, PMF.uniformOfFintype_apply] <;>
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)] <;> norm_num

lemma uniform_tape [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β] :
    product (fun _ : α ↦ PMF.uniformOfFintype β) = PMF.uniformOfFintype (α → β) := by
  ext q
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

def onesCount (m : ℕ) (v : Fin m → Bool) : Fin (m + 1) :=
  ⟨∑ i, if v i then 1 else 0, Nat.lt_succ_of_le (by
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℕ) := Finset.sum_le_sum (fun i _ ↦ by split_ifs <;> decide)
      _ = m := by simp)⟩

lemma count_cons (m : ℕ) (v : Fin m → Bool) (b : Bool) :
    onesCount (m + 1) (Fin.cons b v) =
      if b then (onesCount m v).succ else (onesCount m v).castSucc := by
  apply Fin.ext
  simp only [onesCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  cases b <;> simp [Nat.add_comm]

lemma count_uniform (m : ℕ) :
    (PMF.uniformOfFintype (Fin m → Bool)).map (onesCount m) = countLaw m := by
  simp only [← uniform_tape, ← fair_uniform]
  induction m with
  | zero =>
    have he : onesCount 0 = fun _ ↦ 0 := funext (fun v ↦ Fin.eq_zero _)
    rw [he, countLaw]
    exact PMF.map_const _ 0
  | succ m ih =>
    rw [product_succ, PMF.map_bind, countLaw]
    simp only [PMF.map_comp]
    have he (b : Bool) : onesCount (m + 1) ∘ Fin.cons b =
        (fun w : Fin (m + 1) ↦ if b then w.succ else w.castSucc) ∘ onesCount m := by
      funext v
      exact count_cons m v b
    simp only [he, ← PMF.map_comp, ih]
    change (coin (1 / 2)).bind (fun b ↦ (countLaw m).bind
        (fun w ↦ PMF.pure (if b then w.succ else w.castSucc))) =
      (countLaw m).bind (fun w ↦ (coin (1 / 2)).bind
        (fun b ↦ PMF.pure (if b then w.succ else w.castSucc)))
    exact PMF.bind_comm _ _ _

variable {n : ℕ}

def mismatch (x y : BitString n) : Finset (Fin n) := Finset.univ.filter (fun j ↦ x j ≠ y j)

def bothZero (x y : BitString n) : ℕ := (zeros x ∩ zeros y).card

def mismatchZero (x y : BitString n) (m : BitString n) (j : mismatch x y) : Bool :=
  decide (crossover x y m j = 0)

lemma mismatch_condition (x y : BitString n) (j : mismatch x y) : x j ≠ y j := by
  exact (Finset.mem_filter.mp j.property).2

def mismatchEquiv (x y : BitString n) (j : mismatch x y) : Fin 2 ≃ Bool :=
  if x j = 0 then
    ⟨fun b ↦ decide (b = 1), fun b ↦ if b then 1 else 0,
      fun b ↦ by fin_cases b <;> decide, fun b ↦ by cases b <;> decide⟩
  else
    ⟨fun b ↦ decide (b = 0), fun b ↦ if b then 0 else 1,
      fun b ↦ by fin_cases b <;> decide, fun b ↦ by cases b <;> decide⟩

lemma mismatch_equiv_apply (x y m : BitString n) (j : mismatch x y) :
    mismatchEquiv x y j (m j) = mismatchZero x y m j := by
  have h := mismatch_condition x y j
  unfold mismatchEquiv mismatchZero
  by_cases hx : x j = 0
  · have hy : y j = 1 := bit_eq_one_of_ne_zero _ (fun he ↦ h (hx.trans he.symm))
    by_cases hm : m j = 1 <;> simp [hx, hy, hm, crossover]
  · have hx' := bit_eq_one_of_ne_zero _ hx
    have hy : y j = 0 := by
      by_contra hh
      exact h (hx'.trans (bit_eq_one_of_ne_zero _ hh).symm)
    by_cases hm : m j = 1
    · simp [hx', hm, crossover]
    · have hm' : m j = 0 := by by_contra h; exact hm (bit_eq_one_of_ne_zero _ h)
      simp [hx', hy, hm', crossover]

lemma mismatch_points_uniform (x y : BitString n) :
    (PMF.uniformOfFintype (BitString n)).map (mismatchZero x y) =
      PMF.uniformOfFintype (mismatch x y → Bool) := by
  let e := Equiv.piCongrRight (mismatchEquiv x y)
  have he : mismatchZero x y = e ∘ (fun m : BitString n ↦ fun j : mismatch x y ↦ m j) := by
    funext m j
    exact (mismatch_equiv_apply x y m j).symm
  rw [he, ← PMF.map_comp]
  have h := uniform_restrict (β := Fin 2) (mismatch x y)
  change (PMF.uniformOfFintype (BitString n)).map (fun m (j : mismatch x y) ↦ m j) = _ at h
  rw [h, uniform_map_equiv e]

def mismatchEnum (x y : BitString n) : Fin (mismatch x y).card ≃ mismatch x y :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe (mismatch x y))).symm

def diffCount (x y m : BitString n) : Fin ((mismatch x y).card + 1) :=
  onesCount (mismatch x y).card (fun j ↦ mismatchZero x y m (mismatchEnum x y j))

lemma diffCount_law (x y : BitString n) :
    (PMF.uniformOfFintype (BitString n)).map (diffCount x y) = countLaw (mismatch x y).card := by
  let e := (mismatchEnum x y).symm.arrowCongr (Equiv.refl Bool)
  have he : diffCount x y = onesCount (mismatch x y).card ∘ e ∘ mismatchZero x y := rfl
  rw [he, ← PMF.map_comp, ← PMF.map_comp, mismatch_points_uniform, uniform_map_equiv e, count_uniform]

lemma cross_zeros_count (x y m : BitString n) :
    (zeros (crossover x y m)).card = bothZero x y + (diffCount x y m).val := by
  have he : zeros (crossover x y m) = (zeros x ∩ zeros y) ∪
      (mismatch x y).filter (fun j ↦ crossover x y m j = 0) := by
    ext j
    by_cases h : x j = y j
    · simp [mismatch, h, crossover]
    · by_cases hx : x j = 0 <;> by_cases hy : y j = 0 <;> simp_all [mismatch]
  have hd : Disjoint (zeros x ∩ zeros y) ((mismatch x y).filter (fun j ↦ crossover x y m j = 0)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).2
    have hx := (mem_zeros x j).mp (Finset.mem_inter.mp hj).1
    have hy := (mem_zeros y j).mp (Finset.mem_inter.mp hj).2
    exact hh (hx.trans hy.symm)
  rw [he, Finset.card_union_of_disjoint hd, bothZero]
  congr 1
  change _ = ∑ j : Fin (mismatch x y).card,
    (if mismatchZero x y m (mismatchEnum x y j) then 1 else 0)
  simp only [mismatchZero, decide_eq_true_eq, Finset.card_filter]
  have hh := (mismatchEnum x y).sum_comp (fun j ↦ if crossover x y m j = 0 then (1 : ℕ) else 0)
  exact (Finset.sum_coe_sort (mismatch x y) (fun j ↦ if crossover x y m j = 0 then (1 : ℕ) else 0)).symm.trans hh.symm

lemma zero_mismatch_card (x y : BitString n) :
    (zeros x).card + (zeros y).card = 2 * bothZero x y + (mismatch x y).card := by
  have ht : mismatch x y = (zeros x ∪ zeros y) \ (zeros x ∩ zeros y) := by
    ext j
    simp only [mismatch, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_union, Finset.mem_inter, mem_zeros]
    by_cases hx : x j = 0 <;> by_cases hy : y j = 0
    · simp [hx, hy]
    · simp [hx, bit_eq_one_of_ne_zero _ hy]
    · simp [bit_eq_one_of_ne_zero _ hx, hy]
    · simp [bit_eq_one_of_ne_zero _ hx, bit_eq_one_of_ne_zero _ hy]
  rw [ht, Finset.card_sdiff_of_subset Finset.inter_subset_union, bothZero]
  have h := Finset.card_union_add_card_inter (zeros x) (zeros y)
  have hj := Finset.card_le_card (Finset.inter_subset_union : zeros x ∩ zeros y ⊆ zeros x ∪ zeros y)
  omega

end
end Lax637351Proofs.FairCrossover
