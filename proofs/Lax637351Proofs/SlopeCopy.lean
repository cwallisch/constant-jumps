import Lax637351Proofs.BestRank
import Lax637351Proofs.CopyingProb

namespace Lax637351Proofs.SlopeCopy

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.MarkedStep
open Lax637351Proofs.Ordinary Lax637351Proofs.CopyingModel Lax637351Proofs.CopyingProb
open Lax637351Proofs.BestRank
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma slope_order (hkn : k ≤ n) {x y : BitString n}
    (hx : k ≤ (zeros x).card) (hy : k ≤ (zeros y).card) :
    jump k x ≤ jump k y ↔ (zeros y).card ≤ (zeros x).card := by
  rw [jump_of_many_zeros hkn _ hx, jump_of_many_zeros hkn _ hy, Nat.cast_le]
  have h₁ := Finset.card_le_univ (zeros x)
  have h₂ := Finset.card_le_univ (zeros y)
  simp only [Fintype.card_fin] at h₁ h₂
  omega

lemma best_fitness (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : (zeros A).card = bestZeros P) :
    ∀ i, jump k (P i) ≤ jump k A := by
  intro i
  have hAk : k ≤ (zeros A).card := by rw [hA]; exact (ordinary_iff_bestZeros P).mp hP
  exact (slope_order hkn (hP i) hAk).mpr (hA ▸ bestZeros_le P i)

lemma copy_sel (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : (zeros A).card = bestZeros P) (Q : Population n μ)
    (hQ : Q ∈ (Transitions.insert (jump k) P A).support) : bestZeros Q = bestZeros P := by
  have hall (i : Fin μ) : bestZeros P ≤ (zeros (Q i)).card := by
    obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hQ
    refine Fin.lastCases ?_ (fun j ↦ ?_) d
    · simpa [replace] using bestZeros_le P i
    · by_cases hij : i = j
      · simp [replace, hij, hA]
      · simpa [replace, Function.update_of_ne hij] using bestZeros_le P i
  have hQo : ordinary k Q := fun i ↦ ((ordinary_iff_bestZeros P).mp hP).trans (hall i)
  obtain ⟨i, hi⟩ := bestZeros_attains Q
  exact le_antisymm (lower_best_notlost hkn P Q hP hQo (insert_fitness_mono _ _ _ hQ))
    (hi ▸ hall i)

def birth (m i : ℕ) (c : ℝ) : ℝ := c * ((i : ℝ) / m) * ((m : ℝ) - i) / (m + 1)

def cloneMass (n : ℕ) : ℝ := (independentBits n (1 / (n : ℝ)) (mask ∅)).toReal

lemma cloneMass_lower (hn : 2 ≤ n) : (1 / 8 : ℝ) ≤ cloneMass n := by
  simpa [cloneMass] using weight_lower hn (∅ : Finset (Fin n))

def up (P Q : Population n μ) : Prop :=
  bestZeros Q = bestZeros P ∧ bestCount P + 1 ≤ bestCount Q

def down (P Q : Population n μ) : Prop :=
  bestZeros Q = bestZeros P ∧ bestCount Q < bestCount P

lemma mean_unmarked {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (P : Population n μ) (f : Population n μ → ℝ) :
    mean (step (jump k) p false P) f =
      p * mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
        (fun m ↦ mean (Transitions.insert (jump k) P (mutate y m)) f)) +
      (1 - p) * mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        mean (independentBits n (1 / (n : ℝ)))
          (fun m ↦ mean (Transitions.insert (jump k) P (mutate (P i) m)) f)) := by
  rw [← stepMarked_population (jump k) p false P, mean_map]
  simpa only [select, Bool.false_eq_true, false_and, if_false] using
    (mean_marked hp (jump k) false P (fun _ Q ↦ f Q))

lemma upward_prob (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ordinary k P) :
    birth μ (bestCount P) ((1 - p) * cloneMass n) ≤
      mean (step (jump k) p false P) (fun Q ↦ indicator (up P Q)) := by
  obtain ⟨i, hi, hcount⟩ := bestCount_exists P
  let A := P i
  let b : ℝ := ((μ : ℕ) - copyCount A P : ℝ) / ((μ : ℕ) + 1 : ℝ)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr (by exact_mod_cast copyCount_le A P)) (by positivity)
  have hA : (zeros A).card = bestZeros P := hi
  have hA' : k ≤ (zeros A).card := hP i
  have hh := best_clone_deletion hk hkn P hP A hA' (best_fitness hkn P hP A hA)
  have hq : b ≤ mean (Transitions.insert (jump k) P A) (fun Q ↦ indicator (up P Q)) := by
    apply hh.trans
    apply mean_mono_on_support
    intro Q hQ
    by_cases hg : ordinary k Q ∧ copyCount A Q = copyCount A P + 1
    · have hz := copy_sel hkn P hP A hA Q hQ
      have hc := copyCount_le_of_best Q A (hA.trans hz.symm)
      rw [hg.2, hcount] at hc
      simp [indicator, hg, up, hz, hc]
    · simpa only [indicator, if_neg hg] using indic_nonneg (up P Q)
  have hselect (j : Fin μ) :
      (cloneMass n * b) * indicator (P j = A) ≤
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦
          mean (select (jump k) false false P (P j) (mutate (P j) m))
            (fun Q ↦ indicator (up P Q))) := by
    by_cases hj : P j = A
    · rw [indicator, if_pos hj, mul_one]
      apply le_trans _ (mean_single_lower _ _ (fun m ↦ mean_nonneg _ (fun Q ↦ indic_nonneg _)) (mask ∅))
      have hm : mutate (P j) (mask ∅) = A := by rw [hj]; funext l; simp [mutate, mask]
      simp only [select, Bool.false_eq_true, false_and, if_false, hm]
      exact mul_le_mul_of_nonneg_left hq ENNReal.toReal_nonneg
    · simp only [indicator, if_neg hj, mul_zero]
      exact mean_nonneg _ (fun m ↦ mean_nonneg _ (fun Q ↦ indic_nonneg _))
  have hme := mean_mono (PMF.uniformOfFintype (Fin μ)) hselect
  rw [mean_mul, uniform_copyRate] at hme
  rw [mean_unmarked hp]
  simp only [select, Bool.false_eq_true, false_and, if_false] at hme
  have hcross : 0 ≤ mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
        (fun m ↦ mean (Transitions.insert (jump k) P (mutate y m)) (fun Q ↦ indicator (up P Q)))) :=
    mean_nonneg _ (fun y ↦ mean_nonneg _ (fun m ↦ mean_nonneg _ (fun Q ↦ indic_nonneg _)))
  have hs := mul_le_mul_of_nonneg_left hme (sub_nonneg.mpr hp.2)
  refine le_trans ?_ (le_trans hs (le_add_of_nonneg_left (mul_nonneg hp.1 hcross)))
  rw [← hcount]
  unfold birth b
  exact le_of_eq (by ring)

lemma uniform_delete_count (P : Population n μ) (A : BitString n) :
    mean (PMF.uniformOfFintype (Fin ((μ : ℕ) + 1)))
      (fun d ↦ indicator (∃ i : Fin μ, d = i.castSucc ∧ P i = A)) =
      (copyCount A P : ℝ) / ((μ : ℕ) + 1 : ℝ) := by
  rw [mean_uniform, Fin.sum_univ_castSucc]
  have hlast : ¬ ∃ i : Fin μ, Fin.last (μ : ℕ) = i.castSucc ∧ P i = A := by
    rintro ⟨i, hi, _⟩
    have ht := congrArg Fin.val hi
    simp at ht
    have := i.isLt
    omega
  have hi (i : Fin μ) : (∃ j : Fin μ, i.castSucc = j.castSucc ∧ P j = A) ↔ P i = A := by
    constructor
    · rintro ⟨j, hj, h⟩
      cases Fin.castSucc_injective _ hj
      exact h
    · exact fun h ↦ ⟨i, rfl, h⟩
  simp only [indicator, hlast, if_false, hi, add_zero, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    div_eq_inv_mul]
  rw [count_cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P i = A <;> simp [indicator, h]

lemma deletion_loss (hkn : k ≤ n) (P : Population n μ) (hP : ordinary k P)
    (A : BitString n) (hA : (zeros A).card = bestZeros P)
    (hcount : copyCount A P = bestCount P) (z : BitString n) :
    mean (Transitions.insert (jump k) P z) (fun Q ↦ indicator (down P Q)) ≤
      ((copyCount A P : ℝ) / ((μ : ℕ) + 1 : ℝ)) *
      indicator ((∀ i, (zeros (P i)).card = bestZeros P) ∧ (zeros z).card = bestZeros P ∧ z ≠ A) := by
  have hpoint (d : Fin ((μ : ℕ) + 1))
      (hd : d ∈ (deletionIndex (jump k) (Fin.lastCases z P)).support)
      (hD : down P (replace P z d)) :
      (∃ i : Fin μ, d = i.castSucc ∧ P i = A) ∧
        (∀ i, (zeros (P i)).card = bestZeros P) ∧ (zeros z).card = bestZeros P ∧ z ≠ A := by
    have hcnt := copyCount_le_of_best (replace P z d) A (hA.trans hD.1.symm)
    have hloss : copyCount A (replace P z d) < copyCount A P := hcnt.trans_lt (hcount.symm ▸ hD.2)
    revert hd hD hloss
    refine Fin.lastCases ?_ (fun j ↦ ?_) d
    · simp [replace]
    · intro hd hD hloss
      simp only [replace, Fin.lastCases_castSucc] at hloss
      have hzA : z ≠ A := by
        intro he
        rw [he] at hloss
        by_cases hej : P j = A
        · simp [← hej, Function.update_eq_self] at hloss
        · rw [copyCount_update _ _ _ hej] at hloss
          omega
      have hj : P j = A := by
        by_contra hn
        rw [copyCount_update_other _ _ _ _ hn hzA] at hloss
        omega
      have hp (i : Fin μ) : (zeros (P i)).card = bestZeros P := by
        have hh := deletion_min_lastCases (jump k) P z j.castSucc hd i.castSucc
        simp only [Fin.lastCases_castSucc, hj] at hh
        exact le_antisymm (hA ▸ (slope_order hkn (show k ≤ (zeros A).card by rw [← hj]; exact hP j) (hP i)).mp hh) (bestZeros_le P i)
      have hzo : k ≤ (zeros z).card := by
        have hle := hD.1
        have ht := bestZeros_le (replace P z j.castSucc) j
        rw [hle] at ht
        simp only [replace, Fin.lastCases_castSucc, Function.update_self] at ht
        exact ((ordinary_iff_bestZeros P).mp hP).trans ht
      have hlow := deletion_min_lastCases (jump k) P z j.castSucc hd (Fin.last (μ : ℕ))
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hj] at hlow
      have hzle := (slope_order hkn (show k ≤ (zeros A).card by rw [← hj]; exact hP j) hzo).mp hlow
      have hzhigh := bestZeros_le (replace P z j.castSucc) j
      rw [hD.1] at hzhigh
      simp only [replace, Fin.lastCases_castSucc, Function.update_self] at hzhigh
      exact ⟨⟨j, rfl, hj⟩, hp, le_antisymm (hA ▸ hzle) hzhigh, hzA⟩
  by_cases hb : (∀ i, (zeros (P i)).card = bestZeros P) ∧ (zeros z).card = bestZeros P ∧ z ≠ A
  · have heq : ∀ i, jump k (P i) = jump k z := by
      intro i
      have hzo : k ≤ (zeros z).card := by rw [hb.2.1]; exact (ordinary_iff_bestZeros P).mp hP
      rw [jump_of_many_zeros hkn _ (hP i), jump_of_many_zeros hkn _ hzo, hb.1 i, hb.2.1]
    rw [indicator, if_pos hb, mul_one, insert_eq_uniform _ _ _ heq, mean_map, ← uniform_delete_count P A]
    apply mean_mono_on_support
    intro d hd
    by_cases he : down P (replace P z d)
    · have hd' : d ∈ (deletionIndex (jump k) (Fin.lastCases z P)).support := by
        have hh (j : Fin ((μ : ℕ) + 1)) : jump k (Fin.lastCases z P j) = jump k z := by
          refine Fin.lastCases ?_ (fun i ↦ ?_) j
          · simp
          · simpa only [Fin.lastCases_castSucc] using heq i
        rw [deletion_uniform _ _ _ hh]
        exact hd
      simp [indicator, he, (hpoint d hd' he).1]
    · simpa only [indicator, if_neg he] using indic_nonneg (∃ i : Fin μ, d = i.castSucc ∧ P i = A)
  · rw [indicator, if_neg hb, mul_zero, Transitions.insert, mean_map]
    rw [← mean_const (deletionIndex (jump k) (Fin.lastCases z P)) (0 : ℝ)]
    apply mean_mono_on_support
    intro d hd
    have he : ¬ down P (replace P z d) := fun h ↦ hb (hpoint d hd h).2
    simp [indicator, he]

lemma neutral_mutation (hn : 2 ≤ n) (A y : BitString n) (r : ℕ) (hy : (zeros y).card = r) :
    mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      indicator ((zeros (mutate y m)).card = r ∧ mutate y m ≠ A)) ≤
      cloneMass n * (1 - indicator (y = A)) + (r : ℝ) / n := by
  let H (m : BitString n) := ∃ j ∈ zeros y, m j = 1
  let M := independentBits n (1 / (n : ℝ))
  have hpt (m : BitString n) :
      indicator ((zeros (mutate y m)).card = r ∧ mutate y m ≠ A) ≤
        (1 - indicator (y = A)) * indicator (m = mask ∅) + indicator (H m) := by
    by_cases hh : (zeros (mutate y m)).card = r ∧ mutate y m ≠ A
    · by_cases hH : H m
      · simp only [indicator, if_pos hh, if_pos hH, le_add_iff_nonneg_left]
        split_ifs <;> norm_num
      · have hcard : (zeros (mutate y m)).card = (zeros y).card := hh.1.trans hy.symm
        have heq := equal_card_no_hit y m hH hcard
        have hyA : y ≠ A := fun h ↦ hh.2 (heq.trans h)
        have hm : m = mask ∅ := by
          funext j
          by_contra hj
          have h0 : m j ≠ 0 := by simpa [mask] using hj
          have h1 := bit_eq_one_of_ne_zero _ h0
          have hbit := congrFun heq j
          simp only [mutate, h1, if_true] at hbit
          have hfin := (y j).isLt
          omega
        norm_num only [indicator, if_pos hh, if_neg hH, if_neg hyA, if_pos hm, sub_zero, mul_one, add_zero]
    · rw [indicator, if_neg hh]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr (indic_le_one _)) (indic_nonneg _))
        (indic_nonneg _)
  have hmask : mean M (fun m ↦ indicator (m = mask ∅)) = cloneMass n := by
    unfold mean cloneMass
    dsimp [M]
    rw [Finset.sum_eq_single (mask ∅)]
    · simp [indicator]
    · intro m _ hm
      simp [indicator, hm]
    · simp
  have hmean := mean_mono M hpt
  rw [mean_add, mean_mul, hmask] at hmean
  have hh := mask_hit_upper hn (zeros y)
  rw [hy] at hh
  have hhe : (fun m ↦ indicator (H m)) = (fun m : BitString n ↦ if ∃ j ∈ zeros y, m j = 1 then 1 else 0) := by
    funext m
    by_cases h : ∃ j ∈ zeros y, m j = 1 <;> simp [H, indicator]
  rw [← hhe] at hh
  calc
    _ ≤ (1 - indicator (y = A)) * cloneMass n + mean M (fun m ↦ indicator (H m)) := hmean
    _ ≤ _ := by rw [mul_comm (cloneMass n)]; exact add_le_add_right hh _

lemma downward_prob (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ordinary k P) :
    mean (step (jump k) p false P) (fun Q ↦ indicator (down P Q)) ≤
      let f : ℝ := (bestCount P : ℝ) / (μ : ℕ)
      (((1 - p) * cloneMass n) * (1 - f) + (bestZeros P : ℝ) / n + p * (1 - f ^ 2)) *
        ((bestCount P : ℝ) / ((μ : ℕ) + 1)) := by
  obtain ⟨j, hj, hc⟩ := bestCount_exists P
  let A := P j
  let r := bestZeros P
  let q : ℝ := (copyCount A P : ℝ) / (μ : ℕ)
  let w : ℝ := (copyCount A P : ℝ) / ((μ : ℕ) + 1)
  let v : ℝ := (bestZeros P : ℝ) / n
  let f (Q : Population n μ) := indicator (down P Q)
  have hA : (zeros A).card = r := hj
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' : q ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast copyCount_le A P)
  have hc' : copyCount A P = bestCount P := hc
  change mean (step (jump k) p false P) f ≤ _
  simp only [← hc']
  change _ ≤ (((1 - p) * cloneMass n) * (1 - q) + v + p * (1 - q ^ 2)) * w
  by_cases hAll : ∀ i, (zeros (P i)).card = bestZeros P
  · have hbound (z : BitString n) :
        mean (Transitions.insert (jump k) P z) f ≤ w * indicator ((zeros z).card = r ∧ z ≠ A) := by
      simpa only [hAll, forall_const, true_and] using deletion_loss hkn P hP A hA hc' z
    have hmut (i : Fin μ) :
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦ mean (Transitions.insert (jump k) P (mutate (P i) m)) f) ≤
          w * (cloneMass n * (1 - indicator (P i = A)) + v) := by
      refine (mean_mono _ (fun m ↦ hbound (mutate (P i) m))).trans ?_
      rw [mean_mul]
      exact mul_le_mul_of_nonneg_left (neutral_mutation hn A (P i) r (hAll i)) hw
    have hmutAll := mean_mono (PMF.uniformOfFintype (Fin μ)) hmut
    rw [mean_mul, mean_add, mean_mul, mean_sub, mean_const, mean_const, uniform_copyRate] at hmutAll
    have hpair (i j : Fin μ) :
        mean (PMF.uniformOfFintype (BitString n)) (fun M ↦
          mean (independentBits n (1 / (n : ℝ))) (fun m ↦
            mean (Transitions.insert (jump k) P (mutate (crossover (P i) (P j) M) m)) f)) ≤
        w * (v + (1 - indicator (P i = A) * indicator (P j = A))) := by
      by_cases h₁ : P i = A
      · by_cases h₂ : P j = A
        · have hcross (M : BitString n) : crossover (P i) (P j) M = A := by
            funext t
            simp [crossover, h₁, h₂]
          have hh := hmut i
          simp only [h₁, indicator, if_true, sub_self, mul_zero, zero_add] at hh
          simp_rw [hcross, mean_const]
          simpa only [h₁, h₂, indicator, if_true, mul_one, sub_self, add_zero] using hh
        · rw [indicator, if_pos h₁, indicator, if_neg h₂, mul_zero, sub_zero]
          rw [← mean_const (PMF.uniformOfFintype (BitString n)) (w * (v + 1))]
          apply mean_mono
          intro M
          rw [← mean_const (independentBits n (1 / (n : ℝ))) (w * (v + 1))]
          apply mean_mono
          intro m
          exact (hbound _).trans (mul_le_mul_of_nonneg_left (le_trans (indic_le_one _) (by linarith)) hw)
      · rw [indicator, if_neg h₁, zero_mul, sub_zero]
        rw [← mean_const (PMF.uniformOfFintype (BitString n)) (w * (v + 1))]
        apply mean_mono
        intro M
        rw [← mean_const (independentBits n (1 / (n : ℝ))) (w * (v + 1))]
        apply mean_mono
        intro m
        exact (hbound _).trans (mul_le_mul_of_nonneg_left (le_trans (indic_le_one _) (by linarith)) hw)
    have hcrossAll := mean_mono (PMF.uniformOfFintype (Fin μ × Fin μ)) (fun ij ↦ hpair ij.1 ij.2)
    rw [mean_mul, mean_add, mean_const, mean_sub, mean_const] at hcrossAll
    rw [mean_uniform_pair (fun (i j : Fin μ) ↦ indicator (P i = A) * indicator (P j = A))] at hcrossAll
    simp_rw [mean_mul, uniform_copyRate] at hcrossAll
    have hswap : (fun i : Fin μ ↦ indicator (P i = A) * q) = fun i ↦ q * indicator (P i = A) := by
      funext i
      ring
    change _ ≤ w * (v + (1 - mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ indicator (P i = A) * q))) at hcrossAll
    rw [hswap, mean_mul, uniform_copyRate] at hcrossAll
    rw [mean_unmarked hp]
    simp only [parents, if_true, Bind.bind, Pure.pure, mean_bind, mean_pure]
    apply (add_le_add (mul_le_mul_of_nonneg_left hcrossAll hp.1)
      (mul_le_mul_of_nonneg_left hmutAll (sub_nonneg.mpr hp.2))).trans
    change p * (w * (v + (1 - q * q))) + (1 - p) * (w * (cloneMass n * (1 - q) + v)) ≤ _
    ring_nf
    exact le_rfl
  · have hbound (z : BitString n) : mean (Transitions.insert (jump k) P z) f ≤ 0 := by
      have hh := deletion_loss hkn P hP A hA hc' z
      have he : indicator ((∀ i, (zeros (P i)).card = bestZeros P) ∧
          (zeros z).card = bestZeros P ∧ z ≠ A) = 0 := by simp [indicator, hAll]
      rw [he, mul_zero] at hh
      exact hh
    have hme : mean (step (jump k) p false P) f ≤ 0 := by
      rw [mean_unmarked hp]
      have hc₁ : mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
          (fun m ↦ mean (Transitions.insert (jump k) P (mutate y m)) f)) ≤ 0 := by
        rw [← mean_const (parents P true) (0 : ℝ)]
        apply mean_mono
        intro y
        rw [← mean_const (independentBits n (1 / (n : ℝ))) (0 : ℝ)]
        exact mean_mono _ (fun m ↦ hbound _)
      have hc₂ : mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ mean (independentBits n (1 / (n : ℝ)))
          (fun m ↦ mean (Transitions.insert (jump k) P (mutate (P i) m)) f)) ≤ 0 := by
        rw [← mean_const (PMF.uniformOfFintype (Fin μ)) (0 : ℝ)]
        apply mean_mono
        intro i
        rw [← mean_const (independentBits n (1 / (n : ℝ))) (0 : ℝ)]
        exact mean_mono _ (fun m ↦ hbound _)
      simpa using add_le_add (mul_le_mul_of_nonneg_left hc₁ hp.1)
        (mul_le_mul_of_nonneg_left hc₂ (sub_nonneg.mpr hp.2))
    apply hme.trans
    have hm : 0 ≤ cloneMass n := ENNReal.toReal_nonneg
    have hs : q ^ 2 ≤ 1 := pow_le_one₀ hq hq'
    exact mul_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) hm) (sub_nonneg.mpr hq')) hv)
      (mul_nonneg hp.1 (sub_nonneg.mpr hs))) hw

end
end Lax637351Proofs.SlopeCopy
