import Lax637351Proofs.SubsetPairs
import Lax637351Proofs.FairCrossover
import Lax637351Proofs.FiniteWindows

namespace Lax637351Proofs.CoordinateExtension

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.FiniteWindows
open Lax637351Proofs.FairCrossover Lax637351Proofs.Mutation
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.PairAveraging Lax637351Proofs.PlateauKernel Lax637351Proofs.SubsetPairs
open Lax637351Proofs.MarkedStep
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma mask_pattern_weight (S : Finset (Fin n)) (f : S → Fin 2) :
    mean (PMF.uniformOfFintype (BitString n)) (fun m ↦ indicator ((fun (j : S) ↦ m j) = f)) =
      (1 / 2 : ℝ) ^ S.card := by
  have he := uniform_restrict (β := Fin 2) S
  rw [← mean_map (PMF.uniformOfFintype (BitString n)) (fun m (j : S) ↦ m j) (fun t ↦ indicator (t = f)), he]
  have ht : (fun t ↦ indicator (t = f)) = fun t ↦ indicator (t ∈ ({f} : Set (S → Fin 2))) := by
    funext t
    simp only [Set.mem_singleton_iff]
  rw [ht, mean_event, PMF.toOuterMeasure_apply_singleton]
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, inv_pow, one_div]

lemma forced_copy_weight (x y : BitString n) (i : Fin n) :
    (1 / 2 : ℝ) ^ (mismatch x y).card ≤
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
        indicator (crossover x y m = Function.update x i (y i))) := by
  let S := mismatch x y
  let f (j : S) : Fin 2 := if j.val = i then 0 else 1
  rw [← mask_pattern_weight S f]
  apply mean_mono
  intro m
  by_cases hm : (fun j : S ↦ m j) = f
  · have he : crossover x y m = Function.update x i (y i) := by
      funext j
      by_cases hj : j ∈ S
      · have hs := congrFun hm ⟨j, hj⟩
        change m j = if j = i then 0 else 1 at hs
        by_cases ht : j = i
        · subst j; rw [if_pos rfl] at hs; simp [crossover, hs]
        · rw [if_neg ht] at hs; simp [crossover, ht, hs]
      · have hs : x j = y j := by simpa [S, mismatch, Classical.not_not] using hj
        by_cases ht : j = i
        · subst j; simp [crossover, hs]
        · simp [crossover, ht, hs]
    simp [indicator, hm, he]
  · simpa only [indicator, if_neg hm] using indic_nonneg (crossover x y m = Function.update x i (y i))

lemma extend_mutation (hn : 2 ≤ n) (hsize : 4 * k ≤ n) (U : Finset (Fin n)) (hU : U.card ≤ k)
    (i : Fin n) (_hi : i ∈ U) (x y : BitString n) (hx : (zeros x).card = k)
    (havoid : avoids (U.erase i) x) (hy : y i = 1) :
    (1 / 16 : ℝ) ≤ mean (independentBits n (1 / (n : ℝ))) (fun m ↦
      indicator ((zeros (mutate (Function.update x i (y i)) m)).card = k ∧
        avoids U (mutate (Function.update x i (y i)) m))) := by
  let z := Function.update x i (y i)
  let P (m : BitString n) := (zeros (mutate z m)).card = k ∧ avoids U (mutate z m)
  have hz : zeros z = (zeros x).erase i := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [z, hy]
    · simp [z, Finset.mem_erase, hj]
  have hav : avoids U z := by
    apply Finset.disjoint_left.mpr
    intro j hj hxj
    rw [hz, Finset.mem_erase] at hxj
    exact Finset.disjoint_left.mp havoid (Finset.mem_erase.mpr ⟨hxj.1, hj⟩) hxj.2
  have he : mutate z (mask ∅) = z := by funext j; simp [mutate, mask]
  by_cases hb : i ∈ zeros x
  · let S := (U ∪ zeros z)ᶜ
    have hSz : (zeros z).card + 1 = k := by
      rw [hz, Finset.card_erase_of_mem hb, hx]
      have hh := Finset.card_pos.mpr (show (zeros x).Nonempty from ⟨i, hb⟩)
      omega
    have hSc' : (n : ℝ) / 2 ≤ S.card := by
      have h := Finset.card_union_le U (zeros z)
      have he : S.card = n - (U ∪ zeros z).card := by dsimp only [S]; rw [Finset.card_compl, Fintype.card_fin]
      have hNat : n ≤ 2 * S.card := by omega
      have hh : (n : ℝ) ≤ 2 * S.card := by exact_mod_cast hNat
      linarith only [hh]
    have hS (j : Fin n) (hj : j ∈ S) : P (mask {j}) := by
      have hne : j ∉ U ∧ j ∉ zeros z := by simpa [S] using hj
      have he : zeros (mutate z (mask {j})) = insert j (zeros z) := by
        rw [zero_set_flip]
        ext t
        by_cases hh : t = j
        · subst t
          simp [hne.2]
        · simp [hh]
      unfold P avoids
      rw [he, Finset.card_insert_of_notMem hne.2]
      refine ⟨hSz, ?_⟩
      apply Finset.disjoint_left.mpr
      intro t ht htz
      rcases Finset.mem_insert.mp htz with rfl | htz
      · exact hne.1 ht
      · exact Finset.disjoint_left.mp hav ht htz
    have hh := single_mask_event hn S P hS
    have hf : (1 / 16 : ℝ) ≤ (S.card : ℝ) / (8 * n) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * n)).mpr (by linarith only [hSc'])
    change _ ≤ mean _ (fun m ↦ indicator (P m))
    apply hf.trans (hh.trans ?_)
    apply mean_mono
    intro m
    by_cases h : P m <;> simp [indicator, h]
  · have hZ : (zeros z).card = k := by rw [hz, Finset.erase_eq_of_notMem hb, hx]
    have hPred : indicator (P (mask ∅)) = 1 := if_pos (by dsimp [P]; rw [he]; exact ⟨hZ, hav⟩)
    change _ ≤ mean _ (fun m ↦ indicator (P m))
    have h := mean_single_lower (independentBits n (1 / (n : ℝ))) (fun m ↦ indicator (P m))
      (fun _ ↦ indic_nonneg _) (mask ∅)
    rw [hPred, mul_one] at h
    have hw : (1 / 8 : ℝ) ≤ (independentBits n (1 / (n : ℝ)) (mask ∅)).toReal := by
      simpa only [Finset.card_empty, pow_zero, one_mul] using weight_lower hn (∅ : Finset (Fin n))
    exact (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8).trans (hw.trans h)

def extensionConstant (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + k) / 16

lemma extension_mating (hn : 2 ≤ n) (hsize : 4 * k ≤ n) (U : Finset (Fin n)) (hU : U.card ≤ k)
    (i : Fin n) (hi : i ∈ U) (x y : BitString n) (hx : (zeros x).card = k) (hy : (zeros y).card = k)
    (havoid : avoids (U.erase i) x) (hy1 : y i = 1) :
    extensionConstant k ≤ mean (PMF.uniformOfFintype (BitString n)) (fun s ↦
      mean (independentBits n (1 / (n : ℝ))) (fun m ↦
        let z := mutate (crossover x y s) m
        indicator ((zeros z).card = k ∧ avoids U z))) := by
  let Y := Function.update x i (y i)
  have hpt (s : BitString n) :
      (1 / 16 : ℝ) * indicator (crossover x y s = Y) ≤
        mean (independentBits n (1 / (n : ℝ))) (fun m ↦
          let z := mutate (crossover x y s) m
          indicator ((zeros z).card = k ∧ avoids U z)) := by
    by_cases h : crossover x y s = Y
    · rw [indicator, if_pos h, mul_one, h]
      exact extend_mutation hn hsize U hU i hi x y hx havoid hy1
    · simp only [indicator, if_neg h, mul_zero]
      exact mean_nonneg _ fun m ↦ by split_ifs <;> norm_num
  have hh := mean_mono (PMF.uniformOfFintype (BitString n)) hpt
  rw [mean_mul] at hh
  have hdist := zero_mismatch_card x y
  rw [hx, hy] at hdist
  have hsmall : (mismatch x y).card ≤ k + k := by omega
  have h := (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hsmall).trans (forced_copy_weight x y i)
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 16)).trans hh)
  unfold extensionConstant
  ring_nf
  exact le_rfl

end
end Lax637351Proofs.CoordinateExtension
