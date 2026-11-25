import Lax637351Proofs.PlateauKernel
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

namespace Lax637351Proofs.SubsetPairs

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep
open Lax637351Proofs.PairAveraging Lax637351Proofs.PlateauKernel
open scoped Classical ENNReal

noncomputable section

variable {α : Type*} [DecidableEq α]

lemma extend_subsets (S : Finset α) (r : ℕ) (hr : r < S.card)
    (f : Finset α → ℝ) (hf : ∀ T, 0 ≤ f T) :
    (∑ V ∈ S.powersetCard r, f V) ≤
      ∑ U ∈ S.powersetCard (r + 1), ∑ i ∈ U, f (U.erase i) := by
  have hs (V : Finset α) (hV : V ∈ S.powersetCard r) : ∃ i, i ∈ S ∧ i ∉ V := by
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hV
    by_contra! h
    have he : S ⊆ V := h
    have hh := Finset.card_le_card he
    omega
  obtain ⟨c, _⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  choose a ha using hs
  let f' (V : Finset α) : Sigma (fun _ : Finset α ↦ α) :=
    if hV : V ∈ S.powersetCard r then ⟨insert (a V hV) V, a V hV⟩ else
      ⟨∅, c⟩
  let K := (S.powersetCard (r + 1)).sigma (fun U ↦ U)
  let g (b : Sigma (fun _ : Finset α ↦ α)) := f (b.1.erase b.2)
  have hf' (V : Finset α) (hV : V ∈ S.powersetCard r) : (f' V).1.erase (f' V).2 = V := by
    simp only [f', dif_pos hV]
    exact Finset.erase_insert (ha V hV).2
  have hsub : (S.powersetCard r).image f' ⊆ K := by
    intro b hb
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hVS, hVr⟩ := Finset.mem_powersetCard.mp hV
    simp only [K, f', dif_pos hV, Finset.mem_sigma]
    exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨(ha V hV).1, hVS⟩, by
      rw [Finset.card_insert_of_notMem (ha V hV).2, hVr]⟩, Finset.mem_insert_self _ _⟩
  have hinj : ∀ V ∈ S.powersetCard r, ∀ W ∈ S.powersetCard r, f' V = f' W → V = W := by
    intro V hV W hW h
    rw [← hf' V hV, ← hf' W hW, h]
  calc
    _ = ∑ V ∈ S.powersetCard r, g (f' V) := Finset.sum_congr rfl (fun V hV ↦ congrArg f (hf' V hV).symm)
    _ = ∑ b ∈ (S.powersetCard r).image f', g b := (Finset.sum_image hinj).symm
    _ ≤ ∑ b ∈ K, g b := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ ↦ hf _)
    _ = _ := by dsimp only [K]; rw [Finset.sum_sigma]

variable {n k : ℕ} {μ : ℕ+}

def avoids (S : Finset (Fin n)) (x : BitString n) : Prop := Disjoint S (zeros x)

def avoidsRate (S : Finset (Fin n)) (P : Population n μ) : ℝ :=
  slotMean (fun x ↦ indicator (avoids S x)) P

def choosePair (j : ℕ) (x y : BitString n) : ℝ :=
  ((min (zeros x \ zeros y).card (zeros y \ zeros x).card).choose j : ℝ)

def subsetScore (j : ℕ) (P : Population n μ) : ℝ := pairMean (choosePair j) P

lemma choosePair_symm (j : ℕ) (x y : BitString n) : choosePair j x y = choosePair j y x := by
  unfold choosePair
  rw [min_comm]

lemma choosePair_diag {j : ℕ} (hj : 0 < j) (x : BitString n) : choosePair j x x = 0 := by
  simp [choosePair, Nat.choose_eq_zero_of_lt hj]

lemma choosePair_nonneg (j : ℕ) (x y : BitString n) : 0 ≤ choosePair j x y := by
  unfold choosePair
  positivity

lemma choosePair_upper (j : ℕ) (x y : BitString n) (hx : (zeros x).card ≤ k) :
    choosePair j x y ≤ (2 : ℝ) ^ k := by
  have h : min (zeros x \ zeros y).card (zeros y \ zeros x).card ≤ k :=
    (min_le_left _ _).trans ((Finset.card_le_card Finset.sdiff_subset).trans hx)
  unfold choosePair
  exact_mod_cast (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) h)

lemma choosePair_sum (j : ℕ) (x y : BitString n) (hxy : (zeros x).card = (zeros y).card) :
    choosePair j x y = ∑ U ∈ (zeros x).powersetCard j, indicator (avoids U y) := by
  have h : (zeros x \ zeros y).card = (zeros y \ zeros x).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, hxy, Finset.inter_comm]
  have hset : ((zeros x).powersetCard j).filter (fun U ↦ avoids U y) =
      (zeros x \ zeros y).powersetCard j := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powersetCard, avoids, Finset.disjoint_left]
    constructor
    · rintro ⟨⟨hs, hc⟩, hd⟩
      exact ⟨fun i hi ↦ Finset.mem_sdiff.mpr ⟨hs hi, hd hi⟩, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨fun i hi ↦ (Finset.mem_sdiff.mp (hs hi)).1, hc⟩,
        fun i hi ↦ (Finset.mem_sdiff.mp (hs hi)).2⟩
  unfold choosePair
  rw [h, min_self, ← h, ← Finset.card_powersetCard, ← hset]
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro U _
  by_cases hh : avoids U y <;> simp [indicator, hh]

lemma partnerMean_eq (j : ℕ) (P : Population n μ) (x : BitString n) :
    partnerMean (choosePair j) P x =
      mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ choosePair j x (P i)) := by
  rw [partnerMean, mean_uniform]
  simp [div_eq_inv_mul]

lemma subsetScore_eq (j : ℕ) (P : Population n μ) :
    subsetScore j P = mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ partnerMean (choosePair j) P (P i)) := by
  rw [mean_uniform]
  simp only [Fintype.card_fin, subsetScore, pairMean, pairSum, partnerMean, div_eq_inv_mul, ← Finset.mul_sum, pow_two, mul_inv]
  ring

lemma partnerMean_sum (j : ℕ) (P : Population n μ) (hP : plateau (k := k) P) (x : BitString n)
    (hx : (zeros x).card = k) :
    partnerMean (choosePair j) P x = ∑ U ∈ (zeros x).powersetCard j, avoidsRate U P := by
  rw [partnerMean_eq]
  simp_rw [choosePair_sum j x _ (hx.trans (hP _).symm), mean_sum, avoidsRate, slotMean_eq]

lemma singleton_lower (P : Population n μ) (hP : plateau (k := k) P) (hk : 0 < k)
    (d : ℝ) (_hd : 0 ≤ d) (h : ∀ i, d ≤ avoidsRate {i} P) : d ≤ subsetScore 1 P := by
  rw [subsetScore_eq]
  apply mean_uniform_lower
  intro i
  rw [partnerMean_sum 1 P hP (P i) (hP i)]
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (zeros (P i)).card from hP i ▸ hk)
  have hU : ({j} : Finset (Fin n)) ∈ (zeros (P i)).powersetCard 1 := Finset.mem_powersetCard.mpr ⟨by simpa using hj, by simp⟩
  exact (h j).trans (Finset.single_le_sum (f := fun U ↦ avoidsRate U P)
    (fun U _ ↦ by unfold avoidsRate; rw [slotMean_eq]; exact mean_nonneg _ (fun _ ↦ indic_nonneg _)) hU)

end
end Lax637351Proofs.SubsetPairs
