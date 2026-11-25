import Lax637351Proofs.Sampling

namespace Lax637351Proofs.Independent

open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)]

def product (p : ∀ i, PMF (β i)) : PMF (∀ i, β i) :=
  PMF.ofFintype (fun x ↦ ∏ i, p i (x i)) (by
    rw [← Fintype.prod_sum]
    have hp (i : ι) : (∑ a : β i, p i a) = 1 := by
      simpa only [tsum_fintype] using (p i).tsum_coe
    simp only [hp, Finset.prod_const_one])

@[simp] lemma product_apply (p : ∀ i, PMF (β i)) (x : ∀ i, β i) :
    product p x = ∏ i, p i (x i) := rfl

lemma mean_product (p : ∀ i, PMF (β i)) (f : ∀ i, β i → ℝ) :
    mean (product p) (fun x ↦ ∏ i, f i (x i)) = ∏ i, mean (p i) (f i) := by
  simp only [mean, product_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a ↦ (p i a).toReal * f i a)).symm

lemma product_map {γ : ι → Type*} [∀ i, Fintype (γ i)] (p : ∀ i, PMF (β i))
    (f : ∀ i, β i → γ i) :
    (product p).map (fun x i ↦ f i (x i)) = product (fun i ↦ (p i).map (f i)) := by
  apply PMF.ext
  intro y
  simp only [PMF.map_apply, tsum_fintype, product_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun j ↦ f j (x j)) = y
  · have hc (j : ι) : y j = f j (x j) := (congrFun h j).symm
    rw [if_pos h.symm]
    exact Finset.prod_congr rfl (fun i _ ↦ (if_pos (hc i)).symm)
  · have hh : ∃ j, f j (x j) ≠ y j := by simpa only [funext_iff, not_forall] using h
    obtain ⟨j, hj⟩ := hh
    have hz : (∏ i, if y i = f i (x i) then p i (x i) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj.symm)
    rw [if_neg (show y ≠ (fun i ↦ f i (x i)) from fun he ↦ h he.symm), hz]

end
end Lax637351Proofs.Independent
