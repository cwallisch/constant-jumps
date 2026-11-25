import Lax637351Proofs.FiniteDrift

namespace Lax637351Proofs.RuntimeTransfer

open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift
open scoped Classical ENNReal

noncomputable section

variable {α β : Type*}

def tailSum (K : α → PMF α) (A : Set α) (ν : PMF α) : ℝ≥0∞ :=
  ∑' t, (law K ν t).toOuterMeasure A

lemma tailSum_bind (K : α → PMF α) (A : Set α) (ν : PMF β) (f : β → PMF α) :
    tailSum K A (ν.bind f) = ∑' x, ν x * tailSum K A (f x) := by
  unfold tailSum
  simp only [law_bind, PMF.toOuterMeasure_bind_apply]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

lemma tailSum_succ (K : α → PMF α) (A : Set α) (ν : PMF α) :
    tailSum K A ν = ν.toOuterMeasure A + tailSum K A (ν.bind K) := by
  unfold tailSum
  rw [tsum_eq_zero_add' ENNReal.summable, law_zero]
  congr 1
  apply tsum_congr
  intro t
  rw [Nat.add_comm, law_add']
  congr 2

lemma tailSum_next_le (K : α → PMF α) (A : Set α) (ν : PMF α) :
    tailSum K A (ν.bind K) ≤ tailSum K A ν := by
  rw [tailSum_succ K A ν]
  exact self_le_add_left _ _

lemma tailSum_next_stopped_le (K : α → PMF α) (A I : Set α) (ν : PMF α) :
    tailSum K A (ν.bind (stopped K I)) ≤ tailSum K A ν := by
  have heq := tailSum_bind K A ν PMF.pure
  rw [PMF.bind_pure] at heq
  rw [tailSum_bind, heq]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ I
  · rw [stopped, if_pos hx]
    have h := tailSum_next_le K A (PMF.pure x)
    rw [PMF.pure_bind] at h
    exact mul_le_mul' le_rfl h
  · simp [stopped, hx]

lemma tailSum_law_stopped_le (K : α → PMF α) (A I : Set α) (ν : PMF α) (t : ℕ) :
    tailSum K A (law (stopped K I) ν t) ≤ tailSum K A ν := by
  induction t with
  | zero => rfl
  | succ t ih => exact (tailSum_next_stopped_le K A I _).trans ih

lemma tailSum_ge_from_hit (K : α → PMF α) (A G : Set α) (ν : PMF α)
    (w : ℝ≥0∞) (hG : ∀ x ∈ G, w ≤ tailSum K A (PMF.pure x)) (t : ℕ) :
    (law (stopped K Gᶜ) ν t).toOuterMeasure G * w ≤ tailSum K A ν := by
  let p := law (stopped K Gᶜ) ν t
  apply le_trans _ (tailSum_law_stopped_le K A Gᶜ ν t)
  have heq := tailSum_bind K A p PMF.pure
  rw [PMF.bind_pure] at heq
  change p.toOuterMeasure G * w ≤ tailSum K A p
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, heq]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ G
  · simpa only [Set.indicator_of_mem hx] using mul_le_mul' (le_refl (p x)) (hG x hx)
  · simp [Set.indicator_of_notMem hx]

end
end Lax637351Proofs.RuntimeTransfer
