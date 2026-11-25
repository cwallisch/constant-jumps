import Lax637351Proofs.FiniteHitting

namespace Lax637351Proofs.CopyingStage

open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.FiniteHitting
open scoped Classical ENNReal

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

def waitingSum (a : ℝ) (s : ℕ) : ℝ := ∑ t ∈ Finset.range s, a ^ t

lemma waitingSum_succ (a : ℝ) (s : ℕ) :
    waitingSum a (s + 1) = 1 + a * waitingSum a s := by
  simp [waitingSum, Finset.sum_range_succ', pow_succ', ← Finset.mul_sum, add_comm]

lemma waitingSum_nonneg {a : ℝ} (ha : 0 ≤ a) (s : ℕ) : 0 ≤ waitingSum a s :=
  Finset.sum_nonneg fun t _ ↦ pow_nonneg ha t

lemma waitingSum_lower {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (s : ℕ) :
    (s : ℝ) * a ^ (s - 1) ≤ waitingSum a s := by
  unfold waitingSum
  calc
    _ = ∑ _t ∈ Finset.range s, a ^ (s - 1) := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun t ht ↦ pow_le_pow_of_le_one ha ha' (by
      have := Finset.mem_range.mp ht
      omega)

lemma copying_stage (J : α → PMF (β × α)) (G I N : Set α) (B : ℝ) (hB : 0 ≤ B)
    (a γ : ℝ) (ha : 0 ≤ a) (hγ : 0 ≤ γ) (d : ℕ)
    (fail : α → β × α → Prop) (good : α → β × α → Prop)
    (hI : Disjoint I G)
    (hn : ∀ x ∈ N, B ≤ visit (fun x ↦ (J x).map Prod.snd) G d x)
    (hbad : ∀ x ∈ I, ∀ v, fail x v → ¬ good x v)
    (hsame : ∀ x ∈ I, ∀ v ∈ (J x).support, fail x v → v.2 ∈ I)
    (hgood : ∀ x ∈ I, ∀ v ∈ (J x).support, good x v → v.2 ∈ N)
    (hhold : ∀ x ∈ I, a ≤ mean (J x) (fun v ↦ if fail x v then 1 else 0))
    (hjump : ∀ x ∈ I, γ ≤ mean (J x) (fun v ↦ if good x v then 1 else 0))
    (s : ℕ) (x : α) (hx : x ∈ I) :
    B * γ * waitingSum a s ≤ visit (fun x ↦ (J x).map Prod.snd) G (d + s) x := by
  let K (x : α) := (J x).map Prod.snd
  induction s generalizing x with
  | zero =>
    simpa [waitingSum] using visit_nonneg K G d x
  | succ s ih =>
    have hx' := Set.disjoint_left.mp hI hx
    have hstep (v : β × α) (hv : v ∈ (J x).support) :
        (B * γ * waitingSum a s) * (if fail x v then 1 else 0) +
          B * (if good x v then 1 else 0) ≤ visit K G (d + s) v.2 := by
      by_cases hh : fail x v
      · simpa only [if_pos hh, if_neg (hbad x hx v hh), mul_one, mul_zero, add_zero] using
          ih v.2 (hsame x hx v hv hh)
      · by_cases hg : good x v
        · simpa only [if_neg hh, if_pos hg, mul_zero, mul_one, zero_add] using
            (hn v.2 (hgood x hx v hv hg)).trans (visit_monotone K G v.2 (Nat.le_add_right d s))
        · simpa only [if_neg hh, if_neg hg, mul_zero, add_zero] using visit_nonneg K G (d + s) v.2
    have hm := mean_mono_on_support (J x) hstep
    rw [mean_add, mean_mul, mean_mul] at hm
    have ha' : 0 ≤ B * γ * waitingSum a s := mul_nonneg (mul_nonneg hB hγ) (waitingSum_nonneg ha s)
    have ha'' := mul_le_mul_of_nonneg_left (hhold x hx) ha'
    have hγ' := mul_le_mul_of_nonneg_left (hjump x hx) hB
    change _ ≤ visit K G (d + s + 1) x
    rw [visit, if_neg hx']
    change _ ≤ mean (PMF.map Prod.snd (J x)) _
    rw [mean_map, waitingSum_succ]
    nlinarith only [hm, ha'', hγ']

end
end Lax637351Proofs.CopyingStage
