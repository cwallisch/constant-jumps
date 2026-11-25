import Lax637351Proofs.CopyingExponential
import Lax637351Proofs.MaskKernel
import Lax637351Proofs.RuntimeBridge

namespace Lax637351Proofs.PlateauRegeneration

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace
open Lax637351Proofs.Mutation Lax637351Proofs.MarkedStep Lax637351Proofs.MaskKernel
open Lax637351Proofs.Ordinary Lax637351Proofs.PlateauPairs
open Lax637351Proofs.Charge Lax637351Proofs.Regeneration Lax637351Proofs.RegenerationBounds
open Lax637351Proofs.CopyingExponential Lax637351Proofs.CopyingWindow
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def resets (k : ℕ) : Set (Population n μ) :=
  {P | ¬ plateau (k := k) P ∨ homogeneous P}

def target : Set (Population n μ) := {P | ¬ missing P}

def resetBudget (μ : ℕ+) (p : ℝ) : ℝ := Real.exp (17 * ((μ : ℕ) : ℝ)) / p

lemma resetBudget_ge_one {p : ℝ} (hp : 0 < p ∧ p ≤ 1) : 1 ≤ resetBudget μ p := by
  unfold resetBudget
  apply (le_div_iff₀ hp.1).mpr
  have he : 1 ≤ Real.exp (17 * ((μ : ℕ) : ℝ)) := Real.one_le_exp (by positivity)
  simpa only [one_mul] using hp.2.trans he

lemma span_le_budget (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (hp' : (k + 1 : ℝ) / n ≤ p)
    (t : ℕ) (P : Population n μ) :
    span (masked (jump k) p true) (resets k) t P ≤ resetBudget μ p := by
  let J := masked (jump k) p true (n := n) (μ := μ)
  let K := step (jump k) p true (n := n) (μ := μ)
  let L := resetWindow μ p
  let q := Real.exp (-16 * ((μ : ℕ) : ℝ))
  have hq : 0 < q := Real.exp_pos _
  have hq' : q ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hm : (0 : ℝ) ≤ (μ : ℕ) := by positivity
    linarith)
  have hL : 0 < L := Nat.mul_pos μ.pos (stageLength_pos p)
  have hb (Q : Population n μ) : q ≤ visit (marginal J) (resets k) L Q := by
    rw [marginal_masked]
    by_cases hh : plateau (k := k) Q
    · have ho : ordinary k Q := fun i ↦ (hh i).ge
      have hpl : hasPlateau k Q := ⟨0, hh 0⟩
      have hqwin := reset_window_lower (by omega : 0 < k) (by omega : k ≤ n)
        (by omega : 2 ≤ n) hμ p hp hp' Q ho hpl
      have htransfer := visit_lower_through K {P | homogeneousPlateau k P} (resets k)
        0 1 (by norm_num) le_rfl
        (fun P hP ↦ (visit_in K _ _ _ (show P ∈ resets k from Or.inr hP.2)).ge)
        L Q
      simp only [one_mul, add_zero] at htransfer
      exact hqwin.trans htransfer
    · rw [visit_in K _ _ _ (show Q ∈ resets k from Or.inl hh)]
      exact hq'
  have hh := span_le_of_block J (resets k) L hL q hq hq' hb t P
  apply hh.trans
  have hLs : (L : ℝ) ≤ ((μ : ℕ) : ℝ) * (1 / p) := by
    dsimp [L, resetWindow]
    push_cast
    exact mul_le_mul_of_nonneg_left (stageLength_upper hp) (by positivity)
  have hμE : ((μ : ℕ) : ℝ) ≤ Real.exp ((μ : ℕ) : ℝ) := by
    have he := Real.add_one_le_exp ((μ : ℕ) : ℝ)
    linarith
  calc
    (L : ℝ) / q ≤ (((μ : ℕ) : ℝ) * (1 / p)) / q := div_le_div_of_nonneg_right hLs hq.le
    _ ≤ (Real.exp ((μ : ℕ) : ℝ) * (1 / p)) / q := by
      apply div_le_div_of_nonneg_right _ hq.le
      exact mul_le_mul_of_nonneg_right hμE (one_div_nonneg.mpr hp.1.le)
    _ = _ := by
      dsimp [resetBudget, q]
      rw [show (17 : ℝ) * ((μ : ℕ) : ℝ) = ((μ : ℕ) : ℝ) + 16 * ((μ : ℕ) : ℝ) by ring,
        Real.exp_add, show (-16 : ℝ) * ((μ : ℕ) : ℝ) = -(16 * ((μ : ℕ) : ℝ)) by ring,
        Real.exp_neg]
      simp only [div_eq_mul_inv, inv_inv, one_mul]
      ring

lemma ordinary_no_hit_stays (hkn : k ≤ n) (p : ℝ) (ar : Bool) (P : Population n μ)
    (ho : ordinary k P) (hP : homogeneous P) (v : Finset (Fin n) × Population n μ)
    (hv : v ∈ (masked (jump k) p ar P).support) (hD : Disjoint (zeros (P 0)) v.1) :
    v.2 = P := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨a, ha, rfl⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp ha with ⟨d, hd, ha⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp ha with ⟨Q, hQ, rfl⟩
  let A := P 0
  have hy : d.2.1 = A := parent_support_zero_or_eq (chosen_draw_parent hd) (fun x ↦ x = A)
    hP (fun x y m hx hy ↦ by subst x; subst y; funext j; simp [crossover])
  have hn : ¬ ∃ j ∈ zeros A, d.2.2 j = 1 := by
    rintro ⟨j, hj, hm⟩
    exact Finset.disjoint_left.mp hD hj ((mem_flipped _ _).mpr hm)
  have hz : child d = mutate A d.2.2 := by simp [child, hy]
  have hsub : zeros A ⊆ zeros (child d) := by
    intro j hj
    rw [hz]
    exact zero_persists_no_flip _ _ _ hj (fun hm ↦ hn ⟨j, hj, hm⟩)
  let r := (zeros A).card
  have hcard : r ≤ (zeros (child d)).card := Finset.card_le_card hsub
  have hcard' : k ≤ (zeros (child d)).card := (ho 0).trans hcard
  unfold select at hQ
  split_ifs at hQ
  · exact (PMF.mem_support_pure_iff _ _).mp hQ
  · by_cases h : (zeros (child d)).card = r
    · have he : child d = A := hz.trans (equal_card_no_hit A d.2.2 hn (by rw [← hz, h]))
      rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨u, _, rfl⟩
      refine Fin.lastCases ?_ (fun j ↦ ?_) u
      · simp [replace]
      · simp [replace, he, show A = P j from (hP j).symm, Function.update_eq_self]
    · apply insert_support_of_worse (jump k) P (child d) _ hQ
      intro i
      rw [jump_of_many_zeros hkn _ hcard', jump_of_many_zeros hkn _ (ho i), hP i]
      have hbound := Finset.card_le_univ (zeros (child d))
      simp only [Fintype.card_fin] at hbound
      exact_mod_cast (show k + (n - (zeros (child d)).card) < k + (n - r) by omega)

lemma no_hit_stays (_hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (P : Population n μ)
    (hP : homogeneousPlateau k P) (v : Finset (Fin n) × Population n μ)
    (hv : v ∈ (masked (jump k) p true P).support) (hD : Disjoint (zeros (P 0)) v.1) :
    v.2 = P :=
  ordinary_no_hit_stays hkn p true P (fun i ↦ (hP.1 i).ge) hP.2 v hv hD

lemma stopped_at_plateau_reset (p : ℝ) (P : Population n μ) (hR : P ∈ resets k)
    (hP : missing P) (t : ℕ) :
    visit (stopped (step (jump k) p true) (resets k)ᶜ) target t P = 0 := by
  apply visit_eq_zero_of_absorbed (A := {P})
  · simp [target, hP]
  · intro Q hQ Z hZ
    have hq : Q = P := Set.mem_singleton_iff.mp hQ
    subst Q
    have hnot : P ∉ (resets k)ᶜ := by simpa
    rw [stopped, if_neg hnot, PMF.mem_support_pure_iff] at hZ
    exact hZ
  · simp

lemma reset_charge (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (hp' : (k + 1 : ℝ) / n ≤ p)
    (P : Population n μ) (hP : homogeneousPlateau k P) (t : ℕ) :
    mean (step (jump k) p true P) (visit (stopped (step (jump k) p true) (resets k)ᶜ) target t) ≤
      hitBound (resetBudget μ p) (1 / (n : ℝ)) k / resetBudget μ p := by
  let K := step (jump k) p true (n := n) (μ := μ)
  let J := masked (jump k) p true (n := n) (μ := μ)
  let D := zeros (P 0)
  let ρ : ℝ := 1 / n
  let b := resetBudget μ p
  let V := hitBound b ρ
  let C := V D.card / b
  have hD : D.card = k := hP.1 0
  have hd : intact D P := fun j hj i ↦ by rw [hP.2 i]; exact (mem_zeros _ _).mp hj
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hb : 1 ≤ b := resetBudget_ge_one hp
  have hm (Q : Population n μ) (S : Finset (Fin n)) :
      mean (J Q) (fun v ↦ if S ⊆ v.1 then 1 else 0) ≤ ρ ^ S.card :=
    (independent_hit (by omega : 2 ≤ n) (jump k) p true Q S).le
  have hf (S : Finset (Fin n)) (_ : S ∈ nonemptySubsets D) (s : ℕ) (Q : Population n μ) :
      capture J (resets k) s (D \ S) Q ≤ V (D \ S).card :=
    capture_le J _ b ρ hb hρ hm (span_le_budget hk hkn hμ p hp hp') _ _ _
  have hh := mask_probability_first J (resets k) ρ V (hitBound_nonneg hb hρ) D hm hf C
    (coefficient_le hb hρ D) t P
  change mean (K P) (visit (stopped K (resets k)ᶜ) target t) ≤ _
  rw [show K = marginal J from (marginal_masked _ _ _).symm, marginal, mean_map]
  change mean (J P) (fun v ↦ visit (stopped (marginal J) (resets k)ᶜ) target t v.2) ≤ _
  have hpt (v : Finset (Fin n) × Population n μ) (hv : v ∈ (J P).support) :
      visit (stopped (marginal J) (resets k)ᶜ) target t v.2 ≤
        if Disjoint D v.1 then 0 else capture J (resets k) t (D \ v.1) v.2 := by
    by_cases h : Disjoint D v.1
    · rw [if_pos h, show marginal J = K from marginal_masked _ _ _,
        no_hit_stays (by omega : 0 < k) (by omega : k ≤ n) p P hP v hv h,
        stopped_at_plateau_reset p P (Or.inr hP.2)]
      exact ordinary_missing (by omega : 0 < k) (fun i ↦ (hP.1 i).ge)
    · rw [if_neg h]
      apply stopped_success_le_capture J (resets k) target intact
      · exact fun x hx S hS ↦ intact_missing S x hS hx
      · exact intact_carries (jump k) p true
      · exact intact_carries (jump k) p true P v hv D hd
  apply (mean_mono_on_support _ hpt).trans
  simpa only [C, V, hD] using hh

end
end Lax637351Proofs.PlateauRegeneration
