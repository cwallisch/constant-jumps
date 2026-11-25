import Lax637351Proofs.RareDrift
import Lax637351Proofs.PairRecurrence

namespace Lax637351Proofs.RareScore

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.RareDrift
open Lax637351Proofs.PairRecurrence
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def score (r : ℕ) (P : Population n μ) : ℝ :=
  mean (PMF.uniformOfFintype (Fin μ)) (fun j ↦ parentAverage j r P)

lemma score_nonneg (r : ℕ) (P : Population n μ) : 0 ≤ score r P := by
  unfold score parentAverage
  apply mean_nonneg
  intro j
  apply mean_nonneg
  intro i
  split_ifs
  · exact indic_nonneg _
  · exact le_rfl

lemma score_zero (P : Population n μ) : score 0 P = 1 - ((μ : ℕ) : ℝ)⁻¹ := by
  unfold score parentAverage
  simp only [pairGood_zero, indicator, if_true]
  have he (j : Fin μ) : (mean (PMF.uniformOfFintype (Fin μ)) (fun u ↦ if u ≠ j then 1 else 0)) =
      1 - ((μ : ℕ) : ℝ)⁻¹ := by
    simpa only [Fintype.card_fin, mul_one] using mean_uniform_exclude j 1
  simp_rw [he, mean_const]

lemma half_le_score_zero (hμ : 2 ≤ μ) (P : Population n μ) : 1 / 2 ≤ score 0 P := by
  have hμ' : (2 : ℝ) ≤ ((μ : ℕ) : ℝ) := by exact_mod_cast hμ
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hμ'
  rw [score_zero]
  rw [one_div, one_div] at hh
  linarith

lemma mean_parentAverage (ν : PMF (Population n μ)) (j : Fin μ) (r : ℕ) :
    mean ν (fun P ↦ parentAverage j r P) =
      mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦
        if i ≠ j then mean ν (fun P ↦ indicator (pairGood i j r P)) else 0) := by
  unfold parentAverage
  rw [mean_swap]
  congr 1
  funext i
  by_cases hi : i ≠ j <;> simp [hi, mean_const]

lemma score_step (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hμ : 2 ≤ μ) (B p : ℝ)
    (hB : 0 < B) (hp : 0 ≤ p ∧ p ≤ 1 / 2) (hpB : p ≤ B / n)
    (P : Population n μ) (hP : ¬ missing P ∨ plateau (k := k) P)
    (r : ℕ) (hr : r < k) :
    retain B k n μ * score (r + 1) P + (advance n μ / 2) * score r P ≤
      mean (step (jump k) p true P) (score (r + 1)) := by
  let a := retain B k n μ
  let b := advance n μ
  have hb : 0 ≤ b := by dsimp [b, advance]; positivity
  let K := step (jump k) p true P
  have hj (j : Fin μ) : a * parentAverage j (r + 1) P + (b / 2) * parentAverage j r P ≤
      mean K (fun Q ↦ parentAverage j (r + 1) Q) := by
    rw [mean_parentAverage]
    let x := b * parentAverage j r P
    let f (i : Fin μ) := indicator (pairGood i j (r + 1) P)
    have hpt (i : Fin μ) :
        (a * (if i ≠ j then f i else 0)) + (if i ≠ j then x else 0) ≤
          (if i ≠ j then mean K (fun Q ↦ indicator (pairGood i j (r + 1) Q)) else 0) := by
      by_cases hi : i ≠ j
      · simpa only [if_pos hi] using oneStep_pair hk hn B p hB hp hpB P hP i j hi r hr
      · simp [hi]
    have hmt := mean_mono (PMF.uniformOfFintype (Fin μ)) hpt
    rw [mean_add, mean_mul] at hmt
    have he : (mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ if i ≠ j then x else 0)) =
        (1 - ((μ : ℕ) : ℝ)⁻¹) * x := by
      simpa only [Fintype.card_fin] using mean_uniform_exclude j x
    rw [he] at hmt
    apply le_trans _ hmt
    change _ ≤ a * parentAverage j (r + 1) P + (1 - ((μ : ℕ) : ℝ)⁻¹) * x
    have hh := half_le_score_zero hμ P
    rw [score_zero] at hh
    have hx : 0 ≤ x := by
      apply mul_nonneg hb
      unfold parentAverage
      apply mean_nonneg
      intro i
      split_ifs
      · exact indic_nonneg _
      · exact le_rfl
    have ht := mul_le_mul_of_nonneg_right hh hx
    dsimp [x] at ht
    nlinarith only [ht]
  have ht := mean_mono (PMF.uniformOfFintype (Fin μ)) hj
  rw [mean_add, mean_mul, mean_mul, mean_swap] at ht
  exact ht

lemma score_after (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hμ : 2 ≤ μ) (B p : ℝ)
    (hB : 0 < B) (hp : 0 ≤ p ∧ p ≤ 1 / 2) (hpB : p ≤ B / n)
    (hsize : 4 * (B + k) ≤ ((μ : ℕ) : ℝ) * n)
    (ν : PMF (Population n μ))
    (hν : ∀ P ∈ ν.support, ¬ missing P ∨ plateau (k := k) P)
    (t : ℕ) (ht : k * ((μ : ℕ) * n) ≤ t) :
    (1 / 2) * (Real.exp (-4 * (B + k)) / 128) ^ k ≤
      mean (law (step (jump k) p true) ν t) (score k) := by
  let L : ℕ := (μ : ℕ) * n
  have hL : 0 < L := by dsimp [L]; exact Nat.mul_pos μ.pos (by omega)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  let a := retain B k n μ
  let b := advance n μ / 2
  let c := Real.exp (-4 * (B + k)) / 128
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb : 0 ≤ b := by dsimp [b, advance]; positivity
  have haf : a = 1 - (2 * (B + k)) / (L : ℝ) := by
    simp [a, retain, L, Nat.cast_mul]
  have ha : 0 ≤ a := by
    rw [haf]
    apply sub_nonneg.mpr
    apply (div_le_one hLr).mpr
    dsimp [L] at *
    push_cast
    have hk' : (0 : ℝ) ≤ k := by positivity
    linarith
  have ha' : a ≤ 1 := by rw [haf]; exact sub_le_self _ (by positivity)
  have hprod : (L : ℝ) * b = 1 / 128 := by
    dsimp [L, b, advance]
    push_cast
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hμ' : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
    field_simp
    norm_num
  have hwindow : c ≤ (L : ℝ) * b * a ^ L := by
    rw [hprod, haf]
    have hh := uniform_inactivity (A := 2 * (B + k)) (by positivity) hL (by
      dsimp [L]
      push_cast
      linarith)
    dsimp [c]
    rw [show -4 * (B + k) = -2 * (2 * (B + k)) by ring]
    linarith
  let K := step (jump k) p true (n := n) (μ := μ)
  let E (s r : ℕ) := mean (law K ν s) (score (min r k))
  have hsupport (s : ℕ) : ∀ P ∈ (law K ν s).support, ¬ missing P ∨ plateau (k := k) P := by
    apply law_invariant K ν {Q | ¬ missing Q ∨ plateau (k := k) Q} hν
    intro P hP Q hQ
    rcases hP with hP | hP
    · exact Or.inl (step_preserves_optimum (by omega : 0 < k) p true hP hQ)
    · by_cases hQm : missing Q
      · exact Or.inr (step_preserves_plateau_or_optimum (by omega : 0 < k)
          (by omega : k ≤ n) p true hP hQ hQm)
      · exact Or.inl hQm
  have hzero (s : ℕ) : (1 / 2 : ℝ) ≤ E s 0 := by
    change _ ≤ mean _ (score (min 0 k))
    rw [Nat.zero_min, ← mean_const (law K ν s) (1 / 2)]
    exact mean_mono _ (half_le_score_zero hμ)
  have hnon (s r : ℕ) : 0 ≤ E s r := mean_nonneg _ (score_nonneg _)
  have hstep (s r : ℕ) (hr : r < k) :
      a * E s (r + 1) + b * E s r ≤ E (s + 1) (r + 1) := by
    have hh := mean_mono_on_support (law K ν s) (fun P hP ↦
      score_step hk hn hμ B p hB hp hpB P (hsupport s P hP) r hr)
    rw [mean_add, mean_mul, mean_mul, ← mean_bind] at hh
    simpa only [E, Nat.min_eq_left hr.le, Nat.min_eq_left (Nat.succ_le_of_lt hr), law_succ] using hh
  have hkeep (s r : ℕ) (hr : r ≤ k) : a * E s r ≤ E (s + 1) r := by
    rcases r with _ | r
    · have hE (v : ℕ) : E v 0 = 1 - ((μ : ℕ) : ℝ)⁻¹ := by
        change mean _ (fun P ↦ score (min 0 k) P) = _
        simp only [Nat.zero_min, score_zero, mean_const]
      have hh := (mul_le_mul_of_nonneg_right ha' (hnon s 0)).trans_eq (one_mul (E s 0))
      rw [hE s, hE (s + 1)]
      simpa only [hE s] using hh
    · exact (le_add_of_nonneg_right (mul_nonneg hb (hnon s r))).trans (hstep s r (by omega))
  -- Only ranks up to k occur in the induction.
  have hlimit : ∀ r ≤ k, ∀ s, r * L ≤ s → (1 / 2) * c ^ r ≤ E s r := by
    intro r
    induction r with
    | zero => intro _ s _; simpa using hzero s
    | succ r ih =>
      intro hr s hs
      have hsL : L ≤ s := by rw [Nat.succ_mul] at hs; omega
      let start := s - L
      have hstart : r * L ≤ start := by dsimp [start]; rw [Nat.succ_mul] at hs; omega
      have hw := rank_window ha ha' hb (by positivity : 0 ≤ (1 / 2 : ℝ) * c ^ r)
        (fun v ↦ E (start + v) (r + 1)) (fun v ↦ E (start + v) r)
        (hnon _ _) (ih (by omega) _ (by simpa using hstart))
        (fun v ↦ by simpa only [Nat.add_assoc] using hkeep (start + v) r (by omega))
        (fun v ↦ by simpa only [Nat.add_assoc] using hstep (start + v) r (by omega)) L
      rw [show start + L = s from Nat.sub_add_cancel hsL] at hw
      rw [pow_succ, ← mul_assoc]
      calc
        (1 : ℝ) / 2 * c ^ r * c = c * ((1 / 2) * c ^ r) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right hwindow (by positivity)).trans hw
  simpa only [E, min_self] using hlimit k le_rfl t ht

end
end Lax637351Proofs.RareScore
