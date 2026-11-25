import Lax637351Proofs.RareScore
import Lax637351Proofs.CrossoverSuccess
import Lax637351Proofs.RuntimeBridge

namespace Lax637351Proofs.RareSuccess

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.PlateauPairs Lax637351Proofs.PairStep Lax637351Proofs.RareDrift
open Lax637351Proofs.RareScore Lax637351Proofs.CrossoverSuccess Lax637351Proofs.RuntimeBridge
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def crossRate (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + k) / 8

lemma crossRate_pos (k : ℕ) : 0 < crossRate k := by unfold crossRate; positivity

lemma score_le_one (r : ℕ) (P : Population n μ) : score r P ≤ 1 := by
  unfold score parentAverage
  rw [← mean_const (PMF.uniformOfFintype (Fin μ)) 1]
  apply mean_mono
  intro j
  rw [← mean_const (PMF.uniformOfFintype (Fin μ)) 1]
  apply mean_mono
  intro i
  split_ifs
  · exact indic_le_one _
  · norm_num

lemma success_step (hk : 0 < k) (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ¬ missing P ∨ plateau (k := k) P) :
    success P + (p * crossRate k) * (score k P - success P) ≤
      mean (step (jump k) p true P) success := by
  by_cases hmiss : missing P
  · have hpl := hP.resolve_left (not_not_intro hmiss)
    have hs : success P = 0 := by simp [success, indicator, hmiss]
    let H (i j : Fin μ) : ℝ :=
      mean (PMF.uniformOfFintype (BitString n)) (fun m ↦
        mean (independentBits n (1 / (n : ℝ))) (fun flip ↦
          mean (select (jump k) true true P (crossover (P i) (P j) m)
            (mutate (crossover (P i) (P j) m) flip)) success))
    have hpair (j i : Fin μ) : crossRate k *
        (if i ≠ j then indicator (pairGood i j k P) else 0) ≤ H i j := by
      have hnonneg : 0 ≤ H i j :=
        mean_nonneg _ fun _ ↦ mean_nonneg _ fun _ ↦ mean_nonneg _ success_nonneg
      by_cases hi : i ≠ j
      · by_cases hg : pairGood i j k P
        · have hdist : k ≤ distance (P i) (P j) := hg.resolve_left (not_not_intro hmiss)
          have heq : distance (P i) (P j) = (zeros (P i)).card := by
            have hle := distance_le_card (P i) (P j)
            rw [hpl i] at hle ⊢
            omega
          have hd := (distance_eq_card_iff (P i) (P j)).mp heq
          simpa [hi, indicator, hg, crossRate, H] using success_on_pair hk hn true P hmiss hpl i j hd
        · simpa [hi, indicator, hg] using hnonneg
      · simpa [hi] using hnonneg
    have hcross : crossRate k * score k P ≤
        mean (parents P true) (fun y ↦ mean (independentBits n (1 / (n : ℝ)))
          fun m ↦ mean (select (jump k) true true P y (mutate y m)) success) := by
      unfold score parentAverage
      rw [← mean_mul]
      have hh (j : Fin μ) : crossRate k *
          mean (PMF.uniformOfFintype (Fin μ))
            (fun i ↦ if i ≠ j then indicator (pairGood i j k P) else 0) ≤
          mean (PMF.uniformOfFintype (Fin μ)) (fun i ↦ H i j) := by
        rw [← mean_mul]
        exact mean_mono _ (hpair j)
      apply (mean_mono _ hh).trans_eq
      rw [mean_swap, ← mean_uniform_pair]
      simp [parents, Bind.bind, Pure.pure, mean_bind, mean_pure, H]
    rw [hs, zero_add, sub_zero, mean_step hp, mul_assoc]
    have hother : 0 ≤ mean (PMF.uniformOfFintype (Fin μ)) (fun u ↦
        mean (independentBits n (1 / (n : ℝ))) fun m ↦
          mean (select (jump k) true false P (P u) (mutate (P u) m)) success) :=
      mean_nonneg _ fun _ ↦ mean_nonneg _ fun _ ↦ mean_nonneg _ success_nonneg
    exact (mul_le_mul_of_nonneg_left hcross hp.1).trans
      (le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hp.2) hother))
  · rw [success_mean_of_success hk p true P hmiss]
    rw [show success P = 1 by simp [success, indicator, hmiss]]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hp.1 (crossRate_pos k).le) (sub_nonpos.mpr (score_le_one _ _)))

lemma mean_success_compl (ν : PMF (Population n μ)) :
    mean ν success = 1 - (ν.toOuterMeasure {P | missing P}).toReal := by
  let M : Set (Population n μ) := {P | missing P}
  have heq : (success : Population n μ → ℝ) =
      fun P ↦ 1 - (if P ∈ M then 1 else 0) := by
    funext P
    by_cases h : missing P <;> simp [M, success, indicator, h]
  rw [heq, mean_sub, mean_const, mean_indicator]

def plateauWindow (k n : ℕ) (μ : ℕ+) (p : ℝ) : ℕ :=
  k * ((μ : ℕ) * n) + ⌈1 / (p * crossRate k)⌉₊

def scoreLower (B : ℝ) (k : ℕ) : ℝ := (1 / 2) * (Real.exp (-4 * (B + k)) / 128) ^ k

lemma scoreLower_pos (B : ℝ) (k : ℕ) : 0 < scoreLower B k := by unfold scoreLower; positivity

lemma scoreLower_le_one {B : ℝ} (hB : 0 < B) (k : ℕ) : scoreLower B k ≤ 1 := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have hb : Real.exp (-4 * (B + k)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc : Real.exp (-4 * (B + k)) / 128 ≤ 1 := by linarith
  have hd : (Real.exp (-4 * (B + k)) / 128) ^ k ≤ 1 :=
    pow_le_one₀ (by positivity) hc
  unfold scoreLower
  linarith

lemma plateau_window_success (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hμ : 2 ≤ μ) (B p : ℝ)
    (hB : 0 < B) (hp : 0 < p ∧ p ≤ 1 / 2) (hpB : p ≤ B / n)
    (hsize : 4 * (B + k) ≤ ((μ : ℕ) : ℝ) * n)
    (ν : PMF (Population n μ)) (hν : ∀ P ∈ ν.support, ¬ missing P ∨ plateau (k := k) P) :
    scoreLower B k / 2 ≤ mean (law (step (jump k) p true) ν (plateauWindow k n μ p)) success := by
  let K := step (jump k) p true (n := n) (μ := μ)
  let s (t : ℕ) := mean (law K ν t) success
  let e (t : ℕ) := mean (law K ν t) (score k)
  let q := scoreLower B k
  let c := p * crossRate k
  have hc : 0 < c := mul_pos hp.1 (crossRate_pos k)
  have hq : 0 < q := scoreLower_pos B k
  have hsupport (t : ℕ) : ∀ P ∈ (law K ν t).support, ¬ missing P ∨ plateau (k := k) P := by
    apply law_invariant K ν {Q | ¬ missing Q ∨ plateau (k := k) Q} hν
    intro P hP Q hQ
    rcases hP with hP | hP
    · exact Or.inl (step_preserves_optimum (by omega : 0 < k) p true hP hQ)
    · by_cases hQm : missing Q
      · exact Or.inr (step_preserves_plateau_or_optimum (by omega : 0 < k)
          (by omega : k ≤ n) p true hP hQ hQm)
      · exact Or.inl hQm
  have hstep (t : ℕ) : s t + c * (e t - s t) ≤ s (t + 1) := by
    have hh := mean_mono_on_support (law K ν t) (fun P hP ↦
      success_step (by omega : 0 < k) (by omega : 2 ≤ n) ⟨hp.1.le, by linarith [hp.2]⟩ P
        (hsupport t P hP))
    rw [mean_add, mean_mul, mean_sub, ← mean_bind] at hh
    exact hh
  have hmono : Monotone s := by
    intro a b hab
    simp only [s, mean_success_compl]
    apply sub_le_sub_left
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _))
      (event_law_antitone K ν _ (step_missing_eq_zero (by omega : 0 < k) p true) hab)
  let L := k * ((μ : ℕ) * n)
  let W := ⌈1 / c⌉₊
  have hafter (t : ℕ) (ht : L ≤ t) : q ≤ e t :=
    score_after hk hn hμ B p hB ⟨hp.1.le, hp.2⟩ hpB hsize ν hν t ht
  change q / 2 ≤ s (L + W)
  by_contra! hh
  have hinc (t : ℕ) (ht : t < W) : s (L + t) + c * (q / 2) ≤ s (L + t + 1) := by
    have hs := (hmono (Nat.add_le_add_left ht.le L)).trans hh.le
    have he := hafter (L + t) (Nat.le_add_right _ _)
    have hdiff : q / 2 ≤ e (L + t) - s (L + t) := by linarith
    exact (add_le_add_right (mul_le_mul_of_nonneg_left hdiff hc.le) _).trans (hstep _)
  have hh' (t : ℕ) (ht : t ≤ W) : (t : ℝ) * (c * (q / 2)) ≤ s (L + t) := by
    induction t with
    | zero => simpa using mean_nonneg (law K ν L) success_nonneg
    | succ t ih =>
      push_cast
      rw [← Nat.add_assoc]
      have hm := ih (by omega)
      have hi := hinc t (by omega)
      nlinarith
  have hceil : 1 / c ≤ (W : ℝ) := Nat.le_ceil _
  have hmul : 1 ≤ (W : ℝ) * c := (div_le_iff₀ hc).mp hceil
  have hlast := mul_le_mul_of_nonneg_right hmul (show 0 ≤ q / 2 by positivity)
  have hb := hh' W le_rfl
  nlinarith

end
end Lax637351Proofs.RareSuccess
