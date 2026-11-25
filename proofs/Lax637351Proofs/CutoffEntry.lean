import Lax637351Proofs.Descent
import Lax637351Proofs.SlopeWindow

namespace Lax637351Proofs.CutoffEntry

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.Descent Lax637351Proofs.Ordinary Lax637351Proofs.BestRank
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.Mutation Lax637351Proofs.PairStep Lax637351Proofs.SlopeWindow
open Lax637351Proofs.SlopeCopy Lax637351Proofs.CopyingModel Lax637351Proofs.CopyingProb
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

lemma bestZeros_le_n (P : Population n μ) : bestZeros P ≤ n :=
  (bestZeros_le P 0).trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _))

lemma best_decreases (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (P : Population n μ) (hP : ordinary k P)
    (Q : Population n μ) (hQ : Q ∈ (step (jump k) p false P).support) : bestZeros Q ≤ bestZeros P := by
  obtain ⟨i, hi⟩ := bestZeros_attains P
  exact (bestZeros_le Q i).trans ((safe_step hk hkn p false P
    (fun i ↦ Or.inl (hP i)) Q hQ i).2.trans_eq hi)

def landing (B : ℕ) (d : ℝ) (P : Population n μ) : Prop :=
  (B : ℝ) - d ≤ (bestZeros P : ℝ) ∧ ∃ i : Fin μ, (zeros (P i)).card ≤ B ∧
    ∀ j : Fin μ, j ≠ i → B < (zeros (P j)).card

lemma cutoff_drift (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (P : Population n μ) (hP : ordinary k P) (hbest : k < bestZeros P) :
    mean (step (jump k) p false P) (fun Q ↦ (bestZeros Q : ℝ)) ≤
      (bestZeros P : ℝ) - 1 / (8 * (n : ℝ) * ((μ : ℕ) : ℝ) ^ 2) := by
  obtain ⟨i, hi⟩ := bestZeros_attains P
  have hPos : (zeros (P i)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hj⟩ := hPos
  let F (Q : Population n μ) := indicator (bestZeros Q < bestZeros P)
  have hchoice : 1 ≤ mean (Transitions.insert (jump k) P (mutate (P i) (mask {j}))) F := by
    rw [← mean_const (Transitions.insert (jump k) P (mutate (P i) (mask {j}))) (1 : ℝ)]
    apply mean_mono_on_support
    intro Q hQ
    have h := flip_zero_card (P i) hj
    have hz : k ≤ (zeros (mutate (P i) (mask {j}))).card := by omega
    obtain ⟨u, rfl, _⟩ := improved_site hkn P hP _ hz i (by omega) Q hQ
    have hb := bestZeros_le (Function.update P u (mutate (P i) (mask {j}))) u
    rw [Function.update_self] at hb
    exact (if_pos (show bestZeros (Function.update P u (mutate (P i) (mask {j}))) < bestZeros P by omega)).ge
  have hm := mutation_choice_lower hn P i F (fun Q ↦ indic_nonneg _) {j} 1 (by norm_num) hchoice
  simp only [Finset.card_singleton, pow_one, mul_one] at hm
  have hprob := same_parent_lower p hp P i F (fun Q ↦ indic_nonneg _) ((1 / (n : ℝ)) / 8) (by positivity) hm
  have hpoint (Q : Population n μ) (hQ : Q ∈ (step (jump k) p false P).support) :
      F Q ≤ (bestZeros P : ℝ) - (bestZeros Q : ℝ) := by
    by_cases he : bestZeros Q < bestZeros P
    · have hz : (bestZeros Q : ℝ) + 1 ≤ (bestZeros P : ℝ) := by exact_mod_cast he
      simp only [F, indicator, if_pos he]
      linarith
    · simp only [F, indicator, if_neg he]
      exact sub_nonneg.mpr (by exact_mod_cast best_decreases hk hkn p P hP Q hQ)
  have hh := mean_mono_on_support _ hpoint
  rw [mean_sub, mean_const] at hh
  have heq : (1 / (n : ℝ) / 8) / ((μ : ℕ) : ℝ) ^ 2 = 1 / (8 * (n : ℝ) * ((μ : ℕ) : ℝ) ^ 2) := by ring
  rw [heq] at hprob
  linarith only [hprob, hh]

def cutoffLength (n : ℕ) (μ : ℕ+) : ℕ := 32 * n ^ 2 * (μ : ℕ) ^ 2

lemma landing_window {B : ℕ} (hk : 0 < k) (hn : 2 ≤ n) (hkn : k ≤ B ∧ 2 * B ≤ n)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (d lam : ℝ) (hd : 0 ≤ d)
    (hl : 0 ≤ lam) (hl' : lam ≤ 1) (P : Population n μ) (hP : B < bestZeros P) :
    (3 / 4 : ℝ) - (cutoffLength n μ : ℝ) * Real.exp ((B : ℝ) * lam ^ 2 - lam * d) ≤
      visit (step (jump k) p false) {Q | landing B d Q} (cutoffLength n μ) P := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let G : Set (Population n μ) := {Q | landing B d Q}
  let A : Set (Population n μ) := {Q | B < bestZeros Q}
  let E : Set (Population n μ) := {Q | (bestZeros Q : ℝ) < B - d}
  let C := G ∪ A ∪ E
  let T := cutoffLength n μ
  let q := Real.exp ((B : ℝ) * lam ^ 2 - lam * d)
  let δ := 1 / (8 * (n : ℝ) * ((μ : ℕ) : ℝ) ^ 2)
  let V (Q : Population n μ) := (bestZeros Q : ℝ)
  let ν := law (stopped K A) (PMF.pure P) T
  have hA : P ∈ A := hP
  have hni : k ≤ n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsupp (X : Population n μ) (hX : X ∈ C) (Y : Population n μ) (hY : Y ∈ (stopped K A X).support) : Y ∈ C := by
    by_cases hxA : X ∈ A
    · rw [stopped, if_pos hxA] at hY
      by_cases hyA : Y ∈ A
      · exact Or.inl (Or.inr hyA)
      · by_cases hyE : Y ∈ E
        · exact Or.inr hyE
        · have hyl : bestZeros Y ≤ B := by
            exact le_of_not_gt hyA
          obtain ⟨i, hi⟩ := bestZeros_attains Y
          have hc (j : Fin μ) : B < (zeros (X j)).card := (show B < bestZeros X from hxA).trans_le (bestZeros_le X j)
          have hY_i : (zeros (Y i)).card ≤ B := hi.trans_le hyl
          have hh : landing B d Y := by
            refine ⟨le_of_not_gt hyE, i, hY_i, ?_⟩
            intro j hji
            obtain ⟨z, w, heq⟩ := step_one_slot p false X Y hY
            rw [heq] at hY_i ⊢
            revert hY_i
            refine Fin.lastCases ?_ (fun u ↦ ?_) w
            · simpa only [replace, Fin.lastCases_last] using fun (_ : (zeros (X i)).card ≤ B) ↦ hc j
            · simp only [replace, Fin.lastCases_castSucc]
              by_cases hiu : i = u
              · have hju : j ≠ u := hiu ▸ hji
                simpa only [Function.update_of_ne hju] using fun _ : (zeros ((Function.update X u z) i)).card ≤ B ↦ hc j
              · rw [Function.update_of_ne hiu]
                exact fun h ↦ (not_le_of_gt (hc i) h).elim
          exact Or.inl (Or.inl hh)
    · rw [stopped, if_neg hxA, PMF.mem_support_pure_iff] at hY
      exact hY.symm ▸ hX
  have hnu : ∀ X ∈ ν.support, X ∈ C := law_invariant _ _ _ (by
    intro X hx
    rw [PMF.mem_support_pure_iff] at hx
    exact hx.symm ▸ (show P ∈ C from Or.inl (Or.inr hA))) hsupp T
  have hbad : mean ν (fun X ↦ indicator (X ∈ E)) ≤ T * q := by
    have h := stopped_bad_mass K A E q (Real.exp_pos _).le
      (fun X hX ↦ one_step_drop (k := k) hn p hp false X B d lam
        (by
          have hh : (2 : ℝ) * B ≤ n := by exact_mod_cast hkn.2
          linarith only [hh])
        (by exact_mod_cast (show B ≤ bestZeros X from (show B < bestZeros X from hX).le)) hd hl hl')
      (PMF.pure P) T
    rw [mean_pure] at h
    have hE : P ∉ E := by
      have he : (B : ℝ) ≤ bestZeros P := by exact_mod_cast hP.le
      change ¬ (bestZeros P : ℝ) < B - d
      linarith only [he, hd]
    simpa only [indicator, if_neg hE, zero_add, ν] using h
  have hwait : (ν.toOuterMeasure A).toReal ≤ 1 / 4 := by
    have ht := active_window K A V δ hδ.le (fun X hx ↦
      have hpX : k < bestZeros X := hkn.1.trans_lt (show B < bestZeros X from hx)
      cutoff_drift hk hni hn p hp X ((ordinary_iff_bestZeros X).mpr hpX.le) hpX) T P
    have he : δ * (T : ℝ) = 4 * n := by
      dsimp [δ, T, cutoffLength]
      push_cast
      field_simp; norm_num
    have hzero : 0 ≤ mean ν V := mean_nonneg _ (fun Q ↦ by dsimp [V]; positivity)
    rw [he] at ht
    have hmax : V P ≤ n := by dsimp [V]; exact_mod_cast bestZeros_le_n P
    change mean ν V + (4 * (n : ℝ)) * (ν.toOuterMeasure A).toReal ≤ V P at ht
    apply (le_of_mul_le_mul_left (a := 4 * (n : ℝ)) _ (by positivity))
    nlinarith only [ht, hzero, hmax]
  have hcomb := terminal_partition ν G A E (fun X hx ↦ by
    have h : (X ∈ G ∨ X ∈ A) ∨ X ∈ E := hnu X hx
    tauto)
  have hfin := terminal_mass_le_visit K A G T P
  change mean ν (fun Y ↦ indicator (Y ∈ G)) ≤ _ at hfin
  linarith only [hcomb, hfin, hbad, hwait]

end
end Lax637351Proofs.CutoffEntry
