import Lax637351Proofs.ColumnBarriers
import Lax637351Proofs.SpeciesEntry

namespace Lax637351Proofs.PlateauSuccess

open Lax637351.Algorithm
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.FiniteHitting
open Lax637351Proofs.FiniteWindows Lax637351Proofs.PairStep Lax637351Proofs.PlateauPairs
open Lax637351Proofs.BarrierWindows Lax637351Proofs.SpeciesEntry Lax637351Proofs.SpeciesWindow
open Lax637351Proofs.SpeciesProtection Lax637351Proofs.SpeciesCap
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauKernel Lax637351Proofs.PlateauChanges
open Lax637351Proofs.Endgame Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnBands
open Lax637351Proofs.ColumnBarriers Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.OffspringEstimates Lax637351Proofs.Transitions Lax637351Proofs.Sampling
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def success : Set (Bool × Population n μ) := {s | s.1 = true}

lemma plateau_missing (hk : 0 < k) (P : Population n μ) (hP : plateau (k := k) P) :
    missing P := by
  intro i hi
  have h := hP i
  rw [(zeros_eq_empty_iff (P i)).mpr hi, Finset.card_empty] at h
  omega

lemma tagged_success_eq (hk : 0 < k) (p : ℝ) (ar : Bool) (P : Population n μ)
    (hP : missing P) (t : ℕ) :
    visit (tagged k p ar) success t (false, P) =
      1 - ((law (step (jump k) p ar) (PMF.pure P) t).toOuterMeasure {Q | missing Q}).toReal := by
  have hm := visit_eq_mean_of_absorbing (tagged k p ar) success (tagged_success_absorbing k p ar) t (false, P)
  rw [mean_event] at hm
  have h' := marked_failure_probability hk p ar (PMF.pure P)
    (fun Q hQ ↦ ((PMF.mem_support_pure_iff _ _).mp hQ).symm ▸ hP) t
  rw [PMF.pure_map] at h'
  have he : {s : Bool × Population n μ | s.1 = false} = successᶜ := by
    ext s
    cases hs : s.1 <;> simp [success, hs]
  rw [he] at h'
  have hh := congrArg ENNReal.toReal (event_add_compl (law (tagged k p ar) (PMF.pure (false, P)) t) success)
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _)), ENNReal.toReal_one, ← h', ← hm] at hh
  linarith only [hh]

def speciesFactor (n k : ℕ) (μ : ℕ+) (p : ℝ) (ar : Bool) (t : ℕ) : ℝ :=
  ((t : ℝ) * changeBound n k p ar + 1) *
    Real.exp (-speciesSlope n k p ar * (level k * (μ : ℕ) - 8))

lemma good_endpoint (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (t : ℕ) (ht : 0 < t) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (htime : Real.exp (2 * (a.T : ℕ)) * (μ : ℕ) ≤ entryRate k (a.T : ℕ) / n * t * ζ)
    (P : Population n μ) (hP : plateau (k := k) P) :
    1 ≤ mean (law (auxiliary k p ar) (PMF.pure P) t) (fun Q ↦ indicator (Q ∈ active k ∧ stabilization a Q)) +
      visit (auxiliary k p ar) (active k)ᶜ t P + (2 * k * ζ + 4 * k * barrierFactor a n μ p ar t) := by
  let K : Population n μ → PMF (Population n μ) := auxiliary k p ar
  let A : Set (Population n μ) := active k
  let G : Set (Population n μ) := {Q | Q ∈ A ∧ stabilization a Q}
  let E : Set (Population n μ) := {Q | Q ∈ A ∧ ¬stabilization a Q}
  let ν := law (columnChain k p ar) (PMF.pure P) t
  have hF := column_recovery hk a hn hm p hp ar hcopy t ht ζ hζ htime P hP
  have hG := stopped_good_le K A G (fun _ hp ↦ hp.1) t P
  have hA := terminal_mass_le_visit K A Aᶜ t P
  have h := terminal_partition ν G Aᶜ E (by
    intro Q _
    by_cases hQ : Q ∈ A
    · by_cases hS : stabilization a Q
      · exact Or.inl ⟨hQ, hS⟩
      · exact Or.inr (Or.inr ⟨hQ, hS⟩)
    · exact Or.inr (Or.inl hQ))
  rw [← mean_event] at h
  exact h.trans (add_le_add (add_le_add hG hA) hF)

lemma active_loss_from_strong (hk : 2 ≤ k) (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (P : Population n μ) (hP : plateau (k := k) P) (hs : strong k P) (t : ℕ) :
    visit (auxiliary k p ar) (active k)ᶜ t P ≤ speciesFactor n k μ p ar t := by
  have hkn : k ≤ n := by have := hc.dimension_four_jump; omega
  apply le_trans _ (species_protection hc herror hμ p hp ar P hP hs t)
  apply visit_mono_on_invariant (auxiliary k p ar) {Q | plateau (k := k) Q} _ _
    (auxiliary_preserves_plateau (by omega : 0 < k) hkn p ar) _ t P hP
  intro Q hQ hh hS
  exact hh ⟨hQ, hS⟩

lemma tagged_endgame (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (hμ : (5 : ℕ) ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (M : ℝ) (hM : 1 ≤ M) (hMμ : 2 * M ≤ ((μ : ℕ) + 1 : ℝ))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ M * p)
    (q : ℝ) (_hq : 0 ≤ q) (hq' : q ≤ 1)
    (htail : q + 2 * k * barrierFactor a n μ p ar (gameLength k μ p M) ≤ gameChance k a.frequencyLevel M)
    (x : Bool × Population n μ) :
    q * indicator (x.2 ∈ active k ∧ stabilization a x.2) ≤
      visit (tagged k p ar) success (gameLength k μ p M) x +
        visit (auxiliary k p ar) (active k)ᶜ (gameLength k μ p M) x.2 := by
  let L : Population n μ → PMF (Population n μ) := auxiliary k p ar
  let t := gameLength k μ p M
  let F : Set (Population n μ) := {Q | ¬columns a.frequencyLevel Q}
  by_cases h : x.2 ∈ active k ∧ stabilization a x.2
  · rw [indicator, if_pos h, mul_one]
    cases x with
    | mk b P =>
      cases b
      · have hgame := endgame_success_bound hk hn.four (show (2 : ℕ+) ≤ μ by
          change (2 : ℕ) ≤ μ
          omega) p hp ar a.frequencyLevel M (settings_levels a).2 hM hMμ hLoss P h.1.1
        rw [← tagged_success_eq (by omega : 0 < k) p ar P (plateau_missing (by omega) P h.1.1)] at hgame
        have ht := stop_visit_union L (active k)ᶜ F t P
        rw [compl_compl] at ht
        have hbar := column_protection hk a hn hm p hp ar hcopy t P h.1.1 h.2
        have hbound := ht.trans (add_le_add le_rfl hbar)
        exact (add_le_add_iff_right (2 * k * barrierFactor a n μ p ar t)).mp
          (htail.trans (hgame.trans (by
            change visit (tagged k p ar) success t (false, P) + visit L F t P ≤ _
            linarith only [hbound])))
      · rw [visit_in _ _ _ _ (by rfl : (true, P) ∈ success)]
        exact hq'.trans (le_add_of_nonneg_right (visit_nonneg _ _ _ _))
  · rw [indicator, if_neg h, mul_zero]
    exact add_nonneg (visit_nonneg _ _ _ _) (visit_nonneg _ _ _ _)

lemma speciesFactor_mono (n k : ℕ) (μ : ℕ+) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (ar : Bool)
    {s t : ℕ} (h : s ≤ t) :
    speciesFactor n k μ p ar s ≤ speciesFactor n k μ p ar t := by
  unfold speciesFactor
  gcongr
  exact hp.1.trans (changeBound_ge_p p hp ar)

lemma strong_tagged_success (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (M : ℝ) (hM : 1 ≤ M) (hMμ : 2 * M ≤ ((μ : ℕ) + 1 : ℝ))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ M * p)
    (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (s : ℕ) (hs : 0 < s) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (hst : Real.exp (2 * (a.T : ℕ)) * (μ : ℕ) ≤ entryRate k (a.T : ℕ) / n * s * ζ)
    (hcol : 2 * k * ζ + 4 * k * barrierFactor a n μ p ar s ≤ 1 / 4)
    (hgame : q + 2 * k * barrierFactor a n μ p ar (gameLength k μ p M) ≤ gameChance k a.frequencyLevel M)
    (hspe : speciesFactor n k μ p ar (s + gameLength k μ p M) ≤ q / 4)
    (x : Bool × Population n μ) (hx : plateau (k := k) x.2) (hxs : strong k x.2) :
    q / 4 ≤ visit (tagged k p ar) success (s + gameLength k μ p M) x := by
  let L : Population n μ → PMF (Population n μ) := auxiliary k p ar
  let K : (Bool × Population n μ) → PMF (Bool × Population n μ) := tagged k p ar
  let t := gameLength k μ p M
  let ν := law K (PMF.pure x) s
  let ρ := law L (PMF.pure x.2) s
  let G : Set (Population n μ) := {Q | Q ∈ active k ∧ stabilization a Q}
  have hp' : 0 ≤ p ∧ p ≤ 1 := ⟨hp.1.le, hp.2⟩
  have hproj : ν.map Prod.snd = ρ := by
    exact (tagged_population_law k p ar (PMF.pure x) s).trans (by rw [PMF.pure_map])
  have hgood := good_endpoint hk a hn hm p hp ar hcopy s hs ζ hζ hst x.2 hx
  have Hs := active_loss_from_strong hk hc herror hμ p hp ar x.2 hx hxs s
  have Hs' := (Hs.trans (speciesFactor_mono n k μ p hp' ar (by omega : s ≤ s + t))).trans hspe
  have hhalf : (1 / 2 : ℝ) ≤ mean ρ (fun Q ↦ indicator (Q ∈ G)) := by
    change 1 ≤ mean ρ (fun Q ↦ indicator (Q ∈ G)) + visit L (active k)ᶜ s x.2 +
      (2 * k * ζ + 4 * k * barrierFactor a n μ p ar s) at hgood
    linarith only [hgood, Hs', hcol, hq']
  have h := mean_mono ν (tagged_endgame hk a hn hm hμ p hp ar hcopy M hM hMμ hLoss q hq hq' hgame)
  rw [mean_mul, mean_add] at h
  have hG : mean ν (fun y ↦ indicator (y.2 ∈ active k ∧ stabilization a y.2)) =
      mean ρ (fun Q ↦ indicator (Q ∈ G)) := by
    change mean ν (fun y ↦ indicator (y.2 ∈ G)) = _
    rw [← mean_map ν Prod.snd (fun Q ↦ indicator (Q ∈ G)), hproj]
  have hLossMean : mean ν (fun y ↦ visit L (active k)ᶜ t y.2) = mean ρ (visit L (active k)ᶜ t) := by
    rw [← mean_map ν Prod.snd (visit L (active k)ᶜ t), hproj]
  rw [hG] at h
  change q * mean ρ (fun Q ↦ indicator (Q ∈ G)) ≤
      mean ν (visit K success t) + mean ν (fun y ↦ visit L (active k)ᶜ t y.2) at h
  rw [hLossMean] at h
  have hS := (visit_after L (active k)ᶜ s t x.2).trans
    ((active_loss_from_strong hk hc herror hμ p hp ar x.2 hx hxs (s + t)).trans hspe)
  have hE := visit_after K success s t x
  change q / 4 ≤ visit K success (s + t) x
  exact (show q / 4 ≤ q * (1 / 2 : ℝ) - q / 4 by ring_nf; exact le_rfl).trans
    ((sub_le_sub_right (mul_le_mul_of_nonneg_left hhalf hq) _).trans (by
      change _ ≤ visit K success (s + t) x
      change _ ≤ mean ν (visit K success t) + mean ρ (visit L (active k)ᶜ t) at h
      change mean ν (visit K success t) ≤ _ at hE
      change mean ρ (visit L (active k)ᶜ t) ≤ q / 4 at hS
      linarith only [h, hS, hE]))

lemma plateau_success (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (M : ℝ) (hM : 1 ≤ M) (hMμ : 2 * M ≤ ((μ : ℕ) + 1 : ℝ))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ M * p)
    (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (v s : ℕ) (hs : 0 < s) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (hvt : 6 * (μ : ℕ) ≤ (k : ℝ) / (256 * n) * v)
    (hst : Real.exp (2 * (a.T : ℕ)) * (μ : ℕ) ≤ entryRate k (a.T : ℕ) / n * s * ζ)
    (hcol : 2 * k * ζ + 4 * k * barrierFactor a n μ p ar s ≤ 1 / 4)
    (hgame : q + 2 * k * barrierFactor a n μ p ar (gameLength k μ p M) ≤ gameChance k a.frequencyLevel M)
    (hspe : speciesFactor n k μ p ar (s + gameLength k μ p M) ≤ q / 4)
    (P : Population n μ) (hP : plateau (k := k) P) :
    q / 8 ≤ 1 - ((law (step (jump k) p ar) (PMF.pure P) (v + (s + gameLength k μ p M))).toOuterMeasure
          {Q | missing Q}).toReal := by
  let K : (Bool × Population n μ) → PMF (Bool × Population n μ) := tagged k p ar
  let L : Population n μ → PMF (Population n μ) := auxiliary k p ar
  let G : Set (Population n μ) := {Q | plateau (k := k) Q ∧ strong k Q}
  let t := gameLength k μ p M
  have hsG : ∀ x ∈ Prod.snd ⁻¹' G, q / 4 ≤ visit K success (s + t) x := by
    intro x hx
    exact strong_tagged_success hk a hn hm hc herror hμ p hp ar hcopy M hM hMμ hLoss q hq hq' s hs ζ hζ hst
      hcol hgame hspe x hx.1 hx.2
  have hh := visit_recovery K (Prod.snd ⁻¹' G) success (s + t) (q / 4) (by positivity) hsG v (false, P)
  rw [visit_map K L Prod.snd (tagged_marginal k p ar)] at hh
  have h := species_entry_tail hc hμ p ⟨hp.1.le, hp.2⟩ ar P hP v
  change ((k : ℝ) / (256 * n)) * v * (1 - visit L G v P) ≤ 3 * (μ : ℕ) at h
  have hm' : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have he : (1 / 2 : ℝ) ≤ visit L G v P := by
    have hpv : (0 : ℝ) < (k : ℝ) / (256 * n) * v := by linarith only [hm', hvt]
    have hbound : (k : ℝ) / (256 * n) * v * (1 - visit L G v P) ≤
        (k : ℝ) / (256 * n) * v * (1 / 2) := h.trans (by linarith only [hvt])
    have hu := (mul_le_mul_iff_of_pos_left hpv).mp hbound
    linarith only [hu]
  have hfin := (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ q / 4)).trans hh
  rw [show q / 4 * (1 / 2 : ℝ) = q / 8 by ring] at hfin
  change q / 8 ≤ visit (tagged k p ar) success (v + (s + t)) (false, P) at hfin
  rwa [tagged_success_eq (by omega : 0 < k) p ar P (plateau_missing (by omega) P hP)] at hfin

end
end Lax637351Proofs.PlateauSuccess
