import Lax637351Proofs.PairDrift
import Lax637351Proofs.AffineWindow

namespace Lax637351Proofs.Endgame

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteWindows
open Lax637351Proofs.Auxiliary Lax637351Proofs.PlateauPairs Lax637351Proofs.PlateauKernel
open Lax637351Proofs.SubsetPairs Lax637351Proofs.CoordinateExtension Lax637351Proofs.PairDrift
open Lax637351Proofs.PlateauChanges Lax637351Proofs.RareSuccess
open Lax637351Proofs.MarkedStep Lax637351Proofs.PairStep Lax637351Proofs.AffineWindow
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def columns (δ : ℝ) (P : Population n μ) : Prop := ∀ i : Fin n, δ ≤ avoidsRate {i} P

def endEvent (δ : ℝ) : Set (Bool × Population n μ) :=
  {s | s.1 = true ∨ ¬ columns δ s.2}

def scoreClamp (k r : ℕ) (δ : ℝ) (s : Bool × Population n μ) : ℝ :=
  if s ∈ endEvent δ then 1 else subsetScore r s.2 / (2 : ℝ) ^ k

def growthRate (μ : ℕ+) (p M : ℝ) : ℝ := 2 * M * p / ((μ : ℕ) + 1)
def feedRate (k : ℕ) (δ M : ℝ) : ℝ := extensionConstant k * δ / (2 * M * (k : ℝ))

def gameLength (k : ℕ) (μ : ℕ+) (p M : ℝ) : ℕ :=
  (k - 1) * width (growthRate μ p M) + width (p * crossRate k)

def gameChance (k : ℕ) (δ M : ℝ) : ℝ :=
  (δ / (2 : ℝ) ^ k) * (feedRate k δ M / 2) ^ (k - 1) / 2

lemma end_support (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (s : Bool × Population n μ) (hs : plateau (k := k) s.2)
    (y : Bool × Population n μ) (hy : y ∈ (tagged k p ar s).support) :
    plateau (k := k) y.2 := by
  have hh : y.2 ∈ ((tagged k p ar s).map Prod.snd).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨y, hy, rfl⟩
  rw [tagged_marginal] at hh
  exact auxiliary_preserves_plateau hk hkn p ar s.2 hs y.2 hh

lemma mark_lower (k : ℕ) (p : ℝ) (ar : Bool) (δ : ℝ) (s : Bool × Population n μ) :
    mean (draws p s.2) (fun d ↦ indicator (child d = optimum n)) ≤
      mean (tagged k p ar s) (fun y ↦ indicator (y ∈ endEvent δ)) := by
  rw [tagged, mean_bind]
  apply mean_mono
  intro d
  rw [mean_map]
  by_cases h : child d = optimum n
  · have he (Q : Population n μ) :
        (s.1 || decide (child d = optimum n), Q) ∈ (endEvent δ : Set (Bool × Population n μ)) :=
      Or.inl (by simp [h])
    simp only [indicator, if_pos h, if_pos (he _), mean_const, le_refl]
  · rw [indicator, if_neg h]
    exact mean_nonneg _ (fun _ ↦ indic_nonneg _)

lemma endgame_window (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool) (δ M : ℝ) (hδ : 0 < δ ∧ δ ≤ 1)
    (hM : 1 ≤ M) (hMμ : 2 * M ≤ ((μ : ℕ) + 1 : ℝ))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ M * p)
    (P : Population n μ) (hP : plateau (k := k) P) :
    gameChance k δ M ≤ visit (tagged k p ar) (endEvent δ) (gameLength k μ p M) (false, P) := by
  let α := Bool × Population n μ
  let G : Set α := endEvent δ
  let C : Set α := {s | plateau (k := k) s.2}
  let K := tagged k p ar (n := n) (μ := μ)
  let W := stopped K Gᶜ
  let s : α := (false, P)
  let la := growthRate μ p M
  let a := feedRate k δ M
  let σ := p * crossRate k
  let d := δ / (2 : ℝ) ^ k
  let F (r : ℕ) := scoreClamp k (r + 1) δ (n := n) (μ := μ)
  let R (x : α) := indicator (x ∈ G)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm : (0 : ℝ) < ((μ : ℕ) + 1) := by positivity
  have hM0 : 0 < M := by linarith
  have hla : 0 < la := div_pos (mul_pos (mul_pos (by norm_num) hM0) hp.1) hm
  have hla' : la ≤ 1 := by
    apply (div_le_one hm).mpr
    apply (mul_le_mul_of_nonneg_left hp.2 (by positivity : 0 ≤ 2 * M)).trans
    simpa only [mul_one] using hMμ
  have hσ : 0 < σ := mul_pos hp.1 (crossRate_pos k)
  have hσ' : σ ≤ 1 := by
    have hc : crossRate k ≤ 1 := by
      unfold crossRate
      have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k + k)
      linarith only [h]
    exact mul_le_one₀ hp.2 (crossRate_pos k).le hc
  have hc : extensionConstant k ≤ 1 := by
    unfold extensionConstant
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k + k)
    linarith only [h]
  have ha : 0 ≤ a := div_nonneg (mul_nonneg (by unfold extensionConstant; positivity) hδ.1.le) (by positivity)
  have ha' : a ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * M * (k : ℝ))).mpr
    have h := mul_le_one₀ hc hδ.1.le hδ.2
    have hh : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact h.trans ((one_le_mul_of_one_le_of_one_le (by linarith) hh))
  have hd : 0 ≤ d := div_nonneg hδ.1.le (by positivity)
  have hD : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hd' : d ≤ 1 := (div_le_one (by positivity)).mpr (hδ.2.trans hD)
  have hW (x : α) (hx : x ∈ C) (y : α) (hy : y ∈ (W x).support) : y ∈ C := by
    by_cases hh : x ∈ G
    · rw [show W x = PMF.pure x by simp [W, stopped, hh], PMF.mem_support_pure_iff] at hy
      exact hy.symm ▸ hx
    · rw [show W x = K x by simp [W, stopped, hh]] at hy
      exact end_support (by omega : 0 < k) (by omega : k ≤ n) p ar x hx y hy
  have hF_on (r : ℕ) (x : α) (hx : x ∈ G) : F r x = 1 := if_pos hx
  have hF_off (r : ℕ) (x : α) (hx : x ∉ G) : F r x = subsetScore (r + 1) x.2 / (2 : ℝ) ^ k := if_neg hx
  have hR_on (x : α) (hx : x ∈ G) : R x = 1 := if_pos hx
  have hR_off (x : α) (hx : x ∉ G) : R x = 0 := if_neg hx
  have hbase (x : α) (hx : x ∈ C) : d ≤ F 0 x := by
    by_cases hg : x ∈ G
    · rw [hF_on _ _ hg]; exact hd'
    · have hf : columns δ x.2 := by
        by_contra h
        exact hg (Or.inr h)
      have ht := singleton_lower x.2 hx (by omega : 0 < k) δ hδ.1.le hf
      rw [hF_off _ _ hg]
      exact div_le_div_of_nonneg_right ht (by positivity : 0 ≤ (2 : ℝ) ^ k)
  have hFn (r : ℕ) (x : α) : 0 ≤ F r x := by
    dsimp only [F, scoreClamp]
    split_ifs
    · norm_num
    · exact div_nonneg (subsetScore_nonneg _ _) (by positivity)
  have hstep (r : ℕ) (hr : r < k - 1) (x : α) (hx : x ∈ C) :
      (1 - la) * F (r + 1) x + (la * a) * F r x ≤ mean (W x) (F (r + 1)) := by
    by_cases hg : x ∈ G
    · have he : W x = PMF.pure x := by simp [W, stopped, hg]
      rw [he, mean_pure]
      simp only [hF_on _ _ hg, mul_one]
      linarith only [mul_le_mul_of_nonneg_left ha' hla.le]
    · have hf : columns δ x.2 := by
        by_contra h
        exact hg (Or.inr h)
      have hh := pair_advance (by omega : 0 < k) (by omega : 2 ≤ n) hn hμ (r + 1) (by omega) x.2 hx
        p ⟨hp.1.le, hp.2⟩ ar δ M hδ.1.le hf hLoss
      have hcoef : la * a = p * extensionConstant k * δ / ((k : ℝ) * ((μ : ℕ) + 1)) := by
        dsimp [la, a, growthRate, feedRate]
        field_simp
      have haux : mean (auxiliary k p ar x.2) (fun P ↦ subsetScore (r + 2) P / (2 : ℝ) ^ k) ≤
          mean (K x) (F (r + 1)) := by
        rw [← tagged_marginal k p ar x, mean_map]
        apply mean_mono_on_support
        intro y hy
        by_cases h : y ∈ G
        · have hplat := end_support (by omega : 0 < k) (by omega : k ≤ n) p ar x hx y hy
          rw [hF_on _ _ h]
          exact (div_le_one (by positivity : 0 < (2 : ℝ) ^ k)).mpr (subsetScore_upper (r + 2) y.2 hplat)
        · rw [hF_off _ _ h]
      have hstep := div_le_div_of_nonneg_right hh (show 0 ≤ (2 : ℝ) ^ k by positivity)
      have hmean : mean (auxiliary k p ar x.2) (subsetScore (r + 1 + 1)) / (2 : ℝ) ^ k =
          mean (auxiliary k p ar x.2) (fun P ↦ subsetScore (r + 2) P / (2 : ℝ) ^ k) := by
        simp only [div_eq_inv_mul, mean_mul]
      rw [hmean] at hstep
      rw [show W x = K x by simp [W, stopped, hg]]
      apply le_trans _ (hstep.trans haux)
      rw [hF_off _ _ hg, hF_off _ _ hg, hcoef]
      dsimp only [la, growthRate]
      exact le_of_eq (by ring)
  have hmark (x : α) (hx : x ∈ C) : (1 - σ) * R x + σ * F (k - 1) x ≤ mean (W x) R := by
    by_cases hg : x ∈ G
    · rw [show W x = PMF.pure x by simp [W, stopped, hg], mean_pure]
      simp only [hR_on _ hg, hF_on _ _ hg, mul_one]
      linarith
    · rw [show W x = K x by simp [W, stopped, hg]]
      rw [hF_off _ _ hg, hR_off _ hg, mul_zero, zero_add]
      let A := subsetScore k x.2
      have he : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
      rw [he]
      have hprob := probability_child_opt (by omega : 0 < k) (by omega : 2 ≤ n) p ⟨hp.1.le, hp.2⟩ x.2 hx
      have ht : A / (2 : ℝ) ^ k ≤ A := (div_le_self (subsetScore_nonneg _ _) hD)
      apply (mul_le_mul_of_nonneg_left ht hσ.le).trans
      exact hprob.trans (mark_lower k p ar δ x)
  let E (r t : ℕ) := mean (law W (PMF.pure s) t) (F r)
  let V (t : ℕ) := mean (law W (PMF.pure s) t) R
  have hs : s ∈ C := hP
  have hbal (t : ℕ) : d ≤ E 0 t := by
    have hn := law_invariant W (PMF.pure s) C (fun x hx ↦ ((PMF.mem_support_pure_iff _ _).mp hx).symm ▸ hs) hW t
    refine (mean_const (law W (PMF.pure s) t) d).symm.le.trans ?_
    exact mean_mono_on_support _ (fun y hy ↦ hbase y (hn y hy))
  have hα (r : ℕ) (hr : r < k - 1) (t : ℕ) :
      (1 - la) * E (r + 1) t + (la * a) * E r t ≤ E (r + 1) (t + 1) :=
    law_affine W C hW s hs (F (r + 1)) (F r) (1 - la) (la * a) (hstep r hr) t
  let H := (k - 1) * width la
  let b := d * (a / 2) ^ (k - 1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb' (t : ℕ) (ht : H ≤ t) : b ≤ E (k - 1) t :=
    triangular_growth (k - 1) hla hla' ha hd E (fun r t ↦ mean_nonneg _ (hFn r)) hbal hα (k - 1) le_rfl t ht
  have hV (t : ℕ) : (1 - σ) * V t + σ * E (k - 1) t ≤ V (t + 1) :=
    law_affine W C hW s hs R (F (k - 1)) (1 - σ) σ hmark t
  have hf := window hσ hσ' b hb (fun u ↦ V (H + u)) (mean_nonneg _ (fun _ ↦ indic_nonneg _)) (fun u _ ↦ by
    have h := hV (H + u)
    have ht := mul_le_mul_of_nonneg_left (hb' (H + u) (Nat.le_add_right _ _)) hσ.le
    rw [← Nat.add_assoc]
    linarith only [h, ht])
  change b / 2 ≤ mean (law W (PMF.pure s) (H + width σ)) R at hf
  rw [show R = fun x ↦ if x ∈ G then 1 else 0 from indicator_eq_membership G, ← visit_eq_mean_stopped] at hf
  exact hf

lemma gameChance_pos {δ M : ℝ} (hk : 0 < k) (hδ : 0 < δ) (hM : 0 < M) : 0 < gameChance k δ M := by
  unfold gameChance feedRate extensionConstant
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

lemma gameLength_bound (k : ℕ) (μ : ℕ+) (p M : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (hM : 1 ≤ M) (hMμ : 2 * M ≤ ((μ : ℕ) + 1 : ℝ)) :
    (gameLength k μ p M : ℝ) ≤ (2 * (k : ℝ) + 2 / crossRate k) * (μ : ℕ) / p := by
  have hM' : 0 < M := by linarith
  have hμ : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hμ' : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hR : 0 < growthRate μ p M := by
    unfold growthRate
    exact div_pos (mul_pos (mul_pos (by norm_num) hM') hp.1) (by positivity)
  have hR' : growthRate μ p M ≤ 1 := by
    unfold growthRate
    exact (div_le_one (by positivity)).mpr
      ((by nlinarith only [mul_le_mul_of_nonneg_left hp.2 (by positivity : 0 ≤ 2 * M)] :
        2 * M * p ≤ 2 * M).trans hMμ)
  have hpR : 0 < p * crossRate k := mul_pos hp.1 (crossRate_pos k)
  have hpR' : p * crossRate k ≤ 1 := by
    apply mul_le_one₀ hp.2 (crossRate_pos k).le
    have hh := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k + k)
    unfold crossRate
    linarith only [hh]
  have hw : (width (growthRate μ p M) : ℝ) ≤ 2 * (μ : ℕ) / p := by
    apply (width_upper hR hR').trans
    have he : 2 / growthRate μ p M = (((μ : ℕ) : ℝ) + 1) / M / p := by
      unfold growthRate
      field_simp
    rw [he, div_le_div_iff_of_pos_right hp.1, div_le_iff₀ hM']
    have ht := mul_le_mul_of_nonneg_right hM (show 0 ≤ 2 * ((μ : ℕ) : ℝ) by positivity)
    nlinarith only [ht, hμ']
  have hw' : (width (p * crossRate k) : ℝ) ≤ (2 / crossRate k) * (μ : ℕ) / p := by
    apply (width_upper hpR hpR').trans
    rw [show (2 : ℝ) / (p * crossRate k) = (2 / crossRate k) / p by ring,
      div_le_div_iff_of_pos_right hp.1]
    exact le_mul_of_one_le_right (by have h := crossRate_pos k; positivity) hμ'
  unfold gameLength
  push_cast
  have hk : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
  have h₁ := mul_le_mul hk hw (Nat.cast_nonneg _) (by positivity : 0 ≤ (k : ℝ))
  linarith only [h₁, hw', show
    (k : ℝ) * (2 * (μ : ℕ) / p) + (2 / crossRate k) * (μ : ℕ) / p =
      (2 * (k : ℝ) + 2 / crossRate k) * (μ : ℕ) / p by ring]

lemma tagged_success_absorbing (k : ℕ) (p : ℝ) (ar : Bool)
    (s : Bool × Population n μ) (hs : s.1 = true)
    (y : Bool × Population n μ) (hy : y ∈ (tagged k p ar s).support) : y.1 = true := by
  rw [tagged, PMF.mem_support_bind_iff] at hy
  obtain ⟨d, hd, hy⟩ := hy
  obtain ⟨Q, hQ, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
  simp [hs]

lemma endgame_success_bound (hk : 2 ≤ k) (hn : 4 * k ≤ n) (hμ : 2 ≤ μ)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool) (δ M : ℝ) (hδ : 0 < δ ∧ δ ≤ 1)
    (hM : 1 ≤ M) (hMμ : 2 * M ≤ ((μ : ℕ) + 1 : ℝ))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ M * p)
    (P : Population n μ) (hP : plateau (k := k) P) :
    gameChance k δ M ≤
      1 - ((law (step (jump k) p ar) (PMF.pure P) (gameLength k μ p M)).toOuterMeasure
           {Q | missing Q}).toReal +
      visit (auxiliary k p ar) {Q | ¬columns δ Q} (gameLength k μ p M) P := by
  let K := tagged k p ar (n := n) (μ := μ)
  let t := gameLength k μ p M
  let x : Bool × Population n μ := (false, P)
  let E : Set (Bool × Population n μ) := {s | s.1 = true}
  let F : Set (Population n μ) := {Q | ¬columns δ Q}
  have hGame := endgame_window hk hn hμ p hp ar δ M hδ hM hMμ hLoss P hP
  have hUnion := visit_union_upper K E (Prod.snd ⁻¹' F) t x
  have hproj := visit_map K (auxiliary k p ar) Prod.snd (tagged_marginal k p ar) F t x
  rw [hproj] at hUnion
  have hm := visit_eq_mean_of_absorbing K E (tagged_success_absorbing k p ar) t x
  rw [mean_event] at hm
  have hm' := marked_failure_probability (by omega : 0 < k) p ar (PMF.pure P)
    (fun Q hQ ↦ by
      have he := (PMF.mem_support_pure_iff _ _).mp hQ
      rw [he]
      intro i hi
      have h := hP i
      rw [(zeros_eq_empty_iff (P i)).mpr hi, Finset.card_empty] at h
      omega) t
  rw [PMF.pure_map] at hm'
  have he : {s : Bool × Population n μ | s.1 = false} = Eᶜ := by
    ext s
    cases hs : s.1 <;> simp [E, hs]
  rw [he] at hm'
  change _ = (law K (PMF.pure x) t).toOuterMeasure Eᶜ at hm'
  have hh := congrArg ENNReal.toReal (event_add_compl (law K (PMF.pure x) t) E)
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one _ _)), ENNReal.toReal_one, ← hm', ← hm] at hh
  change gameChance k δ M ≤ visit K (E ∪ Prod.snd ⁻¹' F) t x at hGame
  change _ ≤ 1 - _ + visit (auxiliary k p ar) F t x.2
  linarith only [hGame, hUnion, hh]

end
end Lax637351Proofs.Endgame
