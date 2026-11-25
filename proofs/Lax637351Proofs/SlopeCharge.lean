import Lax637351Proofs.SlopeReset
import Lax637351Proofs.PlateauRegeneration
import Lax637351Proofs.TailLower

namespace Lax637351Proofs.SlopeCharge

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.FiniteChain
open Lax637351Proofs.FiniteHitting Lax637351Proofs.FiniteRace Lax637351Proofs.Ordinary
open Lax637351Proofs.Regeneration Lax637351Proofs.RegenerationBounds
open Lax637351Proofs.Charge Lax637351Proofs.MaskKernel Lax637351Proofs.TailLower
open Lax637351Proofs.RuntimeTransfer Lax637351Proofs.PlateauRegeneration
open Lax637351Proofs.BestRank Lax637351Proofs.SlopeReset
open scoped Classical ENNReal

noncomputable section

variable {n k : ℕ} {μ : ℕ+}

def slopeClass (k B : ℕ) : Set (Population n μ) :=
  {P | ¬ missing P ∨ ordinary k P ∧ bestZeros P ≤ B}

lemma class_invariant (hk : 0 < k) (hkn : k ≤ n) (p : ℝ) (ar : Bool)
    (B : ℕ) (P : Population n μ) (hP : P ∈ slopeClass k B)
    (Q : Population n μ) (hQ : Q ∈ (step (jump k) p ar P).support) : Q ∈ slopeClass k B := by
  rcases hP with ho | ⟨hOrd, hB⟩
  · exact Or.inl (step_preserves_optimum hk p ar ho hQ)
  · by_cases hm : missing Q
    · have ho := ordinary_preserved hkn p ar hOrd hQ hm
      have he := lower_best_notlost hkn P Q hOrd ho (fun i ↦ step_fitness_mono _ _ _ _ hQ i)
      exact Or.inr ⟨ho, he.trans hB⟩
    · exact Or.inl hm

lemma cutoff_stopped_agree (hk : 0 < k) (hkn : k ≤ n) (p : ℝ)
    (B r : ℕ) (hr : r ≤ B) (t : ℕ) (Q : Population n μ) (hQ : Q ∈ slopeClass k r) :
    visit (stopped (step (jump k) p false) (cutoffResets k B)ᶜ) target t Q =
      visit (stopped (step (jump k) p false) (cutoffResets k r)ᶜ) target t Q := by
  let K := step (jump k) p false (n := n) (μ := μ)
  let R := cutoffResets (n := n) (μ := μ) k B
  let S := cutoffResets (n := n) (μ := μ) k r
  change visit (stopped K Rᶜ) target t Q = visit (stopped K Sᶜ) target t Q
  apply visit_agrees_on _ _ _ (slopeClass k r) _ _ t Q hQ
  · intro P hP
    have hf : P ∈ R ↔ P ∈ S := by
      rcases hP with ho | ⟨hOrd, hB⟩
      · have hbad : ¬ ordinary k P := fun he ↦ ho (ordinary_missing hk he)
        simp [R, S, cutoffResets, hbad]
      · have hB' : bestZeros P ≤ B := hB.trans hr
        simp [R, S, cutoffResets, not_lt_of_ge hB, not_lt_of_ge hB']
    simp only [stopped, Set.mem_compl_iff, hf]
  · intro P hP X hX
    by_cases hh : P ∈ Rᶜ
    · rw [stopped, if_pos hh] at hX
      exact class_invariant hk hkn p false r P hP X hX
    · rw [stopped, if_neg hh, PMF.mem_support_pure_iff] at hX
      exact hX.symm ▸ hP

lemma copyBudget_mono (n : ℕ) (μ : ℕ+) (p : ℝ) : Monotone (fun B ↦ copyBudget n B μ p) := by
  intro a b hab
  unfold copyBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  gcongr

lemma reset_span_uniform (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (hμ : 2 ≤ μ)
    (B r : ℕ) (hr : r ≤ B) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (M : ℝ)
    (hM : copyBudget n B μ p ≤ M) (t : ℕ) (Q : Population n μ) :
    span (masked (jump k) p false) (cutoffResets k r) t Q ≤ (max 1 r : ℕ) * M := by
  apply (cutoff_span hk hkn hn hμ r p hp t Q).trans
  have hr' : r - k + 1 ≤ max 1 r := by by_cases h : r = 0 <;> omega
  exact mul_le_mul (by exact_mod_cast hr') ((copyBudget_mono n μ p hr).trans hM)
    (by linarith [copyBudget_one n r μ hp.1]) (by positivity)

def slopeCharge (n : ℕ) (M : ℝ) (r : ℕ) : ℝ :=
  hitBound ((r : ℝ) * M) (1 / (n : ℝ)) r / ((r : ℝ) * M)

lemma slopeCharge_eq (n : ℕ) (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) :
    slopeCharge n M r = (r.factorial : ℝ) * (2 / (n : ℝ)) * (2 * (r : ℝ) * M / n) ^ (r - 1) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold slopeCharge hitBound
  have he : (2 * ((r : ℝ) * M) * (1 / (n : ℝ))) ^ r =
      (2 * ((r : ℝ) * M) * (1 / (n : ℝ))) ^ (r - 1) * (2 * ((r : ℝ) * M) * (1 / (n : ℝ))) := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [he, show 2 * ((r : ℝ) * M) * (1 / (n : ℝ)) = 2 * (r : ℝ) * M / n by ring]
  field_simp

lemma slopeCharge_pos (n : ℕ) (hn : 0 < n) (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) :
    0 < slopeCharge n M r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hF : (0 : ℝ) < r.factorial := by exact_mod_cast r.factorial_pos
  unfold slopeCharge hitBound
  positivity

lemma slopeCharge_succ_le (n B : ℕ) (hn : 0 < n) (M : ℝ) (hM : 0 < M)
    (hsmall : 2 * Real.exp 1 * (B : ℝ) ^ 2 * M / n ≤ 1)
    (r : ℕ) (hr : 0 < r) (hrB : r < B) :
    slopeCharge n M (r + 1) ≤ slopeCharge n M r := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hB : (r : ℝ) + 1 ≤ B := by exact_mod_cast hrB
  let a := 2 * (r : ℝ) * M / n
  let d := 1 + (r : ℝ)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have he : 2 * ((r + 1 : ℕ) : ℝ) * M / n = a * d := by
    push_cast
    dsimp [a, d]
    field_simp
  have hp : d ^ r ≤ Real.exp 1 := by
    have heq : Real.exp ((r : ℝ)⁻¹) ^ r = Real.exp 1 := by
      rw [← Real.exp_nat_mul, mul_inv_cancel₀ hrr.ne']
    rw [← heq]
    exact pow_le_pow_left₀ hd (by dsimp [d]; simpa only [add_comm] using Real.add_one_le_exp ((r : ℝ)⁻¹)) _
  have hn' : (r + 1 : ℕ) - 1 = r := by omega
  have hPow : a ^ r = a ^ (r - 1) * a := by
    nth_rw 1 [← Nat.sub_add_cancel hr]
    exact pow_succ _ _
  have hsmall' : ((r : ℝ) + 1) * a * Real.exp 1 ≤ 1 := by
    have hh : ((r : ℝ) + 1) * (r : ℝ) ≤ (B : ℝ) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hB (show (r : ℝ) ≤ B by linarith) hrr.le (by positivity)
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * Real.exp 1 * M / n by positivity)
    apply le_trans _ hsmall
    dsimp [a]
    convert hm using 1 <;> ring
  rw [slopeCharge_eq n M hM (r + 1) (by omega), slopeCharge_eq n M hM r hr,
    hn', he, mul_pow, hPow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hterm : ((r : ℝ) + 1) * a * d ^ r ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (by positivity)).trans hsmall'
  have hf : (0 : ℝ) ≤ r.factorial := by positivity
  have ht := mul_le_mul_of_nonneg_left hterm (show 0 ≤ (r.factorial : ℝ) * (2 / (n : ℝ)) * a ^ (r - 1) by positivity)
  nlinarith only [ht]

lemma slopeCharge_le (n B : ℕ) (hn : 0 < n) (M : ℝ) (hM : 0 < M)
    (hsmall : 2 * Real.exp 1 * (B : ℝ) ^ 2 * M / n ≤ 1)
    (r : ℕ) (hrk : k ≤ r) (hr : r ≤ B) (hk : 0 < k) :
    slopeCharge n M r ≤ slopeCharge n M k := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases he : r + 1 = k
    · rw [he]
    · have hr' : k ≤ r := by omega
      exact (slopeCharge_succ_le n B hn M hM hsmall r (hk.trans_le hr') (by omega)).trans (ih hr' (by omega))

lemma zero_visit_on_reset {α : Type*} [Fintype α] (K : α → PMF α) (R G : Set α)
    (x : α) (hx : x ∈ R) (hG : x ∉ G) (t : ℕ) :
    visit (stopped K Rᶜ) G t x = 0 := by
  induction t with
  | zero => simp [visit, hG]
  | succ t ih =>
    have ht : x ∉ Rᶜ := by simpa
    rw [visit, if_neg hG, stopped, if_neg ht, mean_pure, ih]

lemma homogeneous_charge_at_cutoff (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (hμ : 2 ≤ μ)
    (B : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (M : ℝ) (hM : copyBudget n B μ p ≤ M)
    (P : Population n μ) (ho : ordinary k P) (hB : bestZeros P ≤ B) (hhom : homogeneous P) (t : ℕ) :
    mean (step (jump k) p false P)
      (visit (stopped (step (jump k) p false) (cutoffResets k B)ᶜ) target t) ≤
      slopeCharge n M (bestZeros P) := by
  let J := masked (jump k) p false (n := n) (μ := μ)
  let K := step (jump k) p false (n := n) (μ := μ)
  let r := bestZeros P
  let R := cutoffResets (μ := μ) (n := n) k r
  let S := cutoffResets (μ := μ) (n := n) k B
  let D := zeros (P 0)
  let ρ : ℝ := 1 / n
  let b := (r : ℝ) * M
  let V := hitBound b ρ
  have hr : k ≤ r := (ordinary_iff_bestZeros P).mp ho
  have hr0 : 0 < r := hk.trans_le hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hm1 : 1 ≤ M := (copyBudget_one n B μ hp.1).trans hM
  have hb : 1 ≤ b := one_le_mul_of_one_le_of_one_le hr1 hm1
  have hrmax : max 1 r = r := max_eq_right hr0
  have hD : D.card = r := by
    obtain ⟨i, hi⟩ := bestZeros_attains P
    simpa only [hhom i, D, r] using hi
  have hD0 : intact D P := fun j hj i ↦ by rw [hhom i]; exact (mem_zeros _ _).mp hj
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hmask (P : Population n μ) (A : Finset (Fin n)) :
      mean (J P) (fun v ↦ if A ⊆ v.1 then 1 else 0) ≤ ρ ^ A.card :=
    (independent_hit hn (jump k) p false P A).le
  have hspan (T : ℕ) (Q : Population n μ) : span J R T Q ≤ b := by
    simpa only [hrmax] using reset_span_uniform hk hkn hn hμ B r hB p hp M hM T Q
  have hcap (A : Finset (Fin n)) (_ : A ∈ nonemptySubsets D) (u : ℕ) (Q : Population n μ) :
      capture J R u (D \ A) Q ≤ V (D \ A).card :=
    capture_le J R b ρ hb hρ hmask hspan (D \ A) u Q
  have hfirst := mask_probability_first J R ρ V (hitBound_nonneg hb hρ) D hmask hcap (V D.card / b)
    (coefficient_le hb hρ D) t P
  change mean (K P) (visit (stopped K Sᶜ) target t) ≤ _
  rw [show K P = (J P).map Prod.snd from (congrFun (marginal_masked _ _ _) P).symm, mean_map]
  have hpt (v : Finset (Fin n) × Population n μ) (hv : v ∈ (J P).support) :
      visit (stopped K Sᶜ) target t v.2 ≤ if Disjoint D v.1 then 0 else capture J R t (D \ v.1) v.2 := by
    have hv2 : v.2 ∈ (K P).support := by
      rw [show K = marginal J from (marginal_masked _ _ _).symm, marginal]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨v, hv, rfl⟩
    have hc : v.2 ∈ slopeClass k r := class_invariant hk hkn p false r P (Or.inr ⟨ho, le_rfl⟩) _ hv2
    change visit (stopped (step (jump k) p false) (cutoffResets k B)ᶜ) target t v.2 ≤ _
    rw [cutoff_stopped_agree hk hkn p B r hB t v.2 hc]
    by_cases hh : Disjoint D v.1
    · rw [if_pos hh, ordinary_no_hit_stays hkn p false P ho hhom v hv hh]
      exact (zero_visit_on_reset K R target P (Or.inr (Or.inr hhom))
        (by simpa [target] using ordinary_missing hk ho) t).le
    · rw [if_neg hh]
      rw [← marginal_masked (jump k) p false]
      apply stopped_success_le_capture J R target intact
      · exact fun x hx A hA ↦ intact_missing A x hA hx
      · exact intact_carries (jump k) p false
      · exact intact_carries (jump k) p false P v hv D hD0
  exact (mean_mono_on_support _ hpt).trans (by simpa only [hD, V, ρ, b, r, slopeCharge] using hfirst)

def fixedColumn (k B : ℕ) (P : Population n μ) : Prop :=
  ordinary k P ∧ bestZeros P ≤ B ∧ ∃ j : Fin n, intact {j} P

lemma fixed_column_lower (hk : 0 < k) (hkn : k ≤ n) (hn : 2 ≤ n) (hμ : 2 ≤ μ)
    (B : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (M : ℝ) (hM : copyBudget n B μ p ≤ M)
    (hsmall : 2 * Real.exp 1 * (B : ℝ) ^ 2 * M / n ≤ 1)
    (hslack : 2 * (B : ℝ) * M / n ≤ 1 / 4)
    (P : Population n μ) (hP : fixedColumn k B P) :
    ENNReal.ofReal (1 / (8 * slopeCharge n M k)) ≤ tailSum (step (jump k) p false)
      {Q | missing Q} (PMF.pure P) := by
  let J := masked (jump k) p false (n := n) (μ := μ)
  let K := step (jump k) p false (n := n) (μ := μ)
  let R := cutoffResets (μ := μ) (n := n) k B
  let C := slopeClass (μ := μ) (n := n) k B
  let a := slopeCharge n M k
  let b := (B : ℝ) * M
  have hB : k ≤ B := ((ordinary_iff_bestZeros P).mp hP.1).trans hP.2.1
  have hM1 := (copyBudget_one n B μ hp.1).trans hM
  have hb : 1 ≤ b := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk.trans_le hB) hM1
  have ha : 0 < a := slopeCharge_pos n (by omega) M (by linarith) k hk
  have hc : P ∈ C := Or.inr ⟨hP.1, hP.2.1⟩
  obtain ⟨j, hj⟩ := hP.2.2
  have htail (t : ℕ) : visit K target t P ≤ (t : ℝ) * a + 1 / 4 := by
    have hh := visit_le_charges K target R C a ha.le (class_invariant hk hkn p false B)
      (fun Q hQ hR hNG T ↦ ?_) t P hc
    · apply hh.trans
      apply add_le_add_right
      rw [show K = marginal J from (marginal_masked _ _ _).symm]
      refine (stopped_success_le_capture J R target intact (fun x hx A hA ↦ intact_missing A x hA hx)
        (intact_carries (jump k) p false) t {j} P hj).trans ?_
      have hcap := capture_le J R b (1 / (n : ℝ)) hb (by positivity)
        (fun Q A ↦ (independent_hit hn (jump k) p false Q A).le)
        (fun T Q ↦ by
          simpa only [max_eq_right (show 1 ≤ B by omega)] using
            reset_span_uniform hk hkn hn hμ B B le_rfl p hp M hM T Q)
        ({j} : Finset (Fin n)) t P
      apply hcap.trans
      simp only [hitBound, Finset.card_singleton, Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
      dsimp [b]
      rw [show 2 * ((B : ℝ) * M) * (1 / (n : ℝ)) = 2 * (B : ℝ) * M / n by ring]
      exact hslack
    have hmiss : missing Q := not_not.mp hNG
    have hr := hQ.resolve_left (not_not_intro hmiss)
    have hom : homogeneous Q := hR.resolve_left (not_not_intro hr.1) |>.resolve_left (not_lt_of_ge hr.2)
    exact (homogeneous_charge_at_cutoff hk hkn hn hμ B p hp M hM Q hr.1 hr.2 hom T).trans
      (slopeCharge_le n B (by omega) M (by linarith) hsmall _ ((ordinary_iff_bestZeros Q).mp hr.1) hr.2 hk)
  have habs : ∀ Q ∈ (target : Set (Population n μ)), ∀ Z ∈ (K Q).support, Z ∈ target :=
    fun Q hQ Z hZ ↦ step_preserves_optimum hk p false hQ hZ
  have hset : (target : Set (Population n μ))ᶜ = {Q | missing Q} := by ext Q; simp [target]
  rw [show (1 : ℝ) / (8 * slopeCharge n M k) = (1 / 4) / (2 * a) by dsimp [a]; ring]
  simpa only [hset] using tail_from_affine K target P habs a (1 / 4) (1 / 4) ha (by norm_num) (by norm_num) htail

end
end Lax637351Proofs.SlopeCharge
