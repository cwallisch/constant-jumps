import Lax637351Proofs.TapeRun

namespace Lax637351Proofs.TapeConcentration

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.TapeDraw Lax637351Proofs.TapeRun Lax637351Proofs.Independent
open Lax637351Proofs.Mutation Lax637351Proofs.SparseDeviation
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.PairStep
open Lax637351Proofs.FiniteChain
open scoped Classical ENNReal

noncomputable section

variable {n L : ℕ} {μ : ℕ+}

def zeroBit (b : Fin 2) : ℝ := indicator (b = 0)

lemma flip_zeroBit (b : Fin 2) : zeroBit (1 - b) = 1 - zeroBit b := by
  fin_cases b <;> norm_num [zeroBit, indicator]

lemma mean_bitProposal (hn : 2 ≤ n) (a : Index μ) (v : Fin μ → Fin 2) :
    mean (coordinateLaw n) (fun m ↦ zeroBit (bitProposal a m v)) =
      1 / (n : ℝ) + (1 - 2 / (n : ℝ)) *
        (if a.1 then (zeroBit (v a.2.1) + zeroBit (v a.2.2)) / 2 else zeroBit (v a.2.1)) := by
  have hflip (b : Fin 2) :
      mean (bitCoin (1 / (n : ℝ))) (fun f ↦ zeroBit (if f = 1 then 1 - b else b)) =
        1 / (n : ℝ) + (1 - 2 / (n : ℝ)) * zeroBit b := by
    rw [bitCoin, mean_map, mean_coin (rate_valid hn)]
    norm_num only [if_true, if_false, Bool.false_eq_true, one_ne_zero, zero_ne_one, flip_zeroBit]
    ring
  simp only [coordinateLaw, mean_bind, mean_map]
  change mean (bitCoin (1 / 2)) (fun c ↦ mean (bitCoin (1 / (n : ℝ))) (fun m ↦
    let b := if a.1 then (if c = 1 then v a.2.1 else v a.2.2) else v a.2.1
    zeroBit (if m = 1 then 1 - b else b))) = _
  simp_rw [hflip]
  by_cases h : a.1 = true
  · simp only [h, if_true, bitCoin, mean_map, mean_coin (p := (1 / 2 : ℝ)) (by norm_num),
      Bool.false_eq_true, if_false, zero_ne_one]
    ring
  · simp only [h, Bool.false_eq_true, if_false, mean_const]

def columnMeans (q : Fin n → PMF (Fin μ → Fin 2)) (i : Fin μ) : ℝ :=
  ∑ j, mean (q j) (fun v ↦ zeroBit (v i))

def stepColumns (q : Fin n → PMF (Fin μ → Fin 2)) (a : Index μ)
    (d : Fin ((μ : ℕ) + 1)) : Fin n → PMF (Fin μ → Fin 2) :=
  fun j ↦ (q j).bind (fun v ↦ (coordinateLaw n).map (fun m ↦ bitUpdate a m d v))

lemma columnMeans_bd (q : Fin n → PMF (Fin μ → Fin 2)) (i : Fin μ) :
    0 ≤ columnMeans q i ∧ columnMeans q i ≤ n := by
  constructor
  · exact Finset.sum_nonneg (fun j _ ↦ mean_nonneg _ (fun _ ↦ indic_nonneg _))
  · unfold columnMeans
    calc
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦
        (mean_mono (q j) fun v ↦ indic_le_one (v i = 0)).trans_eq (mean_const _ 1)
      _ = _ := by simp

lemma columnMeans_step_bounds (hn : 2 ≤ n) (q : Fin n → PMF (Fin μ → Fin 2))
    (a : Index μ) (d : Fin ((μ : ℕ) + 1)) (lo hi : ℝ)
    (hq : ∀ i, lo ≤ columnMeans q i ∧ columnMeans q i ≤ hi) (i : Fin μ) :
    lo - 1 ≤ columnMeans (stepColumns q a d) i ∧ columnMeans (stepColumns q a d) i ≤ hi + 1 := by
  have hkeep (d : Fin ((μ : ℕ) + 1)) (h : columnMeans (stepColumns q a d) i = columnMeans q i) :
      lo - 1 ≤ columnMeans (stepColumns q a d) i ∧ columnMeans (stepColumns q a d) i ≤ hi + 1 := by
    rw [h]
    constructor <;> linarith only [(hq i).1, (hq i).2]
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  revert d
  refine Fin.lastCases ?_ (fun u ↦ ?_)
  · apply hkeep
    simp [columnMeans, stepColumns, bitUpdate, mean_bind, mean_map, mean_const]
  · by_cases he : i = u
    · have havg (g : Fin μ → ℝ) :
        (if a.1 then (g a.2.1 + g a.2.2) / 2 else g a.2.1) =
          (if a.1 then (1 / 2 : ℝ) else 1) * g a.2.1 + (if a.1 then (1 / 2 : ℝ) else 0) * g a.2.2 := by
        by_cases h : a.1 = true <;> simp [h]; ring
      let s := if a.1 then (columnMeans q a.2.1 + columnMeans q a.2.2) / 2 else columnMeans q a.2.1
      have hs : lo ≤ s ∧ s ≤ hi ∧ 0 ≤ s ∧ s ≤ n := by
        have h₁ := hq a.2.1
        have h₂ := hq a.2.2
        have h₃ := columnMeans_bd q a.2.1
        have h₄ := columnMeans_bd q a.2.2
        dsimp [s]
        by_cases h : a.1 = true <;> simp only [h, Bool.false_eq_true, if_false, if_true] <;>
          refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2, h₄.1, h₄.2]
      have heq : columnMeans (stepColumns q a u.castSucc) i = 1 + (1 - 2 / (n : ℝ)) * s := by
        simp only [stepColumns, mean_bind, mean_map, he, bitUpdate, Fin.lastCases_castSucc,
          Function.update_self, columnMeans]
        simp_rw [mean_bitProposal hn, mean_add, mean_const, mean_mul]
        have ha (v : Fin μ → Fin 2) := havg (fun i ↦ zeroBit (v i))
        simp_rw [ha, mean_add, mean_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp only [s]
        rw [havg (columnMeans q)]
        unfold columnMeans
        field_simp
      have hnr : 0 ≤ 2 / (n : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hs.2.2.2 hnr
      have hnon := mul_nonneg hnr hs.2.2.1
      have h2 : (2 / (n : ℝ)) * n = 2 := by field_simp
      rw [h2] at hmul
      rw [heq]
      constructor <;> nlinarith only [hs.1, hs.2.1, hmul, hnon]
    · apply hkeep
      simp [columnMeans, stepColumns, bitUpdate, he, Function.update_of_ne, mean_bind, mean_map, mean_const]

def runColumns : (L : ℕ) → (Fin L → Index μ) → Schedule L μ →
    (Fin n → PMF (Fin μ → Fin 2)) → Fin n → PMF (Fin μ → Fin 2)
  | 0, _, _, q => q
  | L + 1, a, d, q => runColumns L (Fin.tail a) (Fin.tail d) (stepColumns q (a 0) (d 0))

lemma runColumns_eq (L : ℕ) (a : Fin L → Index μ) (d : Schedule L μ)
    (q : Fin n → PMF (Fin μ → Fin 2)) (j : Fin n) :
    runColumns L a d q j =
      (q j).bind (fun v ↦ (product (fun _ : Fin L ↦ coordinateLaw n)).map
        (fun t ↦ runColumn L a t d v)) := by
  induction L generalizing q with
  | zero =>
    simp only [runColumns, runColumn]
    have h (v : Fin μ → Fin 2) : (product (fun _ : Fin 0 ↦ coordinateLaw n)).map (fun _ ↦ v) = PMF.pure v :=
      PMF.map_const _ v
    simp_rw [h, PMF.bind_pure]
  | succ L ih =>
    rw [runColumns, ih, product_succ]
    simp only [stepColumns, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      runColumn, Function.comp_def, Fin.cons_zero, Fin.tail_cons]

lemma runColumns_bounds (hn : 2 ≤ n) (L : ℕ) (a : Fin L → Index μ) (d : Schedule L μ)
    (q : Fin n → PMF (Fin μ → Fin 2)) (lo hi : ℝ)
    (hq : ∀ i, lo ≤ columnMeans q i ∧ columnMeans q i ≤ hi) (i : Fin μ) :
    lo - L ≤ columnMeans (runColumns L a d q) i ∧ columnMeans (runColumns L a d q) i ≤ hi + L := by
  induction L generalizing q lo hi with
  | zero => simpa only [Nat.cast_zero, add_zero, sub_zero, runColumns] using hq i
  | succ L ih =>
    rw [runColumns]
    have hh := ih (Fin.tail a) (Fin.tail d) (stepColumns q (a 0) (d 0)) (lo - 1) (hi + 1)
      (columnMeans_step_bounds hn q (a 0) (d 0) lo hi hq)
    push_cast
    constructor <;> linarith only [hh.1, hh.2]

lemma zero_count_as_score (z : BitString n) : ((zeros z).card : ℝ) = ∑ j, zeroBit (z j) := by
  simp only [zeros, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : z j = 0 <;> simp [zeroBit, indicator, h]

def tapeDelta (L : ℕ) (μ : ℕ+) (hi w lam : ℝ) : ℝ :=
  ((μ : ℕ) + 1 : ℝ) ^ L * (μ : ℕ) * Real.exp ((hi + L) * lam ^ 2 - lam * w)

lemma fixed_schedule_deviation (hn : 2 ≤ n) (L : ℕ) (P : Population n μ)
    (lo hi : ℝ) (hP : ∀ i, lo ≤ ((zeros (P i)).card : ℝ) ∧ ((zeros (P i)).card : ℝ) ≤ hi)
    (a : Fin L → Index μ) (d : Schedule L μ) (i : Fin μ) (w lam : ℝ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) :
    mean (product (fun _ : Fin n ↦ product (fun _ : Fin L ↦ coordinateLaw n)))
      (fun v ↦ indicator (((zeros (scheduled L (assemble a v) d P i)).card : ℝ) < lo - L - w)) ≤
        Real.exp ((hi + L) * lam ^ 2 - lam * w) := by
  let T := product (fun _ : Fin L ↦ coordinateLaw n)
  let M := product (fun _ : Fin n ↦ T)
  let f (j : Fin n) (s : Fin L → Fin 2 × Fin 2) := runColumn L a s d (fun u ↦ P u j) i
  let G (j : Fin n) (s : Fin L → Fin 2 × Fin 2) := f j s = 0
  let q (j : Fin n) := PMF.pure (fun u ↦ P u j)
  have hq (u : Fin μ) : columnMeans q u = ((zeros (P u)).card : ℝ) := by
    simp only [columnMeans, q, mean_pure, zero_count_as_score]
  have hq' (u : Fin μ) : lo ≤ columnMeans q u ∧ columnMeans q u ≤ hi := by simpa only [hq] using hP u
  have hmean : countMean (fun _ : Fin n ↦ T) G = columnMeans (runColumns L a d q) i := by
    unfold countMean columnMeans
    apply Finset.sum_congr rfl
    intro j _
    rw [runColumns_eq, show q j = PMF.pure (fun u ↦ P u j) from rfl, PMF.pure_bind, mean_map]
    rfl
  have hb := runColumns_bounds hn L a d q lo hi hq' i
  have hs (v : Fin n → Fin L → Fin 2 × Fin 2) :
      ((zeros (scheduled L (assemble a v) d P i)).card : ℝ) = countScore G v := by
    rw [zero_count_as_score, countScore]
    apply Finset.sum_congr rfl
    intro j _
    rw [congrFun (column_separates L a v d P j) i]
    rfl
  have hpt (v : Fin n → Fin L → Fin 2 × Fin 2) :
      indicator (((zeros (scheduled L (assemble a v) d P i)).card : ℝ) < lo - L - w) ≤
        indicator (countScore G v ≤ countMean (fun _ : Fin n ↦ T) G - w) := by
    by_cases he : ((zeros (scheduled L (assemble a v) d P i)).card : ℝ) < lo - L - w
    · have hh : countScore G v ≤ countMean (fun _ : Fin n ↦ T) G - w := by
        rw [hmean, ← hs]
        linarith only [he, hb.1]
      simp [indicator, he, hh]
    · simpa only [indicator, if_neg he] using indic_nonneg (countScore G v ≤ countMean (fun _ : Fin n ↦ T) G - w)
  apply (mean_mono M hpt).trans
  rw [show (fun v ↦ indicator (countScore G v ≤ countMean (fun _ : Fin n ↦ T) G - w)) =
      (fun v ↦ if v ∈ {v | countScore G v ≤ countMean (fun _ : Fin n ↦ T) G - w} then 1 else 0) by
        funext v
        by_cases he : countScore G v ≤ countMean (fun _ : Fin n ↦ T) G - w <;>
          simp only [indicator, Set.mem_ofPred_eq, he, if_true, if_false], mean_indicator]
  have hd := lower_deviation (fun _ : Fin n ↦ T) G hlam hlam' w
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh
  apply hh.trans (Real.exp_le_exp.mpr _)
  rw [hmean]
  have ht := mul_le_mul_of_nonneg_right hb.2 (sq_nonneg lam)
  linarith only [ht]

lemma stopped_count_concentration (hn : 2 ≤ n) (k : ℕ) (p : ℝ) (A : Set (Population n μ))
    (L : ℕ) (P : Population n μ) (lo hi : ℝ)
    (hP : ∀ i, lo ≤ ((zeros (P i)).card : ℝ) ∧ ((zeros (P i)).card : ℝ) ≤ hi)
    (w lam : ℝ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1) :
    mean (law (stopped (step (jump k) p false) A) (PMF.pure P) L)
      (fun Q ↦ indicator (∃ i, ((zeros (Q i)).card : ℝ) < lo - L - w)) ≤ tapeDelta L μ hi w lam := by
  let I := product (fun _ : Fin L ↦ indexLaw μ p)
  let M := product (fun _ : Fin n ↦ product (fun _ : Fin L ↦ coordinateLaw n))
  let f (Q : Population n μ) := indicator (∃ i, ((zeros (Q i)).card : ℝ) < lo - L - w)
  let U (a : Fin L → Index μ) (v : Fin n → Fin L → Fin 2 × Fin 2) :=
    ∑ j : Schedule L μ × Fin μ,
      indicator (((zeros (scheduled L (assemble a v) j.1 P j.2)).card : ℝ) < lo - L - w)
  have heq : law (stopped (step (jump k) p false) A) (PMF.pure P) L =
      I.bind (fun a ↦ M.bind (fun v ↦ realize (oneUpdate k A) L (assemble a v) P)) := by
    rw [← show (fun Q ↦ (innovationLaw n μ p).bind (oneUpdate k A Q)) =
      stopped (step (jump k) p false) A from funext (mixture_step k p A)]
    rw [← mixture, factor_tapes, PMF.bind_bind]
    dsimp [I, M]
    simp only [PMF.bind_map, Function.comp_def]
  have hpt (a : Fin L → Index μ) (v : Fin n → Fin L → Fin 2 × Fin 2) :
      mean (realize (oneUpdate k A) L (assemble a v) P) f ≤ U a v := by
    rw [← mean_const (realize (oneUpdate k A) L (assemble a v) P) (U a v)]
    apply mean_mono_on_support
    intro Q hQ
    dsimp only [f]
    by_cases hbad : ∃ i, ((zeros (Q i)).card : ℝ) < lo - L - w
    · obtain ⟨d, rfl⟩ := realized_schedule k A L (assemble a v) P Q hQ
      obtain ⟨i, hi⟩ := hbad
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Schedule L μ × Fin μ)))
        (f := fun j ↦ indicator (((zeros (scheduled L (assemble a v) j.1 P j.2)).card : ℝ) < lo - L - w))
        (fun j _ ↦ indic_nonneg _) (Finset.mem_univ (d, i))
      have hval : indicator (((zeros (scheduled L (assemble a v) d P i)).card : ℝ) < lo - L - w) = 1 := if_pos hi
      change indicator (((zeros (scheduled L (assemble a v) d P i)).card : ℝ) < lo - L - w) ≤ U a v at hh
      rw [hval] at hh
      rw [indicator, if_pos ⟨i, hi⟩]
      exact hh
    · simp only [indicator, if_neg hbad]
      exact Finset.sum_nonneg (fun j _ ↦ indic_nonneg _)
  change mean _ f ≤ _
  rw [heq, mean_bind]
  refine le_trans (mean_mono I (g := fun a ↦ mean M (U a)) (fun a ↦ ?_)) ?_
  · rw [mean_bind]
    exact mean_mono M (hpt a)
  · rw [← mean_const I (tapeDelta L μ hi w lam)]
    apply mean_mono
    intro a
    dsimp only [U]
    rw [mean_sum]
    calc
      _ ≤ ∑ _j : Schedule L μ × Fin μ, Real.exp ((hi + L) * lam ^ 2 - lam * w) :=
        Finset.sum_le_sum fun j _ ↦ fixed_schedule_deviation hn L P lo hi hP a j.1 j.2 w lam hlam hlam'
      _ = _ := by
        simp [tapeDelta, Schedule, nsmul_eq_mul, Nat.cast_pow, mul_assoc]

end
end Lax637351Proofs.TapeConcentration
