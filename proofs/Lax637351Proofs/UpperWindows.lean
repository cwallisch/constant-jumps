import Lax637351Proofs.PlateauSuccess

namespace Lax637351Proofs.UpperWindows

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteChain Lax637351Proofs.FiniteDrift
open Lax637351Proofs.OffspringEstimates
open Lax637351Proofs.PlateauPairs Lax637351Proofs.SubsetPairs Lax637351Proofs.Endgame
open Lax637351Proofs.ColumnParameters Lax637351Proofs.ColumnBands Lax637351Proofs.ColumnBarriers
open Lax637351Proofs.ColumnDriftBound Lax637351Proofs.ColumnNormBounds
open Lax637351Proofs.SpeciesCap Lax637351Proofs.SpeciesWindow Lax637351Proofs.SpeciesProtection
open Lax637351Proofs.PlateauChanges Lax637351Proofs.PlateauSuccess Lax637351Proofs.RareSuccess
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {μ : ℕ+}

def countTime (c : ℝ) (μ : ℕ+) (n : ℕ) : ℕ := ⌈c * ((μ : ℕ) : ℝ) * n⌉₊

lemma countTime_lower (c : ℝ) (μ : ℕ+) (n : ℕ) :
    c * ((μ : ℕ) : ℝ) * n ≤ countTime c μ n :=
  Nat.le_ceil _

lemma countTime_upper (c : ℝ) (hc : 0 ≤ c) (μ : ℕ+) {n : ℕ} (hn : 1 ≤ n) :
    (countTime c μ n : ℝ) ≤ (c + 1) * ((μ : ℕ) : ℝ) * n := by
  have h := (Nat.ceil_lt_add_one (show 0 ≤ c * ((μ : ℕ) : ℝ) * n by positivity)).le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast μ.pos
  have hu := mul_le_mul hm hn' (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ ((μ : ℕ) : ℝ))
  unfold countTime
  nlinarith only [h, hu]

def recoveryTolerance (k : ℕ) : ℝ := 1 / (16 * (k : ℝ))
def speciesTimeConstant (k : ℕ) : ℝ := 1536 / (k : ℝ)
def columnTimeConstant (a : Settings k) : ℝ :=
  Real.exp (2 * (a.T : ℕ)) / (entryRate k (a.T : ℕ) * recoveryTolerance k)
def plateauTimeConstant (a : Settings k) : ℝ :=
  speciesTimeConstant k + 1 + (columnTimeConstant a + 1) + (2 * (k : ℝ) + 2 / crossRate k)
def blockTime (a : Settings k) (μ : ℕ+) (n : ℕ) (p : ℝ) : ℕ :=
  countTime (speciesTimeConstant k) μ n +
    (countTime (columnTimeConstant a) μ n + gameLength k μ p 3)
def plateauChance (a : Settings k) : ℝ := min (1 / 2) (gameChance k a.frequencyLevel 3 / 2)
def failureTolerance (a : Settings k) : ℝ :=
  min (1 / (32 * (k : ℝ))) (min (plateauChance a / (2 * k)) (plateauChance a / 4))
def decay (a : Settings k) : ℝ := min (slopeConstant a * a.columnLevel / 2) (strictAmount k * level k / 128)
def populationFloor (a : Settings k) : ℝ := max (2 * jumpBound a / a.columnLevel) (16 / level k)

lemma plateau_constants (a : Settings k) (hk : 2 ≤ k) :
    0 < columnTimeConstant a ∧ 0 < plateauTimeConstant a ∧ 0 < plateauChance a ∧
      0 < failureTolerance a ∧ 0 < decay a := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hq := gameChance_pos (show 0 < k by omega) (settings_levels a).2.1 (by norm_num : (0 : ℝ) < 3)
  have h₁ := entryRate_pos k ((a.T : ℕ) : ℝ)
  have h₂ := crossRate_pos k
  have h₃ := slope_pos a
  have h₄ := (settings_levels a).1
  have h₅ := strictAmount_pos k
  have h₆ := level_pos k
  unfold plateauTimeConstant columnTimeConstant recoveryTolerance speciesTimeConstant failureTolerance plateauChance decay
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity

lemma windows_bound (a : Settings k) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (hnp : 1 ≤ (n : ℝ) * p)
    (hMμ : (6 : ℝ) ≤ ((μ : ℕ) : ℝ) + 1) :
    (blockTime a μ n p : ℝ) ≤ plateauTimeConstant a * ((μ : ℕ) : ℝ) * n := by
  have h := plateau_constants a hk
  have hs := countTime_upper (speciesTimeConstant k) (by unfold speciesTimeConstant; positivity) μ hn
  have hc := countTime_upper (columnTimeConstant a) h.1.le μ hn
  have hg := gameLength_bound k μ p 3 hp (by norm_num) (by norm_num at hMμ ⊢; exact hMμ)
  have hgp : (gameLength k μ p 3 : ℝ) ≤ (2 * (k : ℝ) + 2 / crossRate k) * ((μ : ℕ) : ℝ) * n := by
    refine hg.trans ((div_le_iff₀ hp.1).mpr ?_)
    have hc := crossRate_pos k
    have hh := mul_le_mul_of_nonneg_left hnp
      (show 0 ≤ (2 * (k : ℝ) + 2 / crossRate k) * ((μ : ℕ) : ℝ) by positivity)
    linarith only [hh]
  unfold blockTime plateauTimeConstant
  push_cast
  linarith only [hs, hc, hgp]

lemma exponential_bound (a : Settings k) (hk : 2 ≤ k) (p : ℝ)
    (hp : 0 < p ∧ p ≤ 1) (ar : Bool) (hμ : populationFloor a ≤ ((μ : ℕ) : ℝ))
    (t : ℕ) (ht : (t : ℝ) ≤ plateauTimeConstant a * ((μ : ℕ) : ℝ) * n) :
    let r := changeBound n k p ar
    let b := (plateauTimeConstant a * ((μ : ℕ) : ℝ) * n * r + 1) *
      Real.exp (-decay a * (μ : ℕ) * p / r)
    barrierFactor a n μ p ar t ≤ b ∧ speciesFactor n k μ p ar t ≤ b := by
  let r := changeBound n k p ar
  let m : ℝ := (μ : ℕ)
  let A := plateauTimeConstant a
  have hr : 0 < r := hp.1.trans_le (changeBound_ge_p p ⟨hp.1.le, hp.2⟩ ar)
  have hμ' : 0 ≤ m := by unfold m; positivity
  have hpp : 0 ≤ m * p / r := div_nonneg (mul_nonneg hμ' hp.1.le) hr.le
  have hts := add_le_add_left (mul_le_mul_of_nonneg_right ht hr.le) 1
  have hts' : 0 ≤ A * m * n * r + 1 := by
    have hA : 0 < A := (plateau_constants a hk).2.1
    positivity
  have h₁ := (div_le_iff₀ (settings_levels a).1).mp ((le_max_left _ _).trans hμ)
  have h₂ := (div_le_iff₀ (level_pos k)).mp ((le_max_right _ _).trans hμ)
  have hb : a.columnLevel * m / 2 ≤ height a μ - jumpBound a := by
    unfold height
    change 2 * jumpBound a ≤ m * a.columnLevel at h₁
    linarith only [h₁]
  have hs : level k * m / 2 ≤ level k * (μ : ℕ) - 8 := by
    change 16 ≤ m * level k at h₂
    change level k * m / 2 ≤ level k * m - 8
    linarith only [h₂]
  have he₁ : Real.exp (-columnSlope a n p ar * (height a μ - jumpBound a)) ≤
      Real.exp (-decay a * m * p / r) := by
    apply Real.exp_le_exp.mpr
    have hd : decay a ≤ slopeConstant a * a.columnLevel / 2 := min_le_left _ _
    have hd' := mul_le_mul_of_nonneg_right hd hpp
    have hc := (slope_range a n p hp ar).1
    have he := mul_le_mul_of_nonneg_left hb hc
    unfold columnSlope at he
    change slopeConstant a * p / r * (a.columnLevel * m / 2) ≤ _ at he
    rw [show -columnSlope a n p ar * (height a μ - jumpBound a) =
        -(columnSlope a n p ar * (height a μ - jumpBound a)) by ring,
      show -decay a * m * p / r = -(decay a * m * p / r) by ring]
    apply neg_le_neg
    exact (show decay a * m * p / r = decay a * (m * p / r) by ring).le.trans
      (hd'.trans ((by ring : _ = slopeConstant a * p / r * (a.columnLevel * m / 2)).le.trans he))
  have he₂ : Real.exp (-speciesSlope n k p ar * (level k * (μ : ℕ) - 8)) ≤
      Real.exp (-decay a * m * p / r) := by
    apply Real.exp_le_exp.mpr
    have hd : decay a ≤ strictAmount k * level k / 128 := min_le_right _ _
    have hd' := mul_le_mul_of_nonneg_right hd hpp
    have hc : 0 ≤ speciesSlope n k p ar := by
      unfold speciesSlope
      change 0 ≤ p * strictAmount k / (64 * r)
      exact div_nonneg (mul_nonneg hp.1.le (strictAmount_pos k).le) (by positivity)
    have he := mul_le_mul_of_nonneg_left hs hc
    change p * strictAmount k / (64 * r) * (level k * m / 2) ≤ _ at he
    rw [show -speciesSlope n k p ar * (level k * (μ : ℕ) - 8) =
        -(speciesSlope n k p ar * (level k * (μ : ℕ) - 8)) by ring,
      show -decay a * m * p / r = -(decay a * m * p / r) by ring]
    apply neg_le_neg
    exact (show decay a * m * p / r = decay a * (m * p / r) by ring).le.trans
      (hd'.trans ((by ring : _ = p * strictAmount k / (64 * r) * (level k * m / 2)).le.trans he))
  exact ⟨mul_le_mul hts he₁ (Real.exp_pos _).le hts', mul_le_mul hts he₂ (Real.exp_pos _).le hts'⟩

lemma plateau_block (hk : 2 ≤ k) (a : Settings k) (hn : Dimension k n a)
    (hm : PopulationSize k a μ) (hc : EntryBounds.Conditions n k (1 / 2))
    (herror : (129 / 100 : ℝ) * PlateauKernelApproximation.approximationError n k ≤ strictAmount k)
    (hμ : (5 : ℕ) ≤ μ) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) (ar : Bool)
    (hnp : 1 ≤ (n : ℝ) * p)
    (hcopy : 3 * (4 * remainderLimit (a.T : ℕ) / ((μ : ℕ) : ℝ)) * copyRate n p ar ≤ p / (8 * (a.T : ℕ)))
    (hLoss : p + (k : ℝ) / n + copyRate n p ar / (μ : ℕ) ≤ 3 * p)
    (hfloor : populationFloor a ≤ ((μ : ℕ) : ℝ))
    (htail : let r := changeBound n k p ar
      (plateauTimeConstant a * ((μ : ℕ) : ℝ) * n * r + 1) *
        Real.exp (-decay a * (μ : ℕ) * p / r) ≤ failureTolerance a)
    (P : Population n μ) (hP : plateau (k := k) P) :
    plateauChance a / 8 ≤
      1 - ((law (step (jump k) p ar) (PMF.pure P) (blockTime a μ n p)).toOuterMeasure {Q | missing Q}).toReal := by
  let q := plateauChance a
  let ζ := recoveryTolerance k
  let v := countTime (speciesTimeConstant k) μ n
  let s := countTime (columnTimeConstant a) μ n
  let t := gameLength k μ p 3
  have hconst := plateau_constants a hk
  have hcoltime : 0 < columnTimeConstant a := hconst.1
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hn.two; omega)
  have hm' : (0 : ℝ) < (μ : ℕ) := by exact_mod_cast μ.pos
  have hq : 0 < q := hconst.2.2.1
  have hq' : q ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hζ : 0 < ζ := by unfold ζ recoveryTolerance; positivity
  have hE := entryRate_pos k ((a.T : ℕ) : ℝ)
  have hMμ : (6 : ℝ) ≤ ((μ : ℕ) : ℝ) + 1 := by
    have h : (5 : ℝ) ≤ (μ : ℕ) := by exact_mod_cast hμ
    linarith only [h]
  have htime := windows_bound a hk (by have := hn.two; omega) p hp hnp hMμ
  have ht (u : ℕ) (hu : u ≤ blockTime a μ n p) :
      barrierFactor a n μ p ar u ≤ failureTolerance a ∧ speciesFactor n k μ p ar u ≤ failureTolerance a := by
    have hu' : (u : ℝ) ≤ (blockTime a μ n p : ℝ) := by exact_mod_cast hu
    have h := exponential_bound a hk p hp ar hfloor u (hu'.trans htime)
    exact ⟨h.1.trans htail, h.2.trans htail⟩
  have hs₀ := countTime_lower (columnTimeConstant a) μ n
  have hs : 0 < s := by
    have h : (0 : ℝ) < (s : ℝ) := (show 0 < columnTimeConstant a * ((μ : ℕ) : ℝ) * n by positivity).trans_le hs₀
    exact_mod_cast h
  apply plateau_success hk a hn hm hc herror hμ p hp ar hcopy 3 (by norm_num) (by norm_num at hMμ ⊢; exact hMμ) hLoss
    q hq.le hq' v s hs ζ hζ.le _ _ _ _ _ P hP
  · have h := mul_le_mul_of_nonneg_left (countTime_lower (speciesTimeConstant k) μ n)
      (show 0 ≤ (k : ℝ) / (256 * n) by positivity)
    change _ ≤ (k : ℝ) / (256 * n) * v at h
    convert h using 1
    unfold speciesTimeConstant
    field_simp
    ring
  · have h := mul_le_mul_of_nonneg_left hs₀
      (show 0 ≤ (entryRate k (a.T : ℕ) / n) * ζ by positivity)
    change _ ≤ _ * (s : ℝ) at h
    have hcancel : (entryRate k (a.T : ℕ) / n * ζ) * (columnTimeConstant a * ((μ : ℕ) : ℝ) * n) =
        Real.exp (2 * (a.T : ℕ)) * (μ : ℕ) := by
      unfold columnTimeConstant
      change entryRate k (a.T : ℕ) / n * ζ *
        (Real.exp (2 * (a.T : ℕ)) / (entryRate k (a.T : ℕ) * ζ) * (μ : ℕ) * n) = _
      field_simp
    rw [hcancel] at h
    exact h.trans_eq (by ring)
  · have hS := (ht s (by unfold blockTime; change s ≤ v + (s + t); omega)).1
    have hS' := hS.trans (min_le_left _ _)
    have hh := mul_le_mul_of_nonneg_left hS' (show 0 ≤ 4 * (k : ℝ) by positivity)
    have hζ' : 2 * (k : ℝ) * ζ = 1 / 8 := by unfold ζ recoveryTolerance; field_simp [hk'.ne']; norm_num
    have hh' : 4 * (k : ℝ) * (1 / (32 * (k : ℝ))) = 1 / 8 := by field_simp [hk'.ne']; norm_num
    rw [hh'] at hh
    linarith only [hh, hζ']
  · have ht' := (ht t (by unfold blockTime; change t ≤ v + (s + t); omega)).1
    have hh := mul_le_mul_of_nonneg_left (ht'.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (show 0 ≤ 2 * (k : ℝ) by positivity)
    have he : 2 * (k : ℝ) * (q / (2 * (k : ℝ))) = q := by field_simp [hk'.ne']
    rw [he] at hh
    have hq₂ : q ≤ gameChance k a.frequencyLevel 3 / 2 := min_le_right _ _
    linarith only [hh, hq₂]
  · exact (ht (s + t) (by unfold blockTime; change s + t ≤ v + (s + t); omega)).2.trans
      ((min_le_right _ _).trans (min_le_right _ _))

end
end Lax637351Proofs.UpperWindows
