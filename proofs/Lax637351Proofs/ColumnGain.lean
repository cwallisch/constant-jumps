import Lax637351Proofs.ColumnEvolution

namespace Lax637351Proofs.ColumnGain

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.OffspringEstimates OffspringEstimates.Genotypes OffspringEstimates.ColumnKernels
open Lax637351Proofs.PredictionMeasure Lax637351Proofs.PredictionNorm Lax637351Proofs.PredictionBounds
open Lax637351Proofs.ColumnKernel Lax637351Proofs.ColumnLinear Lax637351Proofs.ColumnClasses
open Lax637351Proofs.ColumnEvolution Lax637351Proofs.LinearInvasion
open OffspringEstimates.ReproductiveValues
open scoped Classical ENNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ}

def fraction (i : Fin n) (w : Weights (Genotype n k)) : ℝ := mass (project (mutants i) w)

lemma exists_shadow {r : ℕ} (i : Fin n) (x : ColumnClass n (r + 1) i 1) :
    ∃ y : ColumnClass n (r + 1) i 0, PhysicalShadow.Related x y := by
  let Z := OffspringEstimates.Sampling.zeros x.val
  have hZ : Z.card = r + 1 := x.property.1
  have hi : i ∉ Z := by
    intro hi'
    have hz := (OffspringEstimates.Sampling.mem_zeros x.val i).mp hi'
    exact Fin.zero_ne_one (hz.symm.trans x.property.2)
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < Z.card by omega)
  let Y := insert i (Z.erase e)
  have he' : i ≠ e := fun h ↦ hi (h ▸ he)
  have hi' : i ∉ Z.erase e := fun hx ↦ hi (Finset.mem_of_mem_erase hx)
  have hY : Y.card = r + 1 := by
    dsimp [Y]
    rw [Finset.card_insert_of_notMem hi', Finset.card_erase_of_mem he, hZ]
    omega
  let C : Genotype n (r + 1) := ⟨Y, hY⟩
  have hc : Genotypes.toString C i = 0 := by simp [Genotypes.toString, C, Y]
  let y : ColumnClass n (r + 1) i 0 := ⟨Genotypes.toString C, by rw [zeros_toString]; exact hY, hc⟩
  refine ⟨y, ?_⟩
  unfold PhysicalShadow.Related
  change (OffspringEstimates.Sampling.zeros (Genotypes.toString C)).erase i ⊆ Z.erase i
  rw [zeros_toString]
  intro j hj
  have hj' : j ≠ i ∧ j ∈ Y := Finset.mem_erase.mp hj
  rcases Finset.mem_insert.mp hj'.2 with heq | heq
  · exact (hj'.1 heq).elim
  · exact Finset.mem_erase.mpr ⟨hj'.1, Finset.mem_of_mem_erase heq⟩

lemma linear_gain {r : ℕ} (hr : 1 ≤ r) (hn : 4 * (r + 1) ≤ n) (i : Fin n) (e ω : ℝ) (he : 0 ≤ e ∧ e < 1)
    (hω : 0 ≤ ω) (H : ℕ)
    (hpert : (e / (1 - e) - e) * H * (1 + e / (1 - e)) ^ H ≤ 1)
    (horizon : H * e * ReproductiveAdmissibility.error n (r + 1) ≤ 1)
    (hsmall : e * (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) ≤ 1)
    (hdim : (128 * (r + 1 : ℝ) ^ 2 / n) * (3 : ℝ) ^ (r + 1) * (1 + (3 : ℝ) ^ (r + 1)) ≤
      ShadowGaps.delta (r + 1) * ω / 2)
    (a b : Weights (Genotype n (r + 1))) (ha : probability a) (hb : probability b)
    (hA : ∀ x ∈ mutants i, a x = 0) (hB : ∀ x ∉ mutants i, b x = 0)
    (hcap : ∀ t x, predict (replaceKernel i) e t a x ≤ 1 - ω) :
    (1 + e * (ShadowGaps.delta (r + 1) * ω) / (2 * (1 + e) * (3 : ℝ) ^ (r + 1))) ^ H /
          (2 * (3 : ℝ) ^ (r + 1)) ≤
      fraction i (response (replaceKernel i) e H a (b - a)) := by
  let π t := predict (replaceKernel i) e t a
  let hp (t : ℕ) : probability (π t) := predict_probability _ e ⟨he.1, he.2.le⟩ a ha t
  let hR (t : ℕ) := resident_preserved i e ⟨he.1, he.2.le⟩ a ha hA t
  let ν t := partners (π t) (hp t)
  let c t := 1 - e * mass (births i (π t) (π t))
  let M t := mixedKernel (b := 1) (i := i) (k := r + 1) (ν t)
  let R t := mixedKernel (b := 0) (i := i) (k := r + 1) (ν t)
  let m t := view i 1 (response (replaceKernel i) e t a (b - a))
  let p t := view i 0 (π t)
  let D : ℝ := 3 ^ (r + 1)
  let g := (1 + e * (ShadowGaps.delta (r + 1) * ω) / (2 * (1 + e) * D)) ^ H
  have hn' : 2 ≤ n := by omega
  have hV (t : ℕ) : 1 - e ≤ c t ∧ c t ≤ 1 := by
    have h := total_birth_mass i (π t) (hp t)
    dsimp only [c]
    constructor
    · have ht := mul_le_mul_of_nonneg_left h.2 he.1
      linarith only [ht]
    · linarith only [mul_nonneg he.1 h.1]
  have hν (t : ℕ) (u : BitString n) (hu : u ∈ (ν t).support) : (OffspringEstimates.Sampling.zeros u).card = r + 1 :=
    partners_plateau (π t) (hp t) u hu
  have hb' (t : ℕ) (x : ColumnClass n (r + 1) i 0) : (ν t x.val).toReal ≤ 1 - ω := by
    dsimp only [ν]
    rw [← string_fromClass x, partners_point]
    exact hcap t (fromClass x)
  have hm : evolves M e c m := by
    intro t
    have hmass : mass (b - a) = 0 := by rw [mass_sub, ha.2, hb.2, sub_self]
    exact view_mutant_step hn' i e (π t) (response (replaceKernel i) e t a (b - a)) (hp t)
      (response_mass_zero (replaceKernel i) e a _ hmass t) (hR t)
  have hπ : evolves R e c p := fun t ↦ view_resident_step hn' i e (π t) (hp t) (hR t)
  have hm₀ : probability (m 0) := by
    have hmEq : m 0 = view i 1 b := by
      funext x
      have hx : fromClass x ∈ mutants i := by
        change toString (fromClass x) i = 1
        rw [string_fromClass]
        exact x.property.2
      change b (fromClass x) - a (fromClass x) = b (fromClass x)
      rw [hA _ hx, sub_zero]
    rw [hmEq]
    refine ⟨fun x ↦ hb.1 (fromClass x), ?_⟩
    rw [mutant_view_mass]
    have hEq : project (mutants i) b = b := by
      funext x
      by_cases hx : x ∈ mutants i <;> simp [project, hx, hB]
    rw [hEq, hb.2]
  have hp₀ : probability (p 0) := ⟨fun x ↦ ha.1 (fromClass x), (resident_view_mass i a hA).trans ha.2⟩
  have hpH : mass (p H) = 1 := (resident_view_mass i (π H) (hR H)).trans (hp H).2
  have hrel (x : ColumnClass n (r + 1) i 1) : ∃ y, PhysicalShadow.Related x y := exists_shadow i x
  have hd : 0 < D := by unfold D; positivity
  have hg : 0 ≤ g := by
    have h := ShadowGaps.delta_pos (show 1 ≤ r + 1 by omega)
    unfold g
    exact pow_nonneg (add_nonneg zero_le_one (div_nonneg (mul_nonneg he.1 (mul_nonneg h.le hω)) (mul_nonneg (mul_nonneg (by norm_num) (by linarith only [he.1])) hd.le))) _
  have hT := relative_mass M R PhysicalShadow.Related hrel e c H he hV hpert D g hd hg
    (fun x y hxy ↦ ShadowComparison.value_comparison hr hn ν hν ω hω hb' he.1 H horizon hsmall hdim 0 x y hxy)
    (fun y z ↦ ReproductiveAdmissibility.value_ratio (by omega) hn ν hν he.1 H horizon 0 y z)
    m p hm hπ hm₀ hp₀ hpH
  change g / (2 * D) ≤ mass (view i 1 _) at hT
  rw [mutant_view_mass] at hT
  exact hT

end
end Lax637351Proofs.ColumnGain
