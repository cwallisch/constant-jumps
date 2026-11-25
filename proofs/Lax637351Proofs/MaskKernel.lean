import Lax637351Proofs.OffspringProduct
import Lax637351Proofs.Charge

namespace Lax637351Proofs.MaskKernel

open Lax637351.Algorithm Lax637351Proofs.Transitions
open Lax637351Proofs.FiniteDrift Lax637351Proofs.Sampling Lax637351Proofs.Mutation
open Lax637351Proofs.MarkedStep Lax637351Proofs.PairStep Lax637351Proofs.OffspringProduct
open Lax637351Proofs.Regeneration Lax637351Proofs.Charge
open scoped Classical ENNReal

noncomputable section

variable {n : ℕ} {μ : ℕ+}

def flipped (m : BitString n) : Finset (Fin n) := (zeros m)ᶜ

lemma mem_flipped (m : BitString n) (j : Fin n) : j ∈ flipped m ↔ m j = 1 := by
  simp only [flipped, Finset.mem_compl, mem_zeros]
  exact ⟨bit_eq_one_of_ne_zero (m j), fun h ↦ h ▸ one_ne_zero⟩

def masked (fitness : BitString n → ℝ) (p : ℝ) (ar : Bool) :
    Kernel (Population n μ) (Fin n) := fun P ↦
  (stepMarked fitness p ar P).map (fun a ↦ (flipped a.1.2.2, a.2))

lemma marginal_masked (fitness : BitString n → ℝ) (p : ℝ) (ar : Bool) :
    marginal (masked (μ := μ) fitness p ar) = step fitness p ar := by
  funext P
  rw [marginal, masked, PMF.map_comp]
  exact stepMarked_population fitness p ar P

lemma independent_hit (hn : 2 ≤ n) (fitness : BitString n → ℝ) (p : ℝ) (ar : Bool)
    (P : Population n μ) (D : Finset (Fin n)) :
    mean (masked fitness p ar P) (fun v ↦ if D ⊆ v.1 then 1 else 0) = (1 / (n : ℝ)) ^ D.card := by
  rw [masked, mean_map]
  have hfun : (fun v : Draw n × Population n μ ↦
      if D ⊆ flipped v.1.2.2 then (1 : ℝ) else 0) =
      (fun v ↦ (fun d : Draw n ↦ indicator (D ⊆ flipped d.2.2)) (Prod.fst v)) := by
    funext v
    by_cases h : D ⊆ flipped v.1.2.2 <;> simp [indicator, h]
  rw [hfun, ← mean_map (stepMarked fitness p ar P) Prod.fst
    (fun d ↦ indicator (D ⊆ flipped d.2.2)), stepMarked_draws]
  have hfun' : (fun d : Draw n ↦ indicator (D ⊆ flipped d.2.2)) =
      (fun d ↦ (fun m : BitString n ↦ indicator (∀ j ∈ D, m j = 1)) d.2.2) := by
    funext d
    have hh : (D ⊆ flipped d.2.2) ↔ ∀ j ∈ D, d.2.2 j = 1 :=
      ⟨fun h j hj ↦ (mem_flipped _ _).mp (h hj),
       fun h j hj ↦ (mem_flipped _ _).mpr (h j hj)⟩
    simp only [hh]
  rw [hfun', ← mean_map (draws p P) (fun d : Draw n ↦ d.2.2)
    (fun m ↦ indicator (∀ j ∈ D, m j = 1)), mask_marginal]
  exact all_hit_probability (rate_valid hn) D

def intact (D : Finset (Fin n)) (P : Population n μ) : Prop :=
  ∀ j ∈ D, ∀ i, P i j = 0

lemma intact_missing (D : Finset (Fin n)) (P : Population n μ)
    (h : intact D P) (hmiss : ¬ missing P) : D = ∅ := by
  by_contra hn
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hn
  obtain ⟨i, hi⟩ : ∃ i, P i = optimum n := by simpa [missing] using hmiss
  have hh := h j hj i
  rw [hi] at hh
  exact one_ne_zero hh

lemma parent_support_zero_or_eq {P : Population n μ} {cross : Bool} {y : BitString n}
    (hy : y ∈ (parents P cross).support) (f : BitString n → Prop)
    (hP : ∀ i, f (P i)) (hc : ∀ x y m, f x → f y → f (crossover x y m)) : f y := by
  cases cross
  · have hh : y ∈ ((PMF.uniformOfFintype (Fin μ)).map P).support := by simpa [parents] using hy
    rcases (PMF.mem_support_map_iff _ _ _).mp hh with ⟨i, _, rfl⟩
    exact hP i
  · simp only [parents, if_true, Bind.bind, Pure.pure] at hy
    rcases (PMF.mem_support_bind_iff _ _ _).mp hy with ⟨⟨i, j⟩, _, hy⟩
    rcases (PMF.mem_support_bind_iff _ _ _).mp hy with ⟨m, _, hy⟩
    rw [(PMF.mem_support_pure_iff _ _).mp hy]
    exact hc _ _ _ (hP i) (hP j)

lemma chosen_draw_parent {p : ℝ} {P : Population n μ} {d : Draw n}
    (hd : d ∈ (draws p P).support) : d.2.1 ∈ (parents P d.1).support := by
  rcases (PMF.mem_support_bind_iff _ _ _).mp hd with ⟨b, _, hd⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp hd with ⟨y, hy, hd⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hd with ⟨m, _, rfl⟩
  exact hy

lemma intact_carries (fitness : BitString n → ℝ) (p : ℝ) (ar : Bool)
    (P : Population n μ) (v : Finset (Fin n) × Population n μ)
    (hv : v ∈ (masked fitness p ar P).support) (D : Finset (Fin n))
    (hP : intact D P) : intact (D \ v.1) v.2 := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨a, ha, rfl⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp ha with ⟨d, hd, ha⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp ha with ⟨Q, hQ, rfl⟩
  intro j hj i
  have hD := Finset.mem_sdiff.mp hj
  have hy := parent_support_zero_or_eq (chosen_draw_parent hd) (fun x ↦ x j = 0)
    (hP j hD.1) (fun x y m hx hy ↦ by simp [crossover, hx, hy])
  have hm : d.2.2 j ≠ 1 := fun h ↦ hD.2 ((mem_flipped _ _).mpr h)
  have hz : child d j = 0 := by simp [child, mutate, hy, hm]
  unfold select at hQ
  split_ifs at hQ
  · rw [(PMF.mem_support_pure_iff _ _).mp hQ]
    exact hP j hD.1 i
  · rcases (PMF.mem_support_map_iff _ _ _).mp hQ with ⟨index, _, rfl⟩
    refine Fin.lastCases ?_ (fun u ↦ ?_) index
    · simpa only [replace, Fin.lastCases_last] using hP j hD.1 i
    · by_cases hi : i = u
      · simpa [replace, hi] using hz
      · simpa only [replace, Fin.lastCases_castSucc, Function.update_of_ne hi] using hP j hD.1 i

end
end Lax637351Proofs.MaskKernel
