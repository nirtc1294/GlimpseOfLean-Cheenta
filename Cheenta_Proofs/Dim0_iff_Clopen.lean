import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Cheenta_Proofs.BasicLemmasforCD
import Mathlib.Topology.Sets.OpenCover
/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

public section
open Set
universe u v
variable {X : Type u} [TopologicalSpace X]

theorem dim0_iff_disjoint_clopen_refinement_general
    {ι : Type*} (u : ι → Set X) (huo : ∀ i, IsOpen (u i)) (hucov : ⋃ i, u i = univ) :
    (∃ (κ : Type) (v : κ → Set X), (∀ k, IsOpen (v k)) ∧ (⋃ k, v k = univ) ∧ Refines v u ∧ HasOrderLE v 0) ↔
    (∃ (κ : Type) (v : κ → Set X), (∀ k, IsOpen (v k)) ∧ (⋃ k, v k = univ) ∧ Refines v u ∧ ∀ k₁ k₂, k₁ ≠ k₂ → v k₁ ∩ v k₂ = ∅) := by
    constructor
    · rintro ⟨κ, v, hvopen, hvcov, href, hord⟩
      refine ⟨κ, v, hvopen, hvcov, href, ?_⟩
      intro k₁ k₂ hne
      have hle : v k₁ ∩ v k₂ = ∅ := by
        exact hord.1 k₁ k₂ hne
      exact hle
    · rintro ⟨κ, v, hvopen, hvcov, href, hdisj⟩
      rcases isEmpty_or_nonempty κ with hκ | hne
      · have hX : IsEmpty X := ⟨fun x => by
          have h := hvcov ▸ Set.mem_univ x
          rwa [Set.iUnion_eq_empty.mpr fun k => hκ.elim k] at h⟩
        exact ⟨κ, v, hvopen, hvcov, href, fun s _ => eq_empty_of_subset_empty fun x _ => hX.elim x⟩
      · refine ⟨Sum κ ℕ, Sum.elim v (fun _ => ∅), ?_, ?_, ?_⟩
        · constructor
          · rintro (k | _)
            · exact hvopen k
            · exact isOpen_empty
          · simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Sum.exists, Sum.elim_inl,
                       Sum.elim_inr, Set.mem_empty_iff_false]
            intro x
            have ⟨k, hk⟩ := Set.mem_iUnion.mp (hucov ▸ Set.mem_univ x)
            exact Or.inl ⟨k, hk⟩
        · rintro (k | _)
          · exact href k
          · exact ⟨(href hne.some).choose, Set.empty_subset _⟩
        · unfold HasOrderEq
          intro s hf
          by_cases hs : ∃ k₁ ∈ s, ∃ k₂ ∈ s, k₁ ≠ k₂
          · obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hs
            apply eq_empty_of_subset_empty; intro x hx
            simp only [Set.mem_iInter] at hx
            have hd : Sum.elim v (fun _ => ∅) k₁ ∩ Sum.elim v (fun _ => ∅) k₂ = ∅ :=
              match k₁, k₂ with
              | .inl j₁, .inl j₂ => hdisj j₁ j₂ (mt (congrArg Sum.inl) hne)
              | .inl _, .inr _ | .inr _, _ => by simp
            exact hd ▸ ⟨hx k₁ hk₁, hx k₂ hk₂⟩
          · push_neg at hs
            exact absurd
              (Sum.inr_injective (hs _
                (hf Sum.inr Sum.inr_injective 0 (by norm_num)) _
                (hf Sum.inr Sum.inr_injective 1 (by norm_num))))
              (by norm_num)
