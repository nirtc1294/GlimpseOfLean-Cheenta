import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.OpenCover
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Covering_Dimension
import Mathlib.Topology.Sets.Opens
/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

set_option linter.unusedVariables false

public section
open Set Filter Function Topology

universe u
variable {X : Type u} [TopologicalSpace X]


theorem dim0_iff_finite_clopen_partition [NormalSpace X] [Nonempty X] :
  Covering_Dimension (X := X) 0 ↔
  ∀ (m : ℕ) (u : {i : ℕ // i < m} → TopologicalSpace.Opens X),
  TopologicalSpace.IsOpenCover u →
  ∃ (m' : ℕ) (v : {i : ℕ // i < m'} → TopologicalSpace.Opens X),
  TopologicalSpace.IsOpenCover v ∧
  Refines (fun k => (v k : Set X)) (fun i => (u i : Set X)) ∧
  (∀ k, IsClopen (v k : Set X)) ∧
  (∀ k₁ k₂, k₁ ≠ k₂ → (v k₁ : Set X) ∩ (v k₂ : Set X) = ∅) := by
  constructor
  · intro h_dim m u hu_cover
    obtain ⟨m', v, hv_cover, hv_ref, hv_order⟩ := h_dim m u hu_cover
    use m', v
    refine ⟨hv_cover, hv_ref, ?_, ?_⟩
    · intro k
      have h_is_open : IsOpen (v k : Set X) := hv_cover k
      have h_is_closed : IsClosed (v k : Set X) := by
        rw [← isOpen_compl_iff]
        have h_compl : (v k : Set X)ᶜ = ⋃ (j : {i // i < m'}) (_ : j ≠ k), (v j : Set X) := by
          sorry
        rw [h_compl]
        exact isOpen_biUnion (fun j _ => hv_cover j)
      exact ⟨h_is_open, h_is_closed⟩
    · intro k₁ k₂ hne
      sorry
  · intro h_partition m u hu_cover
    rcases h_partition m u hu_cover with ⟨m', v, hv_cover, hv_ref, hv_clopen, hv_disj⟩
    use m', v
    refine ⟨hv_cover, hv_ref, hv_clopen, hv_disj⟩
