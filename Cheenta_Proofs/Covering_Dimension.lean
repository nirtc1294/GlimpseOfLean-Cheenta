import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.OpenCover
import Cheenta_Proofs.BasicLemmasforCD

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

open Set Filter Function
open Filter Topology

universe u w

variable {X : Type u} [TopologicalSpace X]

def CoveringDimensionLE (n : ℕ) : Prop :=
  ∀ {ι : Type*} (u : ι → TopologicalSpace.Opens X), TopologicalSpace.IsOpenCover u →
    ∃ (κ : Type*) (w : κ → TopologicalSpace.Opens X),
      TopologicalSpace.IsOpenCover w ∧
      Refines (fun k => (w k : Set X)) (fun i => (u i : Set X)) ∧
      HasOrderLE (fun k => (w k : Set X)) n
