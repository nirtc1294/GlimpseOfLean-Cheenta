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

def Covering_Dimension {X : Type u} [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (ι : Type w) (u : ι → Set X),
    TopologicalSpace.IsOpenCover u →
    ∃ (κ : Type w) (v : κ → Set X),
      TopologicalSpace.IsOpenCover v ∧
      Refines v u ∧
      HasOrderLENiranjan v n
