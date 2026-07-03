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
    (∀ i, IsOpen (u i)) ∧ (⋃ i, u i = Set.univ) →
    ∃ (κ : Type w) (v : κ → Set X),
      (∀ k, IsOpen (v k)) ∧ (⋃ k, v k = Set.univ) ∧
      Refines v u ∧
      HasOrderLENiranjan v n
