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
  ∀ (ι : Type w) (u : ι → TopologicalSpace.Opens X),
    TopologicalSpace.IsOpenCover u →
    ∃ (κ : Type w) (v : κ → TopologicalSpace.Opens X),
      TopologicalSpace.IsOpenCover v ∧
      Refines (fun k => (v k : Set X)) (fun i => (u i : Set X)) ∧
      HasOrderLE (fun k => (v k : Set X)) n

def Covering_Dimension_Strict (n : ℕ) : Prop :=
  ∀ (m : ℕ) (u : {i : ℕ // i < m} → TopologicalSpace.Opens X),
    TopologicalSpace.IsOpenCover u →
    (∀ i, (u i : Set X) ≠ ∅) →
    Function.Injective u →
    ∃ (m' : ℕ) (v : {j : ℕ // j < m'} → TopologicalSpace.Opens X),
    TopologicalSpace.IsOpenCover v ∧
    Refines (fun j => (v j : Set X)) (fun i => (u i : Set X)) ∧
    HasOrderLE_Strict (fun j => (v j : Set X)) n

def CoveringDimensionLE (n : ℕ) : Prop :=
  ∀ {ι : Type*} (u : ι → TopologicalSpace.Opens X),
    (iSup u = ⊤) → -- IsOpenCover u
    ∃ (κ : Type*) (v : κ → TopologicalSpace.Opens X),
      (iSup v = ⊤) ∧
      (∀ j, ∃ i, (v j : Set X) ⊆ (u i : Set X)) ∧ -- Refines v u
      HasOrderLE (fun j => (v j : Set X)) n
