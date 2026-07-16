import Mathlib.Data.Set.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Cheenta_Proofs.BasicLemmasforCD
import Mathlib.Topology.Sets.OpenCover


variable {X : Type}[TopologicalSpace X]

def DimLe (S : Set X) : ℕ → Prop
  | 0 => ∀ {ι : Type} (C : ι → Set X), IsOpenCover C →
      ∃ (κ : Type) (D : κ → Set X), IsOpenCover D ∧ Refines D C ∧ HasOrderLE D 0
  | n + 1 => ∃ A B : Set X, S = A ∪ B ∧ DimLe A 0 ∧ DimLe B n

lemma dimLe_succ_split {S : Set X} {n : ℕ} :
  DimLe S (n + 1) ↔ ∃ A B : Set X, S = A ∪ B ∧ DimLe A 0 ∧ DimLe B n := by
  rw [DimLe]


lemma dimension_decomposition_set (S : Set X) (n : ℕ) :
  DimLe S n ↔ ∃ Xs : ℕ → Set X, S = (⋃ i ≤ n, Xs i) ∧ ∀ i ≤ n, DimLe (Xs i) 0 := by
  induction n generalizing S with
  | zero =>
    constructor
    · intro h
      refine ⟨fun _ => S, ?_, fun _ _ => h⟩
      ext x
      simp only [Set.mem_iUnion]
      exact ⟨fun hx => ⟨0, by omega, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
    · rintro ⟨Xs, rfl, hDim⟩
      have H : (⋃ i ≤ 0, Xs i) = Xs 0 := by
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨i, hi, hx⟩
          have h_eq : i = 0 := by omega
          rw [h_eq] at hx
          exact hx
        · intro hx
          exact ⟨0, by omega, hx⟩
      exact H.symm ▸ hDim 0 (by omega)
  | succ n ih =>
    constructor
    · rintro h
      rcases dimLe_succ_split.mp h with ⟨A, B, rfl, hA, hB⟩
      rcases (ih B).mp hB with ⟨Ys, rfl, hYs⟩
      let Xs : ℕ → Set X := fun i => match i with
        | Nat.zero => A
        | Nat.succ k => Ys k
      refine ⟨Xs, ?_, ?_⟩
      · ext x
        simp only [Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨0, by omega, hx⟩
          · exact ⟨i + 1, by omega, hx⟩
        · rintro ⟨j, hj, hx⟩
          cases j with
          | zero => exact Or.inl hx
          | succ j' => exact Or.inr ⟨j', by omega, hx⟩
      · intro j hj
        cases j with
        | zero => exact hA
        | succ j' => exact hYs j' (by omega)
    · rintro ⟨Xs, rfl, hDim⟩
      apply dimLe_succ_split.mpr
      use Xs 0
      use ⋃ i ≤ n, Xs (i + 1)
      refine ⟨?_, hDim 0 (by omega),
      (ih _).mpr ⟨fun i => Xs (i + 1), rfl, fun i hi => hDim (i + 1) (by omega)⟩⟩
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj, hx⟩
        cases j with
        | zero => exact Or.inl hx
        | succ j' => exact Or.inr ⟨j', by omega, hx⟩
      · rintro (hx | ⟨j, hj, hx⟩)
        · exact ⟨0, by omega, hx⟩
        · exact ⟨j + 1, by omega, hx⟩


theorem dimension_decomposition (n : ℕ) :
  DimLe (Set.univ : Set X) n ↔ ∃ Xs : ℕ → Set X,
  Set.univ = (⋃ i ≤ n, Xs i) ∧ ∀ i ≤ n, DimLe (Xs i) 0 :=
  dimension_decomposition_set Set.univ n
