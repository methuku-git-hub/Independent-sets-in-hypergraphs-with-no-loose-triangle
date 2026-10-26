module
public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Independently readable conditional target. Its sole placeholder is explicitly
permitted by the user. No Solution may import this module. -/
public section
namespace KMV


/-- A simple hypergraph on the ambient finite vertex type. Isolated vertices
remain in the ambient type and contribute to its cardinality. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- No edge is contained in the vertex set. -/
@[expose] def Independent {V : Type*} (H : Hypergraph V) (I : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

/-- Every edge has size between three and r, inclusively. -/
@[expose] def RankBounds {V : Type*} (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, 3 ≤ e.card ∧ e.card ≤ r

/-- Pairwise intersections are singletons and the triple intersection is empty.
This definition applies to mixed edge sizes. -/
@[expose] def LooseTriangle {V : Type*} [DecidableEq V]
    (e f g : Finset V) : Prop :=
  e ≠ f ∧ f ≠ g ∧ g ≠ e ∧
  (e ∩ f).card = 1 ∧ (f ∩ g).card = 1 ∧ (g ∩ e).card = 1 ∧
  e ∩ f ∩ g = ∅

@[expose] def LooseTriangleFree {V : Type*} [DecidableEq V]
    (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, ∀ g ∈ H, ¬ LooseTriangle e f g


/-- Li--Postle triangles: every pair intersects outside the third edge.
The equivalence with their three-vertex definition is proved separately. -/
@[expose] def Triangle {V : Type*} [DecidableEq V] (e f g : Finset V) : Prop :=
  ((e ∩ f) \ g).Nonempty ∧ ((f ∩ g) \ e).Nonempty ∧ ((g ∩ e) \ f).Nonempty

@[expose] def TriangleFree {V : Type*} [DecidableEq V] (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, ∀ g ∈ H, ¬ Triangle e f g

/-- Counts edges of the specified size containing v, not ordinary total degree. -/
@[expose] def sizeDegree {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (j : ℕ) (v : V) : ℕ :=
  (H.filter fun e => e.card = j ∧ v ∈ e).card

@[expose] def ProperColoring {V : Type*} (H : Hypergraph V)
    {q : ℕ} (color : V → Fin q) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, color x ≠ color y

/-- The sole allowed external premise. This is exactly the ordinary-coloring
form with edge sizes 3 and 4 stated in manuscript Theorem 2.1. It uses real
degree upper bounds at least 8, making absent edge sizes unambiguous.
It is not asserted here as a theorem or introduced as an axiom. -/
@[expose] def LiPostle34 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : Hypergraph (Fin n)), RankBounds H 4 → TriangleFree H →
    ∀ D₃ D₄ : ℝ, 8 ≤ D₃ → 8 ≤ D₄ →
    (∀ v, (sizeDegree H 3 v : ℝ) ≤ D₃) →
    (∀ v, (sizeDegree H 4 v : ℝ) ≤ D₄) →
    ∃ (q : ℕ) (color : Fin n → Fin q), ProperColoring H color ∧
      (q : ℝ) ≤ C * max (Real.rpow (D₃ / Real.log D₃) (1 / 2 : ℝ))
        (Real.rpow (D₄ / Real.log D₄) (1 / 3 : ℝ))

/-- Manuscript version 21, Theorem 1.3, with its full mixed-rank strength. -/
@[expose] def KMVStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
  ∀ n : ℕ, N ≤ n → ∀ H : Hypergraph (Fin n),
  RankBounds H r → LooseTriangleFree H →
  ∃ I : Finset (Fin n), Independent H I ∧
    c * Real.rpow (n : ℝ) (2 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log (n : ℝ))) (1 / 3 : ℝ) ≤ (I.card : ℝ)

/-- Independent advertised statement; proved separately in Solution. -/
theorem main_result (hLP : LiPostle34) : KMVStatement := by
  sorry

end KMV
