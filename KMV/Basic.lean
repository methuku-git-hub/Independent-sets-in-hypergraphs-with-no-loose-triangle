module
public import Mathlib.Data.Finset.Card
public section
namespace KMV

/-- A hypergraph is a finite set of finite vertex sets. No linearity or
antichain condition is imposed. Isolated vertices remain in the ambient type
and contribute to its cardinality. -/
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

/-- Restricting an independent vertex set preserves independence. -/
theorem independent_mono {V : Type*} {H : Hypergraph V}
    {I J : Finset V} (hI : Independent H I) (hJI : J ⊆ I) :
    Independent H J := by
  intro e he heJ
  exact hI e he (fun x hx => hJI (heJ hx))

/-- Empty hypergraphs witness consistency of the structural hypotheses. -/
theorem empty_rank_bounds {V : Type*} (r : ℕ) :
    RankBounds (∅ : Hypergraph V) r := by
  intro e he
  simp at he

end KMV
