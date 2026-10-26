module
public import KMV.Expansion
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Find
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

@[expose] def Antichain (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ⊆ f → e = f

/-- Delete all edges containing X and insert X as an edge. -/
@[expose] def compress (H : Hypergraph V) (X : Finset V) : Hypergraph V :=
  insert X (H.filter fun e => ¬ X ⊆ e)

theorem mem_compress {H : Hypergraph V} {X e : Finset V} :
    e ∈ compress H X ↔ e = X ∨ e ∈ H ∧ ¬ X ⊆ e := by
  simp [compress]

theorem compress_independent {H : Hypergraph V} {X I : Finset V}
    (h : Independent (compress H X) I) : Independent H I := by
  intro e he heI
  by_cases hXe : X ⊆ e
  · exact h X (mem_compress.mpr (Or.inl rfl)) (hXe.trans heI)
  · exact h e (mem_compress.mpr (Or.inr ⟨he, hXe⟩)) heI

theorem compress_rank_bounds {H : Hypergraph V} {X : Finset V} {r : ℕ}
    (hH : RankBounds H r) (hX : Expandable H r X) (hcard : 3 ≤ X.card) :
    RankBounds (compress H X) r := by
  intro e he
  rcases mem_compress.mp he with rfl | ⟨he, _⟩
  · exact ⟨hcard, expandable_card_le hH hX⟩
  · exact hH e he

theorem compress_loose_triangle_free {H : Hypergraph V} {X : Finset V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) (hX : Expandable H r X) :
    LooseTriangleFree (compress H X) := by
  have hext : ∀ e ∈ compress H X, Expandable H r e := by
    intro e he
    rcases mem_compress.mp he with rfl | ⟨he, _⟩
    · exact hX
    · exact edge_expandable hH he
  intro e he f hf g hg
  exact expandable_no_loose_triangle hH hfree (hext e he) (hext f hf) (hext g hg)

theorem compress_antichain {H : Hypergraph V} {X E : Finset V}
    (hanti : Antichain H) (hE : E ∈ H) (hXE : X ⊆ E) (hne : X ≠ E) :
    Antichain (compress H X) := by
  intro e he f hf hef
  rcases mem_compress.mp he with hex | ⟨heOld, hXe⟩
  · subst e
    rcases mem_compress.mp hf with hfx | ⟨_, hXf⟩
    · exact hfx.symm
    · exact (hXf hef).elim
  · rcases mem_compress.mp hf with hfx | ⟨hfOld, _⟩
    · subst f
      have heE : e = E := hanti e heOld E hE (hef.trans hXE)
      have hEX : E ⊆ X := heE ▸ hef
      exact (hne (Finset.Subset.antisymm hXE hEX)).elim
    · exact hanti e heOld f hfOld hef

@[expose] def edgeWeight (H : Hypergraph V) : ℕ := ∑ e ∈ H, e.card

theorem compress_weight_lt {H : Hypergraph V} {X E : Finset V}
    (hE : E ∈ H) (hXE : X ⊆ E) (hne : X ≠ E) :
    edgeWeight (compress H X) < edgeWeight H := by
  classical
  have hcard : X.card < E.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hXE, hne⟩)
  have hmem : E ∈ H.filter (fun e => X ⊆ e) := Finset.mem_filter.mpr ⟨hE, hXE⟩
  have hle : E.card ≤ ∑ e ∈ H.filter (fun e => X ⊆ e), e.card :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hsum := Finset.sum_filter_add_sum_filter_not H (fun e => X ⊆ e) (fun e => e.card)
  have hx : X ∉ H.filter (fun e => ¬ X ⊆ e) := by simp
  simp only [edgeWeight, compress, Finset.sum_insert hx]
  omega

/-- No expandable set of size at least three is properly contained in an edge. -/
@[expose] def Reduced (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ X : Finset V, Expandable H r X → 3 ≤ X.card → ∀ E ∈ H, X ⊆ E → X = E

omit [DecidableEq V] in
theorem reduced_antichain {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hred : Reduced H r) : Antichain H := by
  intro e he f hf hef
  exact hred e (edge_expandable hH he) (hH e he).1 f hf hef

/-- The terminating part of Lemma 4.2, expressed by minimising the integer
sum of edge sizes. The codegree and edge-count bounds are separate obligations. -/
theorem exists_reduced {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) :
    ∃ J : Hypergraph V, RankBounds J r ∧ LooseTriangleFree J ∧
      (∀ I, Independent J I → Independent H I) ∧ Reduced J r ∧ Antichain J := by
  classical
  let P : ℕ → Prop := fun m => ∃ J : Hypergraph V,
    RankBounds J r ∧ LooseTriangleFree J ∧
      (∀ I, Independent J I → Independent H I) ∧ edgeWeight J = m
  have hex : ∃ m, P m := ⟨edgeWeight H, H, hH, hfree, fun _ hi => hi, rfl⟩
  obtain ⟨J, hJ, hJfree, hJI, hweight⟩ := Nat.find_spec hex
  have hred : Reduced J r := by
    intro X hX hcard E hE hXE
    by_contra hne
    have hsmall := compress_weight_lt hE hXE hne
    have hp : P (edgeWeight (compress J X)) :=
      ⟨compress J X, compress_rank_bounds hJ hX hcard,
        compress_loose_triangle_free hJ hJfree hX,
        fun I hi => hJI I (compress_independent hi), rfl⟩
    have hmin := Nat.find_min' hex hp
    omega
  exact ⟨J, hJ, hJfree, hJI, hred, reduced_antichain hJ hred⟩

end KMV
