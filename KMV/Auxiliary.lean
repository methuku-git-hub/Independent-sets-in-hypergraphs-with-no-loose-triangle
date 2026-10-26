module
public import KMV.Codegrees
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

/-- The common argument behind both pair-codegree thresholds. -/
theorem expandable_of_large_codegree {H : Hypergraph V} {r j M : ℕ} {X : Finset V}
    (hX : X.Nonempty) (hlarge : 2 * r * M < codegree H j X)
    (hupper : ∀ y ∉ X, codegree H j (insert y X) ≤ M) : Expandable H r X := by
  by_contra hn
  obtain ⟨Y, hd, hc, hY⟩ := nonexpandable_witness hX hn
  have hs : (∑ y ∈ Y, codegree H j (insert y X)) ≤ Y.card * M := by
    calc
      _ ≤ ∑ _y ∈ Y, M := by
        apply Finset.sum_le_sum
        intro y hy
        exact hupper y (fun hx => Finset.disjoint_left.mp hd hx hy)
      _ = Y.card * M := by simp
  have hb := (codegree_le_sum_insert hY).trans (hs.trans (Nat.mul_le_mul_right M hc))
  omega

@[expose] def Separated (G : V → V → Prop) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G x y ∧ ∀ z, ¬ (G x z ∧ G y z)

theorem expandable_graph_triangle_free {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H)
    {G : V → V → Prop} (hirr : ∀ x, ¬ G x x)
    (hext : ∀ x y, G x y → Expandable H r {x,y}) :
    ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a) := by
  intro a b c ⟨hab, hbc, hca⟩
  have hneab : a ≠ b := fun h => hirr b (h ▸ hab)
  have hneac : a ≠ c := by intro h; subst c; exact hirr a hca
  have hnebc : b ≠ c := fun h => hirr c (h ▸ hbc)
  exact expandable_no_loose_triangle hH hfree (hext a b hab) (hext b c hbc)
    (hext c a hca) (pair_triangle hneab hneac hnebc)

private theorem two_pairs_edge_triangle {e : Finset V} {x y z : V}
    (hx : x ∈ e) (hy : y ∈ e) (hz : z ∉ e) (hxy : x ≠ y) :
    LooseTriangle ({x,z} : Finset V) {y,z} e := by
  have hxz : x ≠ z := by intro h; subst z; exact hz hx
  have hyz : y ≠ z := by intro h; subst z; exact hz hy
  have h₁ : ({x,z} : Finset V) ∩ {y,z} = {z} := by
    ext a; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; grind
  have h₂ : ({y,z} : Finset V) ∩ e = {y} := by
    ext a; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; grind
  have h₃ : e ∩ ({x,z} : Finset V) = {x} := by
    ext a; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; grind
  have hn₁ : ({x,z} : Finset V) ≠ {y,z} := by
    intro h
    have : x ∈ ({y,z} : Finset V) := h ▸ (by simp : x ∈ ({x,z} : Finset V))
    simp [hxy, hxz] at this
  have hn₂ : ({y,z} : Finset V) ≠ e := by
    intro h
    exact hz (h ▸ (by simp : z ∈ ({y,z} : Finset V)))
  have hn₃ : e ≠ ({x,z} : Finset V) := by
    intro h
    exact hz (h.symm ▸ (by simp : z ∈ ({x,z} : Finset V)))
  refine ⟨hn₁, hn₂, hn₃, by simp [h₁], by simp [h₂], by simp [h₃], ?_⟩
  rw [h₁]
  ext a
  simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
  grind

/-- Structural part of Lemma 5.1. The graph can be any loopless relation
whose adjacent pairs are expandable; numerical degree bounds are separate. -/
theorem edge_separated_of_no_graph_pairs {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H)
    {G : V → V → Prop}
    (hext : ∀ x y, G x y → Expandable H r {x,y})
    {e : Finset V} (he : e ∈ H)
    (hn : ∀ x ∈ e, ∀ y ∈ e, ¬ G x y) : Separated G e := by
  intro x hx y hy hxy
  refine ⟨hn x hx y hy, ?_⟩
  intro z ⟨hxz, hyz⟩
  have hz : z ∉ e := fun hz => hn x hx z hz hxz
  exact expandable_no_loose_triangle hH hfree (hext x z hxz) (hext y z hyz)
    (edge_expandable hH he) (two_pairs_edge_triangle hx hy hz hxy)

end KMV
