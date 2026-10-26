module
public import KMV.FiniteCleaning
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]
open scoped Classical

@[expose] noncomputable def avoidGraph (H : Hypergraph V) (G : V → V → Prop) : Hypergraph V :=
  H.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, ¬ G x y)

theorem codegree_mono {H K : Hypergraph V} (h : H ⊆ K) (j : ℕ) (P : Finset V) :
    codegree H j P ≤ codegree K j P := card_le_card (containingEdges_mono h j P)

theorem avoidGraph_subset (H : Hypergraph V) (G : V → V → Prop) : avoidGraph H G ⊆ H := filter_subset _ _

theorem induced_avoidGraph_eq {H : Hypergraph V} {G : V → V → Prop} {U : Finset V}
    (hU : ∀ x ∈ U, ∀ y ∈ U, ¬ G x y) : induced (avoidGraph H G) U = induced H U := by
  ext e
  simp only [induced,avoidGraph,mem_filter]
  constructor
  · rintro ⟨⟨he,_⟩,heU⟩; exact ⟨he,heU⟩
  · rintro ⟨he,heU⟩
    exact ⟨⟨he,fun x hx y hy => hU x (heU hx) y (heU hy)⟩,heU⟩

theorem avoidGraph_pair_codegree {H : Hypergraph V} {G : V → V → Prop} {j : ℕ} {L : ℝ}
    (hL : 0 ≤ L) (hG : ∀ x y, x ≠ y → L < (codegree H j {x,y} : ℝ) → G x y)
    {P : Finset V} (hP : P.card = 2) : (codegree (avoidGraph H G) j P : ℝ) ≤ L := by
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hP
  by_cases h : (codegree H j {x,y} : ℝ) ≤ L
  · exact (Nat.cast_le.mpr (codegree_mono (avoidGraph_subset H G) j {x,y})).trans h
  · have hxyG := hG x y hxy (lt_of_not_ge h)
    have hz : codegree (avoidGraph H G) j {x,y}=0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,_,hPe⟩ := mem_filter.mp he
      have hno := (mem_filter.mp he).2
      exact hno x (hPe (by simp)) y (hPe (by simp)) hxyG
    simpa only [hz,Nat.cast_zero] using hL

theorem avoidThreshold_codegrees {H : Hypergraph V} {L₃ L₄ : ℝ}
    (h₃ : 0 ≤ L₃) (h₄ : 0 ≤ L₄) {P : Finset V} (hP : P.card=2) :
    (codegree (avoidGraph H (thresholdGraph H L₃ L₄)) 3 P : ℝ) ≤ L₃ ∧
    (codegree (avoidGraph H (thresholdGraph H L₃ L₄)) 4 P : ℝ) ≤ L₄ := by
  exact ⟨avoidGraph_pair_codegree h₃ (fun x y hxy h => ⟨hxy,Or.inl h⟩) hP,
    avoidGraph_pair_codegree h₄ (fun x y hxy h => ⟨hxy,Or.inr h⟩) hP⟩

end KMV
