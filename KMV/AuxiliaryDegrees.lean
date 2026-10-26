module
public import KMV.Trimming
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

theorem sum_pairCodegree (H : Hypergraph V) (j : ℕ) (v : V) :
    (∑ x ∈ Finset.univ.erase v, codegree H j {v,x}) = (j-1)*sizeDegree H j v := by
  have hd : ∀ x, codegree H j {v,x} =
      ∑ e ∈ H, if e.card = j ∧ v ∈ e ∧ x ∈ e then 1 else 0 := by
    intro x
    simp [codegree,containingEdges, ← Finset.sum_filter, insert_subset_iff]
  simp_rw [hd]
  rw [Finset.sum_comm]
  have he : ∀ e : Finset V,
      (∑ x ∈ Finset.univ.erase v, if e.card = j ∧ v ∈ e ∧ x ∈ e then 1 else 0) =
        if e.card = j ∧ v ∈ e then j-1 else 0 := by
    intro e
    by_cases h : e.card = j ∧ v ∈ e
    · simp only [h.1,h.2,true_and,ite_true, ← Finset.sum_filter]
      have hf : (Finset.univ.erase v).filter (fun x => x ∈ e) = e.erase v := by
        ext x; simp [and_comm]
      simp [hf,card_erase_of_mem h.2,h.1]
    · have hh : ∀ x, ¬ (e.card = j ∧ v ∈ e ∧ x ∈ e) := fun x hx => h ⟨hx.1,hx.2.1⟩
      simp [h,hh]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp [sizeDegree,Nat.mul_comm]

@[expose] noncomputable def highPairs (H : Hypergraph V) (j : ℕ) (L : ℝ) (v : V) : Finset V :=
  (Finset.univ.erase v).filter (fun x => L < (codegree H j {v,x} : ℝ))

theorem highPairs_card (H : Hypergraph V) (j : ℕ) {L : ℝ} (hL : 0 < L) (v : V) :
    ((highPairs H j L v).card : ℝ) ≤ ((j-1 : ℕ) : ℝ)*sizeDegree H j v / L := by
  apply (le_div_iff₀ hL).mpr
  have hs : (∑ x ∈ highPairs H j L v, L) ≤
      ∑ x ∈ highPairs H j L v, (codegree H j {v,x} : ℝ) :=
    sum_le_sum (fun x hx => (mem_filter.mp hx).2.le)
  have ht : (∑ x ∈ highPairs H j L v, (codegree H j {v,x} : ℝ)) ≤
      ∑ x ∈ Finset.univ.erase v, (codegree H j {v,x} : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x _ _; positivity
  have he : (∑ x ∈ Finset.univ.erase v, (codegree H j {v,x} : ℝ)) =
      ((j-1 : ℕ) : ℝ)*sizeDegree H j v := by exact_mod_cast sum_pairCodegree H j v
  simpa using hs.trans (ht.trans he.le)

@[expose] noncomputable def thresholdGraph (H : Hypergraph V) (L₃ L₄ : ℝ) (v x : V) : Prop :=
  v ≠ x ∧ (L₃ < (codegree H 3 {v,x} : ℝ) ∨ L₄ < (codegree H 4 {v,x} : ℝ))

theorem thresholdGraph_symm (H : Hypergraph V) (L₃ L₄ : ℝ) (v x : V) :
    thresholdGraph H L₃ L₄ v x → thresholdGraph H L₃ L₄ x v := by
  rintro ⟨hne,h⟩
  exact ⟨hne.symm,by simpa [Finset.pair_comm] using h⟩

theorem thresholdGraph_irrefl (H : Hypergraph V) (L₃ L₄ : ℝ) (v : V) :
    ¬ thresholdGraph H L₃ L₄ v v := fun h => h.1 rfl

theorem thresholdGraph_degree (H : Hypergraph V) {L₃ L₄ : ℝ}
    (h₃ : 0 < L₃) (h₄ : 0 < L₄) (v : V) :
    (((Finset.univ.filter (thresholdGraph H L₃ L₄ v)).card) : ℝ) ≤
      2*(sizeDegree H 3 v : ℝ)/L₃ + 3*(sizeDegree H 4 v : ℝ)/L₄ := by
  have he : Finset.univ.filter (thresholdGraph H L₃ L₄ v) =
      highPairs H 3 L₃ v ∪ highPairs H 4 L₄ v := by
    ext x
    simp only [thresholdGraph, highPairs, mem_filter, mem_univ, true_and, mem_union,
      mem_erase, and_true]
    tauto
  rw [he]
  have hc : (((highPairs H 3 L₃ v ∪ highPairs H 4 L₄ v).card) : ℝ) ≤
      (highPairs H 3 L₃ v).card + (highPairs H 4 L₄ v).card := by exact_mod_cast card_union_le _ _
  have hb₃ := highPairs_card H 3 h₃ v
  have hb₄ := highPairs_card H 4 h₄ v
  norm_num at hb₃ hb₄
  linarith

theorem thresholdGraph_expandable {H : Hypergraph V} {r B : ℕ} {L₃ L₄ : ℝ}
    (h₃ : ((2*r : ℕ) : ℝ) ≤ L₃) (h₄ : ((2*r*B : ℕ) : ℝ) ≤ L₄)
    (htr : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B)
    {v x : V} (hG : thresholdGraph H L₃ L₄ v x) : Expandable H r {v,x} := by
  have hP : ({v,x} : Finset V).card = 2 := by simp [hG.1]
  rcases hG.2 with hG | hG
  · apply expandable_of_large_codegree (M:=1) (by simp)
    · have hn : 2*r < codegree H 3 {v,x} := by exact_mod_cast h₃.trans_lt hG
      simpa using hn
    · intro y hy
      have hc : (insert y ({v,x} : Finset V)).card = 3 := by simp [hy,hP]
      simpa only [hc] using (codegree_same_size_le_one (H:=H) (X:=insert y {v,x}))
  · apply expandable_of_large_codegree (M:=B) (j:=4) (by simp)
    · exact_mod_cast h₄.trans_lt hG
    · intro y hy
      exact htr _ (by simp [hy,hP])

/-- The auxiliary graph's finite estimates, before substituting the eventual
logarithmic parameter choices. -/
theorem auxiliary_graph {H : Hypergraph V} {r B : ℕ} {L₃ L₄ : ℝ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H)
    (h₃ : ((2*r : ℕ) : ℝ) ≤ L₃) (h₄ : ((2*r*B : ℕ) : ℝ) ≤ L₄)
    (hL₃ : 0 < L₃) (hL₄ : 0 < L₄)
    (htr : ∀ X : Finset V, X.card = 3 → codegree H 4 X ≤ B) :
    (∀ a b c, ¬ (thresholdGraph H L₃ L₄ a b ∧ thresholdGraph H L₃ L₄ b c ∧
      thresholdGraph H L₃ L₄ c a)) ∧
    (∀ v, (((Finset.univ.filter (thresholdGraph H L₃ L₄ v)).card) : ℝ) ≤
      2*(sizeDegree H 3 v : ℝ)/L₃ + 3*(sizeDegree H 4 v : ℝ)/L₄) ∧
    (∀ e ∈ H, (∀ x ∈ e, ∀ y ∈ e, ¬ thresholdGraph H L₃ L₄ x y) →
      Separated (thresholdGraph H L₃ L₄) e) := by
  have hext : ∀ x y, thresholdGraph H L₃ L₄ x y → Expandable H r {x,y} :=
    fun _ _ h => thresholdGraph_expandable h₃ h₄ htr h
  exact ⟨expandable_graph_triangle_free hH hfree (thresholdGraph_irrefl H L₃ L₄) hext,
    thresholdGraph_degree H hL₃ hL₄,
    fun _ he hn => edge_separated_of_no_graph_pairs hH hfree hext he hn⟩

end KMV
