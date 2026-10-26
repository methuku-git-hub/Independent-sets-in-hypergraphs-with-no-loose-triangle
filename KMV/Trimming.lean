module
public import KMV.Deletion
public import KMV.Statements
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

theorem sum_sizeDegree (H : Hypergraph V) (j : ℕ) :
    (∑ v : V, sizeDegree H j v) = j * codegree H j ∅ := by
  have hd : ∀ v, sizeDegree H j v = ∑ e ∈ H, if e.card = j ∧ v ∈ e then 1 else 0 := by
    intro v
    simp [sizeDegree, ← Finset.sum_filter]
  simp_rw [hd]
  rw [Finset.sum_comm]
  have he : ∀ e : Finset V, (∑ v : V, if e.card = j ∧ v ∈ e then 1 else 0) =
      if e.card = j then j else 0 := by
    intro e
    by_cases hc : e.card = j
    · simp only [hc, true_and, ite_true, ← Finset.sum_filter]
      have hf : Finset.univ.filter (fun v => v ∈ e) = e := by ext v; simp
      simp [hf,hc]
    · simp [hc]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp [codegree, containingEdges, Nat.mul_comm]

@[expose] noncomputable def highDegree (H : Hypergraph V) (j : ℕ) (D : ℝ) : Finset V :=
  Finset.univ.filter (fun v => D < (sizeDegree H j v : ℝ))

theorem highDegree_card (H : Hypergraph V) (j : ℕ) {D : ℝ} (hD : 0 < D) :
    ((highDegree H j D).card : ℝ) ≤ (j : ℝ) * codegree H j ∅ / D := by
  apply (le_div_iff₀ hD).mpr
  have hs : (∑ v ∈ highDegree H j D, D) ≤ ∑ v ∈ highDegree H j D, (sizeDegree H j v : ℝ) :=
    sum_le_sum (fun v hv => (mem_filter.mp hv).2.le)
  have ht : (∑ v ∈ highDegree H j D, (sizeDegree H j v : ℝ)) ≤
      ∑ v : V, (sizeDegree H j v : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _; positivity
  have he : (∑ v : V, (sizeDegree H j v : ℝ)) = (j : ℝ)*codegree H j ∅ := by
    exact_mod_cast sum_sizeDegree H j
  simpa using hs.trans (ht.trans he.le)

@[expose] def induced (H : Hypergraph V) (U : Finset V) : Hypergraph V :=
  H.filter (fun e => e ⊆ U)

theorem induced_degree_le (H : Hypergraph V) (U : Finset V) (j : ℕ) (v : V) :
    sizeDegree (induced H U) j v ≤ sizeDegree H j v := by
  apply card_le_card
  intro e he
  obtain ⟨he,hc⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨(mem_filter.mp he).1,hc⟩

theorem induced_degree_zero {H : Hypergraph V} {U : Finset V} {v : V}
    (hv : v ∉ U) (j : ℕ) : sizeDegree (induced H U) j v = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,_,hve⟩ := mem_filter.mp he
  exact hv ((mem_filter.mp he).2 hve)

theorem independent_induced_transfer {H : Hypergraph V} {U I : Finset V}
    (hI : I ⊆ U) (hind : Independent (induced H U) I) : Independent H I := by
  intro e he heI
  exact hind e (mem_filter.mpr ⟨he,heI.trans hI⟩) heI

theorem induced_rank {H : Hypergraph V} {r : ℕ} (hH : RankBounds H r) (U : Finset V) :
    RankBounds (induced H U) r := fun e he => hH e (mem_filter.mp he).1

theorem induced_looseTriangleFree {H : Hypergraph V} (hH : LooseTriangleFree H) (U : Finset V) :
    LooseTriangleFree (induced H U) := by
  intro e he f hf g hg
  exact hH e (mem_filter.mp he).1 f (mem_filter.mp hf).1 g (mem_filter.mp hg).1

theorem trim_degrees (H : Hypergraph V) (sizes : Finset ℕ) (D : ℕ → ℝ)
    (hD : ∀ j ∈ sizes, 0 < D j) :
    ∃ U : Finset V,
      (Fintype.card V : ℝ) - U.card ≤
        ∑ j ∈ sizes, (j : ℝ)*codegree H j ∅ / D j ∧
      ∀ j ∈ sizes, ∀ v, (sizeDegree (induced H U) j v : ℝ) ≤ D j := by
  let B := sizes.biUnion (fun j => highDegree H j (D j))
  let U := Finset.univ \ B
  have hcard : (Fintype.card V : ℝ) - U.card = B.card := by
    have he := card_sdiff_add_card_eq_card (Finset.subset_univ B)
    change U.card + B.card = Finset.univ.card at he
    have he' : (U.card : ℝ) + B.card = Fintype.card V := by exact_mod_cast he
    linarith
  refine ⟨U,?_,?_⟩
  · rw [hcard]
    have hB : (B.card : ℝ) ≤ ∑ j ∈ sizes, ((highDegree H j (D j)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s:=sizes) (t:=fun j => highDegree H j (D j)))
    exact hB.trans (sum_le_sum (fun j hj => highDegree_card H j (hD j hj)))
  · intro j hj v
    by_cases hv : v ∈ U
    · have hn : v ∉ highDegree H j (D j) := by
        intro hh
        exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨j,hj,hh⟩)
      have hle : (sizeDegree H j v : ℝ) ≤ D j := by
        simpa only [highDegree, mem_filter, mem_univ, true_and, not_lt] using hn
      exact (Nat.cast_le.mpr (induced_degree_le H U j v)).trans hle
    · rw [induced_degree_zero hv j]
      simpa using (hD j hj).le

end KMV
