module
public import KMV.TotalLoss
public section
namespace KMV
open Finset FiniteLaw
variable {V : Type*} [DecidableEq V] [Fintype V]
open scoped Classical

theorem forbiddenUnions_nonempty (H : Hypergraph V) (G : V → V → Prop) :
    ∀ e ∈ forbiddenUnions H G, e.Nonempty := by
  intro e he
  simp only [forbiddenUnions,mem_union] at he
  rcases he with ((he | he) | he) | he
  · simp only [separatedUnions,mem_biUnion] at he
    obtain ⟨i,hi,j,hj,he⟩ := he
    have hc : e.card=i+j-2 := configurationUnions_size he
    simp only [mem_insert,mem_singleton] at hi hj
    exact card_pos.mp (by omega)
  · have hc : e.card=5 := configurationUnions_size he
    exact card_pos.mp (by omega)
  · simp only [remainingTriangleUnions,mem_union,mem_biUnion] at he
    rcases he with ⟨i,hi,j,hj,he⟩ | ⟨j,hj,he⟩
    · have hc : e.card=i+j := configurationUnions_size he
      simp only [mem_insert,mem_singleton] at hi hj
      exact card_pos.mp (by omega)
    · have hc : e.card=j+3 := configurationUnions_size he
      exact card_pos.mp (by omega)
  · have hc := (mem_filter.mp he).2
    exact card_pos.mp (by omega)

theorem sizeDegree_mono {H K : Hypergraph V} (h : H ⊆ K) (j : ℕ) (v : V) :
    sizeDegree H j v ≤ sizeDegree K j v := by
  apply card_le_card
  intro e he
  exact mem_filter.mpr ⟨h (mem_filter.mp he).1,(mem_filter.mp he).2⟩

theorem degree_after_bad_removal {H : Hypergraph V} {I U : Finset V}
    (hUI : U ⊆ I) (j : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hd : Disjoint U (highDegree (induced H I) j D)) :
    ∀ v, (sizeDegree (induced H U) j v : ℝ) ≤ D := by
  intro v
  by_cases hv : v ∈ U
  · have hn : v ∉ highDegree (induced H I) j D := fun h => Finset.disjoint_left.mp hd hv h
    have hb : (sizeDegree (induced H I) j v : ℝ) ≤ D := by
      simpa only [highDegree,mem_filter,mem_univ,true_and,not_lt] using hn
    have hs : induced H U ⊆ induced H I := by
      intro e he
      exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.trans hUI⟩
    exact (Nat.cast_le.mpr (sizeDegree_mono hs j v)).trans hb
  · rw [induced_degree_zero hv j]
    simpa using hD

/-- The complete finite cleaning argument, with an explicit cost expression.
All analytic parameter choices remain outside this theorem. P can retain the
initial surviving-set constraint from the structural reduction. -/
theorem finite_cleaning {d : FiniteLaw (Finset V)} (hd : d.Valid)
    {H : Hypergraph V} {G : V → V → Prop} {r B : ℕ} {Δ M : ℕ → ℕ} {p β D₃ D₄ : ℝ}
    (hr : RankBounds H r) (ha : Antichain H) (hl : LooseTriangleFree H)
    (hp : 0 ≤ p) (hβ : 0 ≤ β) (hD₃ : 0 < D₃) (hD₄ : 0 < D₄)
    (hdegree : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, sizeDegree H j v ≤ Δ j)
    (hpair : ∀ j ∈ ({3,4} : Finset ℕ), ∀ X : Finset V, X.card=2 → codegree H j X ≤ M j)
    (htr : ∀ X : Finset V, X.card=3 → codegree H 4 X ≤ B)
    (hsepEdges : ∀ e ∈ H, (∀ x ∈ e, ∀ y ∈ e, ¬ G x y) → Separated G e)
    (hsep : ∀ S, Separated G S → d.probability (fun I => S ⊆ I) ≤ p^S.card)
    (hcap : ∀ S : Finset V, d.probability (fun I => S ⊆ I) ≤ β^S.card)
    (hind : d.All (fun I => ∀ x ∈ I, ∀ y ∈ I, ¬ G x y))
    {P : Finset V → Prop} (hP : d.All P) :
    ∃ I U : Finset V, P I ∧ U ⊆ I ∧ RankBounds (induced H U) 4 ∧ TriangleFree (induced H U) ∧
      (∀ v, (sizeDegree (induced H U) 3 v : ℝ) ≤ D₃) ∧
      (∀ v, (sizeDegree (induced H U) 4 v : ℝ) ≤ D₄) ∧
      d.expect (fun I => (I.card : ℝ)) - configurationCost H r Δ M B p β -
        (3*(codegree H 3 ∅ : ℝ)*p^3/D₃ + 4*(codegree H 4 ∅ : ℝ)*p^4/D₄) ≤ (U.card : ℝ) := by
  let R := fun I => highDegree (induced H I) 3 D₃ ∪ highDegree (induced H I) 4 D₄
  have hedge : ∀ e ∈ H, d.probability (fun I => e ⊆ I) ≤ p^e.card :=
    fun e he => edge_survival_bound hp hind hsepEdges hsep he
  have hcost := forbidden_loss hd hr hp hβ hdegree hpair htr hsep hcap hedge
  have hbad₃ := expected_highDegree hd hD₃ hedge 3
  have hbad₄ := expected_highDegree hd hD₄ hedge 4
  have hR : d.expect (fun I => ((R I).card : ℝ)) ≤
      3*(codegree H 3 ∅ : ℝ)*p^3/D₃ + 4*(codegree H 4 ∅ : ℝ)*p^4/D₄ := by
    have hm : d.expect (fun I => ((R I).card : ℝ)) ≤
        d.expect (fun I => ((highDegree (induced H I) 3 D₃).card : ℝ)) +
        d.expect (fun I => ((highDegree (induced H I) 4 D₄).card : ℝ)) := by
      rw [← FiniteLaw.expect_add]
      apply FiniteLaw.expect_mono hd (FiniteLaw.all_of_forall d ?_)
      intro I
      exact_mod_cast Finset.card_union_le (highDegree (induced H I) 3 D₃) (highDegree (induced H I) 4 D₄)
    norm_num at hbad₃ hbad₄
    exact hm.trans (add_le_add hbad₃ hbad₄)
  obtain ⟨I,U,hPI,hUI,hUR,hBU,hsize⟩ := exists_after_deletions_with_bad_vertices d hd
    (forbiddenUnions H G) (forbiddenUnions_nonempty H G) R (FiniteLaw.all_and hP hind)
  have hGU : ∀ x ∈ U, ∀ y ∈ U, ¬ G x y := fun x hx y hy => hPI.2 x (hUI hx) y (hUI hy)
  have hclean := cleaned_triangleFree hr ha hl hsepEdges hGU hBU
  refine ⟨I,U,hPI.1,hUI,hclean.1,hclean.2,?_,?_,?_⟩
  · apply degree_after_bad_removal hUI 3 hD₃.le
    exact Finset.disjoint_left.mpr (fun v hv hh => Finset.disjoint_left.mp hUR hv (mem_union_left _ hh))
  · apply degree_after_bad_removal hUI 4 hD₄.le
    exact Finset.disjoint_left.mpr (fun v hv hh => Finset.disjoint_left.mp hUR hv (mem_union_right _ hh))
  · change d.expect (fun I => (I.card : ℝ)) - expectedPresent d (forbiddenUnions H G) -
        d.expect (fun I => ((R I).card : ℝ)) ≤ (U.card : ℝ) at hsize
    linarith

end KMV
