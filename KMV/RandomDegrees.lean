module
public import KMV.IntersectionCounting
public section
namespace KMV
open Finset FiniteLaw
variable {V : Type*} [DecidableEq V]
open scoped Classical

theorem probability_zero_of_all_not {α : Type*} {d : FiniteLaw α} {P : α → Prop}
    (h : d.All (fun x => ¬ P x)) : d.probability P = 0 := by
  unfold FiniteLaw.probability
  calc
    _ = d.expect (fun _ => 0) :=
      FiniteLaw.expect_congr (FiniteLaw.all_mono h (fun _ hx => by simp [hx]))
    _ = 0 := FiniteLaw.expect_const _ _

theorem edge_survival_bound {d : FiniteLaw (Finset V)} {G : V → V → Prop}
    {H : Hypergraph V} {p : ℝ} (hp : 0 ≤ p)
    (hind : d.All (fun I => ∀ x ∈ I, ∀ y ∈ I, ¬ G x y))
    (hsep : ∀ e ∈ H, (∀ x ∈ e, ∀ y ∈ e, ¬ G x y) → Separated G e)
    (hprob : ∀ S, Separated G S → d.probability (fun I => S ⊆ I) ≤ p^S.card)
    {e : Finset V} (he : e ∈ H) : d.probability (fun I => e ⊆ I) ≤ p^e.card := by
  by_cases h : ∀ x ∈ e, ∀ y ∈ e, ¬ G x y
  · exact hprob e (hsep e he h)
  · have hz : d.probability (fun I => e ⊆ I) = 0 := by
      apply probability_zero_of_all_not
      apply FiniteLaw.all_mono hind
      intro I hI heI
      exact h (fun x hx y hy => hI x (heI hx) y (heI hy))
    rw [hz]
    exact pow_nonneg hp _

theorem expected_induced_edges {d : FiniteLaw (Finset V)} {H : Hypergraph V} {p : ℝ}
    (hprob : ∀ e ∈ H, d.probability (fun I => e ⊆ I) ≤ p^e.card) (j : ℕ) :
    d.expect (fun I => (codegree (induced H I) j ∅ : ℝ)) ≤ (codegree H j ∅ : ℝ)*p^j := by
  have he : ∀ I : Finset V, containingEdges (induced H I) j ∅ =
      (containingEdges H j ∅).filter (fun e => e ⊆ I) := by
    intro I
    ext e
    simp only [containingEdges,induced,mem_filter,empty_subset,true_and,and_true]
    tauto
  simp_rw [codegree,he]
  rw [expect_forbidden_count]
  calc
    _ ≤ ∑ _e ∈ containingEdges H j ∅, p^j := by
      apply sum_le_sum
      intro e he
      have hm := mem_filter.mp he
      simpa only [hm.2.1] using hprob e hm.1
    _ = ((containingEdges H j ∅).card : ℝ)*p^j := by simp

theorem expected_highDegree [Fintype V] {d : FiniteLaw (Finset V)} (hd : d.Valid)
    {H : Hypergraph V} {p D : ℝ} (hD : 0 < D)
    (hprob : ∀ e ∈ H, d.probability (fun I => e ⊆ I) ≤ p^e.card) (j : ℕ) :
    d.expect (fun I => ((highDegree (induced H I) j D).card : ℝ)) ≤
      (j : ℝ)*(codegree H j ∅ : ℝ)*p^j/D := by
  have hm := FiniteLaw.expect_mono hd (FiniteLaw.all_of_forall d (fun I =>
    highDegree_card (induced H I) j hD))
  have he : d.expect (fun I => (j : ℝ)*(codegree (induced H I) j ∅ : ℝ)/D) =
      d.expect (fun I => (codegree (induced H I) j ∅ : ℝ)) * ((j : ℝ)/D) := by
    have hf : (fun I : Finset V => (j : ℝ)*(codegree (induced H I) j ∅ : ℝ)/D) =
        (fun I => (codegree (induced H I) j ∅ : ℝ)*((j : ℝ)/D)) := by funext I; ring
    rw [hf,FiniteLaw.expect_mul_const]
  rw [he] at hm
  have hb := mul_le_mul_of_nonneg_right (expected_induced_edges hprob j)
    (div_nonneg (Nat.cast_nonneg j) hD.le)
  calc
    _ ≤ (codegree H j ∅ : ℝ)*p^j*((j : ℝ)/D) := hm.trans hb
    _ = _ := by ring

theorem exists_after_deletions_with_bad_vertices (d : FiniteLaw (Finset V))
    (hd : d.Valid) (B : Hypergraph V) (hne : ∀ e ∈ B, e.Nonempty)
    (R : Finset V → Finset V) {P : Finset V → Prop} (hP : d.All P) :
    ∃ I J : Finset V, P I ∧ J ⊆ I ∧ Disjoint J (R I) ∧ Independent B J ∧
      d.expect (fun I => (I.card : ℝ)) -
        d.expect (fun I => ((B.filter (fun e => e ⊆ I)).card : ℝ)) -
        d.expect (fun I => ((R I).card : ℝ)) ≤ (J.card : ℝ) := by
  obtain ⟨I,hPI,hI⟩ := FiniteLaw.exists_ge_of_all hd hP
    (fun I => (I.card : ℝ) - ((B.filter (fun e => e ⊆ I)).card : ℝ) - ((R I).card : ℝ))
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_sub] at hI
  obtain ⟨J,hJ,hBJ,hcard⟩ := delete_forbidden_sets B (I \ R I) hne
  have hcount : (B.filter (fun e => e ⊆ I \ R I)).card ≤ (B.filter (fun e => e ⊆ I)).card := by
    apply card_le_card
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.trans sdiff_subset⟩
  have hsum : I.card ≤ (I \ R I).card + (R I).card := by
    rw [card_sdiff_add_card]
    exact card_le_card subset_union_left
  have hall : I.card ≤ J.card + (B.filter (fun e => e ⊆ I)).card + (R I).card := by omega
  have hreal : (I.card : ℝ) ≤ (J.card : ℝ) + ((B.filter (fun e => e ⊆ I)).card : ℝ) + (R I).card := by
    exact_mod_cast hall
  refine ⟨I,J,hPI,hJ.trans sdiff_subset,?_,hBJ,by linarith⟩
  exact Finset.disjoint_left.mpr (fun x hx hR => (mem_sdiff.mp (hJ hx)).2 hR)

end KMV
