module
public import KMV.Sampling
public import KMV.Density
public section
namespace KMV
open Finset FiniteLaw
variable {V : Type*} [DecidableEq V]

/-- Delete one representative from each forbidden set present in I. -/
theorem delete_forbidden_sets (B : Hypergraph V) (I : Finset V)
    (hne : ∀ e ∈ B, e.Nonempty) :
    ∃ J : Finset V, J ⊆ I ∧ Independent B J ∧
      I.card ≤ J.card + (B.filter (fun e => e ⊆ I)).card := by
  classical
  let F := B.filter (fun e => e ⊆ I)
  let f : {e // e ∈ F} → V := fun e => (hne e.val (mem_filter.mp e.property).1).choose
  have hf : ∀ e, f e ∈ e.val := fun e => (hne e.val (mem_filter.mp e.property).1).choose_spec
  let R := F.attach.image f
  have hR : R ⊆ I := by
    intro x hx
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp e.property).2 (hf e)
  refine ⟨I \ R,sdiff_subset,?_,?_⟩
  · intro e he heJ
    have heI : e ⊆ I := heJ.trans sdiff_subset
    have heF : e ∈ F := mem_filter.mpr ⟨he,heI⟩
    have hx := heJ (hf ⟨e,heF⟩)
    exact (mem_sdiff.mp hx).2 (mem_image.mpr ⟨⟨e,heF⟩,by simp,rfl⟩)
  · have hRc : R.card ≤ F.card := by
      exact card_image_le.trans (card_attach.le)
    have hcard := card_sdiff_add_card_eq_card hR
    change I.card ≤ (I \ R).card + F.card
    omega

theorem expect_card [Fintype V] (d : FiniteLaw (Finset V)) :
    d.expect (fun I => (I.card : ℝ)) = ∑ v : V, d.probability (fun I => v ∈ I) := by
  classical
  have hc : ∀ I : Finset V, (I.card : ℝ) = ∑ v : V, if v ∈ I then (1:ℝ) else 0 := by
    intro I
    simp only [← Finset.sum_filter]
    have he : Finset.univ.filter (fun v => v ∈ I) = I := by ext v; simp
    simp [he]
  simp_rw [hc]
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_congr rfl
  intro v _
  unfold FiniteLaw.probability
  apply FiniteLaw.expect_congr (FiniteLaw.all_of_forall d ?_)
  intro I
  by_cases h : v ∈ I <;> simp [h]

theorem expect_forbidden_count (d : FiniteLaw (Finset V)) (B : Hypergraph V) :
    d.expect (fun I => ((B.filter (fun e => e ⊆ I)).card : ℝ)) =
      ∑ e ∈ B, d.probability (fun I => e ⊆ I) := by
  classical
  have hc : ∀ I : Finset V, ((B.filter (fun e => e ⊆ I)).card : ℝ) =
      ∑ e ∈ B, if e ⊆ I then (1:ℝ) else 0 := by
    intro I
    simp only [← Finset.sum_filter]
    simp
  simp_rw [hc]
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_congr rfl
  intro e _
  unfold FiniteLaw.probability
  apply FiniteLaw.expect_congr (FiniteLaw.all_of_forall d ?_)
  intro I
  by_cases h : e ⊆ I <;> simp [h]

/-- An expectation argument produces a concrete outcome after deletions.
The predicate P can carry graph independence and further deterministic facts. -/
theorem exists_after_deletions [Fintype V] (d : FiniteLaw (Finset V))
    (hd : d.Valid) (B : Hypergraph V) (hne : ∀ e ∈ B, e.Nonempty)
    {P : Finset V → Prop} (hP : d.All P) :
    ∃ I J : Finset V, P I ∧ J ⊆ I ∧ Independent B J ∧
      (∑ v : V, d.probability (fun I => v ∈ I)) -
        (∑ e ∈ B, d.probability (fun I => e ⊆ I)) ≤ (J.card : ℝ) := by
  classical
  obtain ⟨I,hPI,hI⟩ := FiniteLaw.exists_ge_of_all hd hP
    (fun I => (I.card : ℝ) - ((B.filter (fun e => e ⊆ I)).card : ℝ))
  rw [FiniteLaw.expect_sub, expect_card, expect_forbidden_count] at hI
  obtain ⟨J,hJI,hBJ,hcard⟩ := delete_forbidden_sets B I hne
  have hcast : (I.card : ℝ) ≤ (J.card : ℝ) + ((B.filter (fun e => e ⊆ I)).card : ℝ) := by
    exact_mod_cast hcard
  exact ⟨I,J,hPI,hJI,hBJ,by linarith⟩

end KMV
