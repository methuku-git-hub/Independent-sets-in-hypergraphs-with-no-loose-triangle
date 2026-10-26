module
public import KMV.GraphRestriction
public section
namespace KMV
open Finset FiniteLaw
variable {V : Type*} [DecidableEq V]
open scoped Classical

@[expose] def restrictVertices (d : FiniteLaw (Finset V)) (U : Finset V) : FiniteLaw (Finset V) :=
  d.bind (fun I => .pure (I ∩ U))

theorem restrictVertices_valid {d : FiniteLaw (Finset V)} (hd : d.Valid) (U : Finset V) :
    (restrictVertices d U).Valid :=
  FiniteLaw.valid_bind hd (FiniteLaw.all_of_forall d (fun _ => trivial))

theorem restrictVertices_subset (d : FiniteLaw (Finset V)) (U : Finset V) :
    (restrictVertices d U).All (fun I => I ⊆ U) :=
  FiniteLaw.all_bind (FiniteLaw.all_true d) (fun _ _ => inter_subset_right)

theorem restrictVertices_independent {d : FiniteLaw (Finset V)} {G : V → V → Prop}
    (h : d.All (fun I => ∀ x ∈ I, ∀ y ∈ I, ¬ G x y)) (U : Finset V) :
    (restrictVertices d U).All (fun I => ∀ x ∈ I, ∀ y ∈ I, ¬ G x y) := by
  apply FiniteLaw.all_bind h
  intro I hI x hx y hy
  exact hI x (mem_inter.mp hx).1 y (mem_inter.mp hy).1

theorem restrictVertices_probability_le {d : FiniteLaw (Finset V)} (hd : d.Valid)
    (U S : Finset V) :
    (restrictVertices d U).probability (fun I => S ⊆ I) ≤ d.probability (fun I => S ⊆ I) := by
  simp only [restrictVertices,FiniteLaw.probability,FiniteLaw.expect_bind,FiniteLaw.expect]
  apply FiniteLaw.expect_mono hd (FiniteLaw.all_of_forall d ?_)
  intro I
  by_cases h : S ⊆ I ∩ U
  · simp [h,h.trans inter_subset_left]
  · simp only [h,ite_false]
    split_ifs <;> norm_num

theorem restrictVertices_marginal {d : FiniteLaw (Finset V)} {U : Finset V} {v : V} (hv : v ∈ U) :
    (restrictVertices d U).probability (fun I => v ∈ I) = d.probability (fun I => v ∈ I) := by
  simp only [restrictVertices,FiniteLaw.probability,FiniteLaw.expect_bind,FiniteLaw.expect,mem_inter,hv,and_true]
  apply FiniteLaw.expect_congr (FiniteLaw.all_of_forall d ?_)
  intro I
  by_cases h : v ∈ I <;> simp [h]

theorem restrictVertices_expected_card [Fintype V] {d : FiniteLaw (Finset V)} (hd : d.Valid)
    (U : Finset V) {m : ℝ} (hm : ∀ v ∈ U, m ≤ d.probability (fun I => v ∈ I)) :
    m*(U.card : ℝ) ≤ (restrictVertices d U).expect (fun I => (I.card : ℝ)) := by
  rw [expect_card]
  calc
    _ = ∑ _v ∈ U, m := by simp [mul_comm]
    _ ≤ ∑ v ∈ U, (restrictVertices d U).probability (fun I => v ∈ I) := by
      apply sum_le_sum
      intro v hv
      rw [restrictVertices_marginal hv]
      exact hm v hv
    _ ≤ ∑ v : V, (restrictVertices d U).probability (fun I => v ∈ I) := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ U)
      intro v _ _
      exact probability_nonneg (restrictVertices_valid hd U) _

end KMV
