module
public import KMV.Reduction
public import KMV.Sampling
public import KMV.ColoringSubset
public section
namespace KMV
open Finset FiniteLaw
open scoped Classical

/-- Sampling and all deletions on the retained subset, followed by exact
transfer from graph-avoiding edges back to the original induced hypergraph. -/
theorem sampling_cleaning {n r B : ℕ} {H : Hypergraph (Fin n)} {U₀ : Finset (Fin n)}
    {Δ M : ℕ → ℕ} {L₃ L₄ p β A D₃ D₄ : ℝ}
    (hr : RankBounds H r) (ha : Antichain H) (hl : LooseTriangleFree H)
    (hU₀ : 7*(n : ℝ)/8 ≤ (U₀.card : ℝ))
    (hdegree : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, sizeDegree H j v ≤ Δ j)
    (htr : ∀ X : Finset (Fin n), X.card=3 → codegree H 4 X ≤ B)
    (hL₃ : 0 < L₃) (hL₄ : 0 < L₄)
    (h₃ : ((2*r : ℕ) : ℝ) ≤ L₃) (h₄ : ((2*r*B : ℕ) : ℝ) ≤ L₄)
    (hM₃ : L₃ ≤ (M 3 : ℝ)) (hM₄ : L₄ ≤ (M 4 : ℝ))
    (hp : 0 < p) (hpβ : p < β) (hβ : β ≤ 1/2) (hlog : 1 < Real.log (β/p))
    (hA : 2*(Δ 3 : ℝ)/L₃ + 3*(Δ 4 : ℝ)/L₄ ≤ A)
    (hentropy : 2*A*p^2/(Real.log (β/p)-1) ≤ p/2)
    (hD₃ : 0 < D₃) (hD₄ : 0 < D₄)
    (hcost : configurationCost (avoidGraph H (thresholdGraph H L₃ L₄)) r Δ M B p β ≤ p*n/8)
    (htrim : 3*(codegree H 3 ∅ : ℝ)*p^3/D₃ + 4*(codegree H 4 ∅ : ℝ)*p^4/D₄ ≤ p*n/16) :
    ∃ U : Finset (Fin n), U ⊆ U₀ ∧ RankBounds (induced H U) 4 ∧ TriangleFree (induced H U) ∧
      (∀ v, (sizeDegree (induced H U) 3 v : ℝ) ≤ D₃) ∧
      (∀ v, (sizeDegree (induced H U) 4 v : ℝ) ≤ D₄) ∧ p*n/4 ≤ (U.card : ℝ) := by
  let G := thresholdGraph H L₃ L₄
  let K := avoidGraph H G
  have hKH : K ⊆ H := avoidGraph_subset H G
  obtain ⟨htri,hgd,hse⟩ := auxiliary_graph hr hl h₃ h₄ hL₃ hL₄ htr
  have hgd' : ∀ v, ((Sampling.earlierNeighbors G v n).card : ℝ) ≤ A := by
    intro v
    have hs : Sampling.earlierNeighbors G v n ⊆ univ.filter (G v) := by
      intro x hx
      have hh := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_univ _,thresholdGraph_symm H L₃ L₄ x v hh.2.2⟩
    apply (Nat.cast_le.mpr (card_le_card hs)).trans
    apply (hgd v).trans
    apply le_trans _ hA
    apply add_le_add
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hdegree 3 (by simp) v)) (by norm_num)) hL₃.le
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hdegree 4 (by simp) v)) (by norm_num)) hL₄.le
  obtain ⟨d,hd,hdi,hm,hs,hc⟩ := sampling
    (thresholdGraph_symm H L₃ L₄) (thresholdGraph_irrefl H L₃ L₄) htri hβ hp hpβ hlog hgd'
  let d' := restrictVertices d U₀
  have hd' : d'.Valid := restrictVertices_valid hd U₀
  have hdi' : d'.All (fun I => ∀ x ∈ I, ∀ y ∈ I, ¬ G x y) := restrictVertices_independent hdi U₀
  have hmass : 7*p*n/16 ≤ d'.expect (fun I => (I.card : ℝ)) := by
    have he := restrictVertices_expected_card hd U₀ (m:=p/2)
      (fun v _ => by have hv := (hm v).1; linarith)
    have hu := mul_le_mul_of_nonneg_left hU₀ (by positivity : 0 ≤ p/2)
    dsimp [d']
    nlinarith
  have hKr : RankBounds K r := fun e he => hr e (hKH he)
  have hKa : Antichain K := fun e he f hf => ha e (hKH he) f (hKH hf)
  have hKl : LooseTriangleFree K := fun e he f hf g hg => hl e (hKH he) f (hKH hf) g (hKH hg)
  have hkdeg : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, sizeDegree K j v ≤ Δ j :=
    fun j hj v => (sizeDegree_mono hKH j v).trans (hdegree j hj v)
  have hkpair : ∀ j ∈ ({3,4} : Finset ℕ), ∀ X : Finset (Fin n), X.card=2 → codegree K j X ≤ M j := by
    intro j hj X hX
    have hh := avoidThreshold_codegrees (H:=H) hL₃.le hL₄.le hX
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact_mod_cast hh.1.trans hM₃
    · exact_mod_cast hh.2.trans hM₄
  have hktr : ∀ X : Finset (Fin n), X.card=3 → codegree K 4 X ≤ B :=
    fun X hX => (codegree_mono hKH 4 X).trans (htr X hX)
  obtain ⟨I,U,hI,hUI,hUr,hUt,hUd₃,hUd₄,hsize⟩ := finite_cleaning hd' hKr hKa hKl
    hp.le (hp.trans hpβ).le hD₃ hD₄ hkdeg hkpair hktr
    (fun e he => hse e (hKH he))
    (fun S hS => (restrictVertices_probability_le hd U₀ S).trans (hs S hS))
    (fun S => (restrictVertices_probability_le hd U₀ S).trans (hc S)) hdi'
    (FiniteLaw.all_and (restrictVertices_subset d U₀) hdi')
  have hGU : ∀ x ∈ U, ∀ y ∈ U, ¬ G x y := fun x hx y hy => hI.2 x (hUI hx) y (hUI hy)
  have heq : induced K U = induced H U := induced_avoidGraph_eq hGU
  rw [heq] at hUr hUt hUd₃ hUd₄
  refine ⟨U,hUI.trans hI.1,hUr,hUt,hUd₃,hUd₄,?_⟩
  have htrim' : 3*(codegree K 3 ∅ : ℝ)*p^3/D₃ + 4*(codegree K 4 ∅ : ℝ)*p^4/D₄ ≤ p*n/16 := by
    apply le_trans _ htrim
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hD₃.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (codegree_mono hKH 3 ∅)) (by norm_num)) (by positivity)
    · apply div_le_div_of_nonneg_right _ hD₄.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (codegree_mono hKH 4 ∅)) (by norm_num)) (by positivity)
  change configurationCost K r Δ M B p β ≤ _ at hcost
  linarith

end KMV
