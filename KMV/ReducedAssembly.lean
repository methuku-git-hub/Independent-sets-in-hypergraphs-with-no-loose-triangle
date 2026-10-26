module
public import KMV.AssemblyBounds
public section
namespace KMV
open Finset
open scoped Classical

/-- All scalar estimates have explicit finite interfaces; this theorem
instantiates the sampler, including the natural rounding in candidate counts. -/
theorem parameter_cleaning {n r B : ℕ} {H : Hypergraph (Fin n)} {U₀ : Finset (Fin n)}
    (hB : 0 < B) (hr : RankBounds H r) (ha : Antichain H) (hl : LooseTriangleFree H)
    (hU₀ : 7*(n : ℝ)/8 ≤ (U₀.card : ℝ))
    (hdegree : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, (sizeDegree H j v : ℝ) ≤ initialDegree B n j)
    (htr : ∀ X : Finset (Fin n), X.card=3 → codegree H 4 X ≤ B)
    (hhigh : ∀ j, 4 ≤ j → codegree H j ∅ ≤ n^2*(2*r)^(j-2))
    (hx : 0 < (n : ℝ) ∧ 1 < Real.log (n : ℝ)) (hn1 : 1 ≤ (n : ℝ))
    (hQ : 1 ≤ Real.log (Real.log (n : ℝ))) (ht1 : 1 ≤ targetSize n)
    (hL₃ : max 1 ((2*r : ℕ) : ℝ) ≤ pairThreshold n 3)
    (hL₄ : max 1 ((2*r*B : ℕ) : ℝ) ≤ pairThreshold n 4)
    (hp : 0 < sampleP n) (hpβ : sampleP n < sampleCap n) (hβ : sampleCap n ≤ 1/2)
    (hlog : 1 < Real.log (sampleCap n/sampleP n))
    (hent : 2*graphDegreeEnvelope B n*(sampleP n)^2/(Real.log (sampleCap n/sampleP n)-1) ≤ sampleP n/2)
    (hloss : lossEnvelope n r (degreeEnvelope B n) (pairEnvelope n) B (sampleP n) (sampleCap n) ≤ sampleP n*n/8) :
    ∃ U : Finset (Fin n), U ⊆ U₀ ∧ RankBounds (induced H U) 4 ∧ TriangleFree (induced H U) ∧
      (∀ v, (sizeDegree (induced H U) 3 v : ℝ) ≤ finalDegree B n 3) ∧
      (∀ v, (sizeDegree (induced H U) 4 v : ℝ) ≤ finalDegree B n 4) ∧ sampleP n*n/4 ≤ (U.card : ℝ) := by
  let Δ := roundedDegree B (n : ℝ)
  let M := roundedPair (n : ℝ)
  let G := thresholdGraph H (pairThreshold n 3) (pairThreshold n 4)
  let K := avoidGraph H G
  have hKH : K ⊆ H := avoidGraph_subset H G
  have hL₃1 : 1 ≤ pairThreshold n 3 := (le_max_left _ _).trans hL₃
  have hL₄1 : 1 ≤ pairThreshold n 4 := (le_max_left _ _).trans hL₄
  have hΔ : ∀ j, (Δ j : ℝ) ≤ degreeEnvelope B n j := rounded_degree_bound hB hn1 ht1
  have hM : ∀ j, (M j : ℝ) ≤ pairEnvelope n j := by
    intro j
    have hL : 1 ≤ pairThreshold n j := by
      by_cases hj : j=3
      · simpa only [hj] using hL₃1
      · simpa only [pairThreshold,hj,ite_false,show (4:ℕ) ≠ 3 by decide] using hL₄1
    exact ceil_le_twice hL
  have hdegNat : ∀ j ∈ ({3,4} : Finset ℕ), ∀ v, sizeDegree H j v ≤ Δ j := by
    intro j hj v
    exact Nat.cast_le.mp ((hdegree j hj v).trans (Nat.le_ceil _))
  have hd0 : ∀ j, 0 ≤ degreeEnvelope B n j := fun j => (Nat.cast_nonneg (Δ j)).trans (hΔ j)
  have hm0 : ∀ j, 0 ≤ pairEnvelope n j := fun j => (Nat.cast_nonneg (M j)).trans (hM j)
  have hcount : ∀ j ∈ ({3,4} : Finset ℕ), (codegree K j ∅ : ℝ) ≤ n*degreeEnvelope B n j := by
    intro j hj
    have hj1 : 1 ≤ j := by simp only [mem_insert,mem_singleton] at hj; omega
    apply edge_count_degree_bound hj1
    intro v
    exact (Nat.cast_le.mpr ((sizeDegree_mono hKH j v).trans (hdegNat j hj v))).trans (hΔ j)
  have hcost : configurationCost K r Δ M B (sampleP n) (sampleCap n) ≤ sampleP n*n/8 := by
    apply le_trans _ hloss
    exact configurationCost_le_envelope hp.le (hp.trans hpβ).le hd0 hm0
      (fun j _ => hΔ j) (fun j _ => hM j) hcount
      (fun j hj _ => (codegree_mono hKH j ∅).trans (hhigh j (by omega)))
  have hA : 2*(Δ 3 : ℝ)/pairThreshold n 3 + 3*(Δ 4 : ℝ)/pairThreshold n 4 ≤ graphDegreeEnvelope B n := by
    apply le_trans _ (graph_degree_envelope hx hQ B)
    gcongr
    · exact hΔ 3
    · exact hΔ 4
  have hD := final_degree_log_bounds hx hQ hB
  exact sampling_cleaning hr ha hl hU₀ hdegNat htr
    (by linarith) (by linarith)
    ((le_max_right _ _).trans hL₃) ((le_max_right _ _).trans hL₄)
    (Nat.le_ceil _) (Nat.le_ceil _) hp hpβ hβ hlog hA hent
    (by have := (hD 3 (by simp)).1; linarith) (by have := (hD 4 (by simp)).1; linarith)
    hcost (trim_loss_bound hB hx hdegree)

end KMV
