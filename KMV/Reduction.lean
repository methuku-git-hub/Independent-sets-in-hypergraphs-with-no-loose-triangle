module
public import KMV.RestrictedSampling
public section
namespace KMV
open Finset
open scoped Classical

@[expose] def reductionSum (r : ℕ) : ℕ := ∑ j ∈ Finset.Icc 4 r, j*(2*r)^(j-2)
@[expose] def reductionConstant (r : ℕ) : ℕ := 8*(18*r+reductionSum r+1)

theorem reductionConstant_pos (r : ℕ) : 0 < reductionConstant r := by
  unfold reductionConstant
  omega

/-- Quantitative structural reduction on the original Fin n. The alternative
large independent set is explicit, and the surviving subset loses at most n/8.
No logarithmic substitution or relabeling is built into this finite theorem. -/
theorem structural_reduction {n r : ℕ} {H : Hypergraph (Fin n)} {t : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hr : RankBounds H r) (hl : LooseTriangleFree H) :
    (∃ I : Finset (Fin n), Independent H I ∧ t ≤ (I.card : ℝ)) ∨
    ∃ K : Hypergraph (Fin n), ∃ U : Finset (Fin n),
      RankBounds K r ∧ LooseTriangleFree K ∧ Antichain K ∧
      (∀ I, I ⊆ U → Independent K I → Independent H I) ∧
      (7*(n : ℝ)/8 ≤ (U.card : ℝ)) ∧
      (∀ v, (sizeDegree K 3 v : ℝ) ≤ (reductionConstant r : ℝ)*t) ∧
      (∀ j, 4 ≤ j → j ≤ r → ∀ v, (sizeDegree K j v : ℝ) ≤ (reductionConstant r : ℝ)*n) ∧
      (∀ X : Finset (Fin n), X.card=3 → codegree K 4 X ≤ reductionConstant r) ∧
      (∀ j, 4 ≤ j → codegree K j ∅ ≤ n^2*(2*r)^(j-2)) := by
  by_cases hlarge : ∃ I : Finset (Fin n), Independent H I ∧ t ≤ (I.card : ℝ)
  · exact Or.inl hlarge
  right
  obtain ⟨J,hJr,hJl,hJa,hJI,hJc,hJe⟩ := compression hr hl
  obtain ⟨I,hI,hden⟩ := density hJr hJl
  have hIt : (I.card : ℝ) ≤ t := by
    have hn : ¬ t ≤ (I.card : ℝ) := fun h => hlarge ⟨I,hJI I hI,h⟩
    exact (lt_of_not_ge hn).le
  have hm₃ : (codegree J 3 ∅ : ℝ) ≤ 6*(r : ℝ)*n*t := by
    have hc : (codegree J 3 ∅ : ℝ) ≤ 6*(r : ℝ)*n*I.card := by
      simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using (show (codegree J 3 ∅ : ℝ) ≤
        ((6*r*Fintype.card (Fin n)*I.card : ℕ) : ℝ) by exact_mod_cast hden)
    exact hc.trans (mul_le_mul_of_nonneg_left hIt (by positivity))
  let b := reductionConstant r
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast reductionConstant_pos r
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  let D := fun j : ℕ => if j=3 then (b : ℝ)*t else (b : ℝ)*n
  let sizes := insert 3 (Finset.Icc 4 r)
  have hD : ∀ j ∈ sizes, 0 < D j := by
    intro j _
    dsimp [D]
    split_ifs <;> positivity
  obtain ⟨U,hU,hdeg⟩ := trim_degrees J sizes D hD
  have hthree : (3 : ℝ)*codegree J 3 ∅ / D 3 ≤ ((n : ℝ)/b)*(18*r) := by
    dsimp [D]
    calc
      _ ≤ (3*(6*(r : ℝ)*n*t))/((b : ℝ)*t) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm₃ (by norm_num)) (by positivity)
      _ = _ := by field_simp; ring
  have hrest : (∑ j ∈ Finset.Icc 4 r, (j : ℝ)*codegree J j ∅ / D j) ≤
      ((n : ℝ)/b)*(reductionSum r : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 4 r, ((n : ℝ)/b)*((j*(2*r)^(j-2) : ℕ) : ℝ) := by
        apply sum_le_sum
        intro j hj
        have hj4 := (mem_Icc.mp hj).1
        have hj3 : j ≠ 3 := by omega
        have hc : (codegree J j ∅ : ℝ) ≤ (n : ℝ)^2*((2*r)^(j-2) : ℕ) := by
          exact_mod_cast (by simpa only [Fintype.card_fin] using hJe j hj4)
        dsimp [D]
        rw [ite_eq_right hj3]
        calc
          _ ≤ ((j : ℝ)*((n : ℝ)^2*((2*r)^(j-2) : ℕ)))/((b : ℝ)*n) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg j)) (by positivity)
          _ = _ := by push_cast; field_simp
      _ = _ := by simp only [reductionSum,Nat.cast_sum,Nat.cast_mul,Finset.mul_sum]
  have hb : (b : ℝ) = 8*(18*(r : ℝ)+(reductionSum r : ℝ)+1) := by
    dsimp [b,reductionConstant]
    push_cast
    ring
  have hcoeff : (18*(r : ℝ)+(reductionSum r : ℝ))/(b : ℝ) ≤ 1/8 := by
    apply (div_le_iff₀ hbpos).mpr
    nlinarith
  have hcost : (∑ j ∈ sizes, (j : ℝ)*codegree J j ∅ / D j) ≤ (n : ℝ)/8 := by
    have hn3 : 3 ∉ Finset.Icc 4 r := by simp
    rw [Finset.sum_insert hn3]
    calc
      _ ≤ ((n : ℝ)/b)*(18*r) + ((n : ℝ)/b)*(reductionSum r : ℝ) := add_le_add hthree hrest
      _ = (n : ℝ)*((18*(r : ℝ)+(reductionSum r : ℝ))/(b : ℝ)) := by ring
      _ ≤ (n : ℝ)*(1/8) := mul_le_mul_of_nonneg_left hcoeff hnpos.le
      _ = _ := by ring
  have hUs : 7*(n : ℝ)/8 ≤ (U.card : ℝ) := by
    simp only [Fintype.card_fin] at hU
    have := hU.trans hcost
    linarith
  refine ⟨induced J U,U,induced_rank hJr U,induced_looseTriangleFree hJl U,
    induced_antichain hJa U,?_,hUs,?_,?_,?_,?_⟩
  · intro I hIU hI
    exact hJI I (independent_induced_transfer hIU hI)
  · intro v
    simpa [D,b] using hdeg 3 (by simp [sizes]) v
  · intro j hj4 hjr v
    have hj3 : j ≠ 3 := by omega
    simpa [D,hj3,b] using hdeg j (by simp [sizes,hj4,hjr]) v
  · intro X hX
    have hc := hJc 4 X (by omega) (by omega)
    rw [hX] at hc
    norm_num at hc
    have hb' : 2*r ≤ reductionConstant r := by unfold reductionConstant; omega
    exact (codegree_mono (filter_subset _ _) 4 X).trans (hc.trans hb')
  · intro j hj
    exact (codegree_mono (filter_subset _ _) j ∅).trans
      (by simpa only [Fintype.card_fin] using hJe j hj)

end KMV
