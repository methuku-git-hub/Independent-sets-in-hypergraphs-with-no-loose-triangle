module
public import KMV.SamplingCleaning
public import KMV.Scales
public import Mathlib.Algebra.Order.Floor.Semiring
public section
namespace KMV
open Finset
open scoped Classical

/-- Degree counting in real upper bounds, avoiding rounding in edge counts. -/
theorem edge_count_degree_bound {n j : ℕ} {H : Hypergraph (Fin n)} {d : ℝ}
    (hj : 1 ≤ j) (hd : ∀ v, (sizeDegree H j v : ℝ) ≤ d) :
    (codegree H j ∅ : ℝ) ≤ n*d := by
  have hs : (∑ v : Fin n, (sizeDegree H j v : ℝ)) ≤ n*d := by
    simpa using sum_le_sum (s:=univ) (fun v _ => hd v)
  have he : (∑ v : Fin n, (sizeDegree H j v : ℝ)) = (j : ℝ)*codegree H j ∅ := by
    exact_mod_cast sum_sizeDegree H j
  rw [he] at hs
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm : 0 ≤ (codegree H j ∅ : ℝ) := Nat.cast_nonneg _
  nlinarith

@[expose] noncomputable def lossEnvelope (n r : ℕ) (d m : ℕ → ℝ) (B : ℕ) (p β : ℝ) : ℝ :=
  (∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
    (i.choose 2 : ℝ)*n*d i*m j*p^(i+j-2)) +
  4*n*d 4*B*β^5 +
  ((∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
    256*B*n*d i*d j*β^(i+j)) +
   (∑ j ∈ ({3,4} : Finset ℕ), n*d j*(1024*m 4*B)*β^(j+3))) +
  (∑ j ∈ Finset.Icc 5 r, (n : ℝ)^2*((2*r)^(j-2) : ℕ)*p^j)

theorem configurationCost_le_envelope {n r B : ℕ} {H : Hypergraph (Fin n)}
    {Δ M : ℕ → ℕ} {d m : ℕ → ℝ} {p β : ℝ} (hp : 0 ≤ p) (hβ : 0 ≤ β)
    (hd0 : ∀ j, 0 ≤ d j) (hm0 : ∀ j, 0 ≤ m j)
    (hΔ : ∀ j ∈ ({3,4} : Finset ℕ), (Δ j : ℝ) ≤ d j)
    (hM : ∀ j ∈ ({3,4} : Finset ℕ), (M j : ℝ) ≤ m j)
    (hcount : ∀ j ∈ ({3,4} : Finset ℕ), (codegree H j ∅ : ℝ) ≤ n*d j)
    (hhigh : ∀ j, 5 ≤ j → j ≤ r → codegree H j ∅ ≤ n^2*(2*r)^(j-2)) :
    configurationCost H r Δ M B p β ≤ lossEnvelope n r d m B p β := by
  have h₁ : (∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
      ((i.choose 2*codegree H i ∅*M j : ℕ) : ℝ)*p^(i+j-2)) ≤
      ∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
        (i.choose 2 : ℝ)*n*d i*m j*p^(i+j-2) := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have hdj := hd0 j
    have hm4 := hm0 4
    push_cast
    calc
      _ ≤ (i.choose 2 : ℝ)*(n*d i)*m j*p^(i+j-2) := by
        have hdi := hd0 i
        have hmj := hm0 j
        gcongr
        · exact hcount i hi
        · exact hM j hj
      _ = _ := by ring
  have h₂ : ((4*codegree H 4 ∅*B : ℕ) : ℝ)*β^5 ≤ 4*n*d 4*B*β^5 := by
    push_cast
    calc
      _ ≤ 4*(n*d 4)*B*β^5 := by gcongr; exact hcount 4 (by simp)
      _ = _ := by ring
  have h₃ : (∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ),
      ((256*B*Fintype.card (Fin n)*Δ i*Δ j : ℕ) : ℝ)*β^(i+j)) ≤
      ∑ i ∈ ({3,4} : Finset ℕ), ∑ j ∈ ({3,4} : Finset ℕ), 256*B*n*d i*d j*β^(i+j) := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    have hdi := hd0 i
    gcongr
    · exact hΔ i hi
    · exact hΔ j hj
  have h₄ : (∑ j ∈ ({3,4} : Finset ℕ), ((codegree H j ∅*(1024*M 4*B) : ℕ) : ℝ)*β^(j+3)) ≤
      ∑ j ∈ ({3,4} : Finset ℕ), n*d j*(1024*m 4*B)*β^(j+3) := by
    apply sum_le_sum
    intro j hj
    have hdj := hd0 j
    have hm4 := hm0 4
    push_cast
    gcongr
    · exact hcount j hj
    · exact hM 4 (by simp)
  have h₅ : (∑ j ∈ Finset.Icc 5 r, (codegree H j ∅ : ℝ)*p^j) ≤
      ∑ j ∈ Finset.Icc 5 r, (n : ℝ)^2*((2*r)^(j-2) : ℕ)*p^j := by
    apply sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast hhigh j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  exact add_le_add (add_le_add (add_le_add h₁ h₂) (add_le_add h₃ h₄)) h₅

end KMV
