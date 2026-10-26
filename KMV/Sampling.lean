module
public import KMV.SamplingMarginals
public section
namespace KMV
open Finset FiniteLaw

/-- Manuscript Lemma 3.1, represented by an explicit finite probability tree
of subsets. Every leaf is independent, including leaves of probability zero.
The real degree bound A and all three probability bounds are explicit. -/
theorem sampling {n : ℕ} {G : Fin n → Fin n → Prop} {β p A : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (htri : ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a))
    (hβ : β ≤ 1/2) (hp : 0 < p) (hpβ : p < β) (hlog : 1 < Real.log (β/p))
    (hdeg : ∀ v, ((Sampling.earlierNeighbors G v n).card : ℝ) ≤ A) :
    ∃ d : FiniteLaw (Finset (Fin n)), d.Valid ∧
      d.All (fun I => ∀ u ∈ I, ∀ v ∈ I, ¬ G u v) ∧
      (∀ v, p - 2*A*p^2/(Real.log (β/p)-1) ≤ d.probability (fun I => v ∈ I) ∧
        d.probability (fun I => v ∈ I) ≤ p) ∧
      (∀ S, Separated G S → d.probability (fun I => S ⊆ I) ≤ p^S.card) ∧
      (∀ S, d.probability (fun I => S ⊆ I) ≤ β^S.card) := by
  classical
  have hp1 : p < 1 := by linarith
  let d := (Sampling.run G β p n).bind (fun w => FiniteLaw.pure (Sampling.selected w))
  refine ⟨d, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteLaw.valid_bind (Sampling.run_valid hβ n)
      (FiniteLaw.all_of_forall _ (fun _ => trivial))
  · exact FiniteLaw.all_bind (Sampling.run_independent hsym hirr hβ hp.le hp1)
      (fun _ hw => hw)
  · intro v
    simpa [d, FiniteLaw.probability, FiniteLaw.expect_bind, FiniteLaw.expect, Sampling.selected]
      using Sampling.marginal_bounds hsym hirr htri hβ hp hpβ hlog v (hdeg v)
  · intro S hS
    simpa [d, FiniteLaw.probability, FiniteLaw.expect_bind, FiniteLaw.expect]
      using Sampling.separated_inclusion hsym hβ hp.le hp1 S hS
  · intro S
    simpa [d, FiniteLaw.probability, FiniteLaw.expect_bind, FiniteLaw.expect]
      using Sampling.universal_inclusion (G:=G) hβ (hp.trans hpβ).le hp.le hp1 S

end KMV
