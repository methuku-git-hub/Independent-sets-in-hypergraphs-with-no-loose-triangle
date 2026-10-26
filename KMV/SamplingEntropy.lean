module
public import KMV.SamplingCap
public section
namespace KMV.Sampling
open FiniteLaw Finset
variable {n : ℕ}
open scoped Classical

theorem step_entropy_le {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hβ : β ≤ 1/2) (hp : 0 < p) (i v : Fin n) (hiv : i.val < v.val)
    (w : Fin n → ℝ) (hw : ∀ v, 0 ≤ w v) :
    (step G β i w).expect (fun w => entropy p (w v)) ≤
      entropy p (w v) + (if G i v then w i * w v * 2 else 0) := by
  classical
  have hv : v ≠ i := by intro h; subst v; omega
  have hprod : 0 ≤ w i * w v * 2 := mul_nonneg (mul_nonneg (hw i) (hw v)) (by norm_num)
  by_cases ha : Active β (w i)
  · rw [step, ite_eq_left ha]
    dsimp [FiniteLaw.expect]
    by_cases hG : G i v
    · by_cases hb : w v < β
      · simpa [next, hv, hiv, hG, hb, mul_assoc, mul_comm, mul_left_comm] using
          entropy_update_le hp ha.1.le (ha.2.le.trans hβ) (hw v)
      · simp [next, hv, hb, hG]
        nlinarith
    · simp [next, hv, hG]
      ring_nf
      exact le_refl _
  · rw [step, ite_eq_right ha]
    dsimp [FiniteLaw.expect]
    split_ifs <;> linarith

@[expose] noncomputable def earlierNeighbors (G : Fin n → Fin n → Prop)
    (v : Fin n) (t : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun i => i.val < t ∧ G i v)

theorem earlierNeighbors_succ (G : Fin n → Fin n → Prop) (v i : Fin n) :
    earlierNeighbors G v (i.val+1) = if G i v then insert i (earlierNeighbors G v i.val)
      else earlierNeighbors G v i.val := by
  classical
  have he := filter_prefix_succ i (Finset.univ.filter (fun u => G u v))
  simpa [earlierNeighbors, Finset.filter_filter, and_comm] using he

theorem run_entropy_bound {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (htri : ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a))
    (hβ : β ≤ 1/2) (hp : 0 < p) (hp' : p < 1)
    (v : Fin n) (t : ℕ) (ht : t ≤ v.val) :
    (run G β p t).expect (fun w => entropy p (w v)) ≤
      2*p^2*(earlierNeighbors G v t).card := by
  classical
  induction t with
  | zero => simp [run, FiniteLaw.expect, entropy_self hp, earlierNeighbors]
  | succ t ih =>
    have htn : t < n := by omega
    let i : Fin n := ⟨t,htn⟩
    have hiv : i.val < v.val := by dsimp [i]; omega
    have hs := FiniteLaw.expect_mono (run_valid (G:=G) (p:=p) hβ t)
      (FiniteLaw.all_mono (run_bounded (G:=G) hβ hp.le hp' t (by omega))
        (fun w hw => step_entropy_le (G:=G) hβ hp i v hiv w (fun u => (hw.1 u).1)))
    rw [FiniteLaw.expect_add] at hs
    rw [run, dite_eq_left htn, FiniteLaw.expect_bind]
    change (run G β p t).expect (fun w => (step G β i w).expect (fun w => entropy p (w v))) ≤ _
    apply hs.trans
    have hrec := ih (by omega)
    have hf := earlierNeighbors_succ G v i
    change earlierNeighbors G v (t+1) = _ at hf
    rw [hf]
    by_cases hG : G i v
    · simp only [hG, ite_true, FiniteLaw.expect_mul_const]
      have hpair := adjacent_product_before (p:=p) hsym hirr htri hβ hG t
        (show t ≤ i.val from le_refl _) (by omega)
      rw [hpair]
      have hn : i ∉ earlierNeighbors G v t := by simp [earlierNeighbors, i]
      rw [Finset.card_insert_of_notMem hn, Nat.cast_add, Nat.cast_one]
      nlinarith
    · simp only [hG, ite_false, FiniteLaw.expect_const, add_zero]
      exact hrec

theorem run_entropy_degree_bound {G : Fin n → Fin n → Prop} {β p A : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (htri : ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a))
    (hβ : β ≤ 1/2) (hp : 0 < p) (hp' : p < 1) (v : Fin n)
    (hdeg : ((earlierNeighbors G v n).card : ℝ) ≤ A) :
    (run G β p v.val).expect (fun w => entropy p (w v)) ≤ 2*A*p^2 := by
  classical
  have hsub : earlierNeighbors G v v.val ⊆ earlierNeighbors G v n := by
    intro u hu
    simp only [earlierNeighbors, mem_filter, mem_univ, true_and] at hu ⊢
    exact ⟨u.isLt, hu.2⟩
  have hc : ((earlierNeighbors G v v.val).card : ℝ) ≤ A :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hdeg
  have hb := run_entropy_bound hsym hirr htri hβ hp hp' v v.val (le_refl _)
  nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*p^2 by positivity)]

end KMV.Sampling
