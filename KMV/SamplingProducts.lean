module
public import KMV.SamplingIndependent
public section
namespace KMV.Sampling
open FiniteLaw Finset
variable {n : ℕ}

theorem fork_product {S : Finset (Fin n)} {x : Fin n} (hx : x ∈ S)
    (a : ℝ) (l r w : Fin n → ℝ)
    (hfix : ∀ y ∈ S, y ≠ x → l y = w y ∧ r y = w y)
    (hm : a*l x + (1-a)*r x = w x) :
    a * (∏ y ∈ S, l y) + (1-a) * (∏ y ∈ S, r y) = ∏ y ∈ S, w y := by
  classical
  have hl : (∏ y ∈ S.erase x, l y) = ∏ y ∈ S.erase x, w y :=
    Finset.prod_congr rfl (fun y hy => (hfix y (mem_erase.mp hy).2 (mem_erase.mp hy).1).1)
  have hr : (∏ y ∈ S.erase x, r y) = ∏ y ∈ S.erase x, w y :=
    Finset.prod_congr rfl (fun y hy => (hfix y (mem_erase.mp hy).2 (mem_erase.mp hy).1).2)
  rw [← Finset.mul_prod_erase S l hx, ← Finset.mul_prod_erase S r hx,
    ← Finset.mul_prod_erase S w hx, hl, hr]
  nlinarith [congrArg (fun z => z * ∏ y ∈ S.erase x, w y) hm]

@[expose] def Touch (G : Fin n → Fin n → Prop) (i v : Fin n) : Prop :=
  v = i ∨ G i v

@[expose] def OneTouch (G : Fin n → Fin n → Prop) (i : Fin n) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Touch G i x → Touch G i y → x = y

theorem next_untouched {G : Fin n → Fin n → Prop} {i v : Fin n} {β : ℝ}
    (h : ¬ Touch G i v) (b : Bool) (w : Fin n → ℝ) : next G β i b w v = w v := by
  classical
  have hn : v ≠ i := fun hvi => h (Or.inl hvi)
  have hnG : ¬ G i v := fun hG => h (Or.inr hG)
  simp [next, hn, hnG]

theorem separated_oneTouch {G : Fin n → Fin n → Prop}
    (hsym : ∀ u v, G u v → G v u) {S : Finset (Fin n)} (hS : Separated G S)
    (i : Fin n) : OneTouch G i S := by
  intro x hx y hy hi hj
  by_contra hxy
  have h := hS x hx y hy hxy
  rcases hi with rfl | hi <;> rcases hj with rfl | hj
  · exact hxy rfl
  · exact h.1 hj
  · exact h.1 (hsym _ _ hi)
  · exact h.2 i ⟨hsym _ _ hi, hsym _ _ hj⟩

theorem step_product {G : Fin n → Fin n → Prop} {β : ℝ} (hβ : β ≤ 1/2)
    (i : Fin n) (S : Finset (Fin n)) (hS : OneTouch G i S) (w : Fin n → ℝ) :
    (step G β i w).expect (fun w => ∏ v ∈ S, w v) = ∏ v ∈ S, w v := by
  classical
  by_cases ha : Active β (w i)
  · have hm : ∀ x, w i * next G β i true w x +
        (1-w i) * next G β i false w x = w x := by
      intro x
      simpa [step, ha, FiniteLaw.expect] using step_mean hβ i x w
    simp only [step, ha, ite_true, FiniteLaw.expect]
    by_cases hx : ∃ x ∈ S, Touch G i x
    · obtain ⟨x,hx,ht⟩ := hx
      apply fork_product hx _ _ _ _ _ (hm x)
      intro y hy hyx
      have hn : ¬ Touch G i y := fun hty => hyx (hS y hy x hx hty ht)
      exact ⟨next_untouched hn true w, next_untouched hn false w⟩
    · have he : ∀ b, (∏ v ∈ S, next G β i b w v) = ∏ v ∈ S, w v := by
        intro b
        exact Finset.prod_congr rfl (fun v hv => next_untouched (fun ht => hx ⟨v,hv,ht⟩) b w)
      rw [he true, he false]
      ring
  · simp [step, ha, FiniteLaw.expect]

theorem run_product_until {G : Fin n → Fin n → Prop} {β p : ℝ} (hβ : β ≤ 1/2)
    (t : ℕ) (S : Finset (Fin n))
    (hS : ∀ i : Fin n, i.val < t → OneTouch G i S) :
    (run G β p t).expect (fun w => ∏ v ∈ S, w v) = p ^ S.card := by
  induction t with
  | zero => simp [run, FiniteLaw.expect]
  | succ t ih =>
    unfold run
    split_ifs with ht
    · rw [FiniteLaw.expect_bind]
      simp_rw [step_product hβ _ S (hS ⟨t,ht⟩ (by simp))]
      exact ih (fun i hi => hS i (by omega))
    · exact ih (fun i hi => hS i (by omega))

theorem run_separated_product {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hβ : β ≤ 1/2)
    (t : ℕ) (S : Finset (Fin n)) (hS : Separated G S) :
    (run G β p t).expect (fun w => ∏ v ∈ S, w v) = p ^ S.card :=
  run_product_until hβ t S (fun i _ => separated_oneTouch hsym hS i)

theorem separated_inclusion {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hβ : β ≤ 1/2)
    (hp : 0 ≤ p) (hp' : p < 1) (S : Finset (Fin n)) (hS : Separated G S) :
    (run G β p n).probability (fun w => S ⊆ selected w) ≤ p ^ S.card := by
  classical
  rw [← run_separated_product hsym hβ n S hS]
  apply FiniteLaw.expect_mono (run_valid hβ n)
  apply FiniteLaw.all_mono (run_bounded hβ hp hp' n (le_refl _))
  intro w hw
  by_cases h : S ⊆ selected w
  · have he : (∏ v ∈ S, w v) = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      exact (mem_filter.mp (h hv)).2
    simp [h, he]
  · simp only [h, ite_false]
    exact Finset.prod_nonneg (fun v _ => (hw.1 v).1)

theorem adjacent_oneTouch_before {G : Fin n → Fin n → Prop}
    (hsym : ∀ u v, G u v → G v u)
    (htri : ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a))
    {u v i : Fin n} (huv : G u v) (hiu : i.val < u.val) (hiv : i.val < v.val) :
    OneTouch G i {u,v} := by
  intro x hx y hy hix hiy
  have hnu : u ≠ i := by intro h; subst u; omega
  have hnv : v ≠ i := by intro h; subst v; omega
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx] at hix <;>
    rw [hy] at hiy <;> rw [hx, hy]
  · have hGu : G i u := hix.resolve_left hnu
    have hGv : G i v := hiy.resolve_left hnv
    exact False.elim (htri i u v ⟨hGu,huv,hsym i v hGv⟩)
  · have hGu : G i u := hiy.resolve_left hnu
    have hGv : G i v := hix.resolve_left hnv
    exact False.elim (htri i u v ⟨hGu,huv,hsym i v hGv⟩)

theorem adjacent_product_before {G : Fin n → Fin n → Prop} {β p : ℝ}
    (hsym : ∀ u v, G u v → G v u) (hirr : ∀ u, ¬ G u u)
    (htri : ∀ a b c, ¬ (G a b ∧ G b c ∧ G c a)) (hβ : β ≤ 1/2)
    {u v : Fin n} (huv : G u v) (t : ℕ) (htu : t ≤ u.val) (htv : t ≤ v.val) :
    (run G β p t).expect (fun w => w u * w v) = p^2 := by
  have hne : u ≠ v := by intro h; subst v; exact hirr u huv
  have he := run_product_until (p:=p) hβ t {u,v}
    (fun i hi => adjacent_oneTouch_before hsym htri huv (by omega) (by omega))
  simpa [hne] using he

end KMV.Sampling
