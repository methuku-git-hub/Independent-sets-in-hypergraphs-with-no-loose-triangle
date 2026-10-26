module
public import KMV.Packing
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

theorem looseTriangle_of_card_inter {e f g : Finset V}
    (he : 2 ≤ e.card) (hf : 2 ≤ f.card) (hg : 2 ≤ g.card)
    (hef : (e ∩ f).card = 1) (hfg : (f ∩ g).card = 1) (hge : (g ∩ e).card = 1)
    (hzero : e ∩ f ∩ g = ∅) : LooseTriangle e f g := by
  refine ⟨?_,?_,?_,hef,hfg,hge,hzero⟩
  · intro h; subst f; simp only [inter_self] at hef; omega
  · intro h; subst g; simp only [inter_self] at hfg; omega
  · intro h; subst e; simp only [inter_self] at hge; omega

theorem nonexpandable_pair_triples {H : Hypergraph V} {r : ℕ} {P : Finset V}
    (hP : P.card = 2) (hn : ¬ Expandable H r P) : codegree H 3 P ≤ 2*r := by
  obtain ⟨Y,hd,hc,hY⟩ := nonexpandable_witness (card_pos.mp (by omega)) hn
  have hs : (∑ y ∈ Y, codegree H 3 (insert y P)) ≤ Y.card := by
    calc
      _ ≤ ∑ _y ∈ Y, 1 := by
        apply sum_le_sum
        intro y hy
        have hn : y ∉ P := fun hp => Finset.disjoint_left.mp hd hp hy
        have he : (insert y P).card = 3 := by simp [hn,hP]
        simpa only [he] using (codegree_same_size_le_one (H:=H) (X:=insert y P))
      _ = Y.card := by simp
  exact (codegree_le_sum_insert hY).trans (hs.trans hc)

/-- A transversal of disjoint links of one vertex is independent, because
an edge inside it would complete a loose triangle. -/
theorem star_matching_independent {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H)
    (v : V) {M : Hypergraph V} (hm : Matching M)
    (hM : ∀ e ∈ M, e.Nonempty ∧ v ∉ e ∧ insert v e ∈ H) :
    ∃ X : Finset V, Independent H X ∧ X.card = M.card := by
  obtain ⟨X,hcard,hsub,htrans⟩ := matching_transversal hm (fun e he => (hM e he).1)
  have hvX : v ∉ X := by
    intro hv
    obtain ⟨e,he,hve⟩ := mem_biUnion.mp (hsub hv)
    exact (hM e he).2.1 hve
  refine ⟨X,?_,hcard⟩
  intro F hF hFX
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp
    (show 1 < F.card by have := (hH F hF).1; omega)
  obtain ⟨e,he,hxe⟩ := mem_biUnion.mp (hsub (hFX hx))
  obtain ⟨f,hf,hyf⟩ := mem_biUnion.mp (hsub (hFX hy))
  have hef : e ≠ f := by
    intro h; subst f
    exact hxy (card_le_one.mp (htrans e he).le x
      (mem_inter.mpr ⟨hxe,hFX hx⟩) y (mem_inter.mpr ⟨hyf,hFX hy⟩))
  have hdis := hm e he f hf hef
  have hinter : insert v e ∩ insert v f = {v} := by
    ext a
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨ha,hb⟩
      rcases ha with rfl | ha
      · rfl
      rcases hb with rfl | hb
      · rfl
      · exact False.elim (Finset.disjoint_left.mp hdis ha hb)
    · intro ha; exact ⟨Or.inl ha,Or.inl ha⟩
  have interCard : ∀ a ∈ M, ∀ z ∈ F, z ∈ a → (insert v a ∩ F).card = 1 := by
    intro a ha z hz hza
    have hsub' : insert v a ∩ F ⊆ a ∩ X := by
      intro u hu
      obtain ⟨hua,huF⟩ := mem_inter.mp hu
      refine mem_inter.mpr ⟨?_,hFX huF⟩
      rcases mem_insert.mp hua with rfl | hua
      · exact False.elim (hvX (hFX huF))
      · exact hua
    have hle := (card_le_card hsub').trans (htrans a ha).le
    have hpos : 0 < (insert v a ∩ F).card :=
      card_pos.mpr ⟨z,mem_inter.mpr ⟨mem_insert_of_mem hza,hz⟩⟩
    omega
  have hzero : insert v e ∩ insert v f ∩ F = ∅ := by
    rw [hinter]
    ext a
    simp only [mem_inter, mem_singleton, notMem_empty, iff_false]
    rintro ⟨rfl,ha⟩
    exact hvX (hFX ha)
  apply hfree _ (hM e he).2.2 _ (hM f hf).2.2 F hF
  apply looseTriangle_of_card_inter
    (by have := (hH _ (hM e he).2.2).1; omega)
    (by have := (hH _ (hM f hf).2.2).1; omega)
    (by have := (hH F hF).1; omega)
    (by simp [hinter]) (interCard f hf y hy hyf) _ hzero
  rw [inter_comm]
  exact interCard e he x hx hxe

end KMV
