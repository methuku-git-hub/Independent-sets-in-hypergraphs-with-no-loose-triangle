module
public import KMV.Compression
public import Mathlib.Data.Fintype.Prod
public section
namespace KMV
open Finset
variable {V : Type*} [DecidableEq V]

@[expose] def containingEdges (H : Hypergraph V) (j : ℕ) (X : Finset V) : Hypergraph V :=
  H.filter fun e => e.card = j ∧ X ⊆ e

@[expose] def codegree (H : Hypergraph V) (j : ℕ) (X : Finset V) : ℕ :=
  (containingEdges H j X).card

theorem nonexpandable_witness {H : Hypergraph V} {r : ℕ} {X : Finset V}
    (hX : X.Nonempty) (hn : ¬ Expandable H r X) :
    ∃ Y : Finset V, Disjoint X Y ∧ Y.card ≤ 2 * r ∧
      ∀ e ∈ H, X ⊆ e → (e ∩ Y).Nonempty := by
  simp only [Expandable, hX, true_and] at hn
  push Not at hn
  obtain ⟨Y, hd, hc, hY⟩ := hn
  refine ⟨Y, hd, hc, ?_⟩
  intro e he hXe
  exact Finset.not_disjoint_iff_nonempty_inter.mp (hY e he hXe)

theorem codegree_le_sum_insert {H : Hypergraph V} {j : ℕ} {X Y : Finset V}
    (hY : ∀ e ∈ H, X ⊆ e → (e ∩ Y).Nonempty) :
    codegree H j X ≤ ∑ y ∈ Y, codegree H j (insert y X) := by
  have hsub : containingEdges H j X ⊆
      Y.biUnion (fun y => containingEdges H j (insert y X)) := by
    intro e he
    obtain ⟨heH, hej, hXe⟩ := Finset.mem_filter.mp he
    obtain ⟨y, hy⟩ := hY e heH hXe
    obtain ⟨hye, hyY⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_biUnion.mpr ⟨y, hyY,
      Finset.mem_filter.mpr ⟨heH, hej, Finset.insert_subset_iff.mpr ⟨hye, hXe⟩⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)

theorem codegree_same_size_le_one {H : Hypergraph V} {X : Finset V} :
    codegree H X.card X ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨_, hec, hXe⟩ := Finset.mem_filter.mp he
  obtain ⟨_, hfc, hXf⟩ := Finset.mem_filter.mp hf
  have h1 : X = e := Finset.eq_of_subset_of_card_le hXe hec.le
  have h2 : X = f := Finset.eq_of_subset_of_card_le hXf hfc.le
  exact h1.symm.trans h2

/-- The downward codegree induction in Lemma 4.2(iii). -/
theorem reduced_codegree_bound {H : Hypergraph V} {r : ℕ}
    (hred : Reduced H r) : ∀ d : ℕ, ∀ X : Finset V, 3 ≤ X.card →
      codegree H (X.card + d) X ≤ (2 * r) ^ d := by
  intro d
  induction d with
  | zero =>
    intro X _
    simpa using (codegree_same_size_le_one (H := H) (X := X))
  | succ d ih =>
    intro X hcard
    by_cases hzero : containingEdges H (X.card + (d + 1)) X = ∅
    · simp [codegree, hzero]
    obtain ⟨E, hE⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
    obtain ⟨hEH, hEc, hXE⟩ := Finset.mem_filter.mp hE
    have hn : ¬ Expandable H r X := by
      intro hx
      have heq := hred X hx hcard E hEH hXE
      have := congrArg Finset.card heq
      omega
    obtain ⟨Y, hd, hYc, hY⟩ := nonexpandable_witness
      (Finset.card_pos.mp (by omega)) hn
    have hsum : (∑ y ∈ Y, codegree H (X.card + (d + 1)) (insert y X)) ≤
        Y.card * (2 * r) ^ d := by
      calc
        _ ≤ ∑ _y ∈ Y, (2 * r) ^ d := by
          apply Finset.sum_le_sum
          intro y hy
          have hyX : y ∉ X := fun hx => Finset.disjoint_left.mp hd hx hy
          have hc : (insert y X).card = X.card + 1 := Finset.card_insert_of_notMem hyX
          have hbound := ih (insert y X) (by omega)
          have heq : (insert y X).card + d = X.card + (d + 1) := by omega
          rwa [heq] at hbound
        _ = Y.card * (2 * r) ^ d := by simp
    have h := (codegree_le_sum_insert (j := X.card + (d + 1)) hY).trans hsum
    calc
      _ ≤ Y.card * (2 * r) ^ d := h
      _ ≤ (2 * r) * (2 * r) ^ d := Nat.mul_le_mul_right _ hYc
      _ = (2 * r) ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

theorem reduced_codegree {H : Hypergraph V} {r j : ℕ} {X : Finset V}
    (hred : Reduced H r) (hX : 3 ≤ X.card) (hXj : X.card ≤ j) :
    codegree H j X ≤ (2 * r) ^ (j - X.card) := by
  have h := reduced_codegree_bound hred (j - X.card) X hX
  simpa [Nat.add_sub_of_le hXj] using h

theorem nonexpandable_pair_codegree {H : Hypergraph V} {r j : ℕ} {P : Finset V}
    (hred : Reduced H r) (hP : P.card = 2) (hn : ¬ Expandable H r P)
    (hj : 3 ≤ j) : codegree H j P ≤ (2 * r) ^ (j - 2) := by
  obtain ⟨Y, hd, hYc, hY⟩ := nonexpandable_witness
    (Finset.card_pos.mp (by omega)) hn
  have hsum : (∑ y ∈ Y, codegree H j (insert y P)) ≤ Y.card * (2 * r) ^ (j - 3) := by
    calc
      _ ≤ ∑ _y ∈ Y, (2 * r) ^ (j - 3) := by
        apply Finset.sum_le_sum
        intro y hy
        have hyP : y ∉ P := fun hx => Finset.disjoint_left.mp hd hx hy
        have hc : (insert y P).card = 3 := by rw [Finset.card_insert_of_notMem hyP, hP]
        simpa [hc] using reduced_codegree hred hc.ge (by omega : (insert y P).card ≤ j)
      _ = Y.card * (2 * r) ^ (j - 3) := by simp
  calc
    _ ≤ Y.card * (2 * r) ^ (j - 3) := (codegree_le_sum_insert hY).trans hsum
    _ ≤ (2 * r) * (2 * r) ^ (j - 3) := Nat.mul_le_mul_right _ hYc
    _ = (2 * r) ^ (j - 2) := by
      have heq : j - 2 = (j - 3) + 1 := by omega
      rw [heq, pow_succ, Nat.mul_comm]

theorem pair_triangle {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LooseTriangle ({a,b} : Finset V) {b,c} {c,a} := by
  have h₁ : ({a,b} : Finset V) ∩ {b,c} = {b} := by
    ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; grind
  have h₂ : ({b,c} : Finset V) ∩ {c,a} = {c} := by
    ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; grind
  have h₃ : ({c,a} : Finset V) ∩ {a,b} = {a} := by
    ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; grind
  have hn₁ : ({a,b} : Finset V) ≠ {b,c} := by
    intro heq
    have : a ∈ ({b,c} : Finset V) := heq ▸ (by simp : a ∈ ({a,b} : Finset V))
    simp [hab, hac] at this
  have hn₂ : ({b,c} : Finset V) ≠ {c,a} := by
    intro heq
    have : b ∈ ({c,a} : Finset V) := heq ▸ (by simp : b ∈ ({b,c} : Finset V))
    simp [hab.symm, hbc] at this
  have hn₃ : ({c,a} : Finset V) ≠ {a,b} := by
    intro heq
    have : c ∈ ({a,b} : Finset V) := heq ▸ (by simp : c ∈ ({c,a} : Finset V))
    simp [hac.symm, hbc.symm] at this
  refine ⟨hn₁, hn₂, hn₃, by simp [h₁], by simp [h₂], by simp [h₃], ?_⟩
  rw [h₁]
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
  grind

theorem edge_contains_nonexpandable_pair {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) {e : Finset V} (he : e ∈ H) :
    ∃ P : Finset V, P.card = 2 ∧ P ⊆ e ∧ ¬ Expandable H r P := by
  by_contra hn
  push Not at hn
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    (Finset.two_lt_card (s := e)).mp (by have := (hH e he).1; omega)
  have h₁ : Expandable H r {a,b} := hn _ (by simp [hab])
    (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
  have h₂ : Expandable H r {b,c} := hn _ (by simp [hbc])
    (Finset.insert_subset_iff.mpr ⟨hb, Finset.singleton_subset_iff.mpr hc⟩)
  have h₃ : Expandable H r {c,a} := hn _ (by simp [hac.symm])
    (Finset.insert_subset_iff.mpr ⟨hc, Finset.singleton_subset_iff.mpr ha⟩)
  exact expandable_no_loose_triangle hH hfree h₁ h₂ h₃ (pair_triangle hab hac hbc)

/-- A concrete quadratic bound, counting ordered pairs. This replaces the
manuscript's sharper binomial coefficient by n²; its O_r(n²) conclusion is
unchanged. -/
theorem reduced_edge_count [Fintype V] {H : Hypergraph V} {r j : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) (hred : Reduced H r)
    (hj : 3 ≤ j) :
    codegree H j ∅ ≤ (Fintype.card V) ^ 2 * (2 * r) ^ (j - 2) := by
  classical
  let F : V × V → Hypergraph V := fun p =>
    if p.1 ≠ p.2 ∧ ¬ Expandable H r {p.1,p.2} then
      containingEdges H j {p.1,p.2} else ∅
  have hsub : containingEdges H j ∅ ⊆ Finset.univ.biUnion F := by
    intro e he
    obtain ⟨heH, hej, _⟩ := Finset.mem_filter.mp he
    obtain ⟨P, hc, hPe, hn⟩ := edge_contains_nonexpandable_pair hH hfree heH
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    apply Finset.mem_biUnion.mpr
    refine ⟨(a,b), by simp, ?_⟩
    have hm : e ∈ containingEdges H j {a,b} := Finset.mem_filter.mpr ⟨heH, hej, hPe⟩
    simpa [F, hab, hn] using hm
  have hbound : ∀ p : V × V, (F p).card ≤ (2 * r) ^ (j - 2) := by
    intro p
    dsimp [F]
    split_ifs with h
    · exact nonexpandable_pair_codegree hred (by simp [h.1]) h.2 hj
    · simp
  calc
    _ ≤ (Finset.univ.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ p : V × V, (F p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : V × V, (2 * r) ^ (j - 2) := Finset.sum_le_sum (fun p _ => hbound p)
    _ = (Fintype.card V) ^ 2 * (2 * r) ^ (j - 2) := by simp [pow_two]

/-- Lemma 4.2, with explicit constants and the full independence transfer. -/
theorem compression [Fintype V] {H : Hypergraph V} {r : ℕ}
    (hH : RankBounds H r) (hfree : LooseTriangleFree H) :
    ∃ J : Hypergraph V, RankBounds J r ∧ LooseTriangleFree J ∧ Antichain J ∧
      (∀ I, Independent J I → Independent H I) ∧
      (∀ (j : ℕ) (X : Finset V), 3 ≤ X.card → X.card ≤ j →
        codegree J j X ≤ (2 * r) ^ (j - X.card)) ∧
      (∀ j : ℕ, 4 ≤ j → codegree J j ∅ ≤
        (Fintype.card V) ^ 2 * (2 * r) ^ (j - 2)) := by
  obtain ⟨J, hr, hf, hi, hred, ha⟩ := exists_reduced hH hfree
  exact ⟨J, hr, hf, ha, hi,
    fun _ _ hc hj => reduced_codegree hred hc hj,
    fun _ hj => reduced_edge_count hr hf hred (by omega)⟩

end KMV
