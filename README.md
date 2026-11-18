# Independent sets in hypergraphs with no loose triangle

## The mathematical statement

The mathematical paper is by **Ayush Basu, Abhishek Dhawan and Abhishek Methuku**. The Lean formalization assumes the stated Li–Postle coloring theorem.

Lean formalisation of the independent-set theorem in manuscript version 21,
Theorem 1.3, **assuming the ordinary vertex-coloring bound obtained by specializing
Li–Postle's theorem to hypergraphs with edges of sizes 3 and 4**:

The proved declaration is `KMV.main_result`, with argument
`hLP : KMV.LiPostle34` and conclusion `KMV.KMVStatement`.

Under this assumption, for every fixed integer $r \ge 3$ there are constants
$c_r>0$ and $N_r$ such that every hypergraph $H$ on $n\ge N_r$ vertices, with
edge sizes between $3$ and $r$ and no loose triangle, satisfies

$$\alpha(H)\ge c_r n^{2/3}(\log\log n)^{1/3}.$$

Here $\alpha(H)$ is the largest size of a vertex set containing no edge.
The constants depend on $r$ and the assumed absolute coloring bound, not on
$n$ or $H$. The edge sizes may differ.
The ambient `Fin n` includes isolated vertices. Edges are distinct subsets of
the vertex set.


### Exact Lean statement

The following definition is copied from [`Challenge.lean`](Challenge.lean),
inside the `KMV` namespace:

```lean
@[expose] def KMVStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
  ∀ n : ℕ, N ≤ n → ∀ H : Hypergraph (Fin n),
  RankBounds H r → LooseTriangleFree H →
  ∃ I : Finset (Fin n), Independent H I ∧
    c * Real.rpow (n : ℝ) (2 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log (n : ℝ))) (1 / 3 : ℝ) ≤ (I.card : ℝ)
```

[`Hypergraph`](Challenge.lean) represents the edge set as a finite collection
of finite vertex sets. [`RankBounds`](Challenge.lean) imposes the edge-size
bounds, [`LooseTriangleFree`](Challenge.lean) excludes loose triangles, and
[`Independent`](Challenge.lean) says that the chosen set contains no edge.
The proposition quantifies over $r$ before choosing $c$ and $N$, and then over
$n$ and $H$.

The proved declaration [`KMV.main_result`](KMV/Main.lean) takes the explicit
premise `hLP : LiPostle34` and proves `KMVStatement`. The `sorry` in
[`Challenge.lean`](Challenge.lean) is an intentional statement-only placeholder
for comparison; [`Solution.lean`](Solution.lean) imports the actual proof and
does not import the Challenge.

`LiPostle34` is exactly the ordinary vertex-coloring specialization stated in
manuscript Theorem 2.1. The digits `34`
refer to edge sizes 3 and 4; colors are assigned to vertices, not to edges.
It is a proposition argument,
not a custom axiom. Li–Postle itself is not proved in this development.
There are no other unproved hypotheses in the main theorem.

[**Lean formalisation (Palomar)**](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000016&version=1) — registered on 27 October 2026 as **PALOMAR-2026-10-27-000016, version 1**.
The public record includes the checked statement, mechanical verification,
automated review, and preserved source files.

## Paper abstract

**Paper authors:** Ayush Basu, Abhishek Dhawan and Abhishek Methuku.

An $r$-uniform loose triangle $C_3$ consists of three edges that intersect pairwise in exactly one vertex and have no vertex common to all three.
For graphs, this is the usual triangle, and the Ramsey number $R(C_3,K_t)$ has order of magnitude $t^2/\log t$ by celebrated results of Ajtai, Komlós, and Szemerédi and of Kim.

Kostochka, Mubayi, and Verstraëte proved that $R(C_3,K_t^{(r)})=O_r(t^{3/2})$ for every fixed $r\ge3$ and showed that this bound is sharp up to a logarithmic factor.
Motivated by the logarithmic saving in the graph case, they conjectured in 2013 that the upper bound could be improved to $o(t^{3/2})$.
This conjecture has since received significant attention and has been reiterated in several papers.
We prove the conjecture by showing that, for every fixed $r\ge3$,

$$
R(C_3,K_t^{(r)}) =O_r\left(\frac{t^{3/2}}{\sqrt{\log\log t}}\right).
$$

[*Ramsey numbers of loose triangles versus cliques*](https://arxiv.org/abs/2611.16957)

## Mathematical context and sources

This repository formalises Theorem 1.3 of the
[working manuscript by Ayush Basu, Abhishek Dhawan and Abhishek Methuku](manuscript/KMV_proof.tex),
assuming the vertex-colouring bound specified below as an external premise.
The frozen manuscript is version 21; its SHA-256 hash is recorded in
[`manuscript/provenance.json`](manuscript/provenance.json).

Theorem 3.1 of Kostochka, Mubayi and Verstraëte,
[*Hypergraph Ramsey numbers: Triangles versus cliques*](https://doi.org/10.1016/j.jcta.2013.04.009)
(2013; [author-hosted text](https://homepages.math.uic.edu/~mubayi/papers/tri-finalrevised.pdf)),
shows that, for every integer $r\ge 3$, every $n$-vertex hypergraph $H$ with no
loose triangle and with all edge sizes between $3$ and $r$ satisfies

```math
\alpha(H) \ge \frac{n^{2/3}}{8r^3}.
```

Under the stated Li–Postle assumption, the present result improves the order of
this bound by the unbounded factor $(\log\log n)^{1/3}$ for each fixed $r$ as
$n\to\infty$.

The manuscript derives the following Ramsey bound from the independent-set estimate:

```math
R(C_3,K_t^{(r)}) \le C_r\frac{t^{3/2}}{\sqrt{\log\log t}} = o(t^{3/2}),
```

where, for every fixed integer $r\ge 3$, there is a constant $C_r>0$ for which
the inequality holds for all sufficiently large $t$. Here $C_3$ is the
$r$-uniform loose triangle and $K_t^{(r)}$ is the complete $r$-uniform hypergraph
on $t$ vertices. This is the manuscript’s resolution of the
**2013 Kostochka–Mubayi–Verstraëte conjecture** (Conjecture 1.1 in their paper).
The Lean development proves the independent-set bound conditional on the explicit
Li–Postle premise.

The external premise is based on Theorem 1.4 of Lina Li and Luke Postle,
[*The chromatic number of triangle-free hypergraphs*](https://arxiv.org/abs/2202.02839v3),
version 3 (21 August 2025). The Lean hypothesis `LiPostle34` is the ordinary
vertex-colouring bound for hypergraphs with edges of sizes $3$ and $4$ stated
in manuscript Theorem 2.1.

Every loose triangle is a Li–Postle triangle, but the converse need not hold.
Thus Li–Postle’s triangle-free hypothesis is stronger than the absence of loose
triangles. Both notions are defined explicitly in [`Challenge.lean`](Challenge.lean),
and the Lean development carries out the reduction needed to apply the assumed
colouring bound.

This repository contains the substantive Lean development based on the manuscript.
It uses pinned Mathlib dependencies and does not import a separate prior project
formalisation. The namespace `KMV` refers to the problem’s literature context;
authorship of the working manuscript and of the formalisation is recorded
separately in [`formalization.yaml`](formalization.yaml).

## Verification status

The [official full Palomar preflight](https://github.com/methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle/actions/runs/40351845371)
passed for commit `8c1ffa95ef08c6788434011dbb0bc794884e8bb8` on 26 October 2026.
Its mechanical report records `status: pass`, no errors or report warnings,
and successful sandboxed compilation, statement comparison, axiom checks, and
NanoDa, con-ron and Lean kernel checks. The downloaded report is preserved as
`evidence/palomar-preflight-8c1ffa95.json`.
The final submitted source commit, `ea281d7cf047227e8fde38bfc124db1117ed7c37`,
was registered in [Palomar](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000016&version=1) on 27 October 2026.
Comparator accepted the Solution as a proof of the Challenge, and Lean, NanoDa,
and con-ron checked the exported proof successfully. The automated review
reported “No problems identified”. The registered theorem retains the explicit
Li–Postle hypothesis.
This README records the completed registration; the registered source remains
the immutable commit linked in the Palomar record.

The complete conditional main theorem and all project proof modules pass a
clean local Lean rebuild and axiom audit. The main theorem's machine-derived
closure contains only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
No proof-development declaration contains a placeholder or unchecked shortcut.
`evidence/verification.json` binds the build to exact source hashes;
`evidence/declaration-audit.json` records the actual main dependency closure.
`evidence/kernel-replay.json` records project-module replays against imported
environments; this alone is not a fresh dependency-closure replay.

Exported-data comparison and kernel results, where available, are recorded in
`evidence/export-validation.json`, including exact commands, export hashes and
individual exit codes. This is separate from Palomar's complete official
workflow. Those earlier local reports and the bundled archive retain the status
of their recorded checkpoints; the official preflight above supersedes their
then-pending preflight status. No human review or endorsement is claimed.

## Statement and proof correspondence

`Challenge.lean` independently defines the finite hypergraph, rank bounds,
loose triangles, independence, Li–Postle triangles, proper coloring and both
propositions. Its single deliberate `sorry` advertises the statement only.
`Solution.lean` imports the proved development and never imports Challenge.
The Comparator configuration has no definition holes: the theorem's definition
bodies must be compared recursively, not treated as opaque assumptions.

The primary source is manuscript version 21. Its theorem and proof agree with
version 20; the change adds an explanatory paragraph in the sampling overview.
Exact provenance and the source hash are in `manuscript/provenance.json`.
See `docs/ledger.md`, `docs/dependency-graph.json` and `docs/parameter-proof.md`
for the mathematical correspondence and proved adaptations.

The development includes the finite sampling lemma, compression, a sufficient
density bound, structural reduction, auxiliary graph properties, exhaustive
triangle classification and cover, all configuration counts and losses,
complete cleaning, eventual parameter bounds and the final coloring argument.

## Building and reproduction

The [Palomar-registered snapshot](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000016&version=1)
pins Lean 4.35.0-rc2 and its dependencies. With Git and
[elan](https://github.com/leanprover/elan) installed, it can be checked out and
built with:

```sh
git clone https://github.com/methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle.git
cd Independent-sets-in-hypergraphs-with-no-loose-triangle
git checkout ea281d7cf047227e8fde38bfc124db1117ed7c37
lake exe cache get
lake build
```

The cache command optionally downloads available Mathlib artifacts. A local
build is a reproducibility check, not a Palomar preflight or a new registration.
The historical `scripts/verify.py` rebuilds the proof and checks its axiom
closure; it clears project build products. Earlier environment-specific local
verification and export evidence is preserved in the repository's `evidence/`
directory and in the [verification archive](KMV_Lean_verified_conditional_proof.zip).

## Publication and rights

Abhishek Methuku is the confirmed human formalization author and responsible
maintainer. The formalization software is licensed under Apache-2.0; see the
root `LICENSE`. The manuscript and dependencies retain their existing rights;
this software license does not relicense them.
The Lean development was generated by Codex under Abhishek Methuku's direction.
No human review of the generated proof source is claimed.

The pinned Palomar metadata validator passes. The public source repository is
[methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle](https://github.com/methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle).
Mechanical verification, automated review, and registration are complete for
the pinned snapshot linked above.

The [complete local verification archive](KMV_Lean_verified_conditional_proof.zip)
contains the original Git history, historical checkpoints and certificate bindings.
The current Lean sources and verification records are also ordinary files in this repository.
