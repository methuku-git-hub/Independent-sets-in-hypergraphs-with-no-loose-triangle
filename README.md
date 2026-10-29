# Independent sets in hypergraphs with no loose triangle

Lean formalisation of the independent-set theorem in manuscript version 21,
Theorem 1.3, **assuming the ordinary vertex-coloring bound obtained by specializing
Li–Postle's theorem to hypergraphs with edges of sizes 3 and 4**:

```lean
theorem KMV.main_result (hLP : KMV.LiPostle34) : KMV.KMVStatement
```

Under this assumption, for every fixed integer $r \ge 3$ there are constants
$c_r>0$ and $N_r$ such that every hypergraph $H$ on $n\ge N_r$ vertices, with
edge sizes between $3$ and $r$ and no loose triangle, satisfies

$$\alpha(H)\ge c_r n^{2/3}(\log\log n)^{1/3}.$$

Here $\alpha(H)$ is the largest size of a vertex set containing no edge.
The constants depend on $r$ and the assumed absolute coloring bound, not on
$n$ or $H$. The edge sizes may differ.
The ambient `Fin n` includes isolated vertices. Edges are distinct subsets of
the vertex set.

`LiPostle34` is exactly the ordinary vertex-coloring specialization stated in
manuscript Theorem 2.1, with real degree bounds D3,D4 ≥ 8. The digits `34`
refer to edge sizes 3 and 4; colors are assigned to vertices, not to edges.
It is a proposition argument,
not a custom axiom. Li–Postle itself is not proved in this development.
There are no other unproved hypotheses in the main theorem.
The Ramsey consequence is outside the submitted primary target.

[**Lean formalisation (Palomar)**](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000016&version=1) — registered on 27 October 2026 as **PALOMAR-2026-10-27-000016, version 1**.
The public record includes the checked statement, mechanical verification,
automated review, and preserved source files.

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
$n\to\infty$. The problem connects independent sets and hypergraph colouring
with loose-triangle Ramsey bounds in extremal and probabilistic combinatorics.

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
Li–Postle premise. The asymptotic deduction of the Ramsey bound is proved in the
manuscript and is not yet formalised in this repository.

The external premise is based on Theorem 1.4 of Lina Li and Luke Postle,
[*The chromatic number of triangle-free hypergraphs*](https://arxiv.org/abs/2202.02839v3),
version 3 (21 August 2025). The Lean hypothesis `LiPostle34` states the ordinary
vertex-colouring specialisation for hypergraphs whose edges have size $3$ or $4$,
with real degree upper bounds $D_3,D_4\ge 8$, as stated in manuscript Theorem 2.1.
The manuscript explains how this follows from Li–Postle’s list-colouring theorem;
that derivation is not itself formalised here.

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
Li–Postle hypothesis; the Ramsey deduction is outside its formal scope.
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

## Reproduction

Lean is pinned to 4.35.0-rc2; Mathlib and every transitive package are pinned
in `lake-manifest.json`. On a supported installation:

```sh
lake exe cache get
python3 scripts/verify.py
```

The script clears only project build products, rebuilds the proof, verifies the
main theorem's axiom closure, and separately elaborates Challenge. It does not
run the official Palomar workflow.

In the present environment, the standalone Lean executable fails during
executable-location discovery. The unmodified Lake executable can host the
ordinary Lean frontend with `trustLevel = 0`:

```sh
export KMV_LEAN_ROOT=/absolute/path/to/lean-4.35.0-rc2-linux
python3 scripts/bootstrap_local.py
python3 scripts/verify.py --local
python3 scripts/check_exports.py
```

The last command exports proof data using the pinned official exporter,
compares the statements and audits axioms with the pinned Lake functions,
and invokes the bundled NanoDa, con-ron and Lean kernels on the exports.
It does not evaluate project configuration or execute a source build inside
bubblewrap, and is not Palomar's complete preflight.
This runtime refuses bubblewrap namespace creation; that restriction is not
disabled. The official full workflow has since succeeded on GitHub's runner.

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
