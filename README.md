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
the vertex set. They may intersect in more than one vertex and may contain
one another: neither linearity nor an antichain assumption is imposed.

`LiPostle34` is exactly the ordinary vertex-coloring specialization stated in
manuscript Theorem 2.1, with real degree bounds D3,D4 ≥ 8. The digits `34`
refer to edge sizes 3 and 4; colors are assigned to vertices, not to edges.
It is a proposition argument,
not a custom axiom. Li–Postle itself is not proved in this development.
There are no other unproved hypotheses in the main theorem.
The Ramsey consequence is outside the submitted primary target.

## Mathematical context and sources

This is the conditional formalisation of Theorem 1.3 in the
[working manuscript by Ayush Basu, Abhishek Dhawan and Abhishek Methuku](manuscript/KMV_proof.tex).
The frozen manuscript is version 21; its hash is recorded in
`manuscript/provenance.json`. It is not represented here as a published paper.

Theorem 3.1 of Kostochka, Mubayi and Verstraete,
[*Hypergraph Ramsey numbers: Triangles versus cliques*](https://doi.org/10.1016/j.jcta.2013.04.009)
(2013; [author-hosted text](https://homepages.math.uic.edu/~mubayi/papers/tri-finalrevised.pdf)),
gives the bound n^(2/3)/(8r^3) for the same mixed-rank, loose-triangle-free class.
The present conclusion adds the unbounded factor (log log n)^(1/3), conditional
on the stated coloring premise. The research context is independent sets,
hypergraph coloring, and loose-triangle Ramsey bounds in extremal and
probabilistic combinatorics.

The manuscript derives from this independent-set bound

$$R(C_3,K_t^{(r)})\le C_r\,\frac{t^{3/2}}{\sqrt{\log\log t}}=o(t^{3/2})$$

for every fixed $r\ge3$ and sufficiently large $t$. Here $C_3$ is the
$r$-uniform loose triangle. This is the manuscript's resolution of the
**2013 Kostochka–Mubayi–Verstraëte conjecture** (Conjecture 1.1 in their paper).
The Lean submission proves the independent-set bound conditional on the
explicit Li–Postle premise. The asymptotic conversion to this Ramsey statement
is supplied in the manuscript and is not yet formalised in this repository.

The external premise comes from Lina Li and Luke Postle,
[*The chromatic number of triangle-free hypergraphs*](https://arxiv.org/abs/2202.02839v3),
Theorem 1.4 of version 3 (21 August 2025). The manuscript states the normalized
ordinary vertex-coloring specialization as Theorem 2.1. `LiPostle34` assumes that
precise specialization with degree upper bounds at least 8. Its derivation
from the general list-coloring theorem is explained in the manuscript but is
not itself formalised here. Li–Postle triangles use a different, stronger
forbidden-configuration condition than loose triangles; both definitions are
explicit in `Challenge.lean`, and the proof performs the required reduction.

This repository contains the substantive Lean development built from the
manuscript. It imports the pinned Mathlib dependencies and no separate prior
project formalisation. The namespace `KMV` refers to the problem's literature
context; the working manuscript and the formalisation retain the distinct
authorship recorded in `formalization.yaml`.

## Verification status

The [official full Palomar preflight](https://github.com/methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle/actions/runs/40351845371)
passed for commit `8c1ffa95ef08c6788434011dbb0bc794884e8bb8` on 26 October 2026.
Its mechanical report records `status: pass`, no errors or report warnings,
and successful sandboxed compilation, statement comparison, axiom checks, and
NanoDa, con-ron and Lean kernel checks. The downloaded report is preserved as
`evidence/palomar-preflight-8c1ffa95.json`.
The current revision changes documentation, metadata, and Lean comments;
proof terms, definitions, dependencies, and Comparator configuration are unchanged. Before intake,
use the full commit of the corresponding successful run in
[GitHub Actions](https://github.com/methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle/actions/workflows/palomar-preflight.yml).
Submission, editorial review, and registration remain separate pending steps.

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
The official full preflight result is linked above. Editorial review and
registration remain pending.

The [complete local verification archive](KMV_Lean_verified_conditional_proof.zip)
contains the original Git history, historical checkpoints and certificate bindings.
The current Lean sources and verification records are also ordinary files in this repository.
