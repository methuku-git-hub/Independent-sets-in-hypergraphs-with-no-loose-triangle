# Research and verification ledger — 2026-10-26 (UTC)

## Current authorised objective

The user selected the conditional target: `LiPostle34 → KMVStatement`.
The external premise is precisely manuscript Theorem 2.1, the normalized
ordinary vertex-coloring form for hypergraphs with edge sizes 3 and 4. It has an absolute positive
constant and degree upper bounds D3,D4 at least 8. Li–Postle itself is not
proved or imported as an axiom. No further external theorem is permitted as
an unproved hypothesis in the main result.

The final conclusion is Theorem 1.3 in manuscript version 21, including mixed
edge sizes 3,...,r. Constants c and N are quantified after r and before n,H.
There is no restriction to uniform hypergraphs or loss of the log-log factor.

## Statement fidelity

- `Fin n` counts all vertices, including isolated ones.
- `Hypergraph` is an abbreviation for a finite set of finite sets: no repeated
  edges. `RankBounds` requires 3 ≤ |e| ≤ r.
- `LooseTriangle` uses singleton pairwise intersections and empty triple
  intersection. All three edges are explicitly distinct.
- `Triangle` uses three nonempty differences of pairwise intersections;
  `triangle_iff_witnesses` proves the exact Li–Postle vertex characterization,
  and `triangle_edges_distinct` proves distinctness of its edges.
- `Independent` forbids an edge contained in the chosen set. `ProperColoring`
  requires two differently colored vertices in every edge.
- `sizeDegree` counts only edges of the specified size. The premise bounds
  each vertex degree, equivalently bounding the maximum degree, without
  introducing an undefined maximum on an empty vertex set.
- Real exponents and real logarithms are explicit. The target is only eventual
  in n; no positive-log assumption has been inserted into the conclusion.
- The exported `LiPostle34` is manuscript Theorem 2.1, not a formal encoding of
  the entire rank-k list-coloring Theorem 1.4. The manuscript's padding and
  list-to-ordinary-coloring explanation is not claimed as a checked derivation
  from a separately encoded general theorem. If that broader interface is
  desired later, its normalization must also be formalised.
- `Fin n` is the chosen representation of an n-vertex hypergraph. The compared
  interface gives an independent set directly. Separate arbitrary-finite-type
  transport and independence-number APIs are outside this interface.

## PROVED AND LOCALLY CHECKED

1. Lemma 3.1 in full: `KMV.sampling`. The random object is an explicit finite
   probability tree of subsets. Validity is proved; every leaf, including any
   zero-mass leaf, is independent. The proof includes the coordinate and
   separated-product expectation invariants, the adjacent-product invariant,
   entropy drift including zero weights, freezing loss, both marginal bounds,
   the separated p^|S| bound, and the universal beta^|S| bound.
2. Lemmas 4.1 and 4.2: `KMV.expandable_no_loose_triangle` and `KMV.compression`.
3. Density reduction: `KMV.density`, with m3 ≤ 6 r n α. This implies
   α ≥ d3/(18 r) for n>0. The weaker explicit constant is sufficient for the
   main theorem, whose constant depends only on r.
4. `KMV.trim_degrees`: exact simultaneous degree-trimming bound, with
   double-counting and induced-hypergraph independence transfer.
5. `KMV.auxiliary_graph`: all finite graph properties and the exact degree
   estimate, under explicit threshold and triple-codegree hypotheses.
6. `KMV.triangle_classification`: all three cardinal-pattern cases and
   union sizes 6 to 8. Exhaustiveness uses set-cardinality identities and
   kernel-checked finite integer case analysis, not a classification axiom.
7. Finite candidate-family counts: `typeOneCandidates_card`,
   `pairGeneratedTriples_card`, with membership lemmas for each triangle type.
   `typeOne_loss` and `pairGenerated_loss` give their finite expected losses.
   `triangle_union_covered` checks all orientations and the combined union cover.
   `sum_codegree_fixed_card`, `intersectingAt_card`, and the subsequent loss
   lemmas check the separated-pair and four-edge intersection-three counts.
   `expected_highDegree` checks the random degree-deletion bound, and
   `exists_after_deletions_with_bad_vertices` combines two kinds of deletion.
8. `KMV.exists_after_deletions`: expected-size-minus-cost produces a concrete
   surviving set, carrying deterministic properties from the probability tree.
9. `KMV.structural_reduction`: either an independent set at an arbitrary target
   t>0, or a compressed and trimmed hypergraph on at least 7n/8 vertices.
   All degree, triple-codegree, edge-count and independence-transfer bounds
   use the explicit constant `reductionConstant r`.
10. `KMV.cleaned_triangleFree`, `KMV.forbidden_loss`, `KMV.finite_cleaning`:
   candidate monotonicity, the complete deterministic cover after deletions,
   all finite losses and simultaneous degree trimming.
11. `KMV.sampling_cleaning`: restriction of the sampling law to the structurally
   retained subset and transfer from graph-avoiding edges to the original
   induced hypergraph. Explicit numerical conditions give at least pn/4
   vertices, rank at most 4, triangle-freeness and the prescribed degrees.
12. `KMV.configurationCost_le_envelope`: a scalar upper bound on all losses.
    `KMV.Scales` proves arithmetic and limiting behavior for products of
    powers of n, log n and log log n. The parameter substitution is proved in `KMV.Parameters` and the subsequent assembly modules.
13. `KMV.liPostle34_on_subset`: the final coloring step on a surviving subset;
   retaining the original ambient type avoids needing a relabeling step.

See verification.json for exact build outcomes and source hashes. The axiom
and declaration audit includes the actual transitive closure of `KMV.main_result`.
No proof file contains a placeholder or custom axiom.

## Proof adaptations, not mathematical gap repairs

- Compression minimizes the sum of edge sizes over valid intermediate
  hypergraphs; strict decrease is proved.
- The compression edge count uses n² in place of binomial(n,2).
- Sampling skips a zero-weight processing step entirely. Both successors
  would have identical later weights, and selection has probability zero.
  This ensures deterministic independence even at zero-probability leaves.
- The finite sampling tree replaces measure-theoretic conditioning by exact
  recursive expectation identities. No probabilistic premise is assumed.
- Density calls nonexpandable pairs light. Their triple codegree is at most
  2r; heavy pairs are expandable. This yields the sufficient constant 18r
  in the average-degree formulation instead of the sharper manuscript constant.
- Candidate counting uses constants 256 and 1024 instead of optimized counts.
  The dependence on edge counts, degrees, pair codegrees and B is unchanged.
- Induced hypergraphs retain their original vertex type; color classes are
  explicitly restricted to the surviving set before independence transfer.

The complete conditional implication is now proved. The final asymptotic
substitution is detailed in `docs/parameter-proof.md`; it uses nonoptimal
parameters and constants without weakening the target.

## Completed main theorem and external obligations

`KMV.main_result : LiPostle34 → KMVStatement` is proved and passes the clean
local build. All finite estimates, limits, rounding, transfer and coloring
steps are discharged. The only explicit external hypothesis is the authorized
Li–Postle statement. The solution contains no other unresolved proof obligation.

The full clean build checks 54 modules, including the separate Challenge.
The audit finds 679 project theorem declarations and a main closure of 3982
constants, with exactly the permitted standard axioms. These counts describe
the evidence; completion is established by the checked main declaration itself.

The pinned Lake comparison and axiom functions pass on the official exports.
Definition holes are empty in comparator.json, so the statement's definitions
are compared recursively. The same exported proof data passes NanoDa, con-ron,
and Lean's kernel from a fresh exported environment. Exact export hashes,
commands and exit codes are in `evidence/export-validation.json`.

Publication, attribution, licence, and responsible-maintainer confirmation are
complete. The official full preflight passed at commit `8c1ffa95ef08c6788434011dbb0bc794884e8bb8`;
see `evidence/palomar-preflight-8c1ffa95.json`. The final documentation and comment revision
requires its own passing full workflow at its exact commit. User authentication,
submission, automated editorial review, and explicit registration remain.

## Verification infrastructure and external status

The exact official Lean archive is retained locally. The standalone Lean CLI
still fails during executable-location discovery in this environment. An
unmodified Lake executable successfully invokes Lean.Elab.runFrontend with
trustLevel=0; this is the local checking route. It permits `hasSorry` only for
the isolated Challenge and rejects it for implemented modules.

All dependencies remain pinned. Mathlib cache files were fetched by its own
pinned cache implementation; fetching them is not independent kernel replay.
Earlier bulk default leanchecker and lean4lean attempts were unsuccessful and
are retained in historical evidence. They are superseded for independent
proof-data validation by successful runs of the currently required bundled
NanoDa and con-ron kernels, plus Lean's kernel, on the official exports.
Sequential project-module replay also passes for all 50 proof modules.

The runtime refuses Linux namespace creation (`bwrap: Creating new namespace
failed: Operation not permitted`). No sandbox was disabled. Read-only exported
data validation does not evaluate project configuration or execute a source
build. It does not establish Palomar's full sandboxed workflow result.

Abhishek Methuku has confirmed the human formalization author and responsible
maintainer roles and approved Apache-2.0 for the formalization software. The
root license is applied and the pinned Palomar metadata validator passes.
The public repository is complete and the official full preflight above passed.
No human proof-source review is claimed. Editorial review and registration
remain pending. `Solution.lean` supplies the complete conditional proof.
Prior checkpoints are preserved as historical evidence.
