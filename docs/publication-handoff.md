# Publication and Palomar handoff

Assuming the stated Li–Postle vertex-coloring bound for hypergraphs with edges
of sizes 3 and 4, the Lean theorem proves that for every fixed r >= 3 and all
sufficiently large n, every n-vertex hypergraph with edge sizes between 3 and r
and no loose triangle has an independent set of size at least
c_r n^(2/3) (log log n)^(1/3). The manuscript derives the Ramsey consequence
resolving the 2013 Kostochka–Mubayi–Verstraëte conjecture; that deduction is not
yet formalised in this repository.
The source and verification reports are published in the GitHub repository below.
Official full preflight passed at commit `8c1ffa95ef08c6788434011dbb0bc794884e8bb8`.
The report is `evidence/palomar-preflight-8c1ffa95.json`; submission, editorial
review and registration remain pending. Documentation and comment revisions must also
pass the full workflow at their exact commit before intake.

Confirmed publication metadata:

- Human formalization author: Abhishek Methuku.
- Responsible maintainer: Abhishek Methuku.
- Software license: Apache-2.0, applied in the root `LICENSE`.
- Submitter relationship: responsible author or maintainer.

The user explicitly confirmed these choices. Codex's role in generating the
Lean development is recorded under automation. No human proof review is claimed.
The manuscript and dependencies retain their existing rights.

The user authorized publication to methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle.
Run `.github/workflows/palomar-preflight.yml` at the exact full 40-character SHA to be submitted.
The workflow and pipeline input are pinned to the same official revision,
`c02bbeaed888df45c4e28c4e99dba540ad21552a`, with mode `full` and the standard
execution profile. Inspect every report and fix failures before submission.

The prepared submission layout is:

- Repository: `methuku-git-hub/Independent-sets-in-hypergraphs-with-no-loose-triangle`.
- Commit: use the full SHA of the successful full preflight for the final published revision. The original
  local commit bindings are preserved inside the complete verification archive.
- Project path: repository root.
- Comparator path: `comparator.json`.
- Metadata path: `formalization.yaml`.
- Compared theorem: `KMV.main_result`.
- Authorization relationship: `I am a responsible author or maintainer`.

The original task reserves browser authentication and final submission to the
user. The agent must not drive Palomar browser sign-in. An agent/API route would
need separate explicit agreement on the exact repository, commit, paths and
relationship, under Palomar's current protocol. A successful local proof check
or full preflight is not registration. Register only after the review is available
and the user has authorized that permanent action. Preserve private submission
URLs and tokens outside public artifacts.
