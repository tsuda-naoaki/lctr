LCTR verification supplement
Formal correspondence and finite source-survey computations

Scope
-----
This release covers all 908 recorded source responsibilities in Chapters 2-6:
233 assertions, 348 definitions, 231 proof blocks, and 96 context or restatement
blocks. Chapter totals are 23, 48, 291, 217, and 329 respectively.

This release records each source responsibility at component granularity: types,
quantification, premises, domains, conclusions, dependencies, and the native
encoding in Lean and Isabelle. The 908 responsibilities have 1,200 mapped
components and 9,066 bilingual formula-occurrence locations. The occurrence
count includes references to parameters and inherited premises; it is not a
count of independent mathematical objects or theorems.

The proof-body correspondence traces every responsibility through the native
proofs, definitions, theorem dependencies, local premises and dependent-type
or carrier conditions. The findings are in
inventory/proof-body-correspondence.json and in each entry of correspondence.html.

The construction figure has six panels and 12 bilingual caption references,
recorded in inventory/figure-correspondence.json.

The proof sources use 188 formalization units with 1,982 paired Lean/Isabelle
roots. Lean checks 222 positive modules and two expected-rejection controls.
Isabelle checks 191 target sessions, covering 283 theory source files and their
dependencies. The same Lean root set is exported and rechecked by nanoda and
con-leche. Native type/axiom output is supplied for all 1,982 Lean roots.

The separately distributed PDFs are identified by filename and SHA-256 in
inventory/pdf-editions.json and PDF-SHA256SUMS. This archive contains one
shared verification set, with Japanese and English source correspondence;
it contains no PDF copies. Place the required PDFs in pdf/ to follow the
local links. See pdf/README.txt. Native proof checks do not require PDFs.
The paired Lean/Isabelle formalizations cover Chapters 2-6. The accompanying source-survey computation
reproduces the finite reachability, structure signatures and counts used in
Chapters 7, 8 and the source appendix.

Start with correspondence.html. Its 908 entries link the source responsibilities
to the Japanese and English PDFs, the component meanings, and the published
native declarations. The machine-readable files are:

  inventory/correspondence.json           source responsibilities and clauses
  inventory/component-correspondence.json exact components and native excerpts
  inventory/formula-occurrences.json      occurrences and their reviewed roles
  inventory/formal-root-pairs.json        paired native proof declarations

For unlabelled prose, the PDF link leads to its preceding anchor; proof entries
refer to the result being proved. Formula occurrences share their enclosing
responsibility's PDF anchor. This does not assign a separate equation number.
Native excerpt offsets and line numbers refer to the distributed formal source.

Auxiliary checks and native metadata
-----------------------------------
Seven auxiliary groups cover the finite failure graph, four-state evaluation,
frequency and period identities, finite polynomial jets, the law-candidate
partial-output map, finite-real margin arithmetic, and coordinate units.
AUXILIARY.txt gives the domains, tools and direct execution instructions.
The 46 paired auxiliary proof roots are counted separately from the core roots.
The full entry point runs the core checks, auxiliary checks and native metadata
queries. inventory/auxiliary-correspondence.json links each checked slice to its
manuscript responsibility and formal results.

Native metadata records types, theorem dependencies, axiomatic dependencies and
oracle dependencies. The mathematical component correspondence and the native
derivation data are stored separately. The metadata query sources introduce no
mathematical definitions, assumptions or theorems.

Contents
--------
pdf/                 Placement instructions for separately distributed PDFs
lean/                Current Lean sources and the root statement/axiom query
isabelle/            Current Isabelle theories and session definitions
inventory/           Correspondence, root pairs, source files and build inputs
survey/              Finite survey data, computations, results and instructions
environment/         Pinned tool/library identities and checker configuration
reports/             Successful native-tool reports and the checked proof export
auxiliary/           Final SMT, CAS, unit and semantic-representation inputs
queries/             Native metadata queries and XML expression transformations
SHA256SUMS           Identities of all files contained in this release
PDF-SHA256SUMS       Identities of separately distributed manuscript PDFs
reproduce.sh         Entry point for native-tool reruns
reproduce.py         Command scheduling and result collection
runtime_paths.py     Root-relative path handling and host-path-free logs

The proof export includes the referenced declarations and their dependencies.
reports/lean-statements/statements.txt contains native Lean type and axiom
output for every listed root. Isabelle theory sources include the theorem
statements, proofs and oracle-dependency checks used in the recorded sessions.

Environment
-----------
Use Lean 4.33.1 and the Mathlib commit in environment/lean.json. Use
Isabelle2025-2. Build lean4export, nanoda and con-leche at the commits in
environment/checkers.json, using each project's own pinned toolchain.
Their repositories are listed there. Mathlib dependencies and compiled caches
are obtained using Mathlib's native Lake commands at that pinned revision.

Work from the extracted lctr-verification directory. Every supplied filesystem
path is relative to that root and stays inside it. Place external checkouts and
non-PATH tool files under tools/. Executables may also be specified by command
name on PATH; no host installation path is recorded in the distribution.

Set the following variables to relative paths or executable command names:

  LCTR_MATHLIB       tools/mathlib (the pinned Mathlib checkout)
  LCTR_LEAN         Lean 4.33.1 executable (default: lean)
  LCTR_LAKE         Lake for Lean 4.33.1 (default: lake)
  LCTR_ISABELLE     Isabelle2025-2 executable (default: isabelle)
  LCTR_LEAN4EXPORT  lean4export executable (default: lean4export)
  LCTR_NANODA       nanoda executable (default: nanoda_bin)
  LCTR_CON_LECHE    con-leche executable (default: con-leche)

From the extracted directory, run:

  python3 reproduce.py --output reports/runs/check-01

To reproduce the finite survey computation alone:

  python3 reproduce.py --steps survey --output reports/runs/survey-01

survey/README.txt defines its inputs, closures and generation bounds.

To recheck the supplied export directly, without rebuilding Lean or Isabelle:

  python3 reproduce.py --steps recheck --output reports/runs/recheck-01

Each underlying command can also be run directly. The Lean module order and
Isabelle arguments are in inventory/lean-modules.json and
inventory/isabelle-builds.json. The entry point uses the compatible native
session groups in inventory/isabelle-grouped-builds.json, so shared dependencies
are checked through the native build graph without repeated forced cleaning.
Relative paths are resolved from this directory.
The two entries in inventory/lean-negative-controls.json are expected to be
rejected; they are not positive proof modules and are not imported by LCTRCore.

For direct independent rechecking:

  gzip -dc reports/independent/proof.ndjson.gz > proof.ndjson
  nanoda_bin environment/nanoda.json < proof.ndjson
  con-leche --verified proof.ndjson

The rerun wrapper verifies file hashes, invokes these standard tools, and saves
their output. Source correspondence is recorded separately from tool execution.

Path representation
-------------------
Saved filenames, report links and user-supplied paths are relative to the
extracted root. Absolute paths and paths escaping that root are rejected.
Native tools may resolve files internally; the wrapper converts paths in their
output to root-relative form before saving or displaying them. Host paths that
do not identify a distributed or locally supplied file are replaced by
<host-path omitted>. This affects path metadata, not mathematical expressions,
proof exports, solver verdicts or return codes. Failure messages use the same
handling and do not expose interpreter traceback paths.

LCTR v1.0.1
DOI: 10.5281/zenodo.23273388
https://doi.org/10.5281/zenodo.23273388

Eight PDFs are distributed separately: full, main-only, supplement-only, and
figure collections in Japanese and English. The figure collections retain the
full-edition figure numbers, captions, and reference destinations.
