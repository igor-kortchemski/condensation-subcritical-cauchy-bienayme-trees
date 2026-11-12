# GitHub and Palomar publication preparation

The requested destination is **both GitHub and Palomar**. This record prepares
that work; it does not certify a finished formalization or a passing registry
submission. The mathematical scope and current proofs are tracked in
[FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md).

## Sources checked

Read-only checks on 29 October 2026 resolved the following immutable revisions:

| Source | Revision | Relevant files |
| --- | --- | --- |
| Palomar policy | `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60` | [Submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md), [protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/docs/specification.md) |
| Palomar verification pipeline | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` | [Reusable workflow](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/.github/workflows/submission.yml), [README](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md) |
| Official template | `2891de4c48955af824969a263d31b25e7a9a1406` | [Metadata example](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/formalization.yaml), [Comparator configuration](https://github.com/PalomarRegistry/PalomarTemplate/blob/2891de4c48955af824969a263d31b25e7a9a1406/comparator.json) |
| Upstream metadata schema | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e` | [v0.4 schema](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json) |

These revisions describe the preparation baseline. Refresh binding policy and
the pipeline before a future submission; do not silently substitute moving
branch heads for recorded verification inputs.

## Environment and interface design

The checked [toolchain policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/toolchains.json)
sets a minimum of `v4.35.0-rc2`. The pinned Lean 4.35.0 is newer, and the pinned
Mathlib revision uses precisely Lean 4.35.0. No toolchain change is needed on
that basis. Mathlib is a permitted statement dependency in the checked
[allowlist](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/allowed-challenge-repositories.json).

Plan one `Challenge.lean`, one `Solution.lean`, and one `comparator.json` at the
project root. Challenge must reconstruct the advertised statements independently
of the proof implementation. Its imports cannot reach project-specific Lean
modules: include any necessary custom definitions directly in Challenge and
check that they have the same meaning as their Solution counterparts. Keep
the statement interface small. Use `module`, public declarations, and exposed
definition bodies where semantic comparison requires them. These are design
requirements, not evidence that any proposed statement has passed review.

The advertised Solution declarations may be exported from the proved library;
the Challenge and Solution must use the same fully qualified theorem names.
Proof modules must not import Challenge. Do not create theorem holes in the
proof library. The project's existing rule does not yet authorize Challenge
holes either; settle a permitted statement-artifact design before introducing
them.

The Palomar configuration accepts `challenge_module`, `solution_module`, a
nonempty `theorem_names` list, and `permitted_axioms`; optional keys are
`definition_names` and `enable_nanoda`. Its axiom list may contain only
`propext`, `Quot.sound`, and `Classical.choice`. Do not use Lake's newer
`external_kernels` key in the submitted configuration: it is supported by the
local CLI but absent from the checked Palomar configuration allowlist.
See the [configuration rules](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#23-comparator-configuration).

## Verification route

`lake comparator --help` was inspected under the pinned toolchain. It supports
`lake comparator --config comparator.json`. Its default isolation requires
Linux `bubblewrap`; this workspace is Darwin and no `bwrap` executable was
found. Use an appropriate Linux environment for the isolated comparison. An
unsandboxed local run would not supply the requested publication evidence.

For GitHub, prepare ordinary build CI and a separate isolated Comparator check
against the same candidate. Link badges only to real repository checks and
describe their actual status. A local successful `lake build` cannot certify a
future remote CI run, the Challenge's fidelity, or independent kernel replay.

For Palomar, call the pinned official reusable workflow with `mode: full`,
`execution_profile: palomar-standard-v1`, the exact public repository and
40-character candidate commit, and matching `pipeline_commit`. Supply a
12-character lowercase alphanumeric request identifier and the required path
and authorization options. Use the truthful human authorization relationship;
do not copy the template's personal declaration. Inspect
`mechanical-report.json`, including exact source/pipeline identities and Lean
and NanoDa outcomes. The preparation-only `preflight` mode is insufficient.
See the pinned [pipeline instructions](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md).

## Candidate contents and metadata

Preserve `lean-toolchain`, the single Lakefile, and `lake-manifest.json` in the
candidate. Exclude generated dependency/build state. Audit the final export
against the source, layout, size, dependency, and licensing requirements of the
pinned policy. Keep the mathematical report, statement review, axiom evidence,
and candidate identity together so claims remain traceable.

Use `formalization.yaml` v0.4. It must distinguish the paper's bibliographic
authors from the humans responsible for the Lean work. Record the source as
arXiv:2503.07530v2, describe the exact proved scope, and disclose material AI
contributions under automation. Agent statement reviews must be labeled as such,
without implying human review. Palomar imposes additional requirements beyond
the upstream schema; checking only JSON Schema is insufficient.

The user selected **Apache-2.0** for the new Lean code and designated
**Igor Kortchemski** as formalization author and maintainer on 29 October 2026.
The root `LICENSE` and draft `formalization.yaml` reflect that choice.
The existing skill licenses continue to cover the copied skill material;
the manuscript and figure are not relicensed by the code license.

The intended repository is
`igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees`. The GitHub
account was checked through the connected account. The user explicitly
conditioned repository creation on completion of the final deliverable.
No repository has been created and no code has been published.
`CITATION.cff` distinguishes the incomplete Lean artifact from the paper.

The prepared `.github/workflows/lean.yml` runs a build, the project's axiom audit,
and Lean kernel replay on Linux. Its action references are pinned to inspected
commits. It has not run on GitHub and does not include or claim a Comparator pass.
CI and Comparator badges remain absent until real checks and URLs exist.
The classification `60J80` was checked against the
[AMS MSC database](https://mathscinet.ams.org/mathscinet/search/mscbrowse.html?pc=60J).

On 1 November 2026 the user authorized reuse of the random-tree and declumping
projects. The [BGW snapshot](../Vendor/BGW/README.md) is now included as source
in this repository, with Apache-2.0 notices and a recorded local working-tree
snapshot. It adds no external path dependency and does not change the pinned
Lean or Mathlib versions. Proposition 2.1 and several actual survival/height
components are now proved. A later milestone completes Lemma 4.4(ii), the
survival ratio and independent-forest height estimates, including ceiling height
indices and floor component counts. The logarithmic-forest milestone also proves
first-order independent-forest concentration, both logarithmic survival
threshold limits and the source auxiliary parameter choice. The Introduction
results remain open.

The eventual Comparator Challenge must still satisfy the dependency and size
rules at verification time. Vendoring BGW does not itself establish that it is
an allowed Challenge import. Review the final statement closure and refresh
the policy baseline before claiming a publishable comparison interface.

## Unresolved publication obligations

| Obligation | Current evidence or remaining action |
| --- | --- |
| Complete mathematical scope | Use the result inventory and formalization report; no completion claim is made here. |
| Reviewed comparison interface | Settled 11 November 2026: `Challenge.lean`, `Solution.lean`, `comparator.json` with the 20 frozen, author-approved statements; the official Comparator confirms that the Challenge's definitions and statements are identical to the development's. |
| Human authors and maintainers | Igor Kortchemski, explicitly designated by the user. AI contributions are disclosed. |
| Root license | Apache-2.0, explicitly selected by the user; root license added. |
| Public repository and candidate commit | Created private on 11 November 2026 for the official Comparator; recreated with a single commit `e112dcf` and made **public** on 12 November 2026 at the author's request. The earlier history is kept in a private backup. |
| Metadata and citation record | `formalization.yaml` and `CITATION.cff` describe the completed formalization (from `publication/`, 12 November 2026). |
| Build, axiom audit, and kernel replay | The measurable-analysis build passed without warnings (3242 jobs); the audit passed for 987 declarations with only permitted axioms; all 42 project modules passed kernel replay. The unchanged 28 vendored BGW modules retain earlier replay evidence. The later integrated-tail/centering batch also passed its build (3249 jobs), audit (1035 declarations) and focused replay of all six new modules. Lemma 2.2 is now covered under the approved convention; all Introduction conclusions remain open. See verification records for exact commands and scope. The final clean public candidate still requires verification. |
| Linux Comparator and independent verification | Passed 12 November 2026 on the public commit `e112dcf` (run 43164576822, `verification/2026-11-12-official-comparator/`; build workflow run 43164523853). Earlier, passed 11 November 2026: official sandboxed `lake comparator` with NanoDa and the Lean kernel on the final candidate `87dbd05` (run 43078769747, `verification/2026-11-11-official-comparator-final/`; earlier on `ab42946`, run 43072119896). Linux build, axiom audit and full kernel replay passed (run 43078767972), and so did the full local kernel replay of 169 project and 36 BGW modules. |
| Full official mechanical report | Not run. Requires the public candidate and truthful workflow options; the policy and pipeline revisions recorded above were still current on 11 November 2026. |
| Registry intake and registration | Neither requested as an external action nor performed. A preparation request does not publish the work. |

These outstanding publication decisions do not prevent independent mathematical
development. Complete the authorized work and present the concrete candidate
before requesting any remaining decision needed for publication.
