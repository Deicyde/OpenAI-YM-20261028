# Third-party software and source attribution

## Build dependencies

The ZIP contains project sources and a Lake lockfile. The compiler, the Lake packages, their binary caches, web assets and their Git repositories are obtained separately. The table records the repository-level license at every pinned revision. Upstream file-specific notices continue to apply.

| Component | Version or revision | Repository license |
|---|---|---|
| Lean 4 and Lake | `v4.32.0` | [Apache-2.0](https://github.com/leanprover/lean4/blob/v4.32.0/LICENSE) |
| plausible | `e12c1910fe85` | [Apache-2.0](https://github.com/leanprover-community/plausible/blob/e12c1910fe855cbfc38803cd4e55543906d5fa62/LICENSE) |
| LeanSearchClient | `c5d5b8fe6e51` | [Apache-2.0](https://github.com/leanprover-community/LeanSearchClient/blob/c5d5b8fe6e5158def25cd28eb94e4141ad97c843/LICENSE) |
| importGraph | `7e9612bf0b9e` | [Apache-2.0](https://github.com/leanprover-community/import-graph/blob/7e9612bf0b9ee66db3cb5b9988a35afc706f5a12/LICENSE) |
| ProofWidgets4 | `6e311e2a844d` | [Apache-2.0](https://github.com/leanprover-community/ProofWidgets4/blob/6e311e2a844da9b2cc3971187df2fe0066947b93/LICENSE) |
| aesop | `a7dbf0c63b69` | [Apache-2.0](https://github.com/leanprover-community/aesop/blob/a7dbf0c63b694e47f425f3dcddbc0e178bb432d3/LICENSE) |
| Qq | `38d591e778f1` | [Apache-2.0](https://github.com/leanprover-community/quote4/blob/38d591e778f100aec9762bb582f9c7f55f50e9dc/LICENSE) |
| batteries | `023ce7d62a05` | [Apache-2.0](https://github.com/leanprover-community/batteries/blob/023ce7d62a0531e22a5331e20b587817a80d49ff/LICENSE) |
| Cli | `88679d088c97` | [MIT](https://github.com/leanprover/lean4-cli/blob/88679d088c9720c27ebdf2ba4dafe17341747f94/LICENSE) |
| Mathlib | `81a5d257c8e4` | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/LICENSE) |

The importGraph HTML template carries its own MIT notice, copyright 2021 Eric Wieser. The Cli MIT notice credits mhuisi. The Lean binary distribution also carries notices for the components bundled in that binary. The exact upstream texts are in [third_party_licenses](third_party_licenses). [Template license](https://github.com/leanprover-community/import-graph/blob/7e9612bf0b9ee66db3cb5b9988a35afc706f5a12/html-template/LICENSE_source) · [Lean binary notices](https://github.com/leanprover/lean4/blob/v4.32.0/LICENSES)

## Included source

[NOTICE](NOTICE) describes the challenge and proof adapters and identifies adaptations from four Mathlib files in nine YM modules. The source review compared the project with 11,353 Lean sources from the pinned libraries and compiler, then inspected matching passages and related proofs. This comparison can identify shared text and traceable adaptations. It cannot establish the origin of every independently reworded passage. Apache-2.0 permits redistribution and modification subject to its terms. Section 4 covers providing the license, retaining applicable notices, marking modified files and carrying relevant upstream NOTICE material where supplied. The copyright and permission notices accompany copied substantial portions of MIT software. [Apache-2.0 §4](https://www.apache.org/licenses/LICENSE-2.0#redistribution) · [Cli MIT license](https://github.com/leanprover/lean4-cli/blob/88679d088c9720c27ebdf2ba4dafe17341747f94/LICENSE)

## Project release status

The public OpenAI maths release includes Apache-2.0 at the repository root and in its Lean directory. Its Hodge challenge separately identifies adapted code, including the upstream authors and specific Mathlib source. This project is released under the same [Apache-2.0 license](LICENSE). Its NOTICE follows the source-attribution pattern in the maths release. The dependency inventory and local license copies preserve the separate upstream terms. [Public Lean license](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/LICENSE) · [Hodge notice](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/ComparatorChallenges/HodgeConjectureCMAbelianVarieties/NOTICE)
