<!-- Path: leanasm/docs/openai-20261028/MANIFEST.md -->
<!-- Max Column: 80 Columns -->

# OpenAI 2026-10-28 YM Submission Manifest

## 1. Corpus Overview

- **Root**: subrepos/YM/submissions/openai-20261028
- **Total Files**: 9,782
- **Total Bytes**: 112,942,762
- **Total Lines**: 1,559,828
- **Full Digests**: See `MANIFEST.json` for all SHA-256 hashes.

## 2. Lean Toolchains & Lake Dependencies

- `submission/lean-toolchain`: `leanprover/lean4:v4.32.0`
- `verification/controls/accept/lean-toolchain`: `leanprover/lean4:v4.32.0`
- `verification/controls/definition_mismatch/lean-toolchain`:
  `leanprover/lean4:v4.32.0`
- `verification/controls/forbidden_axiom/lean-toolchain`:
  `leanprover/lean4:v4.32.0`
- `verification/controls/statement_mismatch/lean-toolchain`:
  `leanprover/lean4:v4.32.0`
- **submission/lakefile.toml**: ym_core v0.1.0; targets: WilsonReference,
  WilsonConstruction
- **dep `mathlib`**: https://github.com/leanprover-community/mathlib4.git @
  81a5d257c8e4
- **verification/controls/accept/lakefile.toml**: comparator_control v0.1.0;
  targets: (none)
- **verification/controls/definition_mismatch/lakefile.toml**:
  comparator_control
  v0.1.0; targets: (none)
- **verification/controls/forbidden_axiom/lakefile.toml**: comparator_control
  v0.1.0; targets: (none)
- **verification/controls/statement_mismatch/lakefile.toml**: comparator_control
  v0.1.0; targets: (none)

### Lake Manifest: `submission/lake-manifest.json`

| Package          | InputRev                                 | RevPrefix    |
| ---------------- | ---------------------------------------- | ------------ |
| plausible        | main                                     | e12c1910fe85 |
| LeanSearchClient | main                                     | c5d5b8fe6e51 |
| importGraph      | main                                     | 7e9612bf0b9e |
| proofwidgets     | main                                     | 6e311e2a844d |
| aesop            | master                                   | a7dbf0c63b69 |
| Qq               | master                                   | 38d591e778f1 |
| batteries        | main                                     | 023ce7d62a05 |
| Cli              | v4.32.0                                  | 88679d088c97 |
| mathlib          | 81a5d257c8e410db227a6665ed08f64fea08e997 | 81a5d257c8e4 |

## 3. Counts by Category & Top Directory

| Category | Files |
| -------- | ----- |
| bytecode | 1     |
| checksum | 3     |
| config   | 10    |
| data     | 68    |
| docs     | 10    |
| lean     | 9564  |
| license  | 4     |
| log      | 100   |
| other    | 2     |
| script   | 7     |
| text     | 13    |

| TopDir       | Files | Lean | Bytes      | Lines     |
| ------------ | ----- | ---- | ---------- | --------- |
| (root)       | 4     | 0    | 16,844     | 275       |
| checks       | 43    | 43   | 270,457    | 5,762     |
| docs         | 11    | 7    | 87,842     | 1,638     |
| evidence     | 151   | 0    | 11,768,373 | 222,694   |
| provenance   | 37    | 27   | 3,286,520  | 69,293    |
| runs         | 1     | 0    | 2,504      | 61        |
| scripts      | 1     | 0    | 16,297     | 289       |
| submission   | 9508  | 9477 | 97,489,911 | 1,259,647 |
| verification | 26    | 10   | 4,014      | 169       |

## 4. `submission/YM` Subpackage Breakdown

| Subpkg              | Files | Lean | Lines   |
| ------------------- | ----- | ---- | ------- |
| (YM-root)           | 3     | 3    | 374     |
| Ac                  | 3     | 3    | 354     |
| Analysis            | 11    | 11   | 1,160   |
| Analytic            | 3     | 3    | 228     |
| AnalyticBridge      | 421   | 421  | 55,903  |
| AnalyticNext        | 554   | 554  | 62,457  |
| Axis                | 2     | 2    | 179     |
| Bid                 | 18    | 18   | 1,957   |
| Boundary            | 1     | 1    | 123     |
| Branch              | 9     | 9    | 1,246   |
| CellFourier         | 4     | 4    | 440     |
| Cells               | 17    | 17   | 1,931   |
| Climb               | 4     | 4    | 418     |
| Compact             | 3     | 3    | 305     |
| Complex             | 3     | 3    | 579     |
| Contact             | 3     | 3    | 323     |
| Contacts            | 75    | 75   | 7,185   |
| Corona              | 4     | 4    | 461     |
| Dash                | 7     | 7    | 759     |
| Distribution        | 2     | 2    | 284     |
| Euclid              | 14    | 14   | 1,753   |
| EveryPhase          | 34    | 34   | 5,268   |
| Examples            | 1     | 1    | 112     |
| Extension           | 57    | 57   | 5,330   |
| Exterior            | 3     | 3    | 339     |
| Extra               | 232   | 232  | 29,773  |
| Extraction          | 22    | 22   | 2,663   |
| Fields              | 7     | 7    | 875     |
| Frontier6           | 3     | 3    | 262     |
| FullVolume          | 653   | 653  | 53,514  |
| Further             | 284   | 284  | 34,225  |
| Gauge               | 8     | 8    | 1,352   |
| Ground              | 5     | 5    | 804     |
| Heat                | 5     | 5    | 555     |
| Hilbert             | 1     | 1    | 129     |
| Independent         | 2     | 2    | 99      |
| Integration         | 32    | 32   | 2,968   |
| Labels              | 6     | 6    | 769     |
| Lane                | 1     | 1    | 125     |
| Lattice             | 10    | 10   | 1,325   |
| Laurent             | 4     | 4    | 476     |
| LocalH              | 2     | 2    | 257     |
| Marker              | 3     | 3    | 388     |
| Maxwell             | 9     | 9    | 1,333   |
| MergeProof          | 428   | 428  | 28,372  |
| Mink                | 4     | 4    | 563     |
| MultiNext           | 89    | 89   | 9,882   |
| MultipleContact     | 150   | 150  | 12,878  |
| Next                | 693   | 693  | 113,929 |
| Nonperturbative     | 3     | 3    | 263     |
| OPE                 | 211   | 211  | 16,003  |
| OS                  | 8     | 8    | 1,003   |
| Org                 | 4     | 4    | 432     |
| Ovens               | 1     | 1    | 135     |
| Overlay             | 9     | 9    | 1,015   |
| PCalc               | 4     | 4    | 422     |
| PREC                | 6     | 6    | 757     |
| Paley               | 4     | 4    | 367     |
| Pert                | 115   | 115  | 8,509   |
| PertExtension       | 33    | 33   | 4,069   |
| Phase               | 6     | 6    | 739     |
| PhysicalNext        | 874   | 874  | 84,978  |
| Planned             | 197   | 197  | 22,537  |
| Pressure            | 7     | 7    | 1,158   |
| Price               | 3     | 3    | 531     |
| Primitives          | 56    | 56   | 6,614   |
| Progress            | 63    | 63   | 8,167   |
| ProjectorNext       | 66    | 66   | 7,913   |
| ProofPorts          | 18    | 18   | 2,180   |
| Push                | 553   | 553  | 69,943  |
| R2I                 | 20    | 20   | 2,562   |
| RG                  | 10    | 10   | 1,621   |
| RG05Readout         | 70    | 70   | 6,487   |
| RG08                | 857   | 857  | 68,319  |
| RG12                | 75    | 75   | 5,111   |
| RG17                | 11    | 11   | 1,471   |
| RemainderComparison | 322   | 322  | 29,752  |
| SNAG                | 5     | 5    | 558     |
| SectorNext          | 133   | 133  | 20,810  |
| SectorTools         | 34    | 34   | 4,751   |
| SharpGram           | 27    | 27   | 3,163   |
| Shift               | 8     | 8    | 968     |
| Shoot               | 3     | 3    | 352     |
| Slice               | 15    | 15   | 1,946   |
| Source              | 6     | 6    | 873     |
| Space               | 3     | 3    | 440     |
| Spark               | 2     | 2    | 183     |
| Spec                | 1     | 1    | 91      |
| Spectral            | 2     | 2    | 150     |
| Spin                | 6     | 6    | 568     |
| TimeKernel          | 2     | 2    | 228     |
| Trace               | 16    | 16   | 2,829   |
| Trace2              | 1     | 1    | 263     |
| TraceExtension      | 718   | 718  | 50,636  |
| Tree                | 2     | 2    | 229     |
| UVExt               | 6     | 6    | 906     |
| UVExtension         | 509   | 509  | 39,810  |
| UVNext              | 96    | 96   | 12,361  |
| Vac                 | 3     | 3    | 425     |
| Ward                | 12    | 12   | 1,476   |
| Wilson              | 2     | 2    | 236     |
| WilsonBulk          | 161   | 161  | 12,705  |
| Work                | 169   | 169  | 28,993  |

## 5. Non-`submission/YM` File Digest Sample

All files outside `submission/YM/` (and root `submission/*.lean` files) are
listed below with size, lines, and 12-char SHA-256 prefixes. Full 64-char
digests for all files reside in `MANIFEST.json`.

- `.gitignore` (other, 58 B, 6 L, sha256:eed4048afb52)
- `LICENSE` (license, 11357 B, 201 L, sha256:c71d239df917)
- `NOTICE` (license, 1502 B, 24 L, sha256:265c3c1c625d)
- `README.md` (docs, 3927 B, 44 L, sha256:6982d8adecb6)
- `checks/AFSourceBridge.lean` (lean, 3114 B, 78 L, sha256:d018eec93969)
- `checks/AcceptanceSpec.lean` (lean, 9292 B, 178 L, sha256:c303146d967b)
- `checks/ArityGrowth.lean` (lean, 7844 B, 163 L, sha256:cefb98ba14f6)
- `checks/AxiomAudit.lean` (lean, 486 B, 12 L, sha256:776d80a3f7c6)
- `checks/ClusterCones.lean` (lean, 4913 B, 104 L, sha256:4492d6f33624)
- `checks/ClusterCore.lean` (lean, 3559 B, 73 L, sha256:8ad237a73526)
- `checks/ClusterDomination.lean` (lean, 3527 B, 79 L, sha256:03a2d2c42b48)
- `checks/ClusterKernel.lean` (lean, 4126 B, 92 L, sha256:dc25d6d7dc57)
- `checks/ClusterSchwartz.lean` (lean, 6521 B, 134 L, sha256:9ac62c789eda)
- `checks/ClusterTarget.lean` (lean, 4170 B, 93 L, sha256:fa4330a75ad9)
- `checks/CombinedAcceptance.lean` (lean, 6192 B, 122 L, sha256:40f8c57aa96d)
- `checks/CommonScaleAudit.lean` (lean, 3615 B, 94 L, sha256:ac9b14ad7532)
- `checks/CompleteOS.lean` (lean, 3653 B, 82 L, sha256:4c4fdc2170e3)
- `checks/CompletenessAudit.lean` (lean, 3454 B, 78 L, sha256:36c15bb8b5e3)
- `checks/Coordinates.lean` (lean, 3103 B, 83 L, sha256:58e73fa62750)
- `checks/ImportedAFGauge.lean` (lean, 6425 B, 140 L, sha256:136d59e698dd)
- `checks/ImportedAFSpecification.lean` (lean, 2917 B, 71 L,
sha256:a80bf741dd9f)
- `checks/ImportedCenterWeights.lean` (lean, 1403 B, 34 L, sha256:0df3139e83cc)
- `checks/ImportedDiagonalFlatBounds.lean` (lean, 18687 B, 370 L,
sha256:0dfa0b6b39af)
- `checks/ImportedLGTData.lean` (lean, 4329 B, 121 L, sha256:7e1ff512f011)
- `checks/ImportedReflectionApproximation.lean` (lean, 9256 B, 190 L,
sha256:9f6ad873fd0d)
- `checks/ImportedSchwartzCutoffs.lean` (lean, 8466 B, 183 L,
sha256:6f6fdb12027c)
- `checks/ImportedSchwartzDomain.lean` (lean, 1114 B, 27 L, sha256:da32cc3c4906)
- `checks/ImportedSchwartzProduct.lean` (lean, 11399 B, 222 L,
sha256:a327d573d777)
- `checks/Invariance.lean` (lean, 6669 B, 140 L, sha256:2a0e8864657b)
- `checks/LGTWilsonBridge.lean` (lean, 5914 B, 135 L, sha256:59a4c89ba23a)
- `checks/NonzeroPhysicalObservable.lean` (lean, 5286 B, 126 L,
sha256:34bf80e0c292)
- `checks/OPECheck.lean` (lean, 4567 B, 89 L, sha256:ef5926e323e8)
- `checks/OPESpec.lean` (lean, 2324 B, 45 L, sha256:3ea7ffb5f7b3)
- `checks/ReflectionPositivity.lean` (lean, 2968 B, 58 L, sha256:a5a1e3456b05)
- `checks/ReflectionTransport.lean` (lean, 7380 B, 151 L, sha256:21c7c59a934a)
- `checks/RemainingObligations.lean` (lean, 4910 B, 101 L, sha256:03c85631c118)
- `checks/SourceScalar.lean` (lean, 3288 B, 74 L, sha256:8c39b1a21513)
- `checks/TargetKernel.lean` (lean, 5338 B, 113 L, sha256:e8510fa51b8d)
- `checks/Temperedness.lean` (lean, 5304 B, 117 L, sha256:cdc87faf64a6)
- `checks/TwoPointPhysicalObservable.lean` (lean, 8133 B, 172 L,
sha256:bd2a2cc959f3)
- `checks/WardFormulationAudit.lean` (lean, 3198 B, 67 L, sha256:5943d1d891f9)
- `checks/YangMills/OSRecon/Growth.lean` (lean, 7855 B, 152 L,
sha256:9ceba1c37449)
- `checks/YangMills/OSRecon/Vendored/Axioms.lean` (lean, 11542 B, 224 L,
sha256:a0e70dabf0c0)
- `checks/YangMills/OSRecon/Vendored/OSConj.lean` (lean, 14096 B, 302 L,
sha256:d717b96a013c)
- `checks/YangMills/OSRecon/Vendored/Spacetime.lean` (lean, 15637 B, 354 L,
sha256:efcaee7bec7c)
- `checks/YangMills/OSRecon/Vendored/TensorProduct.lean` (lean, 12325 B, 238 L,
sha256:78cbd9de6446)
- `checks/YangMills/OSRecon/Vendored/ZeroDiagonal.lean` (lean, 12158 B, 281 L,
sha256:160576436d6e)
- `docs/checks.md` (docs, 6846 B, 45 L, sha256:169e7b3d0433)
- `docs/examples/.gitignore` (other, 74 B, 9 L, sha256:ea3e6ba51810)
- `docs/examples/CommonOPE-20261028.lean` (lean, 8086 B, 174 L,
sha256:e041afb3989b)
- `docs/examples/LatticeAndScale-20261028.lean` (lean, 8122 B, 180 L,
sha256:4a85e9b74893)
- `docs/examples/LeadingTrace-20261028.lean` (lean, 17212 B, 357 L,
sha256:8c90d7f53ba7)
- `docs/examples/OSAxioms-20261028.lean` (lean, 8182 B, 180 L,
sha256:414368346561)
- `docs/examples/OctoberChain.lean` (lean, 14677 B, 298 L, sha256:0cdf5fb7d1a5)
- `docs/examples/OperatorContent-20261028.lean` (lean, 6670 B, 153 L,
sha256:3c0cb1eb1efe)
- `docs/examples/README.md` (docs, 5561 B, 49 L, sha256:286f81681956)
- `docs/examples/TranslationWard-20261028.lean` (lean, 5614 B, 129 L,
sha256:5d5da9a434a3)
- `docs/rerun.md` (docs, 6798 B, 64 L, sha256:d646239b8200)
- `evidence/README.md` (docs, 4596 B, 29 L, sha256:8cd7c2f91e92)
- `evidence/documentation-2026-11-10/result.json` (data, 2468 B, 61 L,
sha256:17ac0023635e)
- `evidence/examples-2026-11-10/LeadingTrace-20261028.log` (log, 1428 B, 18 L,
sha256:170035dc8fff)
- `evidence/examples-2026-11-10/OctoberChain.log` (log, 766 B, 7 L,
sha256:22eb74eb480e)
- `evidence/examples-2026-11-10/README.md` (docs, 1587 B, 9 L,
sha256:639186ff9f97)
- `evidence/examples-2026-11-10/additional/CommonOPE-20261028.log` (log, 798 B,
9 L, sha256:1354ae01c5bd)
- `evidence/examples-2026-11-10/additional/LatticeAndScale-20261028.log` (log,
1407 B, 27 L, sha256:9ec59ded1a00)
- `evidence/examples-2026-11-10/additional/OPECheck.log` (log, 441 B, 5 L,
sha256:5cab3e5c20ae)
- `evidence/examples-2026-11-10/additional/OPESpec.log` (log, 0 B, 0 L,
sha256:e3b0c44298fc)
- `evidence/examples-2026-11-10/additional/OSAxioms-20261028.log` (log, 1007 B,
11 L, sha256:9a4fcda590f1)
- `evidence/examples-2026-11-10/additional/OperatorContent-20261028.log` (log,
881 B, 15 L, sha256:8cc7fb74a374)
- `evidence/examples-2026-11-10/additional/README.md` (docs, 2589 B, 21 L,
sha256:4026256085ef)
- `evidence/examples-2026-11-10/additional/TranslationWard-20261028.log` (log,
505 B, 10 L, sha256:5fc8ec6fed74)
- `evidence/examples-2026-11-10/additional/result.json` (data, 18968 B, 538 L,
sha256:317684e76a17)
- `evidence/examples-2026-11-10/references/LeadingTrace-20261028.log` (log, 1428
B, 18 L, sha256:170035dc8fff)
- `evidence/examples-2026-11-10/references/result.json` (data, 5388 B, 133 L,
sha256:77bd8118bc2b)
- `evidence/examples-2026-11-10/result.json` (data, 8698 B, 229 L,
sha256:6f064a5baeae)
- `evidence/release-2026-11-05/README.md` (docs, 1100 B, 12 L,
sha256:4b50eedf0c14)
- `evidence/release-2026-11-05/build/dependency-cache.log` (log, 250 B, 7 L,
sha256:86dbc1f0b19b)
- `evidence/release-2026-11-05/build/result.json` (data, 303234 B, 2599 L,
sha256:a2f6f74246ae)
- `evidence/release-2026-11-05/build/runner-source.py` (script, 16297 B, 289 L,
sha256:24e71f5e3795)
- `evidence/release-2026-11-05/build/submission-build.log` (log, 925995 B, 15305
L, sha256:e2f7965cc0eb)
- `evidence/release-2026-11-05/controls/control-accept.log` (log, 2376 B, 18 L,
sha256:1198203ae30a)
- `evidence/release-2026-11-05/controls/control-definition_mismatch.log` (log,
2353 B, 16 L, sha256:a2602c8c3f91)
- `evidence/release-2026-11-05/controls/control-forbidden_axiom.log` (log, 2328
B, 16 L, sha256:0f8ec3770ebf)
- `evidence/release-2026-11-05/controls/control-statement_mismatch.log` (log,
2364 B, 16 L, sha256:f12b957c606e)
- `evidence/release-2026-11-05/controls/result.json` (data, 6109 B, 148 L,
sha256:7f8cb00ec5d8)
- `evidence/release-2026-11-05/controls/runner-source.py` (script, 16297 B, 289
L, sha256:24e71f5e3795)
- `evidence/release-2026-11-05/files.sha256.json` (data, 7940 B, 76 L,
sha256:0e7920c2242a)
- `evidence/release-2026-11-05/ope-comparator/comparator-ope.log` (log, 928789
B, 15324 L, sha256:987a68b244cd)
- `evidence/release-2026-11-05/ope-comparator/control-accept.log` (log, 2370 B,
18 L, sha256:5022eb158bb5)
- `evidence/release-2026-11-05/ope-comparator/control-definition_mismatch.log`
(log, 2347 B, 16 L, sha256:c7b2ae9be959)
- `evidence/release-2026-11-05/ope-comparator/control-forbidden_axiom.log` (log,
2322 B, 16 L, sha256:f04c93f320a4)
- `evidence/release-2026-11-05/ope-comparator/control-statement_mismatch.log`
(log, 2358 B, 16 L, sha256:82ce732fdf09)
- `evidence/release-2026-11-05/ope-comparator/package-files-at-start.json`
(data, 20019 B, 171 L, sha256:365d08b7ca45)
- `evidence/release-2026-11-05/ope-comparator/result.json` (data, 7910 B, 209 L,
sha256:9da7e3595cdb)
- `evidence/release-2026-11-05/ope-comparator/runner-source.py` (script, 15452
B, 271 L, sha256:03b8e6f5ebc4)
- `evidence/release-2026-11-05/review/result.json` (data, 59595 B, 1724 L,
sha256:c908058be669)
- `evidence/release-2026-11-05/review/review-AFSourceBridge.log` (log, 0 B, 0 L,
sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-AcceptanceSpec.log` (log, 0 B, 0 L,
sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ArityGrowth.log` (log, 290 B, 3 L,
sha256:424c416ffdae)
- `evidence/release-2026-11-05/review/review-AxiomAudit.log` (log, 945 B, 10 L,
sha256:4f1ae53cd6bd)
- `evidence/release-2026-11-05/review/review-ClusterCones.log` (log, 391 B, 4 L,
sha256:8ba8d52dbb94)
- `evidence/release-2026-11-05/review/review-ClusterCore.log` (log, 474 B, 5 L,
sha256:83b5e04599a2)
- `evidence/release-2026-11-05/review/review-ClusterDomination.log` (log, 99 B,
1 L, sha256:c8f8cdd9f5f3)
- `evidence/release-2026-11-05/review/review-ClusterKernel.log` (log, 198 B, 2
L, sha256:aeafdfb4ef64)
- `evidence/release-2026-11-05/review/review-ClusterSchwartz.log` (log, 292 B, 3
L, sha256:23436c7ea1d8)
- `evidence/release-2026-11-05/review/review-ClusterTarget.log` (log, 201 B, 2
L, sha256:7bafdc54a4ea)
- `evidence/release-2026-11-05/review/review-CombinedAcceptance.log` (log, 0 B,
0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-CommonScaleAudit.log` (log, 1243 B,
12 L, sha256:8dc0c035ec87)
- `evidence/release-2026-11-05/review/review-CompleteOS.log` (log, 438 B, 5 L,
sha256:15cde1d08e7c)
- `evidence/release-2026-11-05/review/review-CompletenessAudit.log` (log, 878 B,
8 L, sha256:f9520e33f2a2)
- `evidence/release-2026-11-05/review/review-Coordinates.log` (log, 0 B, 0 L,
sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedAFGauge.log` (log, 0 B, 0
L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedAFSpecification.log` (log,
0 B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedCenterWeights.log` (log, 0
B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedDiagonalFlatBounds.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedLGTData.log` (log, 0 B, 0
L, sha256:e3b0c44298fc)
-
`evidence/release-2026-11-05/review/review-ImportedReflectionApproximation.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedSchwartzCutoffs.log` (log,
0 B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedSchwartzDomain.log` (log, 0
B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ImportedSchwartzProduct.log` (log,
0 B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-Invariance.log` (log, 447 B, 5 L,
sha256:1a749c9e453d)
- `evidence/release-2026-11-05/review/review-LGTWilsonBridge.log` (log, 0 B, 0
L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-NonzeroPhysicalObservable.log`
(log, 605 B, 6 L, sha256:17a41262dba4)
- `evidence/release-2026-11-05/review/review-OPECheck.log` (log, 441 B, 5 L,
sha256:5cab3e5c20ae)
- `evidence/release-2026-11-05/review/review-OPESpec.log` (log, 0 B, 0 L,
sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-ReflectionPositivity.log` (log, 294
B, 3 L, sha256:925d116b0d00)
- `evidence/release-2026-11-05/review/review-ReflectionTransport.log` (log, 0 B,
0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/review-RemainingObligations.log` (log, 375
B, 4 L, sha256:72935a59bc01)
- `evidence/release-2026-11-05/review/review-SourceScalar.log` (log, 276 B, 3 L,
sha256:484f55bd471b)
- `evidence/release-2026-11-05/review/review-TargetKernel.log` (log, 91 B, 1 L,
sha256:b6dbd04b59ee)
- `evidence/release-2026-11-05/review/review-Temperedness.log` (log, 259 B, 3 L,
sha256:09e45e43b4aa)
- `evidence/release-2026-11-05/review/review-TwoPointPhysicalObservable.log`
(log, 958 B, 9 L, sha256:89e73591736a)
- `evidence/release-2026-11-05/review/review-WardFormulationAudit.log` (log, 417
B, 4 L, sha256:177a28d59e84)
- `evidence/release-2026-11-05/review/review-YangMills.OSRecon.Growth.log` (log,
0 B, 0 L, sha256:e3b0c44298fc)
-
`evidence/release-2026-11-05/review/
review-YangMills.OSRecon.Vendored.Axioms.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
-
`evidence/release-2026-11-05/review/
review-YangMills.OSRecon.Vendored.OSConj.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
-
`evidence/release-2026-11-05/review/
review-YangMills.OSRecon.Vendored.Spacetime.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
-
`evidence/release-2026-11-05/review/
review-YangMills.OSRecon.Vendored.TensorProduct.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
-
`evidence/release-2026-11-05/review/
review-YangMills.OSRecon.Vendored.ZeroDiagonal.log`
(log, 0 B, 0 L, sha256:e3b0c44298fc)
- `evidence/release-2026-11-05/review/runner-source.py` (script, 16297 B, 289 L,
sha256:24e71f5e3795)
- `evidence/release-2026-11-05/summary.json` (data, 1520 B, 41 L,
sha256:d61b45c2d9c2)
- `evidence/release-2026-11-05/tools/build-comparator.log` (log, 801 B, 18 L,
sha256:1149a5699334)
- `evidence/release-2026-11-05/tools/build-lean4export.log` (log, 284 B, 8 L,
sha256:b2a9ff14b12c)
- `evidence/release-2026-11-05/tools/checkout-comparator.log` (log, 62 B, 1 L,
sha256:3c2feb74939b)
- `evidence/release-2026-11-05/tools/checkout-lean4export.log` (log, 62 B, 1 L,
sha256:c0a43df8be21)
- `evidence/release-2026-11-05/tools/clone-comparator.log` (log, 100 B, 1 L,
sha256:24b571776372)
- `evidence/release-2026-11-05/tools/clone-lean4export.log` (log, 101 B, 1 L,
sha256:e914d4083ebf)
- `evidence/release-2026-11-05/tools/package-files-at-start.json` (data, 20019
B, 171 L, sha256:365d08b7ca45)
- `evidence/release-2026-11-05/tools/result.json` (data, 5176 B, 152 L,
sha256:1524248c8c13)
- `evidence/release-2026-11-05/tools/runner-source.py` (script, 15452 B, 271 L,
sha256:03b8e6f5ebc4)
- `provenance/__pycache__/normalization-source.cpython-314.pyc` (bytecode, 9773
B, bin L, sha256:eb596c87ab71)
- `provenance/af/YangMills/Core/GaugeGroup.lean` (lean, 6425 B, 140 L,
sha256:136d59e698dd)
- `provenance/af/YangMills/Core/ShortDistance.lean` (lean, 15053 B, 304 L,
sha256:45f906e4d373)
- `provenance/lgt/LGT/Bridge/ScaleTransfer.lean` (lean, 24304 B, 534 L,
sha256:6941b03ea3e7)
- `provenance/lgt/LGT/GaugeField/Connection.lean` (lean, 2938 B, 74 L,
sha256:19292c525d51)
- `provenance/lgt/LGT/GaugeField/GaugeGroup.lean` (lean, 1047 B, 31 L,
sha256:48245614dcdd)
- `provenance/lgt/LGT/GaugeField/Holonomy.lean` (lean, 18 B, 1 L,
sha256:d1062512c5ad)
- `provenance/lgt/LGT/GaugeField/UnitaryGroup.lean` (lean, 9077 B, 223 L,
sha256:7f03bcf7b7a0)
- `provenance/lgt/LGT/Gibbs/YMIsGibbs.lean` (lean, 44774 B, 961 L,
sha256:6f855d8a19fc)
- `provenance/lgt/LGT/Gibbs/YMSpec.lean` (lean, 20154 B, 458 L,
sha256:c13e11434254)
- `provenance/lgt/LGT/Lattice/CellComplex.lean` (lean, 43633 B, 803 L,
sha256:9c6636593a1c)
- `provenance/lgt/LGT/MassGap/StrongCoupling.lean` (lean, 114229 B, 2232 L,
sha256:b94ede83ae5a)
- `provenance/lgt/LGT/MassGap/YMMeasure.lean` (lean, 14477 B, 349 L,
sha256:fbeb4e5153b9)
- `provenance/lgt/LGT/WilsonAction/WilsonLoop.lean` (lean, 20 B, 1 L,
sha256:b09d838f7e34)
- `provenance/licenses/OSreconstruction.txt` (text, 11357 B, 201 L,
sha256:c71d239df917)
- `provenance/licenses/lgt.txt` (text, 11358 B, 202 L, sha256:cfc7749b96f6)
- `provenance/licenses/yang-mills.txt` (text, 10805 B, 190 L,
sha256:375bd1c170a9)
- `provenance/normalization-source.py` (script, 9015 B, 172 L,
sha256:cfc4d5062003)
- `provenance/october-import.json` (data, 2660381 B, 57063 L,
sha256:1ee2d290dfa6)
- `provenance/os-bridge-excerpts.json` (data, 9686 B, 202 L,
sha256:7ed6634cce13)
- `provenance/osreconstruction.json` (data, 709 B, 17 L, sha256:b9252bf5c5a3)
- `provenance/osreconstruction/Specification.lean` (lean, 14589 B, 287 L,
sha256:2077a663d350)
- `provenance/osreconstruction/Specification/Wightman.lean` (lean, 12773 B, 259
L, sha256:a6ee8103f40e)
- `provenance/package-files.json` (data, 23191 B, 197 L, sha256:dbfae791e08c)
- `provenance/review-imports.json` (data, 16152 B, 307 L, sha256:f1045a64c011)
- `provenance/yang-mills/YangMills/Analysis/DiagonalFlatBounds.lean` (lean,
18706 B, 370 L, sha256:6beff2415e11)
- `provenance/yang-mills/YangMills/Analysis/DifferentiatedKernels.lean` (lean,
24293 B, 485 L, sha256:9e98d5d4e409)
- `provenance/yang-mills/YangMills/Analysis/SchwartzExternalProduct.lean` (lean,
14240 B, 275 L, sha256:36f0aa1cbda3)
- `provenance/yang-mills/YangMills/Analysis/SchwartzKernels.lean` (lean, 16277
B, 354 L, sha256:3bda260104eb)
- `provenance/yang-mills/YangMills/Analysis/SchwartzSupportedDensity.lean`
(lean, 44279 B, 862 L, sha256:4d5c45cfd340)
- `provenance/yang-mills/YangMills/OSRecon/Growth.lean` (lean, 7855 B, 152 L,
sha256:9ceba1c37449)
- `provenance/yang-mills/YangMills/OSRecon/ReflectionApproximation.lean` (lean,
9299 B, 190 L, sha256:0e8054e323a7)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/Axioms.lean` (lean, 11542 B,
224 L, sha256:a0e70dabf0c0)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/OSConj.lean` (lean, 14096 B,
302 L, sha256:d717b96a013c)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/Spacetime.lean` (lean, 15637
B, 354 L, sha256:efcaee7bec7c)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/TensorProduct.lean` (lean,
12325 B, 238 L, sha256:78cbd9de6446)
- `provenance/yang-mills/YangMills/OSRecon/Vendored/ZeroDiagonal.lean` (lean,
12033 B, 279 L, sha256:fa510d3adde2)
- `runs/20261112T122756.953476Z/result.json` (data, 2504 B, 61 L,
sha256:7d546c27018d)
- `scripts/verify.py` (script, 16297 B, 289 L, sha256:24e71f5e3795)
- `submission/Challenge.lean` (lean, 257 B, 6 L, sha256:d31b227db6e6)
- `submission/ChallengeSpec.lean` (lean, 10157 B, 190 L, sha256:e48b0be2b72d)
- `submission/ConcreteSU2.lean` (lean, 672 B, 19 L, sha256:646bc0cbc0b3)
- `submission/Construction.lean` (lean, 2403 B, 42 L, sha256:86286ed17925)
- `submission/ContactBridge.lean` (lean, 2525 B, 50 L, sha256:91276437a70e)
- `submission/ContactSpec.lean` (lean, 763 B, 18 L, sha256:60b995a8e78f)
- `submission/HierarchyBridge.lean` (lean, 6425 B, 134 L, sha256:82c27a4ecb39)
- `submission/LICENSE` (license, 11357 B, 201 L, sha256:c71d239df917)
- `submission/NOTICE` (license, 3492 B, 54 L, sha256:b715838cdac0)
- `submission/PublicTheory.lean` (lean, 13123 B, 325 L, sha256:94111ad258b4)
- `submission/PublicView.lean` (lean, 6473 B, 174 L, sha256:60a64851daa5)
- `submission/PublicWilson.lean` (lean, 4244 B, 92 L, sha256:c1542c816cd4)
- `submission/README.md` (docs, 8909 B, 56 L, sha256:5477aa6f3881)
- `submission/SOURCES.sha256` (checksum, 996485 B, 9507 L, sha256:7b4aefb2b755)
- `submission/Solution.lean` (lean, 505 B, 10 L, sha256:1838214ba715)
- `submission/THIRD_PARTY.md` (docs, 4124 B, 28 L, sha256:86f79fe81bb0)
- `submission/TraceBridge.lean` (lean, 2249 B, 45 L, sha256:b3fa347e6ab7)
- `submission/Verify.lean` (lean, 4829 B, 89 L, sha256:54aad5cd830e)
- `submission/VerifyJoint.lean` (lean, 6297 B, 107 L, sha256:f84e8b30a0dc)
- `submission/WilsonBridge.lean` (lean, 2498 B, 69 L, sha256:e927fd2762c5)
- `submission/YM.lean` (lean, 36 B, 1 L, sha256:40e93bee3db1)
- `submission/comparator.json` (data, 189 B, 6 L, sha256:23e159f10cdb)
- `submission/lake-manifest.json` (data, 3549 B, 117 L, sha256:389c72d12e69)
- `submission/lakefile.toml` (config, 651 B, 21 L, sha256:059b094901a9)
- `submission/lean-toolchain` (config, 25 B, 1 L, sha256:2773c517aa90)
- `submission/third_party_licenses/Apache-2.0.txt` (text, 11357 B, 201 L,
sha256:c71d239df917)
- `submission/third_party_licenses/Cli-MIT.txt` (text, 1062 B, 21 L,
sha256:f7e95706807e)
- `submission/third_party_licenses/ImportGraph-template-MIT.txt` (text, 1068 B,
21 L, sha256:49110e6ed999)
- `submission/third_party_licenses/Lean-LICENSE.txt` (text, 9160 B, 71 L,
sha256:8b28515ffffc)
- `submission/third_party_licenses/Lean-binary-LICENSES.txt` (text, 81878 B,
1577 L, sha256:c2ee76ce94a8)
- `submission/third_party_licenses/Mathlib-LICENSE.txt` (text, 11357 B, 201 L,
sha256:b40930bbcf80)
- `submission/verification/CompactCheck.lean` (lean, 6047 B, 102 L,
sha256:52b1882fb70e)
- `submission/verification/Comparator.lean` (lean, 1279 B, 35 L,
sha256:447c88a86503)
- `submission/verification/Inventory.lean` (lean, 1340 B, 28 L,
sha256:e93ca65cc85d)
- `submission/verification/Usage.lean` (lean, 3561 B, 66 L, sha256:1e43b8b0b65c)
- `submission/verification/archive-graph.log` (log, 330 B, 5 L,
sha256:e696719b63c7)
- `submission/verification/attributions.log` (log, 2759 B, 12 L,
sha256:de78bea55882)
- `submission/verification/build.log` (log, 569 B, 6 L, sha256:fdf0d7e8f2f0)
- `submission/verification/challenge.sha256` (checksum, 662 B, 8 L,
sha256:72bd83307251)
- `submission/verification/compact-check.log` (log, 215 B, 3 L,
sha256:40fdaf3a44a9)
- `submission/verification/declaration-usage.tsv` (data, 31994696 B, 250320 L,
sha256:1f16d6cbf7cd)
- `submission/verification/headlines.txt` (text, 384 B, 13 L,
sha256:34c278d4577c)
- `submission/verification/joint-check.log` (log, 2897 B, 58 L,
sha256:6540b07ac9a7)
- `submission/verification/joint-headlines.txt` (text, 471 B, 17 L,
sha256:4a5d4eba5d14)
- `submission/verification/kernel.log` (log, 1656 B, 21 L, sha256:cb57d6f96f2c)
- `submission/verification/module-usage.tsv` (data, 393636 B, 9470 L,
sha256:f9db49e0d1b7)
- `submission/verification/negative-controls.log` (log, 177 B, 3 L,
sha256:ff62bc0526a8)
- `submission/verification/source-match.log` (log, 237 B, 6 L,
sha256:5e677e90a143)
- `submission/verification/su2-check.log` (log, 462 B, 7 L, sha256:f386baf39926)
- `submission/verification/usage.log` (log, 113 B, 1 L, sha256:f30a24774b78)
- `submission/verification/verified-sources.sha256` (checksum, 1700 B, 20 L,
sha256:bfb760fdafc9)
- `verification/AcceptanceChallenge.lean` (lean, 491 B, 14 L,
sha256:538c790f012c)
- `verification/OPEChallenge.lean` (lean, 439 B, 14 L, sha256:257cb4ffe3f9)
- `verification/acceptance.json` (data, 248 B, 12 L, sha256:710440530a85)
- `verification/controls/accept/Challenge.lean` (lean, 56 B, 1 L,
sha256:dc7b8ada3a9b)
- `verification/controls/accept/Solution.lean` (lean, 57 B, 1 L,
sha256:df775891bd34)
- `verification/controls/accept/comparator.json` (data, 204 B, 12 L,
sha256:e5879dd204ce)
- `verification/controls/accept/lakefile.toml` (config, 109 B, 6 L,
sha256:8add75552778)
- `verification/controls/accept/lean-toolchain` (config, 25 B, 1 L,
sha256:2773c517aa90)
- `verification/controls/definition_mismatch/Challenge.lean` (lean, 85 B, 2 L,
sha256:93fd5ba229c2)
- `verification/controls/definition_mismatch/Solution.lean` (lean, 80 B, 2 L,
sha256:f5ae891aa924)
- `verification/controls/definition_mismatch/comparator.json` (data, 204 B, 12
L, sha256:e5879dd204ce)
- `verification/controls/definition_mismatch/lakefile.toml` (config, 109 B, 6 L,
sha256:8add75552778)
- `verification/controls/definition_mismatch/lean-toolchain` (config, 25 B, 1 L,
sha256:2773c517aa90)
- `verification/controls/forbidden_axiom/Challenge.lean` (lean, 56 B, 1 L,
sha256:dc7b8ada3a9b)
- `verification/controls/forbidden_axiom/Solution.lean` (lean, 95 B, 2 L,
sha256:89327e59027b)
- `verification/controls/forbidden_axiom/comparator.json` (data, 204 B, 12 L,
sha256:e5879dd204ce)
- `verification/controls/forbidden_axiom/lakefile.toml` (config, 109 B, 6 L,
sha256:8add75552778)
- `verification/controls/forbidden_axiom/lean-toolchain` (config, 25 B, 1 L,
sha256:2773c517aa90)
- `verification/controls/statement_mismatch/Challenge.lean` (lean, 56 B, 1 L,
sha256:dc7b8ada3a9b)
- `verification/controls/statement_mismatch/Solution.lean` (lean, 57 B, 1 L,
sha256:6fc167a9c3b6)
- `verification/controls/statement_mismatch/comparator.json` (data, 204 B, 12 L,
sha256:e5879dd204ce)
- `verification/controls/statement_mismatch/lakefile.toml` (config, 109 B, 6 L,
sha256:8add75552778)
- `verification/controls/statement_mismatch/lean-toolchain` (config, 25 B, 1 L,
sha256:2773c517aa90)
- `verification/ope.json` (data, 216 B, 12 L, sha256:60c4ac055447)
- `verification/submission.json` (data, 213 B, 12 L, sha256:999fe22d0385)
- `verification/tool-pins.json` (data, 513 B, 18 L, sha256:2ab65d789bf7)

<!-- end of file: leanasm/docs/openai-20261028/MANIFEST.md -->
