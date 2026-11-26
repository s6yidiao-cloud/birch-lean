# Forms and polynomial covers in many variables

Lean formalization of the main results in [*Forms and polynomial covers in many variables*](https://arxiv.org/abs/2611.33114) by Yijie Diao and Lena Wurzinger. The declarations are available after `import Birch`.

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1, smooth Hasse principle | [`Birch.finalSmoothHassePrinciple`](formalization/Birch/FinalUnconditional.lean#L27) |
| Equation (1.1), asymptotic formula for forms | [`Birch.finalFormAsymptotic`](formalization/Birch/FinalUnconditional.lean#L31) |
| Theorem 1.2, Serre's conjecture for covers | [`Birch.finalCoverSerreBound`](formalization/Birch/FinalUnconditional.lean#L35) |
| Theorem 1.3, asymptotic formula for covers | [`Birch.finalCoverAsymptotic`](formalization/Birch/FinalUnconditional.lean#L39) |

Outside this repository, the formalization depends only on Mathlib.

## Build and verify

[![Verify Lean](https://github.com/s6yidiao-cloud/birch-lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/s6yidiao-cloud/birch-lean/actions/workflows/lean.yml?query=branch%3Amain)

Install [elan](https://github.com/leanprover/elan), Git and Python 3.10 or newer. The Lake project pins Lean to v4.35.0 and records the Mathlib revision in its [manifest](formalization/lake-manifest.json). From the repository root, run

```sh
cd formalization
lake exe cache get
cd ..
python3 scripts/verify.py --frozen
```

The verifier checks the source closure, builds the Lean project with warnings as errors, checks the manuscript-shaped theorem signatures, and audits the proof dependencies and axioms.

- Statement correspondence and proof choices are in the [proof map](docs/FORMALIZATION_MAP.md).
- The toolchain and checks are in the [verification notes](docs/verification.md).
- The theorem scope and hypothesis are in the [status file](checks/formalization.yaml).
- Third party provenance and licenses are in the [notice](NOTICE).
