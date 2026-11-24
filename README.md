# Forms and polynomial covers in many variables

Lean 4 formalization of the main results in *Forms and polynomial covers in many variables* by Yijie Diao and Lena Wurzinger. The declarations are available after `import Birch`.

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1, smooth Hasse principle | [`Birch.finalSmoothHassePrinciple`](formalization/Birch/FinalForms.lean) |
| Equation (1.1), asymptotic formula for forms | [`Birch.finalFormAsymptotic`](formalization/Birch/FinalFormGradient.lean) |
| Theorem 1.2, Serre's conjecture for covers | [`Birch.finalCoverSerreBound`](formalization/Birch/FinalCovers.lean) |
| Theorem 1.3, asymptotic formula for covers | [`Birch.finalCoverAsymptotic`](formalization/Birch/FinalCovers.lean) |

We take [Theorem 8.4 in Deligne’s *La conjecture de Weil. I*](formalization/Birch/DeligneFiniteField.lean#L48) as an explicit hypothesis.

## Build and verify

Install [elan](https://github.com/leanprover/elan), Git and Python 3.10 or newer. The Lake project pins Lean and Mathlib to v4.32.0. From this folder, run

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
- Third-party provenance and licenses are in the [notice](NOTICE).
