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

Install [elan](https://github.com/leanprover/elan), Git and Python 3.10 or newer. The Lake project pins Lean to v4.35.0 and records the Mathlib revision in its [manifest](formalization/lake-manifest.json). From the repository root, run

```sh
cd formalization
lake exe cache get
cd ..
python3 scripts/verify.py --frozen
```

The verifier checks the source files against the release manifest, builds the Lean project with warnings as errors, and checks the theorem statements, proof dependencies, and axioms.

## Repository

- [`formalization/`](formalization/) contains the Lean project. The four results above are in [`FinalUnconditional.lean`](formalization/Birch/FinalUnconditional.lean).
- [`checks/`](checks/) contains the [theorem audit](checks/BirchAudit.lean) and the [list of theorem statements and hypotheses](checks/formalization.yaml).
- [`docs/`](docs/) contains the [proof map](docs/FORMALIZATION_MAP.md) and [verification notes](docs/verification.md).
- [`scripts/`](scripts/) contains the [verification script](scripts/verify.py).

## License

The original Birch Lean code is licensed under [Apache 2.0](LICENSE). Third party attributions and licenses are listed in [NOTICE](NOTICE).
