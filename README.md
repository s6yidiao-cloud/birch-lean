# Forms and polynomial covers in many variables

Lean 4 formalization of the main results in `final_v2.tex` by Yijie Diao and Lena Wurzinger. The declarations cover form degrees \(d\ge 2\) and are available after `import Birch`. [Manuscript PDF](paper/final_v2.pdf)

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1.1, smooth Hasse principle at \(n-\sigma\ge 2^{d+1}-3\) | [`Birch.finalSmoothHassePrinciple_of_deligne`](formalization/Birch/FinalForms.lean) |
| Equation (1.1), weighted form asymptotic on the noncritical locus and absolute convergence | [`Birch.finalFormAsymptotic_of_deligne`](formalization/Birch/FinalFormGradient.lean) |
| Theorem 1.2, Serre bound for integral pairs | [`Birch.finalCoverSerreBound_of_deligne`](formalization/Birch/FinalCovers.lean) |
| Theorem 1.3, weighted polynomial-cover asymptotic | [`Birch.finalCoverAsymptotic_of_deligne`](formalization/Birch/FinalCovers.lean) |

The theorems take Deligne’s prime-field exponential-sum bound in degrees at least three as an explicit hypothesis. Quadratic completion uses the checked Gauss-sum bound. The cover proof uses Hua’s moment in cover degrees two through four and a vendored Lean proof of the critical Vinogradov mean value estimate in higher degrees. Mathlib is the external Lake dependency. [Weil I, Theorem 8.4](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf#page=31) · [Weil II, (3.7.2.1)](https://publications.ias.edu/sites/default/files/Number40.pdf#page=79)

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
