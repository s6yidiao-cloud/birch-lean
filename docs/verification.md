# Verification

Lean is pinned to `leanprover/lean4:v4.32.0`. Mathlib is pinned to
`81a5d257c8e410db227a6665ed08f64fea08e997` by the [Lake manifest](../formalization/lake-manifest.json).

The [verifier](../scripts/verify.py) checks the local module closure and scans the Lean sources for proof placeholders. With `--frozen` it also verifies the [SHA-256 manifest](../checks/SHA256SUMS).
From the Lean project directory, it runs

```sh
lake build Birch GafniTao
lake env lean -DwarningAsError=true ../checks/BirchAudit.lean
```

Both libraries set warnings as errors. The audit elaborates the literal manuscript-shaped endpoints, checks the required proof dependencies, and checks transitive axioms for every declaration in the local Birch and GafniTao modules. The allowed kernel axioms are `propext`, `Classical.choice`, and `Quot.sound`. Deligne's bound is a theorem parameter.

The local build used a temporary checkout on macOS arm64 with the pinned dependency cache. It rebuilt the changed modules and their dependents, checked the four manuscript statements and their proof dependencies, and audited the local declarations. Lean also replayed the endpoint and quadratic estimate modules with

```sh
lake env leanchecker -v Birch.FinalQuadraticMetric Birch.FinalForms Birch.FinalFormGradient Birch.FinalCovers
```

The commands and decisive output are in the [build record](../checks/verification.txt).

[GitHub Actions configuration](../.github/workflows/lean.yml) invokes the same verifier with the pinned Mathlib dependency cache.
