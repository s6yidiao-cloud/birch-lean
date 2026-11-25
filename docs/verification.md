# Verification

Lean is pinned to `leanprover/lean4:v4.35.0`. Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679` by the [Lake manifest](../formalization/lake-manifest.json).

The [verifier](../scripts/verify.py) checks the local import closure and scans the Lean sources for proof placeholders, including the vendored Weil, Stepanov, and Wooley sources. With `--frozen` it also verifies the [SHA-256 manifest](../checks/SHA256SUMS).
From the Lean project directory, it runs

```sh
lake build Birch GafniTao
lake env lean -DwarningAsError=true ../checks/BirchAudit.lean
```

Birch, GafniTao, Stepanov, and the audit use warnings as errors. The audit
elaborates the four result types after `import Birch`, checks their required
proof dependencies, and inspects transitive axioms. Its allowed kernel
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

[GitHub Actions configuration](../.github/workflows/lean.yml) invokes the same verifier with the pinned Mathlib dependency cache.
