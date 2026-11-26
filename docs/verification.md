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

## Reproducing the check

From a fresh checkout, run the commands in the [README](../README.md#build-and-verify).
The Mathlib cache supplies compiled Mathlib dependencies. The default verifier builds
the bundled Weil, Stepanov, Wooley, and Birch modules locally.

On x86-64 Linux, after fetching the Mathlib cache, you can run the same command as CI
from the repository root.

```sh
python3 scripts/verify.py --frozen --weil-cache
```

This option also downloads the [Weil project's published Lake artifacts](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/ae6479530ccaaa19b6d7ca02bc3248cbf49611c9/.github/workflows/lean_action_ci.yml).
The verifier checks the SHA-256 of the pinned cache index. Lake reuses matching
build inputs and compiles the remaining modules from source. Both commands run
the same final theorem and axiom audit.

Open a [Verify Lean run on main](https://github.com/s6yidiao-cloud/birch-lean/actions/workflows/lean.yml?query=branch%3Amain)
and select **Build and audit the Lean formalization** to see the output for its
commit. A successful run checks the frozen files, reports the proof route for
each of the four results, and finishes with the axiom-dependency count.
