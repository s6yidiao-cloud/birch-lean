# Wooley nested efficient congruencing proof slice

The proof is taken from S. McColm's Lean monorepo at commit
`6a90ee91cdb8a4037189c1076595bd3846c96c16`. The original package uses Lean
`v4.30.0` and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
The source proof lives in the Gafni–Tao extension package and is distributed
under the included MIT No Attribution license.
[Original source directory](https://github.com/smccolm/Lean/tree/6a90ee91cdb8a4037189c1076595bd3846c96c16/Riemann%20Zeta/9.%20Zero%20Density%2C%20Large%20Values%20and%20Prime%20Transfer/74%20Gafni-Tao%2C%202026/Extension/GafniTao)

The directly imported modules are `WooleySourceCriticalBase`,
`WooleySourceToPadic`, and `WooleyPadicToCritical` in namespace `GafniTao`.
The first supplies `wooleyPolynomialCorollary32_native`, the second
specializes it to monomial p-adic concentration, and the third converts it
to the critical count. The count uses ordered pairs of tuples with entries
in `1,…,Q` and equality of every power sum of order `1,…,k`. At moment
index `k*(k+1)/2` the bound is `C*Q^(k*(k+1)/2+epsilon)`.
[Wooley’s nested efficient congruencing paper](https://arxiv.org/abs/1708.01220)

The source-level Wooley proof needs 111 of the upstream `Wooley*.lean`
files. Its only edge into the broader Ford and Heath–Brown development is the
import of `VinogradovCriticalReduction` by `WooleyCriticalBase`. The
finite-count declarations on that edge are reproduced in
`WooleyCountDependencies.lean`. The definition of `FordPowerSolution`
uses `FordVinogradovTuple`, which is definitionally equal to `FordBox`.
The slice ends with the critical count theorem in
`WooleyPadicToCritical.lean`, before its application to Heath–Brown's argument.

`wooley-provenance.json` gives the pinned Web URL and SHA-256 for every
original file, the SHA-256 of every ported file, all six extraction source
files and their copied declarations. `wooley-port.patch` records the
changes to existing source files.

Birch uses the exact count through its signed-interval adapter. The port
uses Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
as pinned by Birch.
