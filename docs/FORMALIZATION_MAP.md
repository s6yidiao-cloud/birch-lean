# Proof map for final_v2.tex

The source is `final_v2.tex` by Yijie Diao and Lena Wurzinger, SHA-256
`10d428d1fcdb41cadeb8b478703fc0cd4a2a71c30b436338e53ceb5d81891f8d`.
The form degree satisfies \(d\ge 2\) throughout the endpoints. The cover degree satisfies \(e\ge 2\). [Manuscript PDF](../paper/final_v2.pdf)

| Source label | Lean declaration | Checked correspondence |
| --- | --- | --- |
| `thm:main` | `Birch.finalSmoothHassePrinciple_of_deligne` | Closed codimension threshold \(n-\sigma\ge 2^{d+1}-3\). Local nonsingular zeros over \(\mathbb R\) and every \(\mathbb Q_p\) give a nonsingular zero over \(\mathbb Q\). |
| `eq:asymptotic`, `lem:tail` | `Birch.finalFormAsymptotic_of_deligne` | Same codimension threshold. The saving is chosen at fixed \(d,n\), before the form, singular dimension, or weight. The formula includes termwise absolute convergence of the series and integrability of the oscillatory factor. |
| `thm:serre` | `Birch.finalCoverSerreBound_of_deligne` | Closed real threshold \(n-\sigma\ge(2^{d+1}-4)(1/d+1/(2e))\). Counts all distinct integral pairs with \(\lVert\mathbf x\rVert_\infty\le B\). The proof bounds every integral root by a fixed multiple of \(B^{d/e}\) and chooses a dilated weight covering the box. |
| `thm:cover_asymptotic` and its convergence argument | `Birch.finalCoverAsymptotic_of_deligne` | Open threshold \(n-\sigma>(2^{d+1}-4)(1-1/m)\), where \(m=\min(2^e,e(e+1))\). Uses signed cutoff \(\lvert y\rvert\le B^{d/e}\), exponent \(n+d/e-d\), and the two factors of equations (1.4) and (1.5). |

## Definitions

- `RationalGradientDimension F σ` is the Krull dimension of the quotient of the polynomial ring over the algebraic closure of \(\mathbb Q\) by the ideal of the partial derivatives. This measures the affine gradient locus.
- `FinalWeight` and `HasNonvanishingGradientOnSupport` specify a smooth \([0,1]\)-valued weight compactly supported in the open unit cube. At each point of the support, at least one partial derivative is nonzero. The partial derivative can depend on the point.
- `compactWeightedZeros` and `coverWeightedZeros` use full finite-support sums over the integral form variables. The cover sum uses the integer interval \([-\lfloor B^{d/e}\rfloor,\lfloor B^{d/e}\rfloor]\).
- The singular series use unit numerators modulo each positive conductor. Their conductor masses sum the norms of the coefficients before grouping numerators. For the cover, `completeSum_coverPolynomial` identifies the normalization \(q^{-n-1}\) and the phase \(F(\mathbf x)-g(y)\). The real factor uses the leading coefficient of \(g\) and the interval \([-1,1]\).
- The power-saving estimates use an eventual bound at real \(B\to\infty\), with the multiplicative constant chosen after the manuscript data.

## Proof dependencies and classical input

The form and cover arguments share the formalized good-reduction, smooth-section, dilated-differencing and level-measure estimates. For degree two, `quadraticPointwiseEstimate` proves the zero-difference case of Proposition 2.1 using Gauss sums. The quadratic measure bound in Proposition 3.1 is checked by `quadraticMetricDistribution_uniform`, with one choice of constants and scale cutoff for the full range \(1\le T\le B^{1/2}\). The critical moment samples the level estimates on a finite mesh. The Lean measure argument uses covariances of dilated intervals and the manuscript uses Ramanujan sums. In higher degrees the mesh uses bounded products of dilations, while the manuscript counts products of primes.

`formAsymptotic_of_gradientPartition` splits the weight into a finite family on which individual partial derivatives are nonzero. It adds the asymptotics with the same power saving and proves additivity of the singular integral. The Hasse proof uses the weighted formula with a locally chosen transverse weight and positivity of the local factors, including in degree two. The introduction also cites Hasse–Minkowski for the quadratic case.

The form and cover tails follow by summing over shells of reduced fractions. The Lean form proof integrates a Poisson major-arc approximation with its own cutoff, and the manuscript uses fixed \(B^{1/6}\) major arcs and a Riemann sum. The cover proof uses Hua for \(e\le4\) and the checked Wooley reduction for \(e\ge5\).

Each result is conditional on `∀ r, 3 ≤ r → Birch.PrimeDeligneEstimate r`. This is Deligne’s bound \((r-1)^l p^{l/2}\) for the standard unnormalized additive-character sum of an \(l\)-variable polynomial with smooth leading projective hypersurface and \(p>r\). Lean checks the conversion to the normalized complete sums used by the circle method. [Weil I, Theorem 8.4](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf#page=31) · [Weil II, (3.7.2.1)](https://publications.ias.edu/sites/default/files/Number40.pdf#page=79)

The [audit](../checks/BirchAudit.lean) checks the strict-threshold proof routes and the vendored moment proof. Supporting Lean files are the local import closure of the manuscript endpoints. The source slice retains the helpers used by those proofs.
