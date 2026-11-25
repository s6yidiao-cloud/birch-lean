# AxiomMath Stepanov source

These 15 modules are the import closure of
`StacksFrontier.RingTheory.Polynomial.StepanovBound` within AxiomMath’s
Stacks project, at revision `012108f61d7f92a6ffc35ec3f263b6da5d438125`.
The source is licensed under [Apache 2.0](LICENSE).
[Upstream source](https://github.com/AxiomMath/Stacks/tree/012108f61d7f92a6ffc35ec3f263b6da5d438125/StacksFrontier/RingTheory/Polynomial)

[The port patch](stepanov-port.patch) records the Lean 4.35.0 and Mathlib API adaptations,
unused binder names, and the explicit finite-dimensional instances in the
auxiliary polynomial argument. The final lower-bound declaration has the
same statement and proof as upstream.
