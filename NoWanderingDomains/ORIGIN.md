# Origin of the sphere and normal-family modules

These modules are adapted from Will (Ziang) Li's
[no-wandering-domains](https://github.com/will1491/no-wandering-domains)
at commit `0a6497b0cc9ed39a6a705bf013449635894b56d0`.
The original copyright headers are preserved. The code is released under
Apache 2.0; see [LICENSE](LICENSE).

The following upstream module names and mathematical declarations are retained:

- `Sphere.Basic`
- `Sphere.MobiusAction`
- `Sphere.SphericalMetric`
- `Sphere.SphereHolomorphic`
- `NormalFamilies.Basic`
- `NormalFamilies.Spherical`
- `NormalFamilies.Zalcman`

`Sphere.InversionIsometry` contains the complete original proof of
`sphericalDist_inversionGL_smul`, extracted from upstream
`Dynamics/JuliaFatou/RepellingCycles.lean`. This avoids importing the unrelated
dynamics results. Zalcman's imports have been reduced to this small closure
and official Mathlib. The strong sphere Montel development is not included.

For Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, the proof adaptations replace
`Set.mem_ofPred_eq` by `Set.mem_setOf_eq`, derivative-combination `fun_*`
names by `inv`/`mul`/`sub`, and the newer
`hasFDerivAt_iff_isLittleO` convenience lemma by the definition `HasFDerivAt`
followed by `hasFDerivAtFilter_iff_isLittleO`. The same conversion proof
qualifies `ContinuousLinearMap.smul_apply` and explicitly simplifies
`ContinuousLinearMap.toSpanSingleton_apply`, which is the 4.28 scalar
derivative representation. No mathematical assumptions,
normality predicates, sphere holomorphy predicates, or spherical derivative
definitions are changed.

The files additionally use Lean 4.28's `module`, `public import`, and
`@[expose] public section` directives so that other modules can import the
same declarations. These changes affect packaging and visibility only.

The current release port targets Lean `4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The two scalar derivative
characterizations in `NormalFamilies.Zalcman` again use
`hasFDerivAt_iff_isLittleO`. The mathematical statements and definitions are
unchanged. Version comments describing the earlier backport are retained as
development history.

The main provided results are Marty's sufficient criterion, sphere-valued
Weierstrass convergence, convergence of spherical derivatives, and Zalcman's
rescaling lemma. The sphere is `OnePoint ℂ`, with honest infinity values at
poles; relating this to arbitrary point values of a meromorphic complex-valued
representative requires a separate bridge.

The finite-chart spherical derivative has the factor `2` induced by the
chosen chordal metric. Zalcman's scales are positive and tend to zero;
monotonicity of the scale sequence is not asserted in the Lean statement.
