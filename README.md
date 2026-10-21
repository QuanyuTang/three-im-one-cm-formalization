# Three IM and one CM shared values

Authors: **Yixin He, Quanyu Tang, Jun Wang**.

This repository formalizes the main theorem of the authors' unpublished
manuscript *On meromorphic functions sharing three values IM and one value CM*.
Yixin He and Jun Wang gave the original informal proof with assistance from
ChatGPT. Quanyu Tang carried out the formalization based on their proof,
using Aristotle and Codex as formalization tools.

Let \(f,g\) be nonconstant meromorphic functions on \(\mathbb C\). If they share
four pairwise distinct values of the Riemann sphere, three **ignoring
multiplicities (IM)** and the fourth **counting multiplicities (CM)**, then
they share all four values CM. There is no growth or finite-order hypothesis.
The theorem also includes functions with identical meromorphic germs.

IM means equality of fibers; CM means equality of their local multiplicities.
For a finite target, multiplicity is its positive zero order. At infinity it
is the positive pole order. These are meromorphic germ orders, so changing an
assigned representative value at a pole or removable singularity does not
change sharing. Nonconstancy excludes locally constant meromorphic germs;
on the connected plane this is the usual nonconstancy condition.

The public theorem is **`ThreeIMOneCM.three_IM_one_CM`** in `Solution.lean`.
Its independent statement is in `Challenge.lean`; both use the same five
germ-based definitions. Solution proves their equivalence to the substantive
definitions and applies `ThreeIM.three_IM_one_CM` in
`RequestProject/ThreeIM/Main.lean`.

The substantive proof has no unresolved proof or definition holes. Its only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Challenge contains
one deliberate unproved statement, excluded from these proof counts and from
the solution's dependencies. Agent review compared the statement and definitions
with the manuscript and inspected actual compilation and axiom results.

The repository pins Lean and Mathlib in `lean-toolchain` and
`lake-manifest.json`. On Linux, with that toolchain installed:

```sh
python3 scripts/check-lean-sources.py
python3 scripts/check-release-layout.py
lake exe cache get
python3 scripts/build-topological.py --execute --report .ci-output/build.json
lake env lean -j1 -M4096 verification/Audit.lean
bash scripts/verify-comparator.sh
```

The Comparator needs bubblewrap and the pinned toolchain's bundled Nanoda and
con-ron. CI runs source and metadata checks, the build and axiom audit, and
the official Comparator with these independent kernels. Consult the actual
workflow results for its outcome. `definition_names` is empty: no definition
body is exempted from ordinary Comparator comparison.

The formal proof reorganizes some manuscript arguments, including exclusion
of multiplicity defects. Its intermediate constructions are not additional
hypotheses. Numbering in inherited source comments follows the intermediate
formalization draft. The unpublished manuscript and its TeX source are not distributed.
Agent review does not assert completed human author review, peer review, or
Palomar registration.

Maintainer: Quanyu Tang ([QuanyuTang](https://github.com/QuanyuTang)).
Code license: **Apache-2.0**; see `LICENSE` and the preserved source notices.
We thank Lean and Mathlib, Will (Ziang) Li's
[no-wandering-domains](https://github.com/will1491/no-wandering-domains)
for the adapted sphere and normal-family infrastructure, and Stefan Kebekus's
[ProjectVD](https://github.com/kebekus/ProjectVD) for elementary estimates
adapted in `PicardSupport.lean`. See `NOTICE.md` and
`NoWanderingDomains/ORIGIN.md` for the upstream revisions and licensing.
