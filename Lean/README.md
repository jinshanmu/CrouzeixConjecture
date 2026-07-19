# Crouzeix conjecture manuscript formalization

This project audits and formalizes the proof architecture of the baseline manuscript
`../LaTeX/crouzeix_conjecture_proof.tex` at SHA-256
`037e9aafefe5fad57f0acee04b410093aa46f65c508156e80eda987ba1b1478f`.
The submission-formatted article is
`../AnnMath/the_numerical_range_is_a_2_spectral_set.tex`; source-line mappings
in the audit documents intentionally refer to the preserved baseline above.

It uses Lean 4.28.0 and Mathlib pinned at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  The committed dependency
manifest records the transitive revisions needed for a reproducible build;
downloaded packages and build products remain local under `.lake/`.

The library proves the manuscript's polynomial Crouzeix estimate unconditionally.  Its public
pointwise theorem is `CrouzeixConjecture.crouzeixConjecture`: for every matrix on a finite
nonempty complex Euclidean coordinate space and every complex polynomial, the induced Euclidean
operator norm of the matrix polynomial is at most twice the maximum polynomial modulus on the
numerical range.  The quantified form is
`CrouzeixConjecture.crouzeixConjecture_mainTheorem : MainTheoremStatement`.

The proof follows the manuscript architecture: positive-real completion, double-layer
positivity and algebra, projection squared-distance `C¹`, inverse-gauge parametrization of convex
parallel bodies, a scalar implicit-function argument, outward normal/support and orientation,
the radial polynomial Cauchy formula, the double-layer provider, simple-spectrum perturbation,
and the canonical outer limit.  The matrix Herglotz kernel theorem is proved without an axiom.
The manuscript's analytic diagonal correction `D` is explicitly constructed and proved analytic,
diagonal, normalized at zero, and reconstructive.  The general Herglotz measure representation is
not separately packaged; its exact kernel positivity consequence is proved directly.

The rational spectral-set discussion is formalized separately as
`CrouzeixConjecture.crouzeixRationalSpectralSetCorollary`, with pointwise form
`CrouzeixConjecture.crouzeixRationalBound`.  No mathematical flaw was found in the manuscript.

Run plain `lake build` for the complete library.  Plain `lake run` is the authoritative default
verification script: it runs the build and then `lake env lean AxiomAudit.lean`.  Run these
serially; do not overlap Lean/Lake processes.  The delivered checkpoint has passed both commands
with zero errors and zero warnings.

See `FORMALIZATION_MAP.md` for source coverage, `CONTINUATION_STATUS.md` for the proof and
verification checkpoint, `MANUSCRIPT_AUDIT.md` for the adversarial mathematical audit, and
`AXIOM_AUDIT.md` for the trust boundary.
