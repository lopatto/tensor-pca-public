# Statistical thresholds for Tensor PCA

Lean formalization of principal statistical, estimation and constrained-landscape
results from *Statistical thresholds for Tensor PCA* by Aukosh Jagannath,
Patrick Lopatto and Léo Miolane, **The Annals of Applied Probability** 30(4)
(2020), 1910–1933, [doi:10.1214/19-AAP1547](https://doi.org/10.1214/19-AAP1547).
The public source used as the baseline is
[arXiv:1812.03403v2](https://arxiv.org/abs/1812.03403v2).

The formalization follows a local revision of that paper. **Patrick Lopatto,
the formalization's maintainer, alone prepared and is responsible for the
revisions and expansions in this local version, made to facilitate
autoformalization.** The original paper retains its three authors.
The local manuscript is not distributed; `Challenge.lean` gives the exact
formalized statements and hypotheses. The twelve exports in `comparator.json`
cover thirteen principal conclusions.

## Scope and source correspondence

References below distinguish the public arXiv v2 numbering from the local
revision.

- `Paper.detection` (Theorem 1.1 in both versions): total-variation testing
  threshold for even k >= 6, below and above the critical strength.
- `Paper.mleValue` and `mleOverlap` (Theorem 1.2 in both versions), and
  `mleAttainment` (an unnumbered expected-overlap consequence): maximum-likelihood
  value, absolute overlap and expected absolute-overlap attainment for k >= 3.
  Value includes critical strength; overlap and attainment exclude it.
- `Paper.tensorMMSE` (arXiv v2 Proposition 5.8; local Proposition 5.9) and
  `estimatorOptimality` (arXiv v2 Corollary 5.9; local Corollary 5.10): for
  k >= 3, tensor MMSE at positive noncritical strength and bounds on both
  absolute-overlap moments at nonnegative noncritical strength for measurable
  unit estimators with independent randomization. The absolute-overlap
  formulation is part of the maintainer's revision.
- `Paper.finiteStrengthTesting` (an unnumbered introduction claim) and
  `discontinuousTransition` (a consequence of Theorem 1.2): consistent testing
  among any fixed nonempty finite family of distinct supercritical strengths
  and the discontinuous overlap transition.
- `Paper.constrainedLimit` (arXiv v2 Lemma 5.4; local Lemma 5.5) and
  `landscape` (Proposition 1.4 in both versions): constrained expected and
  almost-sure limits for signed overlaps and the secondary local/global
  landscape. Signed overlaps range over [-1,1], including the poles.
- `Paper.variationalConclusions` combines the replica-symmetric formula
  (arXiv v2 Lemma 5.5; local Lemma 5.6) and the four-parameter reduction
  (arXiv v2 Remark 5.10; local Remark 5.11). `fourParameterReduction` also
  exports the latter separately, as equality of variational infima.

Orders, strengths and overlaps are fixed as dimension grows. Almost-sure limits
are pointwise in these parameters and allow arbitrary coupling across dimensions;
estimator randomization is independent within each dimension. The ordered
Frobenius tensor model has observation lambda*sqrt(N)*X^(tensor k)+W with a
uniform unit-sphere prior and independent iid standard Gaussian noise.
The statement files give all ranges, zero-strength cases and endpoint conventions.

Relative to arXiv v2, the maintainer's formulation uses absolute-overlap
estimator optimality, zero-overlap global maximality for
0 <= lambda <= lambda_c, an infimum variational value and the displayed
continuous four-parameter family. These source correspondences identify the
related public results; they do not assert literal identity of every formulation.
The four-parameter result proves equality of infima for k >= 3 and |m| < 1;
unrestricted minimizer attainment is not proved. The package does not advertise
every standalone auxiliary theorem in its full generality.

## Build and verification

With Elan installed, the pinned toolchain and dependencies are used by:

```sh
lake exe cache get
lake build
```

`Challenge` and `Solution` are separate environments. Solution imports neither
Challenge nor StatementChecks. The twelve `sorry` terms are confined to the
advertised Challenge theorem bodies. Solution's proof closure is admission-free;
its permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
StatementChecks gives independent explicit expected types for all advertised
results.

The [official full mechanical preflight runs](https://github.com/lopatto/tensor-pca-public/actions/workflows/palomar-preflight.yml)
record the exact source commit checked, protected statement comparison and the
individual kernel outcomes. For a release, use the completed full-mode report
whose source SHA matches that release's commit. No exact-commit preflight
result is claimed for this snapshot. Mechanical verification is
separate from Palomar editorial acceptance and registration. Challenge exceeds
the preferred 300-line review length and satisfies the hard size limits.

For a local protected check on Linux with working bubblewrap isolation, use
`lake comparator --config=comparator.json --paranoid`. Comparator is built into
the pinned Lean 4.35 toolchain. The manual Palomar workflow in this repository
runs the official policy-matched verification against an explicitly supplied
full source commit SHA. Supplying that SHA as a manual input allows the release
repository to retain a single snapshot commit.

## Automation and provenance

OpenAI Codex agents generated and refined proofs using Lean, Mathlib and Lean
Beam; separate agents checked statements, definitions, prerequisites and axiom
reports. The maintainer also used Codex assistance in preparing the local
manuscript revisions and expansions. The machine-readable automation and
review records are in
`formalization.yaml`.

New code is Apache-2.0. Adapted sources retain their original notices. The nine
`related_formalizations` records identify the direct adaptations and credited
upstream origins at pinned revisions. Some historical origin repositories are
not publicly accessible; their records identify the accessible pinned
slowequilibration distribution used for these files. See `NOTICE` and source
headers for attribution and retained licences.
