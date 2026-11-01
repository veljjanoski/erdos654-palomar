# Erdős Problem 654: distinct distances from a point, no four points on a circle

[![CI](https://github.com/veljjanoski/erdos654-palomar/actions/workflows/ci.yml/badge.svg)](https://github.com/veljjanoski/erdos654-palomar/actions/workflows/ci.yml)

Lean 4 proofs of two solved statements about
[Erdős Problem 654](https://www.erdosproblems.com/654), prepared for the
[Palomar](https://palomar-registry.org/) registry (submission form:
<https://submit.palomar-registry.org/>).

Erdős asked whether, for any $n$ points in the plane with no four on a circle, some point has at
least $(1-o(1))n$ distinct distances to the other points. The proved statements are:

- `Erdos654.erdos_654.parts.i`: the answer is no.
- `Erdos654.erdos_654.variants.feng`: for $m \geq 10$ there are $4m$ points, no four on a circle,
  such that every point has fewer than $3m$ distinct distances to the other points.

The definitions and the statements in `Challenge.lean` are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/654.lean` and `FormalConjecturesForMathlib/Geometry/2d.lean`,
`Metric.lean` at commit `a64e959c32c270df4dd0d96d2027481f15750534`), where they are stated with
`sorry`.

The proof in `Solution.lean` takes the points $(\pm 2i, 0)$ and $(0, \pm(2j-1))$ for
$1 \leq i, j \leq m$. Feng et al. ([arXiv:2601.22401](https://arxiv.org/abs/2601.22401), Section
3.1) answered the question with $2m$ points on each axis at powers of $2$ and $3$. Their
power-of-a-point argument (Lemma 3) rules out four points on a circle; here it is finished by
parity instead of unique factorisation.

## Repository map

- `Challenge.lean`: the statements (with `sorry`) a reader audits.
- `Solution.lean`: the same declarations with proofs.
- `comparator.json`: the declarations `lake comparator` checks.
- `formalization.yaml`: provenance, authorship, automation and review metadata.
- `scripts/`, `test/`, `Gemfile*` and `.github/workflows/ci.yml` come from
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate).

Build with `lake exe cache get && lake build`; check with `scripts/verify-comparator.sh` (Linux,
needs `bwrap`).

## Licence

Apache License 2.0, see `LICENSE`. The statements and definitions copied from formal-conjectures
are also under Apache-2.0.
