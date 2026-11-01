module

public import Mathlib

/-!
# Erdős Problem 654: distinct distances from a point, no four points on a circle

Two solved statements about Erdős Problem 654
([erdosproblems.com/654](https://www.erdosproblems.com/654)). The definitions, the notation `ℝ²`
and the two theorem statements are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0), files
`FormalConjecturesForMathlib/Geometry/2d.lean`, `FormalConjecturesForMathlib/Geometry/Metric.lean`
and `FormalConjectures/ErdosProblems/654.lean` at commit
`a64e959c32c270df4dd0d96d2027481f15750534`, with the same names.

*References:*
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Fe26] T. Feng et al, *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
  Erdős Problems*. arXiv:2601.22401 (2026).
-/

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry Finset

namespace EuclideanGeometry

/-- `NoFourConcyclic X` means that no four distinct points of `X` lie on a common circle.

In the plane, `Cospherical` means lying on a common circle. Four distinct collinear points are
never cospherical, so collinear points are allowed. Stated for `Set ℝ²`; a `Finset` argument
coerces. -/
def NoFourConcyclic (X : Set ℝ²) : Prop :=
  ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

end EuclideanGeometry

section

variable {X : Type*} [MetricSpace X]

open Classical in
/-- Given a finite set of points in a metric space, we define the number of distinct distances
between a given point and all other points. -/
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

end

open Filter Finset EuclideanGeometry

namespace Erdos654

/--
Let $f(n)$ be such that, given any $x_1,\ldots,x_n\in \mathbb{R}^2$ with no four points on a
circle, there exists some $x_i$ with at least $f(n)$ many distinct distances to the other $x_j$.
Is it true that $f(n) > (1-o(1))n$?

Erdős asks this in [Er97e]. The answer is no: Aletheia [Fe26] constructed, for every $m \geq 10$,
a set of $n = 4m$ points with no four on a circle such that every point has fewer than
$\frac{3}{4}n$ distinct distances to the other points. This gives infinitely many $n$, which is
enough to refute the statement with $\varepsilon = 1/8$. See `Erdos654.erdos_654.variants.feng`.
-/
theorem erdos_654.parts.i :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  sorry

/--
Aletheia [Fe26] showed that for every $m \geq 10$ there is a set of $n = 4m$ points in
$\mathbb{R}^2$, no four on a circle, such that every point has fewer than $\frac{3}{4}n = 3m$
distinct distances to the other points.

The construction places $2m$ points on each of two perpendicular lines, so it is not in general
position. Each point has at most $3m - 1$ distinct distances to the other points.
-/
theorem erdos_654.variants.feng (m : ℕ) (hm : 10 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m := by
  sorry

end Erdos654
