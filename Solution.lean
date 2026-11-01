module

public import Mathlib

/-!
# Erdős Problem 654: proofs

Proofs of the two statements of `Challenge.lean`. The definitions are repeated verbatim.

Like the construction of [Fe26, §3.1], the set has `2m` points on each of two perpendicular lines,
symmetric about the origin. [Fe26] takes the points `(±2^j, 0)` and `(0, ±3^k)` with
`10 ≤ j, k < m + 10`. Here the points are `(±2, 0), …, (±2m, 0)` and `(0, ±1), …, (0, ±(2m - 1))`,
and the argument for no four points on a circle uses parity instead.

A circle meets each axis in at most two points. If it met each axis in two points `(s, 0), (t, 0)`
and `(0, u), (0, v)`, then `s * t = u * v` (both equal the power of the origin), which is
impossible since `s, t` are even and `u, v` are odd. A point on one axis has at most `2m - 1`
distances to the other points of its axis, and at most `m` distances to the points of the other
axis, since `(0, w)` and `(0, -w)` are equidistant from it. This gives at most `3m - 1` distinct
distances, as in [Fe26, Theorem 3].

*Reference:* [Fe26] T. Feng et al, *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study
on the Erdős Problems*. arXiv:2601.22401 (2026), Section 3.1.
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

namespace Erdos654Proof

lemma dist_sq (P Q : ℝ²) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

lemma ext_two {P Q : ℝ²} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q :=
  PiLp.ext (Fin.forall_fin_two.2 ⟨h0, h1⟩)

/-- Points of the first axis with even integer coordinate. -/
def XAxis : Set ℝ² := {P | P 1 = 0 ∧ ∃ a : ℤ, P 0 = 2 * a}

/-- Points of the second axis with odd integer coordinate. -/
def YAxis : Set ℝ² := {P | P 0 = 0 ∧ ∃ b : ℤ, P 1 = 2 * b + 1}

/-- Two distinct points of the first axis at distance `r` from `c` are symmetric about `c 0`. -/
lemma axis0_sum {P Q c : ℝ²} {r : ℝ} (hP : P 1 = 0) (hQ : Q 1 = 0) (hPQ : P ≠ Q)
    (hPr : dist P c = r) (hQr : dist Q c = r) : P 0 + Q 0 = 2 * c 0 := by
  have h0 : P 0 ≠ Q 0 := fun h ↦ hPQ (ext_two h (hP.trans hQ.symm))
  have e := dist_sq P c
  have f := dist_sq Q c
  rw [hPr, hP] at e
  rw [hQr, hQ] at f
  have : (P 0 - Q 0) * (P 0 + Q 0 - 2 * c 0) = 0 := by linear_combination f - e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h0
  · linarith

/-- Two distinct points of the second axis at distance `r` from `c` are symmetric about `c 1`. -/
lemma axis1_sum {P Q c : ℝ²} {r : ℝ} (hP : P 0 = 0) (hQ : Q 0 = 0) (hPQ : P ≠ Q)
    (hPr : dist P c = r) (hQr : dist Q c = r) : P 1 + Q 1 = 2 * c 1 := by
  have h1 : P 1 ≠ Q 1 := fun h ↦ hPQ (ext_two (hP.trans hQ.symm) h)
  have e := dist_sq P c
  have f := dist_sq Q c
  rw [hPr, hP] at e
  rw [hQr, hQ] at f
  have : (P 1 - Q 1) * (P 1 + Q 1 - 2 * c 1) = 0 := by linear_combination f - e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · linarith

/-- No four points of `XAxis ∪ YAxis` lie on a circle: a circle meets each axis in at most two
points, and two points on each axis would give `s * t = u * v` with `s, t` even and `u, v` odd. -/
lemma noFourConcyclic_axes : NoFourConcyclic (XAxis ∪ YAxis) := by
  intro T hT h4 ⟨c, r, hcr⟩
  have hTfin : T.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hXfin : (T ∩ XAxis).Finite := hTfin.subset Set.inter_subset_left
  have hYfin : (T ∩ YAxis).Finite := hTfin.subset Set.inter_subset_left
  have hX : (T ∩ XAxis).ncard ≤ 2 := by
    by_contra! h
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := (Set.two_lt_ncard_iff hXfin).1 h
    have h1 := axis0_sum ha.2.1 hb.2.1 hab (hcr a ha.1) (hcr b hb.1)
    have h2 := axis0_sum ha.2.1 hd.2.1 had (hcr a ha.1) (hcr d hd.1)
    exact hbd (ext_two (by linarith) (hb.2.1.trans hd.2.1.symm))
  have hY : (T ∩ YAxis).ncard ≤ 2 := by
    by_contra! h
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := (Set.two_lt_ncard_iff hYfin).1 h
    have h1 := axis1_sum ha.2.1 hb.2.1 hab (hcr a ha.1) (hcr b hb.1)
    have h2 := axis1_sum ha.2.1 hd.2.1 had (hcr a ha.1) (hcr d hd.1)
    exact hbd (ext_two (hb.2.1.trans hd.2.1.symm) (by linarith))
  have hdisj : Disjoint (T ∩ XAxis) (T ∩ YAxis) := by
    rw [Set.disjoint_left]
    rintro P ⟨-, hP1, -⟩ ⟨-, -, b, hb⟩
    rw [hP1] at hb
    have : ((2 * b + 1 : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective this
    omega
  have hsplit : T.ncard = (T ∩ XAxis).ncard + (T ∩ YAxis).ncard := by
    rw [← Set.ncard_union_eq hdisj hXfin hYfin, ← Set.inter_union_distrib_left,
      Set.inter_eq_left.2 hT]
  obtain ⟨p, q, hp, hq, hpq⟩ := (Set.one_lt_ncard_iff hXfin).1 (by omega)
  obtain ⟨u, v, hu, hv, huv⟩ := (Set.one_lt_ncard_iff hYfin).1 (by omega)
  have s1 := axis0_sum hp.2.1 hq.2.1 hpq (hcr p hp.1) (hcr q hq.1)
  have s2 := axis1_sum hu.2.1 hv.2.1 huv (hcr u hu.1) (hcr v hv.1)
  have e1 := dist_sq p c
  have e2 := dist_sq u c
  rw [hcr p hp.1, hp.2.1] at e1
  rw [hcr u hu.1, hu.2.1] at e2
  have key : p 0 * q 0 = u 1 * v 1 := by linear_combination p 0 * s1 - u 1 * s2 + e1 - e2
  obtain ⟨a, ha⟩ := hp.2.2
  obtain ⟨b, hb⟩ := hq.2.2
  obtain ⟨a', ha'⟩ := hu.2.2
  obtain ⟨b', hb'⟩ := hv.2.2
  rw [ha, hb, ha', hb'] at key
  have hZ : 2 * a * (2 * b) = (2 * a' + 1) * (2 * b' + 1) := by
    have : ((2 * a * (2 * b) : ℤ) : ℝ) = ((2 * a' + 1) * (2 * b' + 1) : ℤ) := by
      push_cast; linarith
    exact Int.cast_injective this
  have hodd : Odd ((2 * a' + 1) * (2 * b' + 1)) := Odd.mul ⟨a', rfl⟩ ⟨b', rfl⟩
  have heven : Even (2 * a * (2 * b)) := ⟨a * (2 * b), by ring⟩
  rw [hZ] at heven
  exact (Int.not_even_iff_odd.2 hodd) heven

/-- Half of the first coordinate of the point `xpt p`: `±(i + 1)`. -/
def xh (p : Bool × ℕ) : ℤ := if p.1 then p.2 + 1 else -((p.2 : ℤ) + 1)

/-- The second coordinate of `ypt p` is `2 * yh p + 1 = ±(2 j + 1)`. -/
def yh (p : Bool × ℕ) : ℤ := if p.1 then p.2 else -(p.2 : ℤ) - 1

/-- The point `(±2(i + 1), 0)`. -/
noncomputable def xpt (p : Bool × ℕ) : ℝ² := !₂[2 * (xh p : ℝ), 0]

/-- The point `(0, ±(2 j + 1))`. -/
noncomputable def ypt (p : Bool × ℕ) : ℝ² := !₂[0, 2 * (yh p : ℝ) + 1]

@[simp] lemma xpt_zero (p : Bool × ℕ) : xpt p 0 = 2 * (xh p : ℝ) := rfl
@[simp] lemma xpt_one (p : Bool × ℕ) : xpt p 1 = 0 := rfl
@[simp] lemma ypt_zero (p : Bool × ℕ) : ypt p 0 = 0 := rfl
@[simp] lemma ypt_one (p : Bool × ℕ) : ypt p 1 = 2 * (yh p : ℝ) + 1 := rfl

lemma xh_injective : Function.Injective xh := by
  rintro ⟨σ, i⟩ ⟨τ, k⟩ h
  cases σ <;> cases τ <;> simp [xh] at h ⊢ <;> omega

lemma yh_injective : Function.Injective yh := by
  rintro ⟨σ, i⟩ ⟨τ, k⟩ h
  cases σ <;> cases τ <;> simp [yh] at h ⊢ <;> omega

lemma xpt_injective : Function.Injective xpt := by
  intro p q h
  have := congrArg (· 0) h
  simp only [xpt_zero, mul_eq_mul_left_iff, Int.cast_inj] at this
  exact xh_injective (this.resolve_right two_ne_zero)

lemma ypt_injective : Function.Injective ypt := by
  intro p q h
  have := congrArg (· 1) h
  simp only [ypt_one, add_left_inj, mul_eq_mul_left_iff, Int.cast_inj] at this
  exact yh_injective (this.resolve_right two_ne_zero)

lemma xh_sq (p : Bool × ℕ) : (xh p : ℝ) ^ 2 = ((p.2 : ℝ) + 1) ^ 2 := by
  have h : xh p ^ 2 = ((p.2 : ℤ) + 1) ^ 2 := by unfold xh; split <;> ring
  exact_mod_cast h

lemma yh_sq (p : Bool × ℕ) : (2 * (yh p : ℝ) + 1) ^ 2 = (2 * (p.2 : ℝ) + 1) ^ 2 := by
  have h : (2 * yh p + 1) ^ 2 = (2 * (p.2 : ℤ) + 1) ^ 2 := by unfold yh; split <;> ring
  exact_mod_cast h

/-- The index set: a sign and `i < m`. -/
def idx (m : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range m

lemma card_idx (m : ℕ) : #(idx m) = 2 * m := by simp [idx]

/-- The `2m` points `(±2, 0), …, (±2m, 0)`. -/
noncomputable def XS (m : ℕ) : Finset ℝ² := (idx m).image xpt

/-- The `2m` points `(0, ±1), …, (0, ±(2m - 1))`. -/
noncomputable def YS (m : ℕ) : Finset ℝ² := (idx m).image ypt

/-- The point set: `2m` points on each axis (a variant of the set of [Fe26]). -/
noncomputable def A (m : ℕ) : Finset ℝ² := XS m ∪ YS m

lemma card_XS (m : ℕ) : #(XS m) = 2 * m := by
  rw [XS, card_image_of_injective _ xpt_injective, card_idx]

lemma card_YS (m : ℕ) : #(YS m) = 2 * m := by
  rw [YS, card_image_of_injective _ ypt_injective, card_idx]

lemma disjoint_XS_YS (m : ℕ) : Disjoint (XS m) (YS m) := by
  rw [Finset.disjoint_left]
  simp only [XS, YS, mem_image]
  rintro _ ⟨p, -, rfl⟩ ⟨q, -, hq⟩
  have := congrArg (· 1) hq
  simp only [ypt_one, xpt_one] at this
  have : ((2 * yh q + 1 : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by push_cast; linarith
  have := Int.cast_injective this
  omega

lemma card_A (m : ℕ) : #(A m) = 4 * m := by
  rw [A, card_union_of_disjoint (disjoint_XS_YS m), card_XS, card_YS]
  ring

lemma A_subset_axes (m : ℕ) : (A m : Set ℝ²) ⊆ XAxis ∪ YAxis := by
  intro P hP
  simp only [A, XS, YS, coe_union, coe_image, Set.mem_union, Set.mem_image] at hP
  rcases hP with ⟨p, -, rfl⟩ | ⟨p, -, rfl⟩
  · exact Or.inl ⟨rfl, xh p, rfl⟩
  · exact Or.inr ⟨rfl, yh p, rfl⟩

lemma noFourConcyclic_A (m : ℕ) : NoFourConcyclic (A m : Set ℝ²) :=
  fun T hT ↦ noFourConcyclic_axes T (hT.trans (A_subset_axes m))

/-- If every point of `S` lies in `B` or `C` and `x ∈ B`, then the distances from `x` to the
other points of `S` take at most `#B - 1` values plus the number of distances from `x` to `C`.
Stated for any `DecidableEq` instance, so that it applies to `distinctDistancesFrom`. -/
lemma card_image_erase_le [DecidableEq ℝ²] (S B C : Finset ℝ²) {x : ℝ²}
    (hS : ∀ y ∈ S, y ∈ B ∨ y ∈ C) (hx : x ∈ B) :
    #((S.erase x).image fun y ↦ dist y x) ≤ (#B - 1) + #(C.image fun y ↦ dist y x) := by
  have hsub : S.erase x ⊆ B.erase x ∪ C := by
    intro y hy
    rw [mem_erase] at hy
    rw [mem_union, mem_erase]
    rcases hS y hy.2 with h | h
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr h
  calc #((S.erase x).image fun y ↦ dist y x)
      ≤ #((B.erase x ∪ C).image fun y ↦ dist y x) := card_le_card (image_subset_image hsub)
    _ ≤ #((B.erase x).image fun y ↦ dist y x) + #(C.image fun y ↦ dist y x) := by
      rw [image_union]; exact card_union_le _ _
    _ ≤ #(B.erase x) + #(C.image fun y ↦ dist y x) := by
      gcongr; exact card_image_le
    _ = (#B - 1) + #(C.image fun y ↦ dist y x) := by rw [card_erase_of_mem hx]

lemma distinctDistancesFrom_union_le (B C : Finset ℝ²) {x : ℝ²} (hx : x ∈ B) :
    distinctDistancesFrom (B ∪ C) x ≤ (#B - 1) + #(C.image fun y ↦ dist y x) := by
  unfold distinctDistancesFrom
  convert card_image_erase_le (B ∪ C) B C (fun y hy ↦ mem_union.1 hy) hx

/-- The distances from `x` to the points `f q`, `q ∈ idx m`, take at most `m` values when they
depend only on the second component of `q`. -/
lemma card_image_dist_le (m : ℕ) (f : Bool × ℕ → ℝ²) (x : ℝ²)
    (hf : ∀ q, dist (f q) x = dist (f (true, q.2)) x) :
    #(((idx m).image f).image fun y ↦ dist y x) ≤ m := by
  classical
  rw [image_image]
  have : (idx m).image ((fun y ↦ dist y x) ∘ f) =
      ((idx m).image Prod.snd).image fun j ↦ dist (f (true, j)) x := by
    rw [image_image]
    exact image_congr fun q _ ↦ hf q
  rw [this]
  refine card_image_le.trans ((card_le_card ?_).trans (card_range m).le)
  intro j hj
  simp only [idx, mem_image, mem_product, mem_univ, true_and] at hj
  obtain ⟨⟨_, k⟩, hk, rfl⟩ := hj
  exact hk

lemma dist_eq_of_sq_eq {P Q P' Q' : ℝ²} (h : dist P Q ^ 2 = dist P' Q' ^ 2) :
    dist P Q = dist P' Q' :=
  (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h

lemma dist_ypt (p q : Bool × ℕ) : dist (ypt q) (xpt p) = dist (ypt (true, q.2)) (xpt p) := by
  apply dist_eq_of_sq_eq
  rw [dist_sq, dist_sq]
  simp only [ypt_zero, ypt_one, xpt_zero, xpt_one, sub_zero]
  rw [yh_sq q, yh_sq (true, q.2)]

lemma dist_xpt (p q : Bool × ℕ) : dist (xpt q) (ypt p) = dist (xpt (true, q.2)) (ypt p) := by
  apply dist_eq_of_sq_eq
  rw [dist_sq, dist_sq]
  simp only [ypt_zero, ypt_one, xpt_zero, xpt_one, zero_sub]
  have h1 := xh_sq q
  have h2 := xh_sq (true, q.2)
  nlinarith [h1, h2]

/-- Every point of `A m` has at most `3m - 1` distinct distances to the other points. -/
lemma distinctDistancesFrom_A_lt (m : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ A m, distinctDistancesFrom (A m) x < 3 * m := by
  intro x hx
  rcases mem_union.1 hx with hX | hY
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hX
    have h1 := distinctDistancesFrom_union_le (XS m) (YS m) hX
    have h2 := card_image_dist_le m ypt (xpt p) (fun q ↦ dist_ypt p q)
    rw [card_XS] at h1
    rw [A]
    change _ ≤ _ + #(((idx m).image ypt).image _) at h1
    omega
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hY
    have h1 := distinctDistancesFrom_union_le (YS m) (XS m) hY
    have h2 := card_image_dist_le m xpt (ypt p) (fun q ↦ dist_xpt p q)
    rw [card_YS] at h1
    rw [A, union_comm]
    change _ ≤ _ + #(((idx m).image xpt).image _) at h1
    omega

theorem feng (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m :=
  ⟨A m, card_A m, noFourConcyclic_A m, distinctDistancesFrom_A_lt m hm⟩

theorem parts_i :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1 / 8) (by norm_num))
  set m := max N 1
  obtain ⟨B, hB, hBc, hBd⟩ := feng m (le_max_right N 1)
  have hNm : N ≤ m := le_max_left N 1
  obtain ⟨x, hx, hlt⟩ := hN (4 * m) (by omega) B hB hBc
  have h3 : (distinctDistancesFrom B x : ℝ) < 3 * m := by exact_mod_cast hBd x hx
  push_cast at hlt
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

end Erdos654Proof

namespace Erdos654

theorem erdos_654.parts.i :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) :=
  Erdos654Proof.parts_i

theorem erdos_654.variants.feng (m : ℕ) (hm : 10 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m :=
  Erdos654Proof.feng m (by omega)

end Erdos654
