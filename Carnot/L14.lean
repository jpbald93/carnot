import Carnot.Main

/-!
# Layer 14: Mathlib-only restatements and a witness for Carnot's theorem

The statements `l14_*` mention only Mathlib notions: the signed distance to a side line is
Mathlib's `Affine.Simplex.signedInfDist`, the circumcentre, circumradius and inradius are Mathlib's,
and `l14_carnot_of_dist_eq` characterises the circumcentre by its defining property (a point of
the plane of the triangle equidistant from the three vertices).

`l14w_carnot` is the obtuse scalene triangle `0, 21, 6 + 8i` (sides `21, 10, 17`), with
`cos A = 3/5`, `cos B = 15/17`, `cos C = -13/85`. The signed distance from the circumcentre to the
side opposite the obtuse vertex is negative, the other two are positive and distinct.
-/

namespace Carnot

open EuclideanGeometry Affine Affine.Simplex Complex ComplexConjugate

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Carnot (Mathlib-only).** The signed distances from the circumcentre to the side lines sum
to `R + r`. -/
theorem l14_carnot (t : Triangle ℝ P) :
    ∑ i, t.signedInfDist i t.circumcenter = t.circumradius + t.inradius := by
  rw [← carnot_sum t]
  exact Finset.sum_congr rfl fun i _ =>
    (signedSideDist_eq_signedInfDist t t.circumcenter_mem_affineSpan i).symm

/-- **Carnot (Mathlib-only, defining property).** If `O` lies in the plane of `t` and is at
distance `R` from the three vertices, the signed distances from `O` to the side lines sum to
`R + r`. -/
theorem l14_carnot_of_dist_eq (t : Triangle ℝ P) {O : P}
    (hO : O ∈ affineSpan ℝ (Set.range t.points)) {R : ℝ} (hR : ∀ i, dist (t.points i) O = R) :
    ∑ i, t.signedInfDist i O = R + t.inradius := by
  rw [t.eq_circumradius_of_dist_eq hO hR, t.eq_circumcenter_of_dist_eq hO hR]
  exact l14_carnot t

/-- **Carnot, cosine form (Mathlib-only).** `d(O, side i) = R cos αᵢ`. -/
theorem l14_signedInfDist_circumcenter_eq (t : Triangle ℝ P) :
    t.signedInfDist 0 t.circumcenter =
        t.circumradius * Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) ∧
      t.signedInfDist 1 t.circumcenter =
        t.circumradius * Real.cos (∠ (t.points 0) (t.points 1) (t.points 2)) ∧
      t.signedInfDist 2 t.circumcenter =
        t.circumradius * Real.cos (∠ (t.points 0) (t.points 2) (t.points 1)) := by
  have e := fun i => signedSideDist_eq_signedInfDist t t.circumcenter_mem_affineSpan i
  obtain ⟨h0, h1, h2⟩ := signedSideDist_circumcenter_eq t
  rw [← e 0, ← e 1, ← e 2]
  exact ⟨h0, h1, h2⟩

/-- **Carnot, cosine form (Mathlib-only).** `cos A + cos B + cos C = 1 + r / R`. -/
theorem l14_cos_add_cos_add_cos (t : Triangle ℝ P) :
    Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) +
        Real.cos (∠ (t.points 0) (t.points 1) (t.points 2)) +
        Real.cos (∠ (t.points 0) (t.points 2) (t.points 1)) =
      1 + t.inradius / t.circumradius :=
  cos_add_cos_add_cos t

/-! ### Bridges for the witness -/

theorem l14b_affineIndependent {a b c : ℂ} (h : (conj (b - a) * (c - a)).im ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert a _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r₁, hr₁⟩ := hv b (by simp)
  obtain ⟨r₂, hr₂⟩ := hv c (by simp)
  apply h
  rw [hr₁, hr₂]
  simp only [vadd_eq_add, add_sub_cancel_right, Complex.real_smul, map_mul, Complex.conj_ofReal,
    mul_im, mul_re, conj_re, conj_im, ofReal_re, ofReal_im]
  ring

theorem l14b_norm {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 = r ^ 2) : ‖z‖ = r := by
  rw [← Real.sqrt_sq hr, ← h, Complex.norm_def, normSq_apply]
  congr 1
  ring

theorem l14b_cos_angle (p q r : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : (p - q).re ^ 2 + (p - q).im ^ 2 = a ^ 2) (h2 : (r - q).re ^ 2 + (r - q).im ^ 2 = b ^ 2) :
    Real.cos (∠ p q r) = ((r - q) * conj (p - q)).re / (a * b) := by
  rw [EuclideanGeometry.angle, InnerProductGeometry.cos_angle, Complex.inner, vsub_eq_sub,
    vsub_eq_sub, l14b_norm ha h1, l14b_norm hb h2]

/-! ### Witness -/

/-- **Witness.** For the obtuse scalene triangle `0, 21, 6 + 8i` the three signed distances from
the circumcentre are `3R/5`, `15R/17` and `-13R/85`: one negative, two positive and distinct;
Carnot's identity holds for it. -/
theorem l14w_carnot : ∃ t : Triangle ℝ ℂ, t.points = ![0, 21, 6 + 8 * I] ∧
    t.signedInfDist 2 t.circumcenter < 0 ∧ 0 < t.signedInfDist 0 t.circumcenter ∧
    0 < t.signedInfDist 1 t.circumcenter ∧
    t.signedInfDist 0 t.circumcenter ≠ t.signedInfDist 1 t.circumcenter ∧
    ∑ i, t.signedInfDist i t.circumcenter = t.circumradius + t.inradius := by
  have hi : AffineIndependent ℝ ![(0 : ℂ), 21, 6 + 8 * I] :=
    l14b_affineIndependent (by norm_num)
  refine ⟨⟨_, hi⟩, rfl, ?_⟩
  obtain ⟨e0, e1, e2⟩ := l14_signedInfDist_circumcenter_eq (⟨_, hi⟩ : Triangle ℝ ℂ)
  have hR := (⟨_, hi⟩ : Triangle ℝ ℂ).circumradius_pos
  change _ = _ * Real.cos (∠ (21 : ℂ) 0 (6 + 8 * I)) at e0
  change _ = _ * Real.cos (∠ (0 : ℂ) 21 (6 + 8 * I)) at e1
  change _ = _ * Real.cos (∠ (0 : ℂ) (6 + 8 * I) 21) at e2
  have c0 : Real.cos (∠ (21 : ℂ) 0 (6 + 8 * I)) = 3 / 5 := by
    rw [l14b_cos_angle _ _ _ (a := 21) (b := 10) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have c1 : Real.cos (∠ (0 : ℂ) 21 (6 + 8 * I)) = 15 / 17 := by
    rw [l14b_cos_angle _ _ _ (a := 21) (b := 17) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have c2 : Real.cos (∠ (0 : ℂ) (6 + 8 * I) 21) = -13 / 85 := by
    rw [l14b_cos_angle _ _ _ (a := 10) (b := 17) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  rw [c0] at e0
  rw [c1] at e1
  rw [c2] at e2
  refine ⟨by rw [e2]; nlinarith, by rw [e0]; positivity, by rw [e1]; positivity,
    by rw [e0, e1]; intro h; nlinarith, l14_carnot _⟩

end Carnot
