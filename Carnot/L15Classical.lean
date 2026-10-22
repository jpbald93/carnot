import Carnot.Algebra
import Carnot.Geometry
import Carnot.Main

/-!
# Layer 15: classical statements

Layer 15. These definitions and statements were written independently, from textbook statements, by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves (or proves part of) one of them from this development.
-/

open EuclideanGeometry

noncomputable section

open scoped Classical

namespace Carnot.Classical

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- OWN DEFINITION (writer, verbatim). -/
def signedDistLine (l : AffineSubspace ℝ P) (ref p : P) : ℝ :=
  if l.SOppSide p ref then -Metric.infDist p (l : Set P) else Metric.infDist p (l : Set P)

/-! ## Writer statements, verbatim, packaged as `Prop`s. -/

def classical_TriSimplex1_a : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C]),
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    signedDistLine line[ℝ, B, C] A t.circumcenter +
      signedDistLine line[ℝ, C, A] B t.circumcenter +
      signedDistLine line[ℝ, A, B] C t.circumcenter = t.circumradius + t.inradius

def classical_TriSimplex1_b_signed : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C]),
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    signedDistLine line[ℝ, B, C] A t.circumcenter = t.circumradius * Real.cos (∠ B A C) ∧
    signedDistLine line[ℝ, C, A] B t.circumcenter = t.circumradius * Real.cos (∠ C B A) ∧
    signedDistLine line[ℝ, A, B] C t.circumcenter = t.circumradius * Real.cos (∠ A C B)

def classical_TriSimplex1_b : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C]),
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    Real.cos (∠ B A C) + Real.cos (∠ C B A) + Real.cos (∠ A C B) =
      1 + t.inradius / t.circumradius

def classical_TriSimplex1_b_acute : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C])
    (hA : ∠ B A C < Real.pi / 2) (hB : ∠ C B A < Real.pi / 2) (hC : ∠ A C B < Real.pi / 2),
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    Metric.infDist t.circumcenter (line[ℝ, B, C] : Set P) +
      Metric.infDist t.circumcenter (line[ℝ, C, A] : Set P) +
      Metric.infDist t.circumcenter (line[ℝ, A, B] : Set P) = t.circumradius + t.inradius

def classical_TriSimplex1_b_acute_inside : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C])
    (hA : ∠ B A C < Real.pi / 2) (hB : ∠ C B A < Real.pi / 2) (hC : ∠ A C B < Real.pi / 2),
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    t.circumcenter ∈ t.interior

/-! ## Bridge: the writer's `signedDistLine` against the face equals Mathlib's
`Affine.Simplex.signedInfDist` on the affine span of the simplex. -/

theorem signedDistLine_face_eq {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1))
    {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    signedDistLine (affineSpan ℝ (s.points '' {i}ᶜ)) (s.points i) p = s.signedInfDist i p := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  have hinf : Metric.infDist (Finset.univ.affineCombination ℝ s.points w)
      ((affineSpan ℝ (s.points '' {i}ᶜ) : AffineSubspace ℝ P) : Set P) =
      |s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w)| := by
    rw [Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range i hp,
      Affine.Simplex.orthogonalProjectionSpan, dist_orthogonalProjection_eq_infDist,
      Affine.Simplex.range_faceOpposite_points]
  have hside := s.sOppSide_affineSpan_faceOpposite_point_right_iff hw (i := i)
  rw [Affine.Simplex.range_faceOpposite_points] at hside
  rw [signedDistLine, hinf, Affine.Simplex.signedInfDist_affineCombination _ _ hw]
  have hpos : 0 < ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ := by
    rw [norm_pos_iff, vsub_ne_zero]
    exact s.ne_altitudeFoot i
  split_ifs with h
  · have := hside.1 h
    rw [abs_of_neg (mul_neg_of_neg_of_pos this hpos), neg_neg]
  · have : 0 ≤ w i := by
      by_contra h'; exact h (hside.2 (lt_of_not_ge h'))
    rw [abs_of_nonneg (mul_nonneg this hpos.le)]

lemma face_eq (A B C : P) :
    affineSpan ℝ (![A, B, C] '' {0}ᶜ) = line[ℝ, B, C] ∧
    affineSpan ℝ (![A, B, C] '' {1}ᶜ) = line[ℝ, C, A] ∧
    affineSpan ℝ (![A, B, C] '' {2}ᶜ) = line[ℝ, A, B] := by
  have e0 : ({0}ᶜ : Set (Fin 3)) = {1, 2} := by ext j; fin_cases j <;> simp
  have e1 : ({1}ᶜ : Set (Fin 3)) = {2, 0} := by ext j; fin_cases j <;> simp
  have e2 : ({2}ᶜ : Set (Fin 3)) = {0, 1} := by ext j; fin_cases j <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, Set.image_pair]; rfl
  · rw [e1, Set.image_pair]; rfl
  · rw [e2, Set.image_pair]; rfl

/-- The three writer signed distances are Carnot's `signedSideDist`. -/
lemma sdl_eq_ssd (A B C : P) (h : AffineIndependent ℝ ![A, B, C]) (p : P)
    (hp : p ∈ affineSpan ℝ (Set.range (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).points)) :
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    signedDistLine line[ℝ, B, C] A p = Carnot.signedSideDist t 0 p ∧
    signedDistLine line[ℝ, C, A] B p = Carnot.signedSideDist t 1 p ∧
    signedDistLine line[ℝ, A, B] C p = Carnot.signedSideDist t 2 p := by
  intro t
  obtain ⟨f0, f1, f2⟩ := face_eq A B C
  refine ⟨?_, ?_, ?_⟩
  · rw [Carnot.signedSideDist_eq_signedInfDist t hp, ← signedDistLine_face_eq t 0 hp]
    change _ = signedDistLine (affineSpan ℝ (![A, B, C] '' {0}ᶜ)) A p
    rw [f0]
  · rw [Carnot.signedSideDist_eq_signedInfDist t hp, ← signedDistLine_face_eq t 1 hp]
    change _ = signedDistLine (affineSpan ℝ (![A, B, C] '' {1}ᶜ)) B p
    rw [f1]
  · rw [Carnot.signedSideDist_eq_signedInfDist t hp, ← signedDistLine_face_eq t 2 hp]
    change _ = signedDistLine (affineSpan ℝ (![A, B, C] '' {2}ᶜ)) C p
    rw [f2]

theorem cov_TriSimplex1_a : classical_TriSimplex1_a (P := P) := by
  intro A B C h t
  obtain ⟨e0, e1, e2⟩ := sdl_eq_ssd A B C h t.circumcenter t.circumcenter_mem_affineSpan
  rw [e0, e1, e2]
  exact Carnot.carnot t

theorem cov_TriSimplex1_b_signed : classical_TriSimplex1_b_signed (P := P) := by
  intro A B C h t
  obtain ⟨e0, e1, e2⟩ := sdl_eq_ssd A B C h t.circumcenter t.circumcenter_mem_affineSpan
  obtain ⟨c0, c1, c2⟩ := Carnot.signedSideDist_circumcenter_eq t
  rw [e0, e1, e2, c0, c1, c2, angle_comm C B A]
  exact ⟨rfl, rfl, rfl⟩

theorem cov_TriSimplex1_b : classical_TriSimplex1_b (P := P) := by
  intro A B C h t
  have := Carnot.cos_add_cos_add_cos t
  rw [angle_comm C B A]
  exact this

theorem cov_TriSimplex1_b_acute : classical_TriSimplex1_b_acute (P := P) := by
  intro A B C h hA hB hC t
  have hO := t.circumcenter_mem_affineSpan
  obtain ⟨e0, e1, e2⟩ := sdl_eq_ssd A B C h t.circumcenter hO
  obtain ⟨c0, c1, c2⟩ := Carnot.signedSideDist_circumcenter_eq t
  have hR := t.circumradius_pos
  have pos : ∀ x : ℝ, 0 ≤ x → x < Real.pi / 2 → 0 < t.circumradius * Real.cos x :=
    fun x h0 h1 => mul_pos hR (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
  have k0 : 0 < signedDistLine line[ℝ, B, C] A t.circumcenter := by
    rw [e0, c0]; exact pos _ (angle_nonneg _ _ _) hA
  have k1 : 0 < signedDistLine line[ℝ, C, A] B t.circumcenter := by
    rw [e1, c1]; rw [angle_comm] at hB; exact pos _ (angle_nonneg _ _ _) hB
  have k2 : 0 < signedDistLine line[ℝ, A, B] C t.circumcenter := by
    rw [e2, c2]; exact pos _ (angle_nonneg _ _ _) hC
  have unsign : ∀ (l : AffineSubspace ℝ P) (ref x : P), 0 < signedDistLine l ref x →
      signedDistLine l ref x = Metric.infDist x (l : Set P) := by
    intro l ref x hx
    unfold signedDistLine at hx ⊢
    split_ifs at hx ⊢ with hs
    · exact absurd hx (not_lt.2 (neg_nonpos.2 Metric.infDist_nonneg))
    · rfl
  rw [← unsign _ _ _ k0, ← unsign _ _ _ k1, ← unsign _ _ _ k2]
  exact cov_TriSimplex1_a A B C h

theorem cov_TriSimplex1_b_acute_inside : classical_TriSimplex1_b_acute_inside (P := P) := by
  intro A B C h hA hB hC t
  obtain ⟨w, hw, hOw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
    t.circumcenter_mem_affineSpan
  obtain ⟨c0, c1, c2⟩ := Carnot.signedSideDist_circumcenter_eq t
  have hR := t.circumradius_pos
  have pos : ∀ x : ℝ, 0 ≤ x → x < Real.pi / 2 → 0 < t.circumradius * Real.cos x :=
    fun x h0 h1 => mul_pos hR (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
  have hwi : ∀ i, 0 < w i := by
    intro i
    have key : Carnot.signedSideDist t i t.circumcenter = w i * t.height i := by
      rw [hOw]; exact Carnot.signedSideDist_affineCombination t w hw i
    have hpos : 0 < Carnot.signedSideDist t i t.circumcenter := by
      fin_cases i
      · exact c0 ▸ pos _ (angle_nonneg _ _ _) hA
      · rw [angle_comm] at hB; exact c1 ▸ pos _ (angle_nonneg _ _ _) hB
      · exact c2 ▸ pos _ (angle_nonneg _ _ _) hC
    rw [key] at hpos
    exact pos_of_mul_pos_left hpos (t.height_pos i).le
  refine ⟨w, hw, fun i => ⟨hwi i, ?_⟩, hOw.symm⟩
  have hs := hw
  rw [Fin.sum_univ_three] at hs
  have := hwi 0; have := hwi 1; have := hwi 2
  fin_cases i <;> simp <;> linarith

end Carnot.Classical
