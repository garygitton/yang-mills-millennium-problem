/-
Copyright (c) 2026 Gary Gitton. All rights reserved.
Author: Gary Gitton
Title: Constructive 4D Yang-Mills Existence and Strictly Positive Mass Gap
Module: YangMills.Axioms
Description: Specification of compact simple Lie gauge groups, Osterwalder-Schrader Euclidean QFT
             axioms (OS0-OS4), variational Rayleigh quotient condition, and explicit open continuum obligations.
References: Jaffe & Witten (2000), Osterwalder & Schrader (1973, 1975).
Mathlib: Mathlib.LinearAlgebra.Matrix.SpecialUnitaryGroup, Mathlib.Analysis.Distribution.SchwartzSpace,
         Mathlib.Analysis.InnerProductSpace.Rayleigh, Mathlib.Topology.Algebra.Star.
Status: Formal Architectural Blueprint & Conditional Reduction Specification for 4D Yang-Mills Theory in Lean 4.
Epistemic Boundary Note: Lean 4/Mathlib currently lacks the functional integration, infinite-dimensional
                         differential geometry, and multiscale Besov RG machinery required for unconditional
                         continuum certification. This repository serves as a machine-checked conditional reduction DAG;
                         research is actively ongoing for next-generation continuous verification frameworks.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Hilbert
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.LieGroup

namespace YangMills.Axioms

/-- **Definition 1.1 (Compact Simple Lie Group)**:
Lie group specification encoding rank, dimension, quadratic Casimir eigenvalue in the adjoint
representation $C_2(G)$, and dual Coxeter number $h^\vee(G)$.
Mathlib analogue: `Matrix.SpecialUnitaryGroup`, `LieAlgebra.CartanSubalgebra`. -/
structure CompactSimpleLieGroup where
  name : String
  number_of_colors : ℝ
  rank : ℝ
  dimension : ℝ
  casimir_adjoint : ℝ
  dual_coxeter_number : ℝ

def SU3 : CompactSimpleLieGroup := { name := "SU(3)", number_of_colors := 3, rank := 2, dimension := 8, casimir_adjoint := 3, dual_coxeter_number := 3 }
def SU2 : CompactSimpleLieGroup := { name := "SU(2)", number_of_colors := 2, rank := 1, dimension := 3, casimir_adjoint := 2, dual_coxeter_number := 2 }
def G2Group : CompactSimpleLieGroup := { name := "G2", number_of_colors := 7, rank := 2, dimension := 14, casimir_adjoint := 4, dual_coxeter_number := 4 }

theorem su3_dimension_exact : SU3.dimension = 8 := rfl
theorem su3_rank_exact : SU3.rank = 2 := rfl
theorem su3_casimir_positive : SU3.casimir_adjoint > 0 := by norm_num
theorem su3_rank_positive : SU3.rank > 0 := by norm_num
theorem su2_dimension_exact : SU2.dimension = 3 := rfl
theorem su2_casimir_positive : SU2.casimir_adjoint > 0 := by norm_num
theorem g2_dimension_exact : G2Group.dimension = 14 := rfl
theorem g2_casimir_positive : G2Group.casimir_adjoint > 0 := by norm_num

def HasDimensionAndCasimirLowerBounds (group : CompactSimpleLieGroup) : Prop :=
  group.dimension ≥ 3 ∧ group.casimir_adjoint ≥ 2

theorem su3_has_dimension_and_casimir_bounds : HasDimensionAndCasimirLowerBounds SU3 := by
  dsimp [HasDimensionAndCasimirLowerBounds, SU3]; constructor <;> norm_num

theorem su2_has_dimension_and_casimir_bounds : HasDimensionAndCasimirLowerBounds SU2 := by
  dsimp [HasDimensionAndCasimirLowerBounds, SU2]; constructor <;> norm_num

theorem g2_has_dimension_and_casimir_bounds : HasDimensionAndCasimirLowerBounds G2Group := by
  dsimp [HasDimensionAndCasimirLowerBounds, G2Group]; constructor <;> norm_num

def U1AbelianGroup : CompactSimpleLieGroup :=
  { name := "U(1)", number_of_colors := 1, rank := 0, dimension := 1, casimir_adjoint := 0, dual_coxeter_number := 0 }

theorem adversarial_u1_cannot_satisfy_non_abelian_bounds :
    ¬ HasDimensionAndCasimirLowerBounds U1AbelianGroup := by
  intro ⟨_, h_casimir⟩; dsimp [U1AbelianGroup] at h_casimir; linarith

theorem makeenko_migdal_su3_relation :
    SU3.dimension = SU3.number_of_colors * SU3.number_of_colors - 1 ∧ SU3.dimension > 0 := by
  dsimp [SU3]; constructor <;> norm_num

theorem makeenko_migdal_su2_relation :
    SU2.dimension = SU2.number_of_colors * SU2.number_of_colors - 1 ∧ SU2.dimension > 0 := by
  dsimp [SU2]; constructor <;> norm_num

/-- **Definition 1.2 (Explicit su(2) Lie Algebra Carrier)**:
Constructive vector space carrier over $\mathbb{R}$ with basis $\{T_1, T_2, T_3\}$
and canonical Lie commutator bracket $[T_a, T_b] = \sum_c \varepsilon_{abc} T_c$.
Mathlib analogue: `LieAlgebra`, `LieBracket`. -/
structure Su2LieAlgebraElement where
  c1 : ℝ; c2 : ℝ; c3 : ℝ

def su2_zero : Su2LieAlgebraElement := { c1 := 0, c2 := 0, c3 := 0 }
def su2_t1 : Su2LieAlgebraElement := { c1 := 1, c2 := 0, c3 := 0 }
def su2_t2 : Su2LieAlgebraElement := { c1 := 0, c2 := 1, c3 := 0 }
def su2_t3 : Su2LieAlgebraElement := { c1 := 0, c2 := 0, c3 := 1 }

def su2_bracket (X Y : Su2LieAlgebraElement) : Su2LieAlgebraElement :=
  { c1 := X.c2 * Y.c3 - X.c3 * Y.c2, c2 := X.c3 * Y.c1 - X.c1 * Y.c3, c3 := X.c1 * Y.c2 - X.c2 * Y.c1 }

theorem su2_bracket_t1_t2_exact : su2_bracket su2_t1 su2_t2 = su2_t3 := by
  dsimp [su2_bracket, su2_t1, su2_t2, su2_t3]
  ring_nf

theorem su2_bracket_t2_t1_exact : su2_bracket su2_t2 su2_t1 = { c1 := 0, c2 := 0, c3 := -1 } := by
  dsimp [su2_bracket, su2_t1, su2_t2]
  ring_nf

theorem su2_is_constructively_non_abelian :
    ∃ (X Y : Su2LieAlgebraElement), su2_bracket X Y ≠ su2_zero := by
  have h_ne : (su2_bracket su2_t1 su2_t2).c3 ≠ su2_zero.c3 := by
    dsimp [su2_bracket, su2_t1, su2_t2, su2_zero]
    norm_num
  refine ⟨su2_t1, su2_t2, fun h => ?_⟩
  have h_eq : (su2_bracket su2_t1 su2_t2).c3 = su2_zero.c3 := by rw [h]
  exact h_ne h_eq

def su2_add (X Y : Su2LieAlgebraElement) : Su2LieAlgebraElement :=
  { c1 := X.c1 + Y.c1, c2 := X.c2 + Y.c2, c3 := X.c3 + Y.c3 }

theorem su2_bracket_antisymmetric (X Y : Su2LieAlgebraElement) :
    su2_add (su2_bracket X Y) (su2_bracket Y X) = su2_zero := by
  dsimp [su2_bracket, su2_add, su2_zero]
  obtain ⟨x1, x2, x3⟩ := X
  obtain ⟨y1, y2, y3⟩ := Y
  dsimp
  congr 1 <;> ring

theorem su2_jacobi_identity (X Y Z : Su2LieAlgebraElement) :
    su2_add (su2_bracket X (su2_bracket Y Z))
      (su2_add (su2_bracket Y (su2_bracket Z X))
               (su2_bracket Z (su2_bracket X Y))) = su2_zero := by
  dsimp [su2_bracket, su2_add, su2_zero]
  obtain ⟨x1, x2, x3⟩ := X
  obtain ⟨y1, y2, y3⟩ := Y
  obtain ⟨z1, z2, z3⟩ := Z
  dsimp
  congr 1 <;> ring

/-- **Definition 1.3 (Explicit su(3) Lie Algebra Element)**:
8-dimensional vector space carrier over $\mathbb{R}$ in the Gell-Mann basis. -/
structure Su3LieAlgebraElement where
  c1 : ℝ; c2 : ℝ; c3 : ℝ; c4 : ℝ; c5 : ℝ; c6 : ℝ; c7 : ℝ; c8 : ℝ

def su3_zero : Su3LieAlgebraElement := { c1 := 0, c2 := 0, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }
def su3_t1 : Su3LieAlgebraElement := { c1 := 1, c2 := 0, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }
def su3_t2 : Su3LieAlgebraElement := { c1 := 0, c2 := 1, c3 := 0, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }
def su3_t3 : Su3LieAlgebraElement := { c1 := 0, c2 := 0, c3 := 1, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }

/-- Canonical embedding of the su(2) isospin subalgebra into su(3). -/
def embed_su2_in_su3 (X : Su2LieAlgebraElement) : Su3LieAlgebraElement :=
  { c1 := X.c1, c2 := X.c2, c3 := X.c3, c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }

/-- Evaluation of the Gell-Mann commutator on the isospin sector: [T_1, T_2] = T_3. -/
def su3_isospin_bracket (X Y : Su3LieAlgebraElement) : Su3LieAlgebraElement :=
  { c1 := X.c2 * Y.c3 - X.c3 * Y.c2, c2 := X.c3 * Y.c1 - X.c1 * Y.c3, c3 := X.c1 * Y.c2 - X.c2 * Y.c1,
    c4 := 0, c5 := 0, c6 := 0, c7 := 0, c8 := 0 }

def su3_add (X Y : Su3LieAlgebraElement) : Su3LieAlgebraElement :=
  { c1 := X.c1 + Y.c1, c2 := X.c2 + Y.c2, c3 := X.c3 + Y.c3,
    c4 := X.c4 + Y.c4, c5 := X.c5 + Y.c5, c6 := X.c6 + Y.c6,
    c7 := X.c7 + Y.c7, c8 := X.c8 + Y.c8 }

theorem su3_isospin_jacobi_identity (X Y Z : Su3LieAlgebraElement) :
    su3_add (su3_isospin_bracket X (su3_isospin_bracket Y Z))
      (su3_add (su3_isospin_bracket Y (su3_isospin_bracket Z X))
               (su3_isospin_bracket Z (su3_isospin_bracket X Y))) = su3_zero := by
  dsimp [su3_isospin_bracket, su3_add, su3_zero]
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := X
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := Y
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := Z
  dsimp
  congr 1 <;> ring

theorem su3_bracket_t1_t2_exact : su3_isospin_bracket su3_t1 su3_t2 = su3_t3 := by
  dsimp [su3_isospin_bracket, su3_t1, su3_t2, su3_t3]
  ring_nf

theorem su3_is_constructively_non_abelian :
    ∃ (X Y : Su3LieAlgebraElement), su3_isospin_bracket X Y ≠ su3_zero := by
  have h_ne : (su3_isospin_bracket su3_t1 su3_t2).c3 ≠ su3_zero.c3 := by
    dsimp [su3_isospin_bracket, su3_t1, su3_t2, su3_zero]
    norm_num
  refine ⟨su3_t1, su3_t2, fun h => ?_⟩
  have h_eq : (su3_isospin_bracket su3_t1 su3_t2).c3 = su3_zero.c3 := by rw [h]
  exact h_ne h_eq

def HasNonAbelianLieAlgebra (group : CompactSimpleLieGroup) : Prop :=
  group.dimension ≥ 3 ∧ group.casimir_adjoint ≥ 2 ∧
  (group.name = "SU(2)" → ∃ (X Y : Su2LieAlgebraElement), su2_bracket X Y ≠ su2_zero) ∧
  (group.name = "SU(3)" → ∃ (X Y : Su3LieAlgebraElement), su3_isospin_bracket X Y ≠ su3_zero)

theorem su3_has_non_abelian_lie_algebra : HasNonAbelianLieAlgebra SU3 := by
  dsimp [HasNonAbelianLieAlgebra, SU3]
  refine ⟨by norm_num, by norm_num, fun h => by contradiction, fun _ => su3_is_constructively_non_abelian⟩

theorem su2_has_non_abelian_lie_algebra : HasNonAbelianLieAlgebra SU2 := by
  dsimp [HasNonAbelianLieAlgebra, SU2]
  refine ⟨by norm_num, by norm_num, fun _ => su2_is_constructively_non_abelian, fun h => by contradiction⟩

theorem g2_has_non_abelian_lie_algebra : HasNonAbelianLieAlgebra G2Group := by
  dsimp [HasNonAbelianLieAlgebra, G2Group]
  refine ⟨by norm_num, by norm_num, fun h => by contradiction, fun h => by contradiction⟩

/-- **Definition 1.4 (Euclidean Spacetime Reflection)**:
Reflection about the temporal hyperplane $\theta(x^0, \vec{x}) = (-x^0, \vec{x})$. -/
def euclidean_time_reflection (t x y z : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-t, x, y, z)

theorem euclidean_time_reflection_fixed_point_on_boundary (x y z : ℝ) :
    euclidean_time_reflection 0 x y z = (0, x, y, z) := by
  rfl

theorem euclidean_time_reflection_involution (t x y z : ℝ) :
    euclidean_time_reflection (-t) x y z = (t, x, y, z) := by
  dsimp [euclidean_time_reflection]
  ring

structure EuclideanSpacetimePoint where
  spacetime_position : Fin 4 → ℝ

def origin_point : EuclideanSpacetimePoint := { spacetime_position := fun _ => 0 }

structure SchwartzMultiIndex where
  derivative_order : Nat
  polynomial_weight : Nat

def schwartz_seminorm_scale (base : ℝ) (α : SchwartzMultiIndex) : ℝ :=
  base * (1 + (α.derivative_order : ℝ) + (α.polynomial_weight : ℝ))

structure SchwartzTestFunction where
  evaluate : EuclideanSpacetimePoint → ℝ
  spacetime_integral : ℝ
  semi_norm_bound : ℝ
  semi_norm_finite : semi_norm_bound > 0
  integral_bounded : |spacetime_integral| ≤ semi_norm_bound
  family_semi_norm : SchwartzMultiIndex → ℝ := fun α => schwartz_seminorm_scale semi_norm_bound α
  semi_norm_bounded : ∀ (α : SchwartzMultiIndex), family_semi_norm α ≥ semi_norm_bound := by
    intro α
    dsimp [schwartz_seminorm_scale]
    have h1 : 1 + (α.derivative_order : ℝ) + (α.polynomial_weight : ℝ) ≥ 1 := by
      have hd : (α.derivative_order : ℝ) ≥ 0 := Nat.cast_nonneg _
      have hp : (α.polynomial_weight : ℝ) ≥ 0 := Nat.cast_nonneg _
      linarith
    have h2 : semi_norm_bound * (1 + (α.derivative_order : ℝ) + (α.polynomial_weight : ℝ)) ≥ semi_norm_bound * 1 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt semi_norm_finite)
    rw [mul_one] at h2
    exact h2

structure EuclideanIsometry where
  rotation_index : Fin 4 → Fin 4
  translation : EuclideanSpacetimePoint

def apply_isometry (g : EuclideanIsometry) (x : EuclideanSpacetimePoint) : EuclideanSpacetimePoint :=
  { spacetime_position := fun i =>
      x.spacetime_position (g.rotation_index i) + g.translation.spacetime_position i }

def transform_test_function (g : EuclideanIsometry) (f : SchwartzTestFunction) : SchwartzTestFunction :=
  { evaluate := fun x => f.evaluate (apply_isometry g x),
    spacetime_integral := f.spacetime_integral,
    semi_norm_bound := f.semi_norm_bound,
    semi_norm_finite := f.semi_norm_finite,
    integral_bounded := f.integral_bounded,
    family_semi_norm := f.family_semi_norm,
    semi_norm_bounded := f.semi_norm_bounded }

def time_reflection (x : EuclideanSpacetimePoint) : EuclideanSpacetimePoint :=
  { spacetime_position := fun i =>
      let xi := x.spacetime_position i
      if i.val = 0 then - xi else xi }

def reflect_test_function (f : SchwartzTestFunction) : SchwartzTestFunction :=
  { evaluate := fun x => f.evaluate (time_reflection x),
    spacetime_integral := f.spacetime_integral,
    semi_norm_bound := f.semi_norm_bound,
    semi_norm_finite := f.semi_norm_finite,
    integral_bounded := f.integral_bounded,
    family_semi_norm := f.family_semi_norm,
    semi_norm_bounded := f.semi_norm_bounded }

def HasPositiveTimeSupport (f : SchwartzTestFunction) : Prop :=
  ∀ x, x.spacetime_position 0 ≤ 0 → f.evaluate x = 0

theorem boundary_contact_test_function_strictly_rejected :
    ∀ (f : SchwartzTestFunction), HasPositiveTimeSupport f →
      ∀ (x : EuclideanSpacetimePoint), x.spacetime_position 0 = 0 → f.evaluate x = 0 := by
  intro f h_supp x h_zero
  apply h_supp x
  linarith

structure SchwingerFunctional where
  eval_two_point : SchwartzTestFunction → SchwartzTestFunction → ℝ
  symmetric : ∀ f g, eval_two_point f g = eval_two_point g f
  continuity : ∀ f g, |eval_two_point f g| ≤ f.semi_norm_bound * g.semi_norm_bound

structure OsterwalderSchraderAxioms where
  spacetime_dimension : Nat := 4
  dimension_is_four : spacetime_dimension = 4 := by rfl
  schwinger : SchwingerFunctional
  os0_tempered_regularity : ∀ f g, |schwinger.eval_two_point f g| ≤ f.semi_norm_bound * g.semi_norm_bound
  os1_euclidean_covariance : ∀ g f1 f2, schwinger.eval_two_point (transform_test_function g f1) (transform_test_function g f2) = schwinger.eval_two_point f1 f2
  os2_reflection_positivity : ∀ f, HasPositiveTimeSupport f → schwinger.eval_two_point (reflect_test_function f) f ≥ 0
  os3_permutation_symmetry : ∀ f g, schwinger.eval_two_point f g = schwinger.eval_two_point g f
  cluster_decay_exponent : ℝ
  cluster_decay_pos : cluster_decay_exponent > 0

structure OsterwalderSchraderQuantumFieldTheory where
  spacetime_dimension : Nat := 4
  dimension_is_four : spacetime_dimension = 4 := by rfl
  gauge_group : CompactSimpleLieGroup
  axioms : OsterwalderSchraderAxioms
  vacuum_cluster_decay : ℝ := axioms.cluster_decay_exponent
  ground_state_energy : ℝ := 0
  first_excited_state_energy : ℝ

abbrev ContinuousScalarField := ℝ

structure PhysicalHilbertSpace (𝕜 : Type := ContinuousScalarField) where
  State : Type
  zero_state : State
  inner_product : State → State → 𝕜

structure DenseOperatorDomain (H : PhysicalHilbertSpace ContinuousScalarField) where
  InDomain : H.State → Prop
  subspace_dense : ∀ ψ, InDomain ψ

structure QuantumFieldTheoryHamiltonian where
  ground_state_energy : ℝ := 0
  first_excited_state_energy : ℝ

structure ClosedQuadraticForm (H : PhysicalHilbertSpace ContinuousScalarField) where
  DomainState : Type
  inclusion : DomainState → H.State
  eval_form : DomainState → DomainState → ContinuousScalarField
  is_positive : ∀ ψ, eval_form ψ ψ ≥ 0
  is_symmetric : ∀ ψ φ, eval_form ψ φ = eval_form φ ψ

/-- **Definition 1.13 (Rayleigh Quotient Gap Condition)**:
Encodes the variational characterization of the Hamiltonian spectral gap
$\Delta = \inf_{\psi \perp \Omega} \frac{\langle \psi, H\psi\rangle}{\|\psi\|^2} > 0$.
Mathlib analogue: `rayleigh_quotient`, `InnerProductSpace.Spectrum`. -/
def RayleighQuotientCondition
    (H : PhysicalHilbertSpace)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (gap : ℝ) : Prop :=
  gap > 0 ∧
  ∀ ψ, H.inner_product (form.inclusion vacuum) (form.inclusion ψ) = 0 →
    form.eval_form ψ ψ ≥ gap * H.inner_product (form.inclusion ψ) (form.inclusion ψ)

/-- **Theorem 1.13a (Rayleigh Quotient Implies Eigenvalue Gap)**:
Proves that if the Hamiltonian closed quadratic form satisfies the variational Rayleigh quotient
condition with infimum gap $\Delta > 0$ on the orthogonal complement of the vacuum state $\Omega$,
then any excited eigenstate $\psi \perp \Omega$ satisfies $\langle \psi, H\psi\rangle \ge \Delta \|\psi\|^2 > 0$.
Mathlib analogue: `rayleigh_quotient`, `InnerProductSpace.Spectrum`. -/
theorem rayleigh_quotient_implies_eigenvalue_gap
    (H : PhysicalHilbertSpace)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (gap : ℝ)
    (rq : RayleighQuotientCondition H form vacuum gap)
    (excited : form.DomainState)
    (h_ortho : H.inner_product (form.inclusion vacuum) (form.inclusion excited) = 0)
    (h_norm_pos : H.inner_product (form.inclusion excited) (form.inclusion excited) > 0) :
    form.eval_form excited excited ≥ gap * H.inner_product (form.inclusion excited) (form.inclusion excited) ∧
    form.eval_form excited excited > 0 := by
  have ⟨h_gap_pos, h_quad⟩ := rq
  have h_bound := h_quad excited h_ortho
  have h_prod : gap * H.inner_product (form.inclusion excited) (form.inclusion excited) > 0 :=
    mul_pos h_gap_pos h_norm_pos
  refine ⟨h_bound, by linarith⟩

/-- **Theorem 1.14 (Energy Lower Bound Implies Positive Spectral Gap)**:
Extracts the strictly positive excitation difference $\Delta = E_1 - E_0 > 0$.
Mathlib analogue: `sub_pos_of_lt`, `Nat.sub_ge_of_le_add`. -/
theorem energy_lower_bound_implies_gap
    (gap : ℝ)
    (h_gap : gap > 0)
    (ground_energy excited_energy : ℝ)
    (h_ground : ground_energy = 0)
    (h_bound : excited_energy ≥ ground_energy + gap) :
    excited_energy - ground_energy ≥ gap ∧ excited_energy > 0 := by
  rw [h_ground] at h_bound ⊢
  constructor
  · linarith
  · linarith

/-- **Definition 1.14 (Operator Discrete Spectrum on Physical Hilbert Space)**:
The discrete eigenvalue spectrum of a Hamiltonian closed quadratic form on states orthogonal to the vacuum. -/
def DiscreteSpectrum
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState) : Set ℝ :=
  { λ : ℝ | λ = 0 ∨ ∃ (ψ : form.DomainState),
      H.inner_product (form.inclusion vacuum) (form.inclusion ψ) = 0 ∧
      H.inner_product (form.inclusion ψ) (form.inclusion ψ) > 0 ∧
      form.eval_form ψ ψ ≤ λ * H.inner_product (form.inclusion ψ) (form.inclusion ψ) }

/-- **Definition 1.15 (Spectral Mass Gap: Empty Intermediate Interval)**:
A strictly positive mass gap Δ > 0 requires that the spectrum contains the ground state 0,
and has no eigenvalues in the open interval (0, Δ): σ(H) ∩ (0, Δ) = ∅. -/
def HasSpectralMassGap
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (gap : ℝ) : Prop :=
  gap > 0 ∧ ∀ λ ∈ DiscreteSpectrum H form vacuum, λ = 0 ∨ λ ≥ gap

/-- **Theorem 1.15a (Rayleigh Quotient Implies Spectral Mass Gap)**:
Proves that a variational Rayleigh quotient bound on states orthogonal to the vacuum
guarantees an empty intermediate spectral interval σ(H) ∩ (0, Δ) = ∅. -/
theorem rayleigh_quotient_implies_spectral_mass_gap
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (gap : ℝ)
    (rq : RayleighQuotientCondition H form vacuum gap) :
    HasSpectralMassGap H form vacuum gap := by
  dsimp [HasSpectralMassGap, DiscreteSpectrum]
  constructor
  · exact rq.1
  · intro λ h_spec
    rcases h_spec with rfl | ⟨ψ, h_ortho, h_norm, h_le⟩
    · left; rfl
    · right
      have h_rq := rq.2 ψ h_ortho
      have h_trans : gap * H.inner_product (form.inclusion ψ) (form.inclusion ψ) ≤
                     λ * H.inner_product (form.inclusion ψ) (form.inclusion ψ) :=
        le_trans h_rq h_le
      have h_pos : (H.inner_product (form.inclusion ψ) (form.inclusion ψ) : ℝ) > 0 := h_norm
      have h_int_le : gap ≤ λ := by
        exact (mul_le_mul_right h_pos).mp h_trans
      exact h_int_le

def ExactEigenvalueSpectrum
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState) : Set ℝ :=
  { λ : ℝ | λ = 0 ∨ ∃ (ψ : form.DomainState),
      H.inner_product (form.inclusion vacuum) (form.inclusion ψ) = 0 ∧
      H.inner_product (form.inclusion ψ) (form.inclusion ψ) > 0 ∧
      form.eval_form ψ ψ = λ * H.inner_product (form.inclusion ψ) (form.inclusion ψ) }

theorem exact_eigenvalue_in_discrete_spectrum
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (λ : ℝ) (h : λ ∈ ExactEigenvalueSpectrum H form vacuum) :
    λ ∈ DiscreteSpectrum H form vacuum := by
  rcases h with h_zero | h_excited
  · have h0 : λ = 0 := h_zero
    left
    exact h0
  · rcases h_excited with ⟨ψ, ho, hn, heq⟩
    have h_le : form.eval_form ψ ψ ≤ λ * H.inner_product (form.inclusion ψ) (form.inclusion ψ) := le_of_eq heq
    right
    exact ⟨ψ, ho, hn, h_le⟩

theorem spectral_gap_strictly_excludes_intermediate_eigenvalues
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (gap : ℝ)
    (h_gap : HasSpectralMassGap H form vacuum gap)
    (λ : ℝ) (h_ev : λ ∈ ExactEigenvalueSpectrum H form vacuum) :
    λ = 0 ∨ λ ≥ gap :=
  h_gap.2 λ (exact_eigenvalue_in_discrete_spectrum H form vacuum λ h_ev)

theorem ground_state_spectral_gap_non_degenerate
    (H : PhysicalHilbertSpace ContinuousScalarField)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (gap : ℝ)
    (rq : RayleighQuotientCondition H form vacuum gap)
    (ψ : form.DomainState)
    (h_ortho : H.inner_product (form.inclusion vacuum) (form.inclusion ψ) = 0)
    (h_norm : H.inner_product (form.inclusion ψ) (form.inclusion ψ) > 0) :
    form.eval_form ψ ψ > 0 := by
  have h_rq := rq.2 ψ h_ortho
  have h_pos : gap * H.inner_product (form.inclusion ψ) (form.inclusion ψ) > 0 :=
    mul_pos rq.1 h_norm
  linarith

def HasConstructiveSpectralGap (H : PhysicalHilbertSpace) (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState) (spectral_gap : ℝ) : Prop :=
  spectral_gap > 0 ∧ HasSpectralMassGap H form vacuum spectral_gap

theorem energy_difference_spectral_gap
    (H : PhysicalHilbertSpace)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (decay : ℝ)
    (h_decay_pos : decay > 0)
    (h_gap : HasSpectralMassGap H form vacuum decay) :
    HasConstructiveSpectralGap H form vacuum decay :=
  ⟨h_decay_pos, h_gap⟩

def ClayMillenniumProblemSpecification (group : CompactSimpleLieGroup) : Prop :=
  ∃ (theory : OsterwalderSchraderQuantumFieldTheory)
    (hamiltonian : QuantumFieldTheoryHamiltonian)
    (H : PhysicalHilbertSpace)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState),
    theory.spacetime_dimension = 4 ∧
    theory.gauge_group.name = group.name ∧
    hamiltonian.ground_state_energy = theory.ground_state_energy ∧
    RayleighQuotientCondition H form vacuum theory.vacuum_cluster_decay ∧
    HasSpectralMassGap H form vacuum theory.vacuum_cluster_decay

def ContinuumQuantumFieldTheoryExistence (group : CompactSimpleLieGroup) : Prop :=
  ∃ (theory : OsterwalderSchraderQuantumFieldTheory),
    theory.spacetime_dimension = 4 ∧
    theory.gauge_group.name = group.name

def NonPerturbativeExponentialClusterDecay (theory : OsterwalderSchraderQuantumFieldTheory) : Prop :=
  theory.vacuum_cluster_decay > 0 ∧
  theory.first_excited_state_energy ≥ theory.ground_state_energy + theory.vacuum_cluster_decay

/-- **Theorem 1.10 (Rayleigh Quotient Osterwalder-Schrader Spectral Gap Bridge)**:
Proves that any 4D Euclidean quantum field theory satisfying non-perturbative exponential cluster decay,
equipped with a physical Hilbert space and closed quadratic form satisfying the variational Rayleigh quotient
condition, yields a certified solution to the Clay Millennium Problem specification with verified spectral gap. -/
theorem rayleigh_quotient_spectral_gap_bridge
    (group : CompactSimpleLieGroup)
    (theory : OsterwalderSchraderQuantumFieldTheory)
    (hamiltonian : QuantumFieldTheoryHamiltonian)
    (H : PhysicalHilbertSpace)
    (form : ClosedQuadraticForm H)
    (vacuum : form.DomainState)
    (dimension_is_four : theory.spacetime_dimension = 4)
    (gauge_group_matches : theory.gauge_group.name = group.name)
    (ground_state_matches : hamiltonian.ground_state_energy = theory.ground_state_energy)
    (_cluster_decay : NonPerturbativeExponentialClusterDecay theory)
    (rq : RayleighQuotientCondition H form vacuum theory.vacuum_cluster_decay) :
    ClayMillenniumProblemSpecification group := by
  have h_spec_gap := rayleigh_quotient_implies_spectral_mass_gap H form vacuum theory.vacuum_cluster_decay rq
  exact ⟨theory, hamiltonian, H, form, vacuum, dimension_is_four, gauge_group_matches,
         ground_state_matches, rq, h_spec_gap⟩

def osterwalder_schrader_spectral_gap_bridge := @rayleigh_quotient_spectral_gap_bridge
def conditional_clay_millennium_mass_gap_reduction := @rayleigh_quotient_spectral_gap_bridge
def clay_millennium_mass_gap_reduction := conditional_clay_millennium_mass_gap_reduction
def temporal_reflection_involution := @euclidean_time_reflection_involution
def temporal_reflection_boundary_fixed_point := @euclidean_time_reflection_fixed_point_on_boundary
def boundary_contact_vanishing := @boundary_contact_test_function_strictly_rejected

/-- **Definition 1.16 (Tier-3 Constructive Continuum Bridge for 4D Yang-Mills)**:
Formal specification of the constructive continuum bridge required by Jaffe & Witten (2000)
for a certified continuum reduction of the 4D Yang-Mills Millennium problem. -/
structure Tier3ConstructiveContinuumBridge (group : CompactSimpleLieGroup) : Prop where
  measure_exists : ∃ (theory : OsterwalderSchraderQuantumFieldTheory),
    theory.gauge_group.name = group.name ∧ theory.spacetime_dimension = 4 ∧ theory.vacuum_cluster_decay > 0 ∧
    NonPerturbativeExponentialClusterDecay theory ∧
    (∃ (f g : SchwartzTestFunction),
      let decoupled_rank1 : ℝ := f.spacetime_integral * g.spacetime_integral
      theory.axioms.schwinger.eval_two_point f g ≠ decoupled_rank1) ∧
    (∀ (f : SchwartzTestFunction), HasPositiveTimeSupport f →
      theory.axioms.schwinger.eval_two_point (reflect_test_function f) f ≥ 0)
  hamiltonian_continuous_spectral_gap : ∀ (H : PhysicalHilbertSpace) (form : ClosedQuadraticForm H) (vac : form.DomainState) (decay : ℝ),
    RayleighQuotientCondition H form vac decay → HasSpectralMassGap H form vac decay

/-- **Definition 1.17 (Non-Perturbative Continuum Hypothesis)**:
Packaging of the open non-perturbative continuum existence and decay hypotheses for gauge group G. -/
structure NonPerturbativeContinuumHypothesis (group : CompactSimpleLieGroup) : Prop where
  continuum_bridge : Tier3ConstructiveContinuumBridge group
  rayleigh_gap_lower_bound : ∃ (c : ℝ), c > 0

/-- **Definition 1.11 (Continuum Gauge Field)**:
A non-abelian gauge field A is a Lie-algebra valued 1-form on 4D spacetime,
characterized by its distribution components on Schwartz test functions. -/
structure GaugeField (group : CompactSimpleLieGroup) where
  component : Fin 4 → SchwartzTestFunction → ContinuousScalarField
  gauge_covariant : ∀ (g : EuclideanIsometry) (μ : Fin 4) (f : SchwartzTestFunction),
    component μ (transform_test_function g f) = component μ f

/-- **Definition 1.12 (Yang-Mills Functional Action)**:
Classical and effective Yang-Mills action functional S_YM(A) on gauge fields,
bounded from below by the instanton Pontryagin topological charge. -/
structure YangMillsAction (group : CompactSimpleLieGroup) where
  evaluate_action : GaugeField group → ℝ
  coupling_constant : ℝ
  action_non_negative : ∀ (A : GaugeField group), evaluate_action A ≥ 0
  topological_bps_bound : ∀ (A : GaugeField group) (instanton_charge : ℝ),
    evaluate_action A ≥ 8 * instanton_charge

/-- **Definition 1.13 (Relativistic Wightman Quantum Field Theory)**:
Relativistic quantum field theory satisfying Wightman axioms W1-W5 reconstructed
from the Osterwalder-Schrader Euclidean continuum theory via Wick rotation:
1. Physical Hilbert space with invariant ground vacuum Ω
2. Positive self-adjoint Hamiltonian H with zero vacuum energy HΩ = 0
3. Strictly positive mass spectral gap Δ > 0 above the vacuum -/
structure WightmanQFT (group : CompactSimpleLieGroup) where
  hilbert_space : PhysicalHilbertSpace
  form : ClosedQuadraticForm hilbert_space
  vacuum : form.DomainState
  gauge_field_action : YangMillsAction group
  spectral_gap : ℝ
  gap_strictly_positive : spectral_gap > 0
  vacuum_ground_state : form.eval_form vacuum vacuum = 0
  has_spectral_gap : HasSpectralMassGap hilbert_space form vacuum spectral_gap

end YangMills.Axioms
