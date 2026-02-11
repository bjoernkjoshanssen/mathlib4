/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Reflection
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic --  Orientation.oangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine --  EuclideanGeometry.oangle

/-!
# Action of the general linear group on projectivization

Show that the general linear group of `V` acts on `ℙ K V`.
-/

open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

namespace Projectivization

section DivisionRing

variable {K V : Type*} [AddCommGroup V] [DivisionRing K] [Module K V]

/-- The general linear group of `V` acts on `ℙ V`. -/
instance instGLAction : MulAction (LinearMap.GeneralLinearGroup K V) (ℙ K V) where
  smul g x := x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective
  one_smul := congr_fun Projectivization.map_id
  mul_smul g g' x := congr_fun (Projectivization.map_comp
    g'.toLinearEquiv.toLinearMap _ g.toLinearEquiv.toLinearMap _ _) x

lemma smul_apply
    (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl

lemma smul_mk (g : LinearMap.GeneralLinearGroup K V) {v : V} (hv : v ≠ 0) :
    g • Projectivization.mk K v hv =
      Projectivization.mk K (g • v) ((smul_ne_zero_iff_ne _).mpr hv) := by
  rfl

end DivisionRing

section Field

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- For a field `K`, the group `GL n K` acts on `ℙ K (n → K)`. -/
instance instGLFinAction : MulAction (GL n K) (ℙ K (n → K)) :=
  .compHom _ Matrix.GeneralLinearGroup.toLin.toMonoidHom

@[simp]
lemma pi_smul_apply (g : GL n K) {v : n → K} (hv : v ≠ 0) :
    g • mk K v hv = mk K (g.val *ᵥ v) (g.toLin.toLinearEquiv.map_ne_zero_iff.mpr hv) := by
  rfl

/-- For a field `K`, the group `GL (Fin 2) K` acts on `ℙ K (K × K)`. -/
instance instGLFinTwoAction : MulAction (GL (Fin 2) K) (ℙ K (K × K)) :=
  .compHom _ (Matrix.GeneralLinearGroup.toLin.trans
    <| LinearMap.GeneralLinearGroup.compLinearEquiv <| LinearEquiv.finTwoArrow K K).toMonoidHom

end Field

end Projectivization


example (m₀ m₁ : GL (Fin 2) ℝ) (v : ℙ ℝ (Fin 2 → ℝ)): (m₀ • m₁) • v = m₀ • (m₁ • v) := by
  simp only [smul_eq_mul]
  exact mul_smul m₀ m₁ v

noncomputable def m : GL (Fin 2) ℝ := Matrix.nonsingInvUnit !![1,1;0,1] (by simp)
noncomputable def n : GL (Fin 2) ℝ := Matrix.nonsingInvUnit !![0,1;1,1] (by simp)

def w : ℙ ℝ (Fin 2 → ℝ) := Projectivization.mk' ℝ ⟨![0,1], by simp⟩

example : m • w ≠ w := by
  simp [m,w, Matrix.nonsingInvUnit]
  rw [ Projectivization.mk_eq_mk_iff]
  intro ⟨a,ha⟩
  simpa using congrFun ha 0

def v : ℙ ℝ (Fin 2 → ℝ) := Projectivization.mk' ℝ ⟨![1,0], by simp⟩

example : m • v = v := by
  simp [m,v, Matrix.nonsingInvUnit]
  congr
  ext i
  fin_cases i <;> simp

example : m • n • v ≠ v := by
  simp [m,n,v, Matrix.nonsingInvUnit, Matrix.vecHead, Matrix.vecTail]
  rw [Projectivization.mk_eq_mk_iff]
  intro ⟨a,ha⟩
  simpa using congrFun ha 1

def astMat {α : Type*} {R : Type*} [CommRing R]
  {n q : ℕ} (word : Fin n → α) (matrices : α → GL (Fin q) R) :
  Fin q → Fin q → R := match n with
| 0 => fun x y => ite (x=y) 1 0
| Nat.succ m => Matrix.mulᵣ (matrices (word (Fin.last m))) (astMat (Fin.init word) matrices)
-- https://leanprover-community.github.io/install/project.html
-- noncomputable def astMatProj {α : Type*} {R : Type*} [CommRing R]
--   {n q : ℕ} (word : Fin n → α) (matrices : α → GL (Fin q) R) :
--   GL (Fin q) R := match n with
-- | 0 => 1
-- | Nat.succ m => Matrix.nonsingInvUnit
--     ((matrices (word (Fin.last m))) • (astMatProj (Fin.init word) matrices)) (by
--     have := @Matrix.det_mul (Fin m.succ) _ _ R _ (matrices (word (Fin.last m)))
--     sorry
-- )



/-- The `q × 1` column vector representing a state. -/
def astCol {α R : Type*} [CommRing R] {n q : ℕ}
  (word : Fin n → α)
  (matrices : α → GL (Fin q) R)
  (init : Fin q → Fin 1 → R) : Fin q → Fin 1 → R :=
  Matrix.mulᵣ (astMat word matrices) init

/-- The `q`-tuple representing a state. -/
def astM {α R : Type*} [CommRing R] {n q : ℕ} (word : Fin n → α)
  (matrices : α → GL (Fin q) R)
  (init : Fin q → R) : Fin q → R := fun a =>
    (astCol word matrices fun x => fun _ => init x) a 0

instance {q : ℕ} [NeZero q] : AddCommGroup (Fin q) := by
     (expose_names; refine Fin.addCommGroup q)

-- def astMproj {α R : Type*} [DivisionRing R] [CommRing R] {n q : ℕ} [NeZero q] [Module R (Fin q)] (word : Fin n → α)
--   (matrices : α → GL (Fin q) R)
--   (init : ℙ R (Fin q)) : ℙ R (Fin q) := ⟦⟨fun a =>
--     (astCol word matrices init) a 0, sorry⟩⟧


def Al_at_most {α : Type*} (R : Type*) [CommRing R] {n : ℕ}
  (word : Fin n → α) (q : ℕ) : Prop :=
  ∃ matrices : α → GL (Fin q) R,
  ∃ init final : Fin q → R, ∀ v : Fin n → α,
    astM v matrices init = final ↔ v = word
