/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Simon Hudon, Alice Laroche, Frédéric Dupuis, Jireh Loreaux
-/

import Lean
import Mathlib.Lean.Expr
import Mathlib.Logic.Basic
import Mathlib.Init.Algebra.Order

namespace Mathlib.Tactic.PushNeg

open Lean Meta Elab.Tactic Parser.Tactic

variable (p q : Prop) (s : α → Prop)

theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
theorem not_and_distrib_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_distrib
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or_distrib
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext not_imp
theorem not_ne_eq (x y : α) : (¬ (x ≠ y)) = (x = y) := ne_eq x y ▸ not_not_eq _

variable {β : Type u} [LinearOrder β]
theorem not_le_eq (a b : β) : (¬ (a ≤ b)) = (b < a) := propext not_le
theorem not_lt_eq (a b : β) : (¬ (a < b)) = (b ≤ a) := propext not_lt

/-- Make `push_neg` use `not_and_distrib` rather than the default `not_and`. -/
register_option push_neg.use_distrib : Bool :=
  { defValue := false
    group := ""
    descr := "Make `push_neg` use `not_and_distrib` rather than the default `not_and`." }

/-- Push negations at the top level of the current expression. -/
def transformNegationStep (e : Expr) : SimpM (Option Simp.Step) := do
  let mkSimpStep (e : Expr) (pf : Expr) : Simp.Step :=
    Simp.Step.visit { expr := e, proof? := some pf }
  let e_whnf ← whnfR e
  let some ex := e_whnf.not? | return Simp.Step.visit { expr := e }
  match ex.getAppFnArgs with
  | (``Not, #[e]) =>
      return mkSimpStep e (← mkAppM ``not_not_eq #[e])
  | (``And, #[p, q]) =>
      match ← getBoolOption `push_neg.use_distrib with
      | false => return mkSimpStep (.forallE `_ p (mkNot q) default) (←mkAppM ``not_and_eq #[p, q])
      | true  => return mkSimpStep (mkOr (mkNot p) (mkNot q)) (←mkAppM ``not_and_distrib_eq #[p, q])
  | (``Or, #[p, q]) =>
      return mkSimpStep (mkAnd (mkNot p) (mkNot q)) (←mkAppM ``not_or_eq #[p, q])
  | (``Eq, #[_ty, e₁, e₂]) =>
      return Simp.Step.visit { expr := ← mkAppM ``Ne #[e₁, e₂] }
  | (``Ne, #[_ty, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``Eq #[e₁, e₂]) (← mkAppM ``not_ne_eq #[e₁, e₂])
  | (``LE.le, #[_ty, _inst, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``LT.lt #[e₂, e₁]) (← mkAppM ``not_le_eq #[e₁, e₂])
  | (``LT.lt, #[_ty, _inst, e₁, e₂]) =>
      return mkSimpStep (← mkAppM ``LE.le #[e₂, e₁]) (← mkAppM ``not_lt_eq #[e₁, e₂])
  | (``Exists, #[_, .lam n typ bo bi]) =>
      return mkSimpStep (.forallE n typ (mkNot bo) bi)
                        (← mkAppM ``not_exists_eq #[.lam n typ bo bi])
  | (``Exists, #[_, _]) =>
      return none
  | _ => match ex with
          | .forallE name ty body binfo => do
              if (← isProp ty) then
                return mkSimpStep (← mkAppM ``And #[ty, mkNot body]) (← mkAppM ``not_implies_eq #[ty, body])
              else
                let body' : Expr := .lam name ty (mkNot body) binfo
                let body'' : Expr := .lam name ty body binfo
                return mkSimpStep (← mkAppM ``Exists #[body']) (← mkAppM ``not_forall_eq #[body''])
          | _ => return none

/-- Recursively push negations at the top level of the current expression. This is needed
to handle e.g. triple negation. -/
partial def transformNegation (e : Expr) : SimpM Simp.Step := do
  let Simp.Step.visit r₁ ← transformNegationStep e | return Simp.Step.visit { expr := e }
  match r₁.proof? with
  | none => return Simp.Step.visit r₁
  | some _ => do
      let Simp.Step.visit r₂ ← transformNegation r₁.expr | return Simp.Step.visit r₁
      return Simp.Step.visit (← Simp.mkEqTrans r₁ r₂)

/-- Execute main loop of `push_neg` at the main goal. -/
def pushNegTarget : TacticM Unit := withMainContext do
  let myctx : Simp.Context :=
    { config := { eta := true },
      simpTheorems := #[ ]
      congrTheorems := (← getSimpCongrTheorems) }
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let (myres, _) ← Simp.main tgt myctx (methods := { pre := transformNegation })
  replaceMainGoal [← applySimpResultToTarget goal tgt myres]

/-- Execute main loop of `push_neg` at a local hypothesis. -/
def pushNegLocalDecl (fvarId : FVarId): TacticM Unit := withMainContext do
  let ldecl ← fvarId.getDecl
  if ldecl.isAuxDecl then return
  let tgt := (← fvarId.getDecl).type
  let tgt ← instantiateMVars tgt
  let myctx : Simp.Context :=
    { config := { eta := true },
      simpTheorems := #[ ]
      congrTheorems := (← getSimpCongrTheorems) }
  let goal ← getMainGoal
  let (myres, _) ← Simp.main tgt myctx (methods := { pre := transformNegation })
  let some ⟨_, newGoal⟩ ← applySimpResultToLocalDecl goal fvarId myres False | throwError "fail"
  replaceMainGoal [newGoal]

/--
Push negations into the conclusion of a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.
This tactic pushes negations inside expressions. For instance, given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(The pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).

Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢` as usual.

This tactic has two modes: in standard mode, it transforms `¬(p ∧ q)` into `p → ¬q`, whereas in
distrib mode it produces `¬p ∨ ¬q`. To use distrib mode, use `set_option push_neg.use_distrib true`.
-/
elab "push_neg " loc:(ppSpace location)? : tactic =>
  match loc with
  | none => pushNegTarget
  | some loc =>
      let loc := expandLocation loc
      withLocation loc
        pushNegLocalDecl
        pushNegTarget
        (fun _ => logInfo "push_neg couldn't find a negation to push")
