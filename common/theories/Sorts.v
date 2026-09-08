From Stdlib Require Import OrdersAlt MSetList MSetAVL MSetFacts MSetProperties MSetDecide FMapAVL.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils MRMSets MRFSets.
From MetaRocq.Common Require Import BasicAst config Levels.
From Stdlib Require Import ssreflect.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

Implicit Types (cf : checker_flags).

Module Sort.
  Variant t := sProp | sSProp | sType.
  Derive NoConfusion EqDec for t.

  Inductive lt : t -> t -> Prop :=
  | ltSPropProp : lt sSProp sProp
  | ltsPropType : lt sSProp sType
  | ltPropType  : lt sProp sType.

  #[global] Instance lt_strorder : StrictOrder lt.
  Proof.
	constructor.
	- intros [] contra; inversion contra.
	- intros [] [] []; cbn; intros; try easy.
	  constructor.
  Qed.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y e z t e'. hnf in * |- ; subst. reflexivity.
  Qed.

  Definition compare (s s' : t) : comparison :=
  match s, s' with
  | sSProp, sSProp => Eq
  | sSProp, _ => Lt
  | _, sSProp => Gt
  | sProp, sProp => Eq
  | sProp, _ => Lt
  | _, sProp => Gt
  | sType, sType => Eq
  end.

  Lemma compare_spec s s' : CompareSpec (eq s s') (lt s s') (lt s' s) (compare s s').
  Proof.
    destruct s, s'; cbn; constructor; try easy; constructor.
  Qed.

  Definition eqb (s s' : t) : bool :=
    match s, s' with
	| sProp, sProp
	| sSProp, sSProp
	| sType, sType => true
	| _, _ => false
	end.

  #[global, program] Instance reflect_eq_sort : ReflectEq t :=
    { eqb := eqb }.
  Next Obligation.
    destruct x, y; cbn; constructor; easy.
  Qed.
End Sort.

Notation sProp := Sort.sProp.
Notation sSProp := Sort.sSProp.
Notation sType := Sort.sType.
