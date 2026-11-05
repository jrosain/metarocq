(* Distributed under the terms of the MIT license. *)
From Stdlib.ssr Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import LibHypsNaming.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

(** * Weakening lemmas w.r.t. the checker configuration *)

(** ** Constraints *)

#[global] Instance subrel_config_impl_cmp cf1 cf2 cs pb :
  config.impl cf1 cf2 ->
  RelationClasses.subrelation (@compare_univ cf1 cs pb) (@compare_univ cf2 cs pb).
Proof.
  cbv [compare_univ eq_univ eq_univ_ leq_univ leq_univ_n leq_univ_n_ eq_ulvl leq_ulvl_n config.impl].
  destruct cf1, cf2; cbn.
  move => H u1 u2; move: H.
  repeat match goal with
         | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
         end; cbn => //=; try reflexivity.
  all: repeat move => /andP[]; cbv [is_true]; intros; repeat (cbn in *; subst).
  all: destruct u1 as [[| |] u1], u2 as [[| |] u2]; cbn in *; auto.
  all: subst; auto.
Qed.

#[global] Instance subrel_config_impl_eq_pb cf1 cf2 cs pb :
  config.impl cf1 cf2 ->
  RelationClasses.subrelation (@eq_univ cf1 cs) (@compare_univ cf2 cs pb).
Proof.
  change (@eq_univ ?cf ?φ) with (@compare_univ cf φ Conv).
  etransitivity; [ now eapply (@subrel_config_impl_cmp cf1 cf2) | ].
  tc.
Qed.

#[global] Instance subrel_config_impl_eq cf1 cf2 u :
  config.impl cf1 cf2 ->
  RelationClasses.subrelation (@eq_univ cf1 u) (@eq_univ cf2 u).
Proof. change (@eq_univ ?cf ?φ) with (@compare_univ cf φ Conv). tc. Qed.

#[global] Instance subrel_config_impl_le cf1 cf2 u :
  config.impl cf1 cf2 ->
  RelationClasses.subrelation (@leq_univ cf1 u) (@leq_univ cf2 u).
Proof. change (@leq_univ ?cf ?φ) with (@compare_univ cf φ Cumul). tc. Qed.

#[global] Instance subrel_config_impl_eq_le cf1 cf2 u :
  config.impl cf1 cf2 ->
  RelationClasses.subrelation (@eq_univ cf1 u) (@leq_univ cf2 u).
Proof. change (@leq_univ ?cf ?φ) with (@compare_univ cf φ Cumul). tc. Qed.

Lemma weakening_config_is_allowed_elimination cf1 cf2 cs u allowed :
  config.impl cf1 cf2 ->
  @is_allowed_elimination cf1 cs allowed u ->
  @is_allowed_elimination cf2 cs allowed u.
Proof.
  destruct allowed; cbnr; trivial; cbv [is_lSet].
  move => ? [?|H]; [ left | right ] => //; move: H.
  now apply subrel_config_impl_eq.
Qed.
(*#[global] Hint Resolve weakening_config_is_allowed_elimination : extends.*)

Lemma weakening_config_consistent_instance cf1 cf2 Σ ctrs u :
  config.impl cf1 cf2 ->
  @consistent_instance_ext cf1 Σ ctrs u ->
  @consistent_instance_ext cf2 Σ ctrs u.
Proof.
  rewrite /consistent_instance_ext/consistent_instance/valid_constraints/config.impl.
  do 2 case: check_univs; cbn => //=.
  case: ctrs => //=; intuition auto.
Qed.
(*#[global] Hint Resolve weakening_config_consistent_instance : extends.*)
