(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool Utf8 CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Warnings "-notation-overridden".
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICCasesContexts
     PCUICSigmaCalculus PCUICClosed PCUICContexts PCUICSubstitution
     PCUICWeakeningEnv PCUICWeakening 
     PCUICUnivSubst PCUICGlobalEnv PCUICTyping PCUICGeneration
     PCUICConversion PCUICOnFreeVars PCUICInductives
     PCUICValidity PCUICArities PCUICInversion PCUICInductiveInversion
     PCUICCases PCUICWellScopedCumulativity PCUICSpine PCUICSR
     PCUICSafeLemmata PCUICInductives PCUICInductiveInversion.
From MetaCoq.PCUIC Require Import PCUICEquality PCUICExpandLets.
Set Warnings "+notation_overridden".

Import MCMonadNotation.

Implicit Types cf : checker_flags. (* Use {cf} to parameterize by checker_flags where needed *)

(** Translation from PCUIC back to template-coq terms. 

  This translation is not direct due to two peculiarities of template-coq's syntax:
  - applications are n-ary and not all terms are well-formed, so we have to 
    use an induction on the size of derivations to transform the binary applications
    into n-ary ones.
  - The representation of cases in template-coq is "compact" in the sense that 
    the predicate and branches contexts do not appear in the syntax of terms but can 
    be canonically rebuilt on-demand, as long as the environment has a declaration for the 
    inductive type. In contrast, PCUIC has these contexts explicitely present in terms, 
    so that the theory of reduction (confluence) and conversion do not need to rely on any 
    such well-formedness arguments about the global environment, considerably simplifying the theory:
    For example one couldn't do recursive calls on such "rebuilt" contexts using simple structural
    recursion, the new contexts having no structural relation to the terms at hand.

    This means that Template-Coq's `red1` reduction of cases requires well-formedness conditions
    not readily available in PCUIC's. We solve this conundrum using subject reduction: indeed
    cumulativity is always called starting with two well-sorted types, and we can hence show
    that every one-step reduction in a PCUIC cumulativity derivation goes from a well-typed term
    to a well-typed term. We can hence prove that Template-Coq's `red1` reductions follow from the
    untyped PCUIC reduction when restricted to well-typed terms (which have many more invariants).
    We actually just need the term to be reduced to be well-typed to show that the interpretation 
    preserves one-step reduction in [trans_red1}].
*)

(** Source = PCUIC, Target = Coq *)
Module S := PCUICAst.
Module SE := PCUICEnvironment.
Module ST := PCUICTyping.
Module T := S.
Module TT := ST.

Module SL := PCUICLiftSubst.
Module TL := SL.


Ltac solve_list :=
  rewrite !map_map_compose ?compose_on_snd ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma mapOne {X Y} (f:X->Y) x:
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma trans_local_app Γ Δ : trans_local (SE.app_context Γ Δ) = trans_local Γ ,,, trans_local Δ.
Proof.
  now rewrite /trans_local map_app.
Qed.

Lemma forget_types_map_context {term term'} (f : term' -> term) ctx : 
  forget_types (map_context f ctx) = forget_types ctx.
Proof.
  now rewrite /forget_types map_map_context.
Qed.

Lemma All_fold_map_context (P : context -> context_decl -> Type) (f : term -> term) ctx :
  All_fold P (map_context f ctx) <~> All_fold (fun Γ d => P (map_context f Γ) (map_decl f d)) ctx.
Proof.
  induction ctx.
  - split; constructor.
  - cbn. split; intros H; depelim H; constructor; auto; now apply IHctx.
Qed.

Lemma on_decl_trans_on_free_vars_decl (Γ : context) n (d : context_decl) :
  ondecl
    (λ t : term,
     on_free_vars (closedP (#|Γ| + n) xpredT) (trans t)) d ->
  on_free_vars_decl
    (shiftnP #|map_context trans Γ| (closedP n xpredT)) (trans_decl d).
Proof.
  intros []. unfold on_free_vars_decl, test_decl.
  destruct d as [na [b|] ty]; cbn in * => //;
     rewrite map_context_length shiftnP_closedP shiftnP_xpredT //.
  apply/andP. split; auto.
Qed.

Lemma All_fold_closed_on_free_vars_ctx n ctx : 
  All_fold (λ Γ : context, ondecl (λ t : term,
        on_free_vars (closedP (#|Γ| + n) xpredT)
      (trans t))) ctx ->
  on_free_vars_ctx (closedP n xpredT) (map_context trans ctx).
Proof.
  intros af.
  eapply on_free_vars_ctx_All_fold.
  eapply All_fold_map_context, All_fold_impl; tea => ctx' d; cbn.
  now intros; eapply on_decl_trans_on_free_vars_decl.
Qed.

Definition plengths := 
    (@context_assumptions_subst_context,
    @context_assumptions_app,
    @context_assumptions_subst_instance, @context_assumptions_lift_context,
     @expand_lets_ctx_length, @subst_context_length,
    @subst_instance_length, @expand_lets_k_ctx_length, @inds_length, @lift_context_length,
    @app_length, @List.rev_length, @extended_subst_length, @reln_length,
    Nat.add_0_r, @app_nil_r, 
    @map_length, @mapi_length, @mapi_rec_length,
    @fold_context_k_length, @cofix_subst_length, @fix_subst_length,
    @smash_context_length, @arities_context_length).
  

Lemma trans_on_free_vars P t : 
  on_free_vars P t -> on_free_vars P (trans t).
Proof.
  revert P t. eapply term_on_free_vars_ind; cbn; auto; 
    lazymatch goal with |- context [case_info] => idtac | _ => solve_all end.
  - intros; rtoProp; intuition auto.
    * solve_all.
    * now rewrite map_context_length.
    * rewrite map_length.
      rewrite test_context_k_closed_on_free_vars_ctx.
      now eapply All_fold_closed_on_free_vars_ctx. 
    * solve_all.
      rewrite test_context_k_closed_on_free_vars_ctx.
      rewrite on_free_vars_ctx_smash //.
      destruct X as [_ IH _ _].
      now eapply All_fold_closed_on_free_vars_ctx.
      rewrite smash_context_length /=.
      eapply on_free_vars_expand_lets_k. now len.
      destruct X as [hctx ihctx _ _].
      eapply on_free_vars_ctx_subst_context0.
      rewrite !plengths.
      eapply All_fold_closed_on_free_vars_ctx in ihctx.
      rewrite -> closedP_shiftnP in ihctx.
      rewrite /id. rewrite on_free_vars_ctx_subst_instance.
      eapply on_free_vars_ctx_impl; tea.
      { unfold shiftnP. intros i. rewrite orb_false_r.
        move/Nat.ltb_lt => hlt. now apply/orP; left; eapply Nat.ltb_lt. }
      solve_all.
      rewrite !plengths. now apply X.
  - unfold test_def. solve_all. cbn. now len in b1.
  - unfold test_def. solve_all. cbn. now len in b1.
Qed.

Lemma on_free_vars_ctx_trans k ctx : 
  on_free_vars_ctx (closedP k xpredT) ctx ->
  on_free_vars_ctx (closedP k xpredT) (map_context trans ctx).
Proof.
  intros H; apply on_free_vars_ctx_All_fold in H. 
  eapply All_fold_closed_on_free_vars_ctx.
  eapply All_fold_impl; tea; cbn.
  intros ? ? h.
  destruct x as [na [b|] ty]; cbn in *;
  constructor; cbn; (move/andP: h => /= // || move: h) ;
  rewrite ?shiftnP_closedP ?shiftnP_xpredT //;
  intros; try now eapply trans_on_free_vars.
Qed.

Lemma trans_on_free_vars_ctx k ctx : 
  on_free_vars_ctx (shiftnP k xpred0) ctx ->
  on_free_vars_ctx (shiftnP k xpred0) (map_context trans ctx).
Proof.
  intros hctx.
  rewrite -closedP_shiftnP. eapply on_free_vars_ctx_trans.
  rewrite closedP_shiftnP //.
Qed.

Lemma closedP_mon n n' P i : n <= n' -> closedP n P i -> closedP n' P i.
Proof.
  intros hn; rewrite /closedP.
  repeat nat_compare_specs => //.
Qed.

Ltac len := rewrite !plengths.

Lemma trans_lift (t : S.term) P n k :
  on_free_vars P t ->
  trans (S.lift n k t) = T.lift n k (trans t).
Proof.
  intros onfvs.
  revert P t onfvs k. 
  apply: term_on_free_vars_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - f_equal; auto. 
    rewrite /T.map_predicate_k /id /PCUICAst.map_predicate /= /=. 
    f_equal. autorewrite with map; solve_all.
    rewrite map_context_length. solve_all.
    rewrite !map_map_compose. solve_all.
    rewrite /trans_branch /T.map_branch_k. cbn -[expand_lets].
    len. rewrite (Nat.add_comm (context_assumptions _) k).
    f_equal. destruct X as [onbctx ihbctx hbod ->].
    relativize (context_assumptions _).
    erewrite <- expand_lets_lift. 2:len. 2:reflexivity.
    rewrite !plengths.
    rewrite /id. f_equal.
    rewrite distr_lift_subst_context.
    rewrite !plengths. f_equal.
    rewrite map_rev. f_equal. solve_all.
    rewrite PCUICClosed.closed_ctx_lift //.
    rewrite closedn_ctx_on_free_vars.
    rewrite on_free_vars_ctx_subst_instance.
    eapply on_free_vars_ctx_trans. eapply on_free_vars_ctx_impl; tea.
    intros i. eapply closedP_mon. lia.
  - f_equal. solve_all.
  - f_equal; red in X, X0; solve_all.
Qed.

Definition on_fst {A B C} (f:A->C) (p:A×B) := (f p.1, p.2).

Definition trans_def (decl:def PCUICAst.term) : def term.
Proof.
  destruct decl.
  constructor.
  - exact dname.
  - exact (trans dtype).
  - exact (trans dbody).
  - exact rarg.
Defined.

Lemma trans_global_ext_levels Σ:
  S.global_ext_levels Σ = T.global_ext_levels (trans_global Σ).
Proof.
  unfold S.global_ext_levels, global_ext_levels.
  destruct Σ.
  cbn [trans_global fst snd].
  f_equal.
  induction g.
  - reflexivity.
  - unfold S.global_levels in IHg.
    cbn.
    rewrite IHg.
    f_equal.
    destruct a.
    cbn.
    unfold T.monomorphic_levels_decl, T.monomorphic_udecl_decl, T.on_udecl_decl.
    unfold S.monomorphic_levels_decl, S.monomorphic_udecl_decl, S.on_udecl_decl.
    destruct g0.
    + cbn.
      destruct c.
      reflexivity.
    + cbn.
      destruct m.
      reflexivity.
Qed.

Lemma trans_global_ext_constraints Σ :
  S.global_ext_constraints Σ = T.global_ext_constraints (trans_global Σ).
Proof.
  destruct Σ.
  unfold S.global_ext_constraints, T.global_ext_constraints. simpl.
  f_equal. clear u.
  induction g.
  - reflexivity.
  - simpl. rewrite IHg. f_equal. clear.
    destruct a as [? []]; reflexivity.
Qed.

Lemma trans_mem_level_set l Σ:
  LevelSet.mem l (S.global_ext_levels Σ) ->
  LevelSet.mem l (T.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_in_level_set l Σ:
  LevelSet.In l (S.global_ext_levels Σ) ->
  LevelSet.In l (T.global_ext_levels (trans_global Σ)).
Proof.
  intros.
  rewrite <- trans_global_ext_levels.
  apply H.
Qed.

Lemma trans_lookup Σ cst :
  lookup_env (trans_global_decls Σ) cst = option_map trans_global_decl (SE.lookup_env Σ cst).
Proof.
  cbn in *.
  induction Σ.
  - reflexivity.
  - cbn.
    unfold eq_kername in *; destruct kername_eq_dec; subst.
    + destruct a; auto.
    + now rewrite IHΣ.
Qed.

Lemma trans_declared_constant Σ cst decl:
  S.declared_constant Σ cst decl ->
  T.declared_constant (trans_global_decls Σ) cst (trans_constant_body decl).
Proof.
  unfold T.declared_constant.
  rewrite trans_lookup.
  unfold S.declared_constant.
  intros ->.
  reflexivity.
Qed.

Lemma trans_constraintSet_in x Σ:
  ConstraintSet.In x (S.global_ext_constraints Σ) ->
  ConstraintSet.In x (T.global_ext_constraints (trans_global Σ)).
Proof.
  rewrite trans_global_ext_constraints.
  trivial.
Qed.

Lemma trans_consistent_instance_ext {cf} Σ decl u:
  S.consistent_instance_ext Σ decl u ->
  T.consistent_instance_ext (trans_global Σ) decl u.
Proof.
  intros H.
  unfold consistent_instance_ext, S.consistent_instance_ext in *.
  unfold consistent_instance, S.consistent_instance in *.
  destruct decl;trivial.
  destruct H as (?&?&?).
  repeat split;trivial.
  - eapply forallb_impl.
    2: apply H.
    cbv beta.
    intros.
    now apply trans_mem_level_set.
  - unfold valid_constraints in *.
    destruct config.check_univs;trivial.
    unfold valid_constraints0 in *.
    intros.
    apply H1.
    unfold satisfies in *.
    unfold ConstraintSet.For_all in *.
    intros.
    apply H2.
    now apply trans_constraintSet_in.
Qed.

Lemma trans_declared_inductive Σ ind mdecl idecl:
  S.declared_inductive Σ ind mdecl idecl ->
  T.declared_inductive (trans_global_decls Σ) ind (trans_minductive_body mdecl) (trans_one_ind_body mdecl (inductive_ind ind) idecl).
Proof.
  intros [].
  split.
  - unfold T.declared_minductive, S.declared_minductive in *.
    now rewrite trans_lookup H.
  - cbn. now rewrite nth_error_mapi H0 /=.
Qed.

Lemma trans_declared_constructor Σ c mdecl idecl cdecl :
  let ind := (inductive_ind (fst c)) in
  S.declared_constructor Σ c mdecl idecl cdecl ->
  T.declared_constructor (trans_global_decls Σ) c (trans_minductive_body mdecl) (trans_one_ind_body mdecl ind idecl)
    (trans_constructor_body ind mdecl cdecl).
Proof.
  intros ind [].
  split.
  - now apply trans_declared_inductive.
  - now apply map_nth_error.
Qed.

Lemma trans_mkApps t args:
  trans (PCUICAst.mkApps t args) =
  mkApps (trans t) (map trans args).
Proof.
  induction args in t |- *.
  - reflexivity. 
  - cbn [map].
    cbn.
    rewrite IHargs.
    reflexivity.
Qed.

Lemma trans_decl_type decl:
  trans (decl_type decl) =
  decl_type (trans_decl decl).
Proof. 
  destruct decl.
  reflexivity.
Qed.

Lemma expand_lets_subst_comm Γ k s : 
  expand_lets (subst_context s k Γ) ∘ subst s (#|Γ| + k) =1 
  subst s (context_assumptions Γ + k) ∘ expand_lets Γ.
Proof.
  unfold expand_lets, expand_lets_k; simpl; intros x. len.
  rewrite !PCUICSigmaCalculus.subst_extended_subst.
  rewrite distr_subst. rewrite Nat.add_comm; f_equal; len.
  now rewrite commut_lift_subst_rec.
Qed.

Lemma subst_context_subst_context s k s' Γ :
  subst_context s k (subst_context s' 0 Γ) =
  subst_context (map (subst s k) s') 0 (subst_context s (k + #|s'|) Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ']; simpl; auto; 
    rewrite !subst_context_snoc /= /subst_decl /map_decl /=; f_equal; 
    auto; f_equal; len;
  rewrite distr_subst_rec; lia_f_equal.
Qed.

Lemma trans_subst p q xs k t :
  on_free_vars p t ->
  forallb (on_free_vars q) xs ->
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  intros onfvs; revert p t onfvs k.
  apply: term_on_free_vars_ind; intros; cbn.
  all: cbn;try congruence.
  - destruct Nat.leb;trivial.
    rewrite nth_error_map.
    destruct nth_error eqn:hnth;cbn.
    2:now rewrite map_length.
    rewrite (trans_lift _ q) //.
    eapply nth_error_forallb in H0; tea.
  - f_equal.
    do 2 rewrite map_map.
    apply All_map_eq.
    solve_all. rewrite b //. solve_all.
  - rewrite H0 // H2 //.
  - rewrite H0 // H2 //.
  - rewrite H0 // H2 // H4 //.
  - rewrite H0 // H2 //.
  - f_equal; trivial.
    rewrite /= /id /T.map_predicate_k /map_predicate_k /map_predicate /=.
    f_equal; solve_all.
    * rewrite b //. solve_all.
    * rewrite H1 //. solve_all. now rewrite map_context_length.
    * rewrite H3 //.
    * rewrite /trans_branch; rewrite !map_map_compose.
      eapply All_map_eq, All_impl; tea; cbv beta; intros.
      rewrite /T.map_branch_k /=. f_equal; auto.
      len => /=. destruct X3 as [hctx ihctx hb ihb].
      rewrite ihb // /id. 
      replace (context_assumptions (map_context trans (bcontext x))) with
        (context_assumptions ((subst_context (List.rev (map trans (pparams pred))) 0
        (map_context trans (bcontext x))@[puinst pred]))). 2:now len.
      cbn. erewrite <- expand_lets_subst_comm. f_equal.
      2:now len.
      rewrite subst_context_subst_context. f_equal.
      rewrite map_rev; f_equal. solve_all. rewrite b //. solve_all. len.
      rewrite PCUICSpine.closed_ctx_subst //.
      eapply on_free_vars_ctx_trans in hctx.
      rewrite closedn_ctx_on_free_vars.
      rewrite on_free_vars_ctx_subst_instance.
      eapply on_free_vars_ctx_impl; tea.
      intros. eapply closedP_mon; tea. lia.
  - f_equal. rewrite H0 //.
  - f_equal. rewrite !map_map_compose. solve_all.
    rewrite a //. solve_all.
    rewrite b1 //. solve_all.
  - f_equal. rewrite !map_map_compose. solve_all.
    rewrite a //. solve_all.
    rewrite b1 //. solve_all.
Qed.

Lemma trans_subst_ctx (Γ : context) xs k t :
  on_free_vars (shiftnP (#|xs| + #|Γ|) xpred0) t ->
  forallb (on_free_vars (shiftnP #|Γ| xpred0)) xs ->
  trans (S.subst xs k t) =
  T.subst (map trans xs) k (trans t).
Proof.
  intros ont onxs. 
  now erewrite trans_subst; tea.
Qed.

Lemma trans_subst10 u p q B :
  on_free_vars p B -> 
  on_free_vars q u ->
  trans (S.subst1 u 0 B) =
  T.subst10 (trans u) (trans B).
Proof.
  unfold S.subst1. intros onB onu.
  rewrite (trans_subst p q) //. cbn. now rewrite onu.
Qed.

Lemma trans_subst_instance u t:
  trans (subst_instance u t) =
  subst_instance u (trans t).
Proof.
  induction t in u |- * using PCUICInduction.term_forall_list_ind;cbn;auto;try congruence.
  - do 2 rewrite map_map. 
    f_equal.
    apply All_map_eq. solve_all.
  - red in X, X0.
    f_equal.
    + rewrite /map_predicate /=. f_equal. solve_all. solve_all.
    + solve_all.
    + rewrite !map_map_compose. eapply All_map_eq, All_impl; tea; cbv beta.
      intros ? []. rewrite /trans_branch /= /map_branch /= /id. f_equal.
      rewrite PCUICUnivSubstitution.subst_instance_expand_lets e.
      rewrite PCUICUnivSubstitution.subst_instance_subst_context. f_equal.
      f_equal. rewrite [_@[u]]map_rev. f_equal. solve_all.
      solve_all. rewrite [_@[u]] map_map_compose.
      setoid_rewrite compose_map_decl.
      setoid_rewrite PCUICUnivSubstitution.subst_instance_two.
      clear -a. rewrite [_@[_]]map_map_compose.
      rewrite map_map_compose. solve_all.
  - f_equal.
    unfold tFixProp in X. rewrite !map_map_compose. solve_all.
  - f_equal.
    unfold tFixProp in X.
    rewrite !map_map_compose; solve_all.
Qed.

Lemma trans_subst_instance_ctx Γ u :
  trans_local Γ@[u] = (trans_local Γ)@[u].
Proof.
  rewrite /subst_instance /= /trans_local /SE.subst_instance_context /subst_instance_context 
    /map_context.
  rewrite !map_map_compose. apply map_ext.
  move => [na [b|] ty]; cbn;
  rewrite /trans_decl /map_decl /=; f_equal; cbn;
  now rewrite trans_subst_instance.
Qed.

Lemma trans_cst_type decl:
  trans (SE.cst_type decl) =
  cst_type (trans_constant_body decl).
Proof.
  reflexivity.
Qed.

Lemma trans_ind_type mdecl i idecl:
  trans (SE.ind_type idecl) =
  ind_type (trans_one_ind_body mdecl i idecl).
Proof.
  reflexivity.
Qed.

Lemma trans_dtype decl:
  trans (dtype decl) =
  dtype (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_dbody decl:
  trans (dbody decl) =
  dbody (trans_def decl).
Proof.
  destruct decl.
  reflexivity.
Qed.

Lemma trans_inds ind u mdecl : 
  map trans (PCUICCases.inds (inductive_mind ind) u (SE.ind_bodies mdecl)) = 
  inds (inductive_mind ind) u (ind_bodies (trans_minductive_body mdecl)).
Proof.
  rewrite PCUICCases.inds_spec inds_spec.
  rewrite map_rev map_mapi. simpl.
  f_equal. rewrite mapi_mapi. apply mapi_ext => n //.
Qed.

Lemma trans_declared_projection Σ p mdecl idecl cdecl pdecl :
  let ind := (inductive_ind (fst (fst p))) in
  S.declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  T.declared_projection (trans_global Σ).1 p (trans_minductive_body mdecl) (trans_one_ind_body mdecl ind idecl) 
    (trans_constructor_body ind mdecl cdecl) (on_snd trans pdecl).
Proof.
  intros ind []. split; [|split].
  - now apply trans_declared_constructor.
  - unfold on_snd.
    destruct H0.
    destruct pdecl, p.
    cbn in *.
    change (Some (i, trans t)) with
      (Some((fun '(x, y) => (x, trans y)) (i,t))).
    now apply map_nth_error.
  - now destruct mdecl;cbn in *.
Qed.

Lemma inv_opt_monad {X Y Z} (f:option X) (g:X->option Y) (h:X->Y->option Z) c:
  (x <- f;;
  y <- g x;;
  h x y) = Some c ->
  exists a b, f = Some a /\
  g a = Some b /\ h a b = Some c.
Proof.
  intros H.
  destruct f eqn: ?;cbn in *;try congruence.
  destruct (g x) eqn: ?;cbn in *;try congruence.
  do 2 eexists.
  repeat split;eassumption.
Qed.

Lemma trans_destr_arity x:
  destArity [] (trans x) =
  option_map (fun '(xs,u) => (map trans_decl xs,u)) (destArity [] x).
Proof.
  set xs := (@nil context_decl). unfold xs at 1.
  replace (@nil context_decl) with (map trans_decl xs) at 1 by (now subst). clearbody xs.
  induction x in xs |- *;cbn;trivial;unfold snoc.
  - rewrite <- IHx2.
    reflexivity.
  - rewrite <- IHx3.
    reflexivity.
Qed.

Lemma trans_mkProd_or_LetIn a t:
  trans (SE.mkProd_or_LetIn a t) =
  mkProd_or_LetIn (trans_decl a) (trans t).
Proof.
  destruct a as [? [] ?];cbn;trivial.
Qed.

Lemma trans_it_mkProd_or_LetIn xs t:
  trans (SE.it_mkProd_or_LetIn xs t) =
  it_mkProd_or_LetIn (map trans_decl xs) (trans t).
Proof.
  induction xs in t |- *;simpl;trivial.
  rewrite IHxs.
  f_equal.
  apply trans_mkProd_or_LetIn.
Qed.


Lemma trans_nth n l x : trans (nth n l x) = nth n (List.map trans l) (trans x).
Proof.
  induction l in n |- *; destruct n; trivial.
  simpl in *. congruence.
Qed.

Lemma trans_isLambda t :
  T.isLambda (trans t) = S.isLambda t.
Proof.
  destruct t; cbnr.
Qed.

Lemma trans_unfold_fix p mfix idx narg fn :
  on_free_vars p (tFix mfix idx) ->
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros onfvs [= <- <-]. simpl.
  repeat f_equal.
  rewrite (trans_subst (shiftnP #|mfix| p) p).
  unshelve eapply nth_error_forallb in onfvs; tea. now move/andP: onfvs => //.
  eapply (on_free_vars_fix_subst _ _ idx). tea.
  f_equal. clear Hdef. simpl.
  unfold fix_subst. rewrite map_length.
  revert onfvs.
  generalize mfix at 1 2 3 5.
  induction mfix; trivial.
  simpl; intros mfix' hfvs. f_equal.
  now eapply IHmfix.  
Qed.

Lemma trans_unfold_cofix p mfix idx narg fn :
  on_free_vars p (tCoFix mfix idx) ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros onfvs [= <- <-]. simpl.
  repeat f_equal.
  rewrite (trans_subst (shiftnP #|mfix| p) p).
  unshelve eapply nth_error_forallb in onfvs; tea. now move/andP: onfvs => //.
  eapply (on_free_vars_cofix_subst _ _ idx). tea.
  f_equal. clear Hdef. simpl.
  unfold cofix_subst. rewrite map_length.
  revert onfvs.
  generalize mfix at 1 2 3 5.
  induction mfix; trivial.
  simpl; intros mfix' hfvs. f_equal.
  now eapply IHmfix.  
Qed.
  
Lemma trans_is_constructor:
  forall (args : list S.term) (narg : nat),
    is_constructor narg args = true -> is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold is_constructor.
  rewrite nth_error_map //. destruct nth_error => //. simpl. intros.
  unfold isConstruct_app, decompose_app in *.
  destruct (decompose_app_rec t []) eqn:da. simpl in H.
  destruct t0 => //.
  apply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps /=.
  rewrite decompose_app_rec_mkApps //. 
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> red1 Σ Γ t u -> red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> red1 Σ Γ t u -> red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.

Lemma forallb_mapi_ext {A B} (p : A -> bool) (l : list A) {f g : nat -> A -> B} :
  forallb p l ->
  (forall i x, p x -> f i x = g i x) ->
  mapi f l = mapi g l.
Proof.
  unfold mapi; generalize 0. induction l; cbn; auto.
  move=> n /andP[] pa pl hf.
  rewrite hf //. f_equal. apply IHl => //.
Qed.

Lemma trans_fix_context p mfix idx :
  on_free_vars p (tFix mfix idx) ->
  map trans_decl (SE.fix_context mfix) =
  fix_context (map (map_def trans trans) mfix).
Proof.
  unfold trans_local.
  unfold fix_context.
  rewrite map_rev map_mapi.
  cbn. move=> onfvs. f_equal.
  rewrite mapi_map. eapply forallb_mapi_ext; tea => i x hx.
  cbn. rewrite /trans_decl /= /vass. f_equal.
  rewrite (trans_lift _ p) //.
  now move/andP: hx.
Qed.

Lemma trans_subst_decl p q s k d : 
  on_free_vars_terms p s ->
  on_free_vars_decl q d ->
  trans_decl (SE.subst_decl s k d) = subst_decl (map trans s) k (trans_decl d).
Proof.
  destruct d as [na [b|] ty]; cbn; rewrite /trans_decl /= /subst_decl /= /map_decl /=.
  intros ons ond.
  f_equal. f_equal.
  rewrite (trans_subst q p) //. 
  now move/andP: ond => /=.
  rewrite (trans_subst q p) //. 
  now move/andP: ond => /=.
  intros ons ond.
  f_equal. f_equal.
  rewrite (trans_subst q p) //. 
Qed.
  
Lemma trans_subst_context p q s k Γ : 
  on_free_vars_ctx p Γ ->
  on_free_vars_terms q s ->
  trans_local (SE.subst_context s k Γ) = subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|d Γ]; simpl; auto.
  rewrite !subst_context_snoc /= on_free_vars_ctx_snoc.
  move=> /andP[] onΓ ond ons.
  erewrite trans_subst_decl; tea. rewrite /app_context /snoc. len. f_equal.
  now apply IHΓ.
Qed.

Lemma trans_lift_decl p n k d : 
  on_free_vars_decl p d ->
  trans_decl (SE.lift_decl n k d) = lift_decl n k (trans_decl d).
Proof.
  destruct d as [na [b|] ty]; cbn; rewrite /trans_decl /= /lift_decl /= /map_decl /=.
  intros ond.
  f_equal. f_equal.
  rewrite (trans_lift _ p) //. 
  now move/andP: ond => /=.
  rewrite (trans_lift _ p) //. 
  now move/andP: ond => /=.
  intros ond.
  f_equal. f_equal.
  rewrite (trans_lift _ p) //. 
Qed.

Lemma trans_lift_context p n k Γ : 
  on_free_vars_ctx p Γ ->
  trans_local (SE.lift_context n k Γ) = lift_context n k (trans_local Γ).
Proof.
  induction Γ as [|d]; auto.
  rewrite /= !lift_context_snoc /= on_free_vars_ctx_snoc.
  move/andP => [] onΓ ond.
  rewrite (trans_lift_decl (shiftnP #|Γ| p)) //. len. unfold snoc. f_equal.
  now apply IHΓ.
Qed.

Lemma trans_smash_context p Γ Δ : 
  on_free_vars_ctx (shiftnP #|Δ| p) Γ ->
  on_free_vars_ctx p Δ ->
  trans_local (SE.smash_context Γ Δ) = smash_context (trans_local Γ) (trans_local Δ).
Proof.
  induction Δ in p, Γ |- *; simpl; auto.
  rewrite on_free_vars_ctx_snoc.
  move=> onΓ /andP [] onΔ ona.
  destruct a as [na [b|] ty] => /=.
  rewrite (IHΔ p) //.
  eapply on_free_vars_ctx_subst_context0.
  now rewrite shiftnP_add. cbn.
  move/andP: ona => [] /= -> //.
  f_equal.
  rewrite (trans_subst_context (shiftnP (S #|Δ|) p) (shiftnP #|Δ| p)) //.
  move/andP: ona => [] /= -> //; cbn; auto.
  rewrite (IHΔ p) //. 
  rewrite on_free_vars_ctx_app /=.
  cbn. rewrite shiftnP0. move/andP: ona => [] _ ->.
  now rewrite shiftnP_add. f_equal. rewrite trans_local_app //.
Qed.

Lemma context_assumptions_map ctx : context_assumptions (map trans_decl ctx) = SE.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto; lia.
Qed.

Lemma on_free_vars_ctx_k_eq p n Γ : 
  on_free_vars_ctx_k p n Γ = on_free_vars_ctx (shiftnP n p) Γ.
Proof.
  rewrite /on_free_vars_ctx_k.
  rewrite alli_shift //.
  rewrite /on_free_vars_ctx.
  eapply alli_ext. intros i x.
  now rewrite shiftnP_add Nat.add_comm.
Qed.

Lemma trans_extended_subst p Γ n :
  on_free_vars_ctx p Γ ->
  map trans (extended_subst Γ n) = extended_subst (trans_local Γ) n.
Proof.
  induction Γ in n, p |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto.
  rewrite on_free_vars_ctx_snoc. move/andP => [] onΓ /andP[] onb onty.
  erewrite (trans_subst _ _); revgoals.
  eapply on_free_vars_extended_subst.
  erewrite on_free_vars_ctx_k_eq => //.
  eapply on_free_vars_ctx_impl; tea. intros i pi. rewrite /shiftnP.
  nat_compare_specs; cbn. auto. now instantiate (1 := xpredT).
  erewrite on_free_vars_lift. eapply onb.
  erewrite (trans_lift _ _); revgoals. eapply onb.
  rewrite (IHΓ p) //. f_equal. f_equal. len.
  now rewrite context_assumptions_map.
  rewrite on_free_vars_ctx_snoc => /andP[] onΓ ont.
  f_equal; eauto.
Qed.

Lemma trans_expand_lets_k p Γ k T : 
  on_free_vars_ctx p Γ ->
  on_free_vars (shiftnP #|Γ| p) T ->
  trans (SE.expand_lets_k Γ k T) = expand_lets_k (trans_local Γ) k (trans T).
Proof.
  rewrite /SE.expand_lets_k => onΓ onT.
  erewrite (trans_subst _ _); revgoals.
  eapply on_free_vars_extended_subst. rewrite on_free_vars_ctx_k_eq shiftnP0. exact onΓ.
  erewrite on_free_vars_lift. exact onT.
  erewrite (trans_lift _) => //. 2:exact onT.
  erewrite trans_extended_subst; tea.
  rewrite /expand_lets /expand_lets_k.
  now rewrite (context_assumptions_map Γ) map_length.
Qed.

Lemma trans_expand_lets p Γ T : 
  on_free_vars_ctx p Γ ->
  on_free_vars (shiftnP #|Γ| p) T ->
  trans (expand_lets Γ T) = expand_lets (trans_local Γ) (trans T).
Proof.
  move=> onΓ onT.
  rewrite /SE.expand_lets /SE.expand_lets_k.
  rewrite (trans_expand_lets_k p) //.
Qed.

Lemma alpha_eq_trans {Γ Δ} : 
  All2 (compare_decls eq eq) Γ Δ ->
  All2 (compare_decls eq eq) (trans_local Γ) (trans_local Δ).
Proof.
  intros.
  eapply All2_map, All2_impl; tea.
  intros x y []; constructor; subst; auto.
Qed.

Definition wt {cf} Σ Γ t := ∑ T, Σ ;;; Γ |- t : T.

Lemma isType_wt {cf} Σ Γ T : isType Σ Γ T -> wt Σ Γ T.
Proof.
  intros [s hs]; now exists (PCUICAst.tSort s).
Qed.
Coercion isType_wt : isType >-> wt.

Lemma wt_wf_local {cf} {Σ} {Γ t} : wt Σ Γ t -> wf_local Σ Γ.
Proof.
  intros [s hs]. now eapply typing_wf_local.
Qed.

Coercion wt_wf_local : wt >-> All_local_env.

Lemma wt_red {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t u} : wt Σ Γ t -> red1 Σ Γ t u -> wt Σ Γ u.
Proof.
  intros [s hs] r. exists s.
  eapply subject_reduction; tea. now apply red1_red.
Qed.

Section wtsub.
  Context {cf} {Σ : PCUICEnvironment.global_env_ext} {wfΣ : PCUICTyping.wf Σ}.
  Import PCUICAst.
  Definition wt_subterm Γ (t : term) : Type := 
    let wt := wt Σ in
    match t with
    | tLambda na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tProd na A B => wt Γ A × wt (Γ ,, vass na A) B
    | tLetIn na b ty b' => [× wt Γ b, wt Γ ty & wt (Γ ,, vdef na b ty) b']
    | tApp f a => wt Γ f × wt Γ a
    | tCase ci p c brs => 
      All (wt Γ) p.(pparams) ×
      ∑ mdecl idecl, 
      [× declared_inductive Σ ci mdecl idecl,
         consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p),
         wf_predicate mdecl idecl p,
         All2 (PCUICEquality.compare_decls eq eq) (PCUICCases.ind_predicate_context ci mdecl idecl) (PCUICAst.pcontext p),
         wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) p.(pcontext)@[p.(puinst)],
         PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p) (List.rev (PCUICAst.pparams p))
          (PCUICEnvironment.smash_context [] (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p]),
          wt (Γ ,,, PCUICCases.case_predicate_context ci mdecl idecl p) p.(preturn),
          wt Γ c &
          All2i (fun i cdecl br => 
            [× wf_branch cdecl br,
               All2 (PCUICEquality.compare_decls eq eq) (bcontext br) (PCUICCases.cstr_branch_context ci mdecl cdecl),
               wf_local_rel Σ (Γ ,,, smash_context [] (ind_params mdecl)@[p.(puinst)]) br.(bcontext)@[p.(puinst)],
               All2 (PCUICEquality.compare_decls eq eq) 
                (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl)
                (Γ ,,, inst_case_branch_context p br) &
              wt (Γ ,,, PCUICCases.case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl) br.(bbody)]) 0 idecl.(ind_ctors) brs]
    | tProj p c => wt Γ c
    | tFix mfix idx | tCoFix mfix idx => 
      All (fun d => wt Γ d.(dtype) × wt (Γ ,,, fix_context mfix) d.(dbody)) mfix
    | tEvar _ l => False
    | tRel i => wf_local Σ Γ
    | _ => unit
    end.
  Import PCUICGeneration PCUICInversion.

  Lemma spine_subst_wt Γ args inst Δ : PCUICSpine.spine_subst Σ Γ args inst Δ ->
    All (wt Σ Γ) inst.
  Proof.
    intros []. clear -inst_subslet wfΣ.
    induction inst_subslet; constructor; auto.
    eexists; tea. eexists; tea.
  Qed.

  Lemma wt_inv {Γ t} : wt Σ Γ t -> wt_subterm Γ t.
  Proof.
    destruct t; simpl; intros [T h]; try exact tt.
    - now eapply typing_wf_local in h.
    - now eapply inversion_Evar in h.
    - eapply inversion_Prod in h as (?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Lambda in h as (?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_LetIn in h as (?&?&?&?&?&?); tea.
      repeat split; eexists; eauto.
    - eapply inversion_App in h as (?&?&?&?&?&?); tea.
      split; eexists; eauto.
    - eapply inversion_Case in h as (mdecl&idecl&decli&indices&[]&?); tea.
      assert (tty := PCUICValidity.validity scrut_ty).
      eapply PCUICInductiveInversion.isType_mkApps_Ind_smash in tty as []; tea.
      2:eapply (wf_predicate_length_pars wf_pred).
      split.
      eapply spine_subst_wt in s. now eapply All_rev_inv in s.
      exists mdecl, idecl. split; auto. now symmetry.
      * eapply wf_local_app_inv. eapply wf_local_alpha.
        eapply All2_app; [|reflexivity].
        eapply alpha_eq_subst_instance. symmetry; tea.
        eapply wf_ind_predicate; tea. pcuic.
      * eexists; tea.
      * eexists; tea.
      * eapply Forall2_All2 in wf_brs.
        eapply All2i_All2_mix_left in brs_ty; tea.
        eapply All2i_nth_hyp in brs_ty.
        solve_all. split; auto.
        { eapply wf_local_app_inv. eapply wf_local_alpha.
          eapply All2_app; [|reflexivity].
          eapply alpha_eq_subst_instance in a2.
          symmetry; tea.
          eapply validity in scrut_ty.
          epose proof (wf_case_branch_type ps _ decli scrut_ty wf_pred pret_ty conv_pctx i x y).
          forward X. { split; eauto. }
          specialize (X a1) as [].
          eapply wf_local_expand_lets in a5.
          rewrite /PCUICCases.cstr_branch_context.
          rewrite PCUICUnivSubstitution.subst_instance_expand_lets_ctx.
          rewrite PCUICUnivSubstitution.subst_instance_subst_context.
          rewrite PCUICUnivSubstitution.subst_instance_inds.
          erewrite PCUICUnivSubstitution.subst_instance_id_mdecl; tea. }
        erewrite PCUICCasesContexts.inst_case_branch_context_eq; tea. reflexivity.
        eexists; tea.
    - eapply inversion_Proj in h as (?&?&?&?&?&?&?&?&?); tea.
      eexists; eauto.
    - eapply inversion_Fix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? h; exact h.
      eapply (All_impl a0). intros ? h; eexists; tea.
    - eapply inversion_CoFix in h as (?&?&?&?&?&?&?); tea.
      eapply All_prod.
      eapply (All_impl a). intros ? h; exact h.
      eapply (All_impl a0). intros ? h; eexists; tea.
  Qed.
End wtsub.

Ltac outtimes :=
  match goal with
  | ih : _ × _ |- _ =>
    destruct ih as [? ?]
  end.

Lemma red1_cumul {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> cumul Σ Γ T U.
Proof.
  intros r.
  econstructor 2; tea. constructor. apply leq_term_refl.
Qed.

Lemma red1_cumul_inv {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> cumul Σ Γ U T.
Proof.
  intros r.
  econstructor 3; tea. constructor. eapply leq_term_refl.
Qed.

Definition TTconv {cf} (Σ : global_env_ext) Γ : relation term := 
  clos_refl_sym_trans (relation_disjunction (red1 Σ Γ) (eq_term Σ (T.global_ext_constraints Σ))).

Lemma red1_conv {cf} (Σ : global_env_ext) Γ T U : red1 Σ Γ T U -> TTconv Σ Γ T U.
Proof.
  intros r.
  now repeat constructor. 
Qed.

Lemma trans_expand_lets_ctx p q Γ Δ : 
  on_free_vars_ctx p Γ ->
  on_free_vars_ctx q Δ ->
  trans_local (SE.expand_lets_ctx Γ Δ) = expand_lets_ctx (trans_local Γ) (trans_local Δ).
Proof.
  move=> onΓ onΔ.
  rewrite /SE.expand_lets_ctx /SE.expand_lets_k_ctx /expand_lets_ctx /expand_lets_k_ctx.
  erewrite trans_subst_context.
  erewrite trans_extended_subst; tea.
  erewrite trans_lift_context; tea.
  rewrite context_assumptions_map map_length //.
  erewrite <- on_free_vars_ctx_lift_context; tea.
  eapply on_free_vars_extended_subst. rewrite on_free_vars_ctx_k_eq shiftnP0; tea. 
Qed.

Lemma trans_cstr_branch_context p i ci mdecl cdecl :
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0) (cstr_args cdecl) ->
  smash_context [] (trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)) = 
  cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body i mdecl cdecl).
Proof.
  move=> onpars onargs.
  rewrite /PCUICCases.cstr_branch_context /cstr_branch_context.
  erewrite trans_expand_lets_ctx; tea.
  erewrite trans_subst_context; tea.
  erewrite trans_inds.
  rewrite -(PCUICContexts.expand_lets_smash_context _ []).
  f_equal.
  rewrite PCUICContexts.smash_context_subst_empty.
  f_equal => //. now cbn; rewrite map_length.
  eapply (inds_is_open_terms []).
  eapply on_free_vars_ctx_subst_context. len. exact onargs.
  eapply (inds_is_open_terms []).
Qed.

Lemma trans_cstr_branch_context_inst p i ci mdecl cdecl u :
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0) (cstr_args cdecl) ->
  smash_context [] (trans_local (PCUICCases.cstr_branch_context ci mdecl cdecl)@[u]) = 
  (cstr_branch_context ci (trans_minductive_body mdecl) (trans_constructor_body i mdecl cdecl))@[u].
Proof.
  move=> onps onargs.
  rewrite trans_subst_instance_ctx -(PCUICUnivSubstitution.subst_instance_smash _ _ []). 
  rewrite (trans_cstr_branch_context p i) //.
Qed.

Lemma map2_set_binder_name_alpha (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  All2 (compare_decls eq eq) Δ Δ' ->
  All2 (compare_decls eq eq) (map2 set_binder_name nas Δ) Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  constructor; auto. destruct r; subst; cbn; constructor; auto;
  now transitivity na.
Qed.

Notation eq_names := (All2 (fun x y => x = (decl_name y))).

Lemma eq_names_subst_context nas Γ s k : 
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * cbn; auto. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance nas Γ u : 
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma map2_set_binder_name_alpha_eq (nas : list aname) (Δ Δ' : context) :
  All2 (fun x y => x = (decl_name y)) nas Δ' ->
  All2 (compare_decls eq eq) Δ Δ' ->
  (map2 set_binder_name nas Δ) = Δ'.
Proof.
  intros hl. induction 1 in nas, hl |- *; cbn; auto.
  destruct nas; cbn; auto.
  destruct nas; cbn; auto; depelim hl.
  f_equal; auto. destruct r; subst; cbn; auto.
Qed.

Require Import PCUICContexts.

Lemma eq_names_smash_context Γ :
  All2 (fun x y => decl_name x = decl_name y) (smash_context [] (trans_local Γ)) (smash_context [] Γ).
Proof.
  induction Γ.
  * constructor.
  * destruct a as [na [b|] ty]; cbn; auto.
    rewrite smash_context_acc (smash_context_acc _ [_]). constructor; auto.
Qed.

Lemma trans_inst_case_branch_context_gen p q pred i br ci mdecl cdecl :
  let pred' := PCUICAst.map_predicate id trans trans (map_context trans) pred in
  wf_branch cdecl br ->
  on_free_vars_ctx p (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
    (cstr_args cdecl) ->
  on_free_vars_terms q pred.(pparams) ->
  on_free_vars_ctx (shiftnP #|pred.(pparams)| xpred0) br.(bcontext) ->
  (* on_free_vars_ctx p cdecl.(cstr_args) -> *)
  All2 (compare_decls eq eq) br.(PCUICAst.bcontext) (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  let br' := trans_branch pred' (map_branch trans (map_context trans) br) in
  (case_branch_context ci
    (trans_minductive_body mdecl) pred' (forget_types br'.(bcontext)) (trans_constructor_body i mdecl cdecl)) =
    (trans_local (smash_context [] (inst_case_branch_context pred br))).
Proof.
  intros p' wfbr onindpars onargs onpars onbctx.
  rewrite /inst_case_branch_context.
  rewrite /inst_case_context.
  rewrite /case_branch_context /case_branch_context_gen.
  rewrite (trans_smash_context q) //.
  { eapply on_free_vars_ctx_impl. 2:eapply on_free_vars_ctx_subst_context.
    3:rewrite forallb_rev //; tea.
    intros i'; rewrite shiftnP0 //.
    len. rewrite on_free_vars_ctx_subst_instance //.
    eapply on_free_vars_ctx_impl; tea.
    intros o. rewrite /shiftnP /=. rewrite orb_false_r.
    repeat nat_compare_specs; auto => //. } 
  rewrite (trans_subst_context (shiftnP #|pred.(pparams)| xpred0) q).
  { rewrite on_free_vars_ctx_subst_instance //. }
  { rewrite [on_free_vars_terms _ _]forallb_rev //. }
  intros eq.
  rewrite map_rev.
  rewrite PCUICContexts.smash_context_subst_empty.
  eapply map2_set_binder_name_alpha_eq.
  { apply eq_names_subst_context.
    eapply All2_map_left.
    rewrite -(trans_smash_context (shiftnP #|pred.(pparams)| xpred0) []) //.
    { rewrite on_free_vars_ctx_subst_instance //. }
    eapply All2_map_right.
    rewrite -(PCUICUnivSubstitution.subst_instance_smash _ _ []).
    eapply All2_map_right; cbn.
    apply eq_names_smash_context. }
  eapply alpha_eq_subst_context.
  eapply alpha_eq_subst_instance in eq.
  symmetry in eq.
  eapply alpha_eq_trans in eq.
  rewrite -(trans_cstr_branch_context_inst p i) //.
  eapply alpha_eq_smash_context. exact eq.
Qed.

Lemma alpha_eq_on_free_vars_ctx {p Γ Δ} :
  All2 (compare_decls eq eq) Γ Δ ->
  on_free_vars_ctx p Γ ->
  on_free_vars_ctx p Δ.
Proof.
  induction 1 => //.
  rewrite !on_free_vars_ctx_snoc=> /andP[] clx cll.
  apply /andP; split; auto.
  destruct r; unfold ws_decl, test_decl in *; cbn in *; subst; auto; now rewrite -(All2_length X).
Qed.


Lemma trans_inst_case_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ : context} {pred i br ci c mdecl idecl cdecl} :
  let pred' := PCUICAst.map_predicate id trans trans (map_context trans) pred in
  let br' := trans_branch pred' (map_branch trans (map_context trans) br) in
  wf_predicate mdecl idecl pred ->
  wf_branch cdecl br ->
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  on_free_vars_terms (shiftnP #|Γ| xpred0) pred.(pparams) ->
  All2 (compare_decls eq eq) br.(PCUICAst.bcontext) (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  (case_branch_context ci
    (trans_minductive_body mdecl) pred' (forget_types br'.(bcontext)) (trans_constructor_body i mdecl cdecl)) =
    (trans_local (smash_context [] (inst_case_branch_context pred br))).
Proof.
  intros pred' br' wfp wfbr declc onps com.
  eapply (trans_inst_case_branch_context_gen xpred0 (shiftnP #|Γ| xpred0)) => //.
  eapply closed_ctx_on_free_vars; eapply (declared_inductive_closed_params declc).
  rewrite -closedn_ctx_on_free_vars. rewrite Nat.add_comm; eapply (declared_constructor_closed_args declc).
  eapply alpha_eq_on_free_vars_ctx. symmetry; tea.
  rewrite -closedn_ctx_on_free_vars.
  relativize #|pparams pred|. eapply (closed_cstr_branch_context declc).
  rewrite (wf_predicate_length_pars wfp).
  now rewrite (declared_minductive_ind_npars declc).
Qed.

Lemma context_assumptions_map2_set_binder_name nas Γ :
  #|nas| = #|Γ| ->
  context_assumptions (map2 set_binder_name nas Γ) = context_assumptions Γ.
Proof.
  induction Γ in nas |- *; destruct nas; simpl; auto; try discriminate.
  intros [=]. destruct (decl_body a); auto.
  f_equal; auto.
Qed.

Require Import PCUICSpine.

(* Lemma case_branch_context_assumptions ind mdecl cdecl p (br : branch term) :
  Forall2 (fun na decl => eq_binder_annot na decl.(decl_name)) br.(bcontext) (cstr_args cdecl) ->
  context_assumptions (case_branch_context ind mdecl cdecl p br) = context_assumptions (cstr_args cdecl).
Proof.
  rewrite /case_branch_context /case_branch_context_gen.
  intros Hforall.
  rewrite context_assumptions_map2_set_binder_name. len.
  eapply (Forall2_length Hforall).
  now do 3 rewrite !context_assumptions_subst_context ?context_assumptions_lift_context ?context_assumptions_subst_instance 
    /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
Qed. *)

Lemma cstr_branch_context_assumptions ci mdecl cdecl : 
  SE.context_assumptions (PCUICCases.cstr_branch_context ci mdecl cdecl) =
  SE.context_assumptions (SE.cstr_args cdecl).
Proof.
  rewrite /cstr_branch_context /PCUICEnvironment.expand_lets_ctx
    /PCUICEnvironment.expand_lets_k_ctx.
  now do 2 rewrite !SE.context_assumptions_subst_context ?SE.context_assumptions_lift_context.
Qed.

Lemma trans_reln l p Γ : map trans (SE.reln l p Γ) = 
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; auto.
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (SE.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

Lemma trans_ind_predicate_context ci mdecl idecl :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP #|ind_params mdecl| xpred0) (ind_indices idecl) ->
  trans_local (PCUICCases.ind_predicate_context ci mdecl idecl) = 
  (ind_predicate_context ci (trans_minductive_body mdecl)
      (trans_one_ind_body mdecl (inductive_ind ci) idecl)).
Proof.
  move=> clpars clindices.
  rewrite /ind_predicate_context /Ast.ind_predicate_context /=.
  rewrite /trans_decl /=. f_equal.
  f_equal. rewrite trans_mkApps /=. f_equal.
  rewrite trans_to_extended_list trans_local_app /to_extended_list.
  f_equal. f_equal.
  now rewrite (trans_smash_context xpred0).
  now rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)).
  now rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)).
Qed.

Lemma trans_ind_predicate_context_eq p ci mdecl idecl :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP #|ind_params mdecl| xpred0) (ind_indices idecl) ->
  All2 (compare_decls eq eq) (PCUICAst.pcontext p)
    (PCUICCases.ind_predicate_context ci mdecl idecl) -> 
  All2
    (λ (x : binder_annot name) (y : context_decl),
       eq_binder_annot x (decl_name y))
    (map decl_name (trans_local (PCUICAst.pcontext p)))
    (ind_predicate_context ci (trans_minductive_body mdecl)
       (trans_one_ind_body mdecl (inductive_ind ci) idecl)).
Proof.
  move=> clpars clindices.
  rewrite -trans_ind_predicate_context //.
  intros. eapply All2_map, All2_map_left.
  solve_all.
  destruct X; cbn; subst; auto.
Qed.

Lemma trans_cstr_branch_context_eq ci mdecl cdecl p i br :
  is_closed_context (ind_params mdecl) ->
  on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
  (cstr_args cdecl) ->
  All2 (compare_decls eq eq) (PCUICAst.bcontext br) 
    (PCUICCases.cstr_branch_context ci mdecl cdecl) ->
  All2 (compare_decls eq eq)
    (bcontext (trans_branch p (map_branch trans (map_context trans) br)))
    (cstr_branch_context ci (trans_minductive_body mdecl)
      (trans_constructor_body i mdecl cdecl)).
Proof.
  intros clpars clargs a.
  rewrite -(trans_cstr_branch_context xpred0) //.
  cbn. eapply alpha_eq_smash_context.
  eapply All2_map. solve_all.
  destruct X; subst; auto; constructor; cbn; auto.
Qed.

Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' :
  map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite IHl.
Qed.

Lemma map2_map_map {A B C D} (f : A -> B -> C) (g : D -> B) l l' :
  map2 (fun x y => f x (g y)) l l' = map2 f l (map g l').
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  now rewrite IHl.
Qed.

Lemma trans_set_binder na y :
  trans_decl (PCUICEnvironment.set_binder_name na y) = set_binder_name na (trans_decl y).
Proof.
  destruct y as [na' [b|] ty]; cbn; auto.
Qed.

Require Import Morphisms.
#[global] Instance map2_Proper {A B C} : Morphisms.Proper (pointwise_relation A (pointwise_relation B (@eq C)) ==> eq ==> eq ==> eq) map2.
Proof.
  intros f g Hfg ? ? -> ? ? ->.
  eapply PCUICNameless.map2_ext, Hfg.
Qed.

Lemma map2_set_binder_name_eq nas Δ Δ' :
  All2 (compare_decls eq eq) Δ Δ' ->
  map2 set_binder_name nas Δ = map2 set_binder_name nas Δ'.
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  rewrite IHX. destruct r; subst; cbn; reflexivity.
Qed.

Lemma eq_binder_trans (nas : list aname) (Δ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas Δ ->
  All2 (fun x y => eq_binder_annot x (decl_name y)) nas (trans_local Δ).
Proof.
  intros. eapply All2_map_right, All2_impl; tea.
  cbn. intros x y H. destruct y; apply H.
Qed.

Lemma trans_local_set_binder nas Γ : 
  trans_local (map2 PCUICEnvironment.set_binder_name nas Γ) =
  map2 set_binder_name nas (trans_local Γ).
Proof.
  rewrite /trans_local map_map2.
  setoid_rewrite trans_set_binder.
  now rewrite map2_map_map.
Qed.

Lemma All2_eq_binder_lift_context (l : list (binder_annot name)) n k (Γ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (PCUICEnvironment.lift_context n k Γ).
Proof.
  induction 1; cbn; rewrite ?PCUICLiftSubst.lift_context_snoc //; constructor; auto.
Qed.

Lemma All2_eq_binder_expand_lets_ctx (l : list (binder_annot name)) (Δ Γ : PCUICEnvironment.context) :
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l Γ ->
  All2 (fun x y => eq_binder_annot x y.(decl_name)) l (PCUICEnvironment.expand_lets_ctx Δ Γ).
Proof.
  intros a.
  now eapply All2_eq_binder_subst_context, All2_eq_binder_lift_context.
Qed.

Lemma trans_local_set_binder_name_eq nas Γ Δ :
  All2 (PCUICEquality.compare_decls eq eq) Γ Δ ->
  trans_local (map2 PCUICEnvironment.set_binder_name nas Γ) =
  trans_local (map2 PCUICEnvironment.set_binder_name nas Δ).
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  f_equal. destruct r; subst; f_equal.
  apply IHX.
Qed.

Lemma map2_trans l l' :
  map2
  (λ (x : aname) (y : PCUICEnvironment.context_decl),
      trans_decl (PCUICEnvironment.set_binder_name x y)) l l' =
  map2 (fun (x : aname) (y : PCUICEnvironment.context_decl) =>
    set_binder_name x (trans_decl y)) l l'.
Proof.
  eapply map2_ext.
  intros x y. rewrite /trans_decl. now destruct y; cbn.
Qed.

Lemma closed_ctx_is_closed_context Γ :
  closed_ctx Γ -> is_closed_context Γ.
Proof.
  now rewrite closedn_ctx_on_free_vars closedP_shiftnP shiftnP0.
Qed.
#[local] Hint Resolve closed_ctx_is_closed_context : pcuic.
#[local] Hint Resolve declared_inductive_closed_params : pcuic.

Lemma closedn_ctx_on_free_vars n (Δ : context) :
  closedn_ctx n Δ -> on_free_vars_ctx (shiftnP n xpred0) Δ.
Proof.
  rewrite closedn_ctx_on_free_vars closedP_shiftnP //.
Qed.

#[local] Hint Resolve closedn_ctx_on_free_vars : pcuic.

Lemma declared_inductive_closed_indices {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  closedn_ctx #|ind_params mdecl| (ind_indices idecl).
Proof.
  move/declared_inductive_closed_pars_indices.
  rewrite closedn_ctx_app /= => /andP[] //.
Qed.
#[local] Hint Resolve declared_inductive_closed_indices : pcuic.

Lemma trans_case_predicate_context {cf} {Σ : PCUICEnvironment.global_env_ext}
  {wfΣ : PCUICTyping.wf Σ} {Γ ci mdecl idecl p} : 
  S.declared_inductive Σ ci mdecl idecl ->
  S.consistent_instance_ext Σ (PCUICEnvironment.ind_universes mdecl) (PCUICAst.puinst p) → 
  let parctx := (PCUICEnvironment.ind_params mdecl)@[PCUICAst.puinst p] in
  PCUICSpine.spine_subst Σ Γ (PCUICAst.pparams p)
      (List.rev (PCUICAst.pparams p))
      (PCUICEnvironment.smash_context [] parctx) ->
  wf_predicate mdecl idecl p ->
  let p' := map_predicate id trans trans trans_local p in  
  (case_predicate_context ci (trans_minductive_body mdecl) (trans_one_ind_body mdecl (inductive_ind ci) idecl) p') =
  (trans_local (PCUICCases.case_predicate_context ci mdecl idecl p)).
Proof.
  intros.
  rewrite /case_predicate_context /PCUICCases.case_predicate_context.
  rewrite /case_predicate_context_gen /PCUICCases.case_predicate_context_gen.
  rewrite /trans_local map_map2 map2_trans.
  rewrite -PCUICUnivSubstitution.map2_map_r. f_equal.
  rewrite /p' /=. now rewrite forget_types_map_context.
  rewrite /pre_case_predicate_context_gen /inst_case_context.
  rewrite /PCUICCases.pre_case_predicate_context_gen /PCUICCases.inst_case_context.
  rewrite [map _ _](trans_subst_context (shiftnP (context_assumptions mdecl.(ind_params)) xpred0)
    (shiftnP #|Γ| xpred0)).
  rewrite -closedP_shiftnP on_free_vars_ctx_subst_instance.
  eapply (on_free_vars_ind_predicate_context H).
  now eapply inst_subslet, subslet_open in X.
  rewrite map_rev. f_equal.
  rewrite trans_subst_instance_ctx. 
  rewrite trans_ind_predicate_context; pcuic.
Qed.

Lemma OnOne2All2i_OnOne2All {A B : Type} (l1 l2 : list A) (l3 : list B) 
  (R1 : A → A → Type) (R2 : nat → B → A → Type) (n : nat) (R3 : B -> A -> A -> Type) :
  OnOne2 R1 l1 l2 → 
  All2i R2 n l3 l1 → 
  (forall (n0 : nat) (x y : A) (z : B), R1 x y → R2 n0 z x → R3 z x y) → OnOne2All R3 l3 l1 l2.
Proof.
  induction 1 in n, l3 |- *; intros H; depelim H.
  intros H'. constructor. now eapply H'. eapply (All2i_length _ _ _ _ H).
  intros H'. constructor. now eapply IHX.
Qed.

Lemma trans_eq_binder_annot (Γ : list aname) Δ :
  Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ ->
  Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ (trans_local Δ).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma map_context_trans Γ : map_context trans Γ = trans_local Γ.
Proof.
  rewrite /map_context /trans_local /trans_decl.
  eapply map_ext. intros []; reflexivity.
Qed.

Lemma trans_bcontext p br :  
  (bcontext (trans_branch p (map_branch trans (map_context trans) br))) = smash_context [] (trans_local (bcontext br)).
Proof.
  now cbn.
Qed.

Lemma OnOne2All_map2_map_all {A B I I'} {P} {i : list I} {l l' : list A} (g : B -> I -> I') (f : A -> B) :
  OnOne2All (fun i x y => P (g (f x) i) (f x) (f y)) i l l' -> OnOne2All P (map2 g (map f l) i) (map f l) (map f l').
Proof.
  induction 1; simpl; constructor; try congruence. len.
  now rewrite map2_length !map_length. 
Qed.

Lemma wt_on_free_vars {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t} : wt Σ Γ t -> on_free_vars (shiftnP #|Γ| xpred0) t.
Proof.
  intros [T wt]. now eapply subject_is_open_term in wt.
Qed.

Ltac fuse_shifts :=
  match goal with
  [ H : is_true (on_free_vars (shiftnP 1 (shiftnP _ _)) _) |- _ ] => 
    rewrite -> shiftnP_add in H; cbn in H
  end.

Ltac tofvs := repeat match goal with [ H : wt _ _ _ |- _ ] => apply wt_on_free_vars in H end; 
  try inv_on_free_vars; repeat fuse_shifts. 

#[local] Hint Extern 3 (is_true (_ && true)) => rewrite andb_true_r : pcuic.

Lemma skipn_map_length {A B} {n} {f : A -> B} {l} : #|skipn n (map f l)| = #|skipn n l|.
Proof.
  now rewrite !List.skipn_length map_length.
Qed.

Lemma on_free_vars_ctx_cstr_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {c mdecl idecl cdecl} :
  declared_constructor Σ c mdecl idecl cdecl ->
  on_free_vars_ctx (shiftnP (context_assumptions (ind_params mdecl)) xpred0) 
    (cstr_branch_context c.1 mdecl cdecl).
Proof.
  intros. eapply closedn_ctx_on_free_vars. eapply (PCUICInst.closedn_ctx_cstr_branch_context H).
Qed.

Lemma typing_spine_wt {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {args Γ x2 x3} :
  typing_spine Σ Γ x2 args x3 ->
  All (wt Σ Γ) args.
Proof.
  intros sp.
  dependent induction sp; constructor; auto.
  now exists A.
Qed.

Lemma wt_mkApps_inv {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ f args} : 
  wt Σ Γ (mkApps f args) -> wt Σ Γ f × All (wt Σ Γ) args.
Proof.
  intros [ha tapp].
  eapply inversion_mkApps in tapp as [ty [tf targs]].
  split.
  - exists ty; eauto.
  - now eapply typing_spine_wt. 
Qed.

Lemma red_expand_lets {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ Δ t t' :
  Σ ;;; Γ ,,, Δ ⊢ t ⇝ t' ->
  Σ ;;; Γ ,,, smash_context [] Δ ⊢ expand_lets Δ t ⇝ expand_lets Δ t'.
Proof.
  intros reds.
  rewrite /expand_lets /expand_lets_k. cbn.
  eapply (untyped_closed_red_subst (Γ := _ ,,, _) (Γ' := [])).
  eapply untyped_subslet_extended_subst; tea.
  len => /=. rewrite -shiftnP_add. rewrite foron_free_vars_extended_subst //.
  now move/PCUICAlpha.is_closed_context_app_right: (clrel_ctx reds).
  relativize #|Δ|. relativize (context_assumptions Δ).
  eapply weakening_closed_red; tea. all:try now len. 2:reflexivity.
  eapply is_closed_context_smash_end; fvs.
Qed.

From MetaCoq.PCUIC Require Import PCUICConfluence PCUICNormal.

Lemma red_context_rel_assumptions {cf} {Σ : global_env_ext} {Γ Δ Δ'} :
  red_context_rel Σ Γ Δ Δ' -> context_assumptions Δ = context_assumptions Δ'.
Proof.
  induction 1; cbn; auto. destruct p; cbn; auto. lia.
Qed.

Lemma equality_expand_lets {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {le} {Δ} {T T'} : 
  Σ ;;; Γ ,,, Δ ⊢ T ≤[le] T' ->
  Σ ;;; Γ ,,, smash_context [] Δ ⊢ expand_lets Δ T ≤[le] expand_lets Δ T'.
Proof.
  intros cum.
  pose proof (equality_is_closed_context cum).
  eapply (weakening_equality (Γ'' := smash_context [] Δ)) in cum; tea.
  rewrite /expand_lets /expand_lets_k.
  eapply (PCUICConversion.untyped_substitution_equality (Γ'' := [])) in cum; tea. len in cum; tea.
  simpl.
  len.
  now eapply PCUICContexts.untyped_subslet_extended_subst.
  len. cbn. rewrite -shiftnP_add.
  rewrite foron_free_vars_extended_subst //.
  now move: H; rewrite on_free_vars_ctx_app => /andP[].
  now eapply is_closed_context_smash_end.
Qed.

Lemma red_terms_lift {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ ts us} : 
  is_closed_context (Γ ,,, Δ) ->
  red_terms Σ Γ ts us ->
  red_terms Σ (Γ ,,, Δ) (map (lift0 #|Δ|) ts) (map (lift0 #|Δ|) us).
Proof.
  intros r. solve_all.
  eapply (weakening_closed_red (Γ' := [])) => //.
Qed.

Lemma onfvs_app Γ Δ : is_closed_context (Γ ,,, Δ) -> 
  is_closed_context Γ /\ on_free_vars_ctx (shiftnP #|Γ| xpred0) Δ.
Proof.
  now rewrite on_free_vars_ctx_app => /andP.
Qed.

Lemma untyped_subslet_context_equality {cf} {Γ Γ' Δ Δ'} {s} :
  untyped_subslet (Γ ,,, Δ) s Γ' ->
  untyped_subslet (Γ ,,, Δ') s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.
  
Lemma weakening_is_closed_context Γ Δ : 
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, smash_context [] Δ ,,, lift_context (context_assumptions Δ) 0 Δ).
Proof.
  move=> cl. rewrite on_free_vars_ctx_app.
  apply/andP; split.
  now eapply is_closed_context_smash_end.
  eapply on_free_vars_ctx_lift_context0.
  len => /=. rewrite -shiftnP_add addnP_shiftnP.
  now move/PCUICAlpha.is_closed_context_app_right: cl.
Qed.

Lemma red_context_rel_conv_extended_subst {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} :
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context (Γ ,,, Δ') ->
  red_context_rel Σ Γ Δ Δ' ->
  red_terms Σ (Γ ,,, smash_context [] Δ) (extended_subst Δ 0) (extended_subst Δ' 0) ×
  context_equality_rel false Σ Γ (smash_context [] Δ) (smash_context [] Δ').
Proof.
  intros wfl wfr cum.
  assert (is_closed_context (Γ ,,, smash_context [] Δ)).
  { eapply is_closed_context_smash_end in wfl. eauto with fvs. }
  induction cum in |- *; simpl; auto.
  - split; constructor => //. constructor.
  - depelim p; simpl.
    move: wfl => /= /on_free_vars_ctx_snoc_ass_inv [] wfl clT.
    move: wfr => /= /on_free_vars_ctx_snoc_ass_inv [] wfr clT';
    specialize (IHcum wfl wfr) as [conv cum'];
    try assert (is_closed_context (Γ,,, smash_context [] Γ0)) by
      (rewrite /= smash_context_acc /= on_free_vars_ctx_snoc in H; now move/andP: H) => //.
    all:auto.
    * split; try constructor; auto.
      + eapply into_closed_red => //. cbn. len. now cbn.
      + rewrite !(lift_extended_subst _ 1).
        move: H.
        rewrite /= ![smash_context [_] _]smash_context_acc /= /map_decl /= => ha.
        eapply (red_terms_lift (Δ := [_])) => //.
      + now move/onfvs_app: H.
      + move: H; simpl; rewrite /= !(smash_context_acc _ [_]) /=;
        constructor; auto.
        apply cum'. rewrite /map_decl /=.
        constructor; auto.
        eapply into_closed_red in r; fvs.
        eapply red_equality in r.
        eapply equality_expand_lets in r; tea.
        etransitivity;tea. rewrite /expand_lets /expand_lets_k. simpl.
        rewrite -(length_of cum).
        rewrite -(red_context_rel_assumptions cum).
        move: (PCUICSubstitution.context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
        change (Γ ,,, smash_context [] Γ0) with (Γ ,,, smash_context [] Γ0 ,,, []).
        eapply (untyped_substitution_equality_subst_conv (Γ' := [])); tea.
        now eapply red_terms_equality_terms in conv.
        3:eapply PCUICContexts.untyped_subslet_extended_subst.
        3:{ eapply untyped_subslet_context_equality.
            now eapply untyped_subslet_extended_subst. }
        now eapply weakening_is_closed_context.
        cbn -[is_closed_context]. rewrite on_free_vars_ctx_app.
        apply/andP; split. now apply is_closed_context_smash_end.
        len => /=. rewrite -shiftnP_add. eapply on_free_vars_ctx_lift_context0.
        rewrite (red_context_rel_assumptions cum) addnP_shiftnP.
        now move/PCUICAlpha.is_closed_context_app_right: wfr.
        rewrite PCUICSubstitution.context_assumptions_smash_context /=.
        rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
        relativize #|Γ0|.
        eapply is_open_term_lift.
        len. rewrite (All2_fold_length cum). now len in clT'. reflexivity.
    * move: wfl => /= /on_free_vars_ctx_snoc_def_inv => [] [] clΓ0 clb clT.
      move: wfr => /= /on_free_vars_ctx_snoc_def_inv => [] [] clΓ0' clb' clT'.
      specialize (IHcum clΓ0 clΓ0' ltac:(auto)) as [].
      split; auto.
      constructor; auto.
      len.
      eapply into_closed_red in r; fvs.
      eapply red_expand_lets in r; tea.
      etransitivity; tea. rewrite subst_context_nil.
      rewrite /expand_lets /expand_lets_k. simpl.
      rewrite -(length_of cum).
      rewrite -(red_context_rel_assumptions cum).
      move: (PCUICSubstitution.context_assumptions_smash_context [] Γ0); cbn => <-. simpl.
      change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
      cbn. rewrite smash_context_acc /=.
      change (smash_context [] Γ0 ++ Γ) with (Γ ,,, smash_context [] Γ0 ,,, []).
      eapply (closed_red_red_subst (Γ := _ ,,, _) (Γ' := [])); tea.
      2:{ eapply PCUICContexts.untyped_subslet_extended_subst. }
      { now eapply weakening_is_closed_context. }
      rewrite PCUICSubstitution.context_assumptions_smash_context /=.
      rewrite -[context_assumptions Γ0](smash_context_length []); cbn.
      relativize #|Γ0|.
      eapply is_open_term_lift. 
      len. rewrite (All2_fold_length cum). now len in clb'. reflexivity.
Qed.

From MetaCoq.PCUIC Require Import PCUICSubstitution.

Lemma is_closed_context_subst Γ Γ' s Δ :
  is_closed_context (Γ ,,, Γ' ,,, Δ) ->
  forallb (is_open_term Γ) s ->
  #|s| = #|Γ'| ->
  is_closed_context (Γ ,,, subst_context s 0 Δ).
Proof.
  intros clΓ cls slen.
  rewrite on_free_vars_ctx_app.
  rewrite  -app_context_assoc on_free_vars_ctx_app in clΓ.
  move/andP: clΓ => [] -> /=; rewrite on_free_vars_ctx_app => /andP[] o o'.
  apply on_free_vars_ctx_subst_context0 => //. now rewrite slen.
Qed.

Lemma red_expand_lets_ctx {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Γ'' Δ s s' t} :
  is_closed_context (Γ ,,, Γ' ,,, Δ) ->
  is_closed_context (Γ ,,, Γ'' ,,, Δ) ->
  untyped_subslet Γ s Γ' ->
  untyped_subslet Γ s' Γ'' ->
  All2 (closed_red Σ Γ) s s' ->
  is_open_term (Γ ,,, subst_context s 0 Δ) t ->
  Σ ;;; Γ ,,, subst_context s 0 (smash_context [] Δ) ⊢
    (expand_lets (subst_context s 0 Δ) t) ⇝
    (expand_lets (subst_context s' 0 Δ) t).
Proof.
  intros wf wf' subs subs' reds ont.
  rewrite -smash_context_subst /= subst_context_nil.
  have cls : is_closed_context (Γ,,, subst_context s 0 Δ).
  { eapply is_closed_context_subst; tea. eapply closed_red_terms_open_left in reds. solve_all.
    now rewrite -(untyped_subslet_length subs') (All2_length reds). }
  have cls' : is_closed_context (Γ,,, subst_context s' 0 Δ).
  { eapply is_closed_context_subst; tea. eapply closed_red_terms_open_right in reds. solve_all. 
    now rewrite -(untyped_subslet_length subs'). }
  etransitivity.
  eapply red_expand_lets; tea.
  eapply into_closed_red; tea. reflexivity.
  rewrite /expand_lets /expand_lets_k. len. cbn.
  eapply (closed_red_red_subst (Γ := _ ,,, _) (Γ' := [])); tea.
  3:{ eapply untyped_subslet_extended_subst. }
  eapply weakening_is_closed_context => //.
  eapply (red_context_rel_conv_extended_subst) => //.
  eapply red_ctx_rel_subst; tea. solve_all. apply X.
  solve_all. apply X.
  rewrite context_assumptions_subst.
  rewrite -[context_assumptions Δ](smash_context_length []).
  relativize #|smash_context [] _|. relativize #|Δ|.
  eapply is_open_term_lift. 2-3:now len. apply ont.
Qed.

Require Import PCUICSubstitution.

Lemma untyped_subslet_lift (Γ Δ : context) s Δ' :
  untyped_subslet Γ s Δ' ->
  untyped_subslet (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(untyped_subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
Qed.

Lemma OnOne2_All2i_All2 {A B} {P : A -> A -> Type} {Q R} {n} {l l' : list A} {l'' : list B} : 
  OnOne2 P l l' ->
  All2i Q n l'' l ->
  (forall n x y z, P x y -> Q n z x -> R x y) ->
  (forall n x z, Q n z x -> R x x) ->
  All2 R l l'.
Proof.
  intros o a. induction a in o, l' |- *. depelim o.
  depelim o.
  - intros. constructor; eauto.
    clear -a X0.
    induction a; constructor; eauto.
  - intros. constructor.
    eapply X0; tea.
    eapply IHa; tea.
Qed.

Require Import PCUICUnivSubstitution.

Lemma OnOne2_All_OnOne2 {A} {P : A -> A -> Type} {Q R} l l' : 
  OnOne2 P l l' ->
  All Q l ->
  (forall x y, Q x -> P x y -> R x y) ->
  OnOne2 R l l'.
Proof.
  induction 1; intros H; depelim H; intros IH; constructor; eauto.
Qed.

Lemma OnOne2_All_All2 {A} {P : A -> A -> Type} {Q R} l l' : 
  OnOne2 P l l' ->
  All Q l ->
  (forall x y, Q x -> P x y -> R x y) ->
  (forall x, Q x -> R x x) ->
  All2 R l l'.
Proof.
  induction 1; intros H; depelim H; intros IH; constructor; eauto.
  clear -H X; solve_all.
Qed.

Lemma All2i_map_right_inv {A B C} {P : nat -> A -> B -> Type} {f : C -> B} n (l : list A) l' : 
  All2i P n l (map f l') ->
  All2i (fun n x y => P n x (f y)) n l l'.
Proof.
  induction l' in n, l |- *; cbn; intros h; depelim h; constructor; auto.
Qed.

Lemma All2i_map_left_inv {A B C} {P : nat -> A -> B -> Type} {f : C -> A} n l l' : 
  All2i P n (map f l) l' ->
  All2i (fun n x y => P n (f x) y) n l l'.
Proof.
  induction l in n, l' |- *; cbn; intros h; depelim h; constructor; auto.
Qed.

Lemma trans_is_closed_context Γ : is_closed_context Γ -> is_closed_context (map_context trans Γ).
Proof.
  move=> cl; eapply on_free_vars_ctx_impl; [|eapply (on_free_vars_ctx_trans 0)].
  intros i. rewrite /closedP; now cbn.
  now rewrite closedP_shiftnP shiftnP0.
Qed.

Lemma on_free_vars_ind_params {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {P ind mdecl idecl u} : 
  declared_inductive Σ ind mdecl idecl ->
  on_free_vars_ctx P (ind_params mdecl)@[u].
Proof.
  intros decl.
  eapply on_free_vars_ctx_impl; [|eapply closedn_ctx_on_free_vars]; revgoals.
  rewrite closedn_subst_instance_context.
  eapply (declared_inductive_closed_params decl).
  intros i; rewrite shiftnP0 //.
Qed.

Lemma shiftnP_mon n n' i : n <= n' -> shiftnP n xpred0 i -> shiftnP n' xpred0 i.
Proof.
  rewrite /shiftnP.
  repeat nat_compare_specs; cbn; auto.
Qed.

Lemma is_closed_context_cstr_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ ind mdecl idecl cdecl u} : 
  declared_constructor Σ ind mdecl idecl cdecl ->
  is_closed_context Γ ->
  is_closed_context (Γ ,,, (smash_context [] (ind_params mdecl))@[u] ,,, (cstr_branch_context ind.1 mdecl cdecl)@[u]).
Proof.
  intros declc clΓ.
  rewrite -app_context_assoc on_free_vars_ctx_app clΓ /=.
  rewrite on_free_vars_ctx_app.
  apply/andP; split.
  rewrite subst_instance_smash.
  eapply on_free_vars_ctx_smash => //. apply (on_free_vars_ind_params declc).
  len. cbn. 
  rewrite on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_impl; [|eapply (on_free_vars_ctx_cstr_branch_context declc)].
  intros i. rewrite shiftnP_add. eapply shiftnP_mon.
  move: (context_assumptions_bound (ind_params mdecl)). lia.
Qed.

Lemma trans_untyped_subslet {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ s Δ} : 
  wf_local Σ (Γ ,,, Δ) ->
  All (wt Σ Γ) s ->
  untyped_subslet Γ s Δ -> 
  untyped_subslet (trans_local Γ) (map trans s) (trans_local Δ).
Proof.
  induction 3 in |- *; cbn; try constructor; auto.
  cbn. depelim X. now depelim X0.
  depelim X. depelim X0.
  rewrite (trans_subst (shiftnP #|Γ ,,, Δ|  xpred0) (shiftnP #|Γ| xpred0)).
  red in l0. now eapply subject_is_open_term in l0. solve_all. now eapply wt_on_free_vars. 
  constructor ; auto.
Qed.

Lemma untyped_subslet_length Γ s s' Δ : 
  untyped_subslet Γ s Δ -> #|s| = #|s'| -> assumption_context Δ -> untyped_subslet Γ s' Δ.
Proof.
  induction 1 in s' |- *; cbn; destruct s' => /= //. constructor.
  intros [=]. constructor ; auto. eapply IHX; auto. now depelim H.
  intros. elimtype False; depelim H0. 
Qed.

Lemma wf_local_ind_params_weaken {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ind mdecl u} : 
  declared_minductive Σ ind mdecl ->
  wf_local Σ Γ ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (Γ ,,, (ind_params mdecl)@[u]).
Proof.
  intros decli wfΓ cu.
  eapply weaken_wf_local => //.
  now eapply on_minductive_wf_params.
Qed.

Lemma trans_red1 {cf} (Σ : global_env_ext) {wfΣ : wf Σ} {wfΣ' : wf (trans_global_decls Σ.1)} Γ T U :
  red1 Σ Γ T U ->
  wt Σ Γ T ->
  red (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  induction 1 using red1_ind_all; simpl in *; intros wt;
    match goal with 
    | |- context [tCase _ _ _ _] => idtac
    | |- context [tFix _ _] => idtac
    | |- context [tCoFix _ _] => idtac
    | _ => eapply wt_inv in wt; tea; cbn in wt; repeat outtimes
    end;
    try solve [econstructor; eauto].
  
  - simpl. tofvs.
    rewrite (trans_subst_ctx Γ) /=; pcuic. eapply red1_red; constructor.
    
  - destruct wt. tofvs. rewrite (trans_subst_ctx Γ); pcuic. repeat constructor.

  - destruct nth_error eqn:Heq => //. simpl in H. noconf H.
    simpl. destruct c; noconf H => //.
    rewrite (trans_lift _ (shiftnP #|skipn (S i) Γ| xpred0)); eauto.
    eapply nth_error_All_local_env in wt0; tea. cbn in wt0.
    now eapply subject_is_open_term.
    do 2 constructor. now rewrite nth_error_map Heq.
    
  - pose proof (wt_on_free_vars wt).
    inv_on_free_vars.
    destruct wt as [s Hs].
    eapply inversion_Case in Hs as [mdecl [idecl [decli [indices [[] ?]]]]].
    epose proof (PCUICValidity.inversion_mkApps scrut_ty) as [? [hc hsp]]; tea.
    eapply inversion_Construct in hc as (mdecl'&idecl'&cdecl&wfΓ&declc&cu&tyc); tea.
    destruct (declared_inductive_inj decli (proj1 declc)) as [-> ->]. 2:auto.
    rewrite trans_mkApps /=.
    have lenskip : #|skipn (ci_npar ci) (map trans args)| =
      context_assumptions (cstr_args cdecl).
    { destruct (Construct_Ind_ind_eq _ scrut_ty declc) as [[] _].
      rewrite skipn_length. len. rewrite -eq_npars. lia. len.
      rewrite -eq_npars. rewrite e0. lia. }
    eapply All2i_nth_error_r in brs_ty; tea.
    destruct brs_ty as [cdecl' [Hcdecl' [bctxeq [wfbrctx [hbody hbodyty]]]]].
    rewrite (proj2 declc) in Hcdecl'. noconf Hcdecl'.
    have lenbctx : context_assumptions (cstr_args cdecl) = context_assumptions (bcontext br).
    { rewrite (alpha_eq_context_assumptions _ _ bctxeq).
      rewrite cstr_branch_context_assumptions. lia. } 
    relativize (trans (iota_red _ _ _ _)).
    eapply red1_red; eapply red_iota; tea; eauto. all:auto.
    * rewrite !nth_error_map H; reflexivity.
    * rewrite (PCUICSubstitution.context_assumptions_smash_context []) /= context_assumptions_map. lia.
    * rewrite /iota_red. rewrite skipn_map_length in lenskip.
      have oninst : on_free_vars_ctx (shiftnP #|Γ| xpred0) (inst_case_branch_context p br).
      { rewrite -(PCUICCasesContexts.inst_case_branch_context_eq bctxeq).
        eapply typing_wf_local in hbody. eapply wf_local_closed_context in hbody.
        rewrite -> on_free_vars_ctx_app in hbody.
        move/andP: hbody => [] //. }
      have onb : on_free_vars (shiftnP #|inst_case_branch_context p br| (shiftnP #|Γ| xpred0)) (bbody br).
      { rewrite -(PCUICCasesContexts.inst_case_branch_context_eq bctxeq).   
        eapply subject_is_open_term in hbody. len in hbody. rewrite shiftnP_add //. }
      rewrite (trans_subst_ctx Γ).
      { len. rewrite lenskip.
        rewrite -shiftnP_add.
        eapply on_free_vars_expand_lets_k => //.
        rewrite /inst_case_branch_context /inst_case_context.
        rewrite context_assumptions_subst_context context_assumptions_subst_instance. lia. }
      { rewrite forallb_rev forallb_skipn //. 
        rewrite on_free_vars_mkApps in p3. move: p3 => /= //. }
      rewrite map_rev map_skipn. f_equal.
      rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
      cbn -[expand_lets].
      rewrite expand_lets_assumption_context.
      { apply assumption_context_subst_context.
        apply assumption_context_subst_instance.
        apply smash_context_assumption_context => //.
        constructor. }
      f_equal.
      rewrite /inst_case_branch_context /inst_case_context.
      rewrite (trans_subst_context (shiftnP (#|Γ| + #|ind_params mdecl|) xpred0) (shiftnP #|Γ| xpred0)).
      { rewrite on_free_vars_ctx_subst_instance.
        eapply alpha_eq_on_free_vars_ctx; [symmetry; tea|].
        eapply on_free_vars_ctx_impl; [|eapply (on_free_vars_ctx_cstr_branch_context declc)].
        intros i. rewrite /shiftnP. rewrite !orb_false_r.
        move/Nat.ltb_lt => H'. apply Nat.ltb_lt. 
        pose proof (context_assumptions_bound (ind_params mdecl)). lia. }
      { rewrite [on_free_vars_terms _ _]forallb_rev //. }
      rewrite map_rev. f_equal.
      rewrite trans_subst_instance_ctx //.
    
  - simpl. rewrite !trans_mkApps /=.
    eapply wt_mkApps_inv in wt as [wtf wtargs].
    unfold is_constructor in H0.
    destruct nth_error eqn:hnth.
    pose proof (nth_error_Some_length hnth).
    destruct args. simpl. elimtype False; cbn in H1. lia.
    cbn -[mkApps]. 
    eapply red1_red, red_fix.
    apply (trans_unfold_fix (shiftnP #|Γ| xpred0)); eauto.
    now eapply wt_on_free_vars in wtf.
    eapply (trans_is_constructor (t0 :: args)).
    now rewrite /is_constructor hnth.
    discriminate.
    
  - rewrite trans_mkApps.
    rewrite !trans_mkApps; eauto with wf.
    eapply wt_inv in wt. cbn in wt.
    destruct wt as [wtpars [idecl [cdecl []]]].
    eapply wt_mkApps_inv in w2 as [].
    apply (trans_unfold_cofix (shiftnP #|Γ| xpred0)) in H; eauto with wf.
    eapply red1_red, red_cofix_case; eauto.
    now eapply wt_on_free_vars in w2.

  - rewrite !trans_mkApps.
    eapply wt_inv in wt. cbn in wt.
    eapply wt_mkApps_inv in wt as [].  
    apply (trans_unfold_cofix (shiftnP #|Γ| xpred0)) in H; eauto with wf.
    eapply red1_red, red_cofix_proj; eauto.
    now eapply wt_on_free_vars in w.
    
  - rewrite trans_subst_instance. eapply red1_red; econstructor.
    apply (trans_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body0.

  - rewrite trans_mkApps; eauto with wf.
    simpl. eapply red1_red; constructor; now rewrite nth_error_map H.
  
  - eapply red_abs; eauto.
  - eapply red_abs; eauto.
  - destruct wt as []; eapply red_letin; eauto.
  - destruct wt as []; eapply red_letin; eauto.
  - destruct wt as []; eapply red_letin; eauto.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply OnOne2_All_mix_left in X; tea.
    relativize (map_predicate id _ _ _ (set_pparams _ _)).
    eapply red_case. 5:reflexivity. all:try reflexivity.
    cbn. 
    eapply OnOne2_All2. eapply OnOne2_map.
    2:intros x y h; exact h. 2:reflexivity.
    eapply OnOne2_All_OnOne2; tea. cbv beta.
    intros x y wtt [[r IH] wt]. specialize (IH wt).
    red. apply IH.
    rewrite /trans_branch. cbn.
    eapply All2_map. cbn. eapply All2_map, All_All2_refl.
    eapply All2i_nth_hyp in a0.
    eapply All2i_All_right; tea. cbv beta. clear a0.
    intros ctor cdecl br [hnth [wfbr eqbctx wfbctx eqinst wtb]].
    split => //. cbn [bcontext map_branch]. rewrite /id.
    rewrite [map (map_decl _) _](subst_instance_smash _ _ []) /=.
    eapply (red_expand_lets_ctx (Σ := trans_global Σ) 
      (Γ' := (trans_local (smash_context [] (ind_params mdecl))@[puinst p]))
      (Γ'' := (trans_local (smash_context [] (ind_params mdecl))@[puinst p]))).
    * eapply alpha_eq_on_free_vars_ctx.
      eapply All2_app; [|reflexivity].
      eapply alpha_eq_subst_instance.
      eapply alpha_eq_trans. symmetry. exact eqbctx.
      rewrite - !trans_subst_instance_ctx -!trans_local_app.
      rewrite -[_ ++ _]trans_local_app.
      eapply trans_is_closed_context.
      have declc : declared_constructor Σ (ci, ctor) mdecl idecl cdecl.
      { split; tea. }
      eapply (is_closed_context_cstr_branch_context declc).
      destruct w2 as [? ? % typing_closed_ctx]; eauto.
    * eapply alpha_eq_on_free_vars_ctx.
      eapply All2_app; [|reflexivity].
      eapply alpha_eq_subst_instance.
      eapply alpha_eq_trans. symmetry. exact eqbctx.
      rewrite - !trans_subst_instance_ctx -!trans_local_app.
      rewrite -[_ ++ _]trans_local_app.
      eapply trans_is_closed_context.
      have declc : declared_constructor Σ (ci, ctor) mdecl idecl cdecl.
      { split; tea. }
      eapply (is_closed_context_cstr_branch_context declc).
      destruct w2 as [? ? % typing_closed_ctx]; eauto.
    * rewrite -map_rev.
      eapply trans_untyped_subslet.
      { rewrite subst_instance_smash. eapply wf_local_smash_end.
        eapply wf_local_ind_params_weaken; tea. exact d. exact w2. }
      { solve_all. }
      rewrite subst_instance_smash.
      eapply subslet_untyped_subslet; exact s.
    * rewrite -map_rev.
      eapply trans_untyped_subslet.
      { rewrite subst_instance_smash. eapply wf_local_smash_end.
        eapply wf_local_ind_params_weaken; tea. exact d. exact w2. }
      { solve_all.
        eapply spine_subst_wt_terms in s.
        solve_all. eapply OnOne2_impl_All_r; tea.
        2:solve_all. cbv beta; intros x y wtx [[Hr _]].
        eapply wt_red; tea. }
      eapply untyped_subslet_length.
      rewrite subst_instance_smash. exact s. len.
      eapply (OnOne2_length X).
      pcuic. 
    * eapply All2_rev. eapply All2_map.
      eapply OnOne2_All_All2; tea; cbv beta.
      intros x y wtx [[r Hr] wt].
      specialize (Hr wt).
      destruct wtx. eapply into_closed_red => //.
      eapply typing_closed_ctx in t; tea.
      now eapply trans_is_closed_context.
      eapply trans_on_free_vars. len.
      now eapply subject_is_open_term in t.
      intros x []. eapply into_closed_red. reflexivity.
      eapply typing_closed_ctx in t. now eapply trans_is_closed_context. auto.
      eapply subject_is_open_term in t. eapply trans_on_free_vars. now len.
    * len. destruct wtb. cbn in t.
      eapply subject_is_open_term in t.
      len in t. rewrite (case_branch_context_length wfbr) in t.
      now eapply trans_on_free_vars.
  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply red_case_p.
    symmetry in a. rewrite (inst_case_predicate_context_eq a) in w1.
    specialize (IHX w1).
    rewrite -(inst_case_predicate_context_eq a) in IHX.
    eapply alpha_eq_trans in a.
    rewrite trans_ind_predicate_context in a. 
    { eapply closed_ctx_is_closed_context, declared_inductive_closed_params; tea. }
    { epose proof (declared_inductive_closed_indices _ _ _ d).
      now eapply closedn_ctx_on_free_vars in H. }
    set (p' := map_predicate id trans _ _ p).
    rewrite -(inst_case_predicate_context_eq (p:=p') a).
    rewrite (trans_case_predicate_context d c0 s w).
    now rewrite -trans_local_app.  

  - eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply red_case_c; eauto.
  
  - pose proof (wt_on_free_vars wt). inv_on_free_vars.
    eapply forallb_All in p4.
    eapply wt_inv in wt as [hpars [mdecl [idecl []]]].
    eapply red_case_brs.
    do 2 eapply All2_map.
    eapply All2i_All_mix_right in a0; tea.
    eapply OnOne2_All2i_All2; tea; cbv beta.
    intros _ br br' cdecl [[hred ih] eqctx].
    intros [[] onfvs].
    intros ctx. split => //. 2:{ cbn. now rewrite eqctx. }
    2:{ intros; split; reflexivity. }
    rewrite -{1}(PCUICCasesContexts.inst_case_branch_context_eq a1) in ih.
    specialize (ih w5).
    rewrite trans_local_app in ih.
    cbn -[expand_lets].
    rewrite [map (map_decl _) _](subst_instance_smash _ _ []).
    rewrite -(smash_context_subst []) /=. len. rewrite subst_context_nil /id.
    rewrite -eqctx.
    eapply (red_expand_lets (trans_global Σ)). cbn.
    rewrite /inst_case_branch_context in ih.
    rewrite /inst_case_context in ih.
    rewrite (trans_subst_context (shiftnP #|pparams p| xpred0) (shiftnP #|Γ| xpred0)) // in ih.
    { rewrite on_free_vars_ctx_subst_instance //.
      move/andP: onfvs. rewrite test_context_k_closed_on_free_vars_ctx.
      now rewrite closedP_shiftnP. }
    { rewrite [on_free_vars_terms _ _]forallb_rev. solve_all. }
    rewrite map_rev in ih.
    rewrite trans_subst_instance_ctx in ih.
    move: ih.
    rewrite -![map (map_decl _) _]trans_subst_instance_ctx -trans_subst_instance_ctx.
    rewrite -!map_rev -!(trans_subst_context (closedP #|pparams p| xpredT) (shiftnP #|Γ| xpred0)).
    { move/andP: onfvs => [] onctx _. rewrite test_context_k_closed_on_free_vars_ctx in onctx.
      now rewrite on_free_vars_ctx_subst_instance. }
    { rewrite /on_free_vars_terms forallb_rev. solve_all. }
    rewrite -!trans_local_app. 
    intros r; eapply into_closed_red => //.
    { eapply trans_is_closed_context.
      rewrite -[SE.subst_context _ _ _](PCUICCasesContexts.inst_case_branch_context_eq (p:=p) a1).
      destruct w5 as [? wt]. now eapply typing_closed_ctx in wt. }
    { eapply trans_on_free_vars.
      move/andP: onfvs => [] onctx onb. len.
      now rewrite -shiftnP_add. }
        
  - eapply red_proj_c; eauto.
  - eapply red_app; eauto.
  - eapply red_app; eauto.
  - eapply red_prod; eauto.
  - eapply red_prod; eauto.
  - eapply red_fix_congr.
    eapply All2_map.
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H0; reflexivity.
    cbn. congruence.
    intros. repeat split; reflexivity.

  - eapply red_fix_congr.
    eapply All2_map.
    pose proof (wt_on_free_vars wt).
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H1; reflexivity.
    cbn. 
    rewrite -(trans_fix_context (shiftnP #|Γ| xpred0) _ idx) //.
    now rewrite trans_local_app in X0. cbn; congruence.
    intros. repeat split; reflexivity.

  - eapply red_cofix_congr.
    eapply All2_map.
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H0; reflexivity.
    cbn. congruence.
    intros. repeat split; reflexivity.

  - eapply red_cofix_congr.
    pose proof (wt_on_free_vars wt).
    eapply All2_map.
    eapply wt_inv in wt. cbn in wt.
    eapply OnOne2_All_mix_left in X; tea.
    eapply OnOne2_All2; tea; cbv beta.
    intros; intuition auto. cbn. noconf b0. rewrite H1; reflexivity.
    cbn. 
    rewrite -(trans_fix_context (shiftnP #|Γ| xpred0) _ idx) //.
    now rewrite trans_local_app in X0. cbn; congruence. 
    intros. repeat split; reflexivity.
Qed.

Lemma trans_R_global_instance Σ Re Rle gref napp u u' :
  R_global_instance Σ Re Rle gref napp u u' ->
  R_global_instance (trans_global_decls Σ) Re Rle gref napp u u'.
Proof.
  unfold PCUICEquality.R_global_instance, PCUICEquality.global_variance.
  destruct gref; simpl; auto.
  - unfold S.lookup_inductive, S.lookup_minductive.
    unfold lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_mapi.
    destruct nth_error => /= //.
    rewrite trans_destr_arity.
    destruct PCUICAstUtils.destArity as [[ctx ps]|] => /= //.
    now rewrite context_assumptions_map.
  - unfold S.lookup_constructor, S.lookup_inductive, S.lookup_minductive.
    unfold lookup_constructor, lookup_inductive, lookup_minductive.
    rewrite trans_lookup. destruct SE.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_mapi.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
Qed. 

Lemma trans_eq_context_gen_eq_binder_annot Γ Δ :
  eq_context_gen eq eq Γ Δ ->
  All2 eq_binder_annot (map decl_name (trans_local Γ)) (map decl_name (trans_local Δ)).
Proof.
  move/All2_fold_All2.
  intros; do 2 eapply All2_map. solve_all.
  destruct X; cbn; auto.
Qed.

Lemma trans_eq_context_gen Γ Δ :
  eq_context_gen eq eq Γ Δ ->
  eq_context_gen eq eq (trans_local Γ) (trans_local Δ).
Proof.
  move/All2_fold_All2 => e. apply All2_fold_All2.
  eapply All2_map. solve_all.
  destruct X; cbn; subst; constructor; auto.
Qed.

Lemma eq_context_gen_extended_subst {Γ Δ n} :
  eq_context_gen eq eq Γ Δ ->
  extended_subst Γ n = extended_subst Δ n.
Proof.
  induction 1 in n |- *; cbn; auto.
  destruct p; subst; cbn. f_equal; auto.
  rewrite IHX.
  now rewrite (PCUICConfluence.eq_context_gen_context_assumptions X).
Qed.

Lemma eq_context_gen_smash_context {Γ Δ} :
  eq_context_gen eq eq Γ Δ ->
  eq_context_gen eq eq (smash_context [] Γ) (smash_context [] Δ).
Proof.
  induction 1; try constructor.
  rewrite (smash_context_app [] [d]) smash_context_acc.
  rewrite (smash_context_app [] [d']) (smash_context_acc Γ').
  cbn. destruct p; subst; cbn. eapply All2_fold_All2.
  eapply All2_app. 2:now eapply All2_fold_All2.
  rewrite !lift_context_snoc /=.
  rewrite (All2_fold_length X). repeat constructor; cbn; auto.
  rewrite (eq_context_gen_extended_subst X).
  now rewrite (PCUICConfluence.eq_context_gen_context_assumptions X).
  eapply All2_fold_app => //.
  constructor.
Qed.

Lemma eq_context_upto_context_assumptions {cf} {Σ Re Rle} {Γ Δ} :
  eq_context_upto Σ Re Rle Γ Δ ->
  context_assumptions Γ = context_assumptions Δ.
Proof.
  induction 1; cbn; auto.
  destruct p; subst; cbn; auto. f_equal; auto.
Qed.

Lemma eq_term_upto_univ_expand_lets {cf} {Σ Re Rle Γ Δ t u napp} :
  subrelation Re Rle ->
  eq_context_upto Σ Re Rle Γ Δ ->
  eq_term_upto_univ_napp Σ Re Rle napp t u ->
  eq_term_upto_univ_napp Σ Re Rle napp (expand_lets Γ t) (expand_lets Δ u).
Proof.
  intros subr eqctx eqt.
  rewrite /expand_lets /expand_lets_k.
  eapply eq_term_upto_univ_substs => //.
  rewrite (eq_context_upto_length eqctx).
  rewrite (eq_context_upto_context_assumptions eqctx). 
  now eapply eq_term_upto_univ_lift.
  apply (PCUICConfluence.eq_context_extended_subst eqctx).
Qed.

Lemma trans_eq_term_upto_univ {cf} {Σ Re Rle t u napp} : 
  Reflexive Re -> Reflexive Rle ->
  Transitive Re -> SubstUnivPreserving Re ->
  subrelation Re Rle ->
  PCUICEquality.eq_term_upto_univ_napp Σ Re Rle napp t u ->
  eq_term_upto_univ_napp (trans_global_decls Σ) Re Rle napp (trans t) (trans u).
Proof.
  intros hre hrle hret hres hsub e.
  induction t using term_forall_list_ind in Rle, hrle, hsub, napp, u, e |- *.
  all: invs e; cbn.
  all: try solve [ constructor ; auto ].
  all: try solve [
    repeat constructor ;
    match goal with
    | ih : forall Rle u (napp : nat), _ |- _ =>
      eapply ih ; eauto using subrelation_refl
    end
  ].
  1,2,3,4,5,6: try solve [ constructor; solve_all; eauto using subrelation_refl ].
  all: try solve [ constructor; now eapply trans_R_global_instance ].
  - destruct X1 as [Hpars [Huinst [Hctx Hret]]].
    destruct X as [IHpars [IHctx IHret]].
    constructor; cbn; auto. solve_all.
    constructor; cbn. solve_all.
    1,3:eauto using subrelation_refl.
    repeat split; eauto using subrelation_refl.
    rewrite !map_context_trans.
    now eapply trans_eq_context_gen.
    red in X0. do 2 apply All2_map.
    eapply All2_All_mix_left in X3; tea.
    eapply All2_impl; tea; cbv beta.
    intuition auto.
    eapply eq_context_gen_smash_context.
    now eapply trans_eq_context_gen in a.
    apply eq_term_upto_univ_expand_lets; eauto; tc.
    apply eq_context_upto_subst_context; eauto; tc.
    rewrite /id.
    eapply PCUICConfluence.eq_context_upto_univ_subst_instance'; tc; auto.
    cbn.
    rewrite !map_context_trans /id.
    now eapply trans_eq_context_gen.
    cbn. eapply All2_rev. solve_all. eauto using subrelation_refl.
    cbn. eauto using subrelation_refl.
  - constructor. solve_all; eauto using subrelation_refl.
  - constructor; solve_all; eauto using subrelation_refl.
Qed.

Lemma trans_leq_term {cf} Σ ϕ T U :
  PCUICEquality.leq_term Σ ϕ T U ->
  leq_term (trans_global_decls Σ) ϕ (trans T) (trans U).
Proof.
  eapply trans_eq_term_upto_univ ; eauto; tc.
Qed.

Section wtcumul.
  Import PCUICAst PCUICTyping PCUICEquality.
  Record wt_red1 {cf} (Σ : PCUICEnvironment.global_env_ext) (Γ : PCUICEnvironment.context) T U := 
  { wt_red1_red1 : PCUICReduction.red1 Σ Γ T U;
    wt_red1_dom : isType Σ Γ T;
    wt_red1_codom : isType Σ Γ U }.

  Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level).

  Inductive wt_cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | wt_cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_l t u v : wt_red1 Σ Γ t v -> Σ ;;; Γ |-- v <= u -> Σ ;;; Γ |-- t <= u
  | wt_cumul_red_r t u v : Σ ;;; Γ |-- t <= v -> wt_red1 Σ Γ u v -> Σ ;;; Γ |-- t <= u
  where " Σ ;;; Γ |-- t <= u " := (wt_cumul Σ Γ t u) : type_scope.
    
  Lemma cumul_decorate {cf} (Σ : global_env_ext) {wfΣ : wf Σ} Γ T U :
    isType Σ Γ T -> isType Σ Γ U ->
    cumul Σ Γ T U ->
    wt_cumul Σ Γ T U.
  Proof.
    intros ht hu.
    induction 1. 
    - constructor. auto.
    - pose proof (isType_red1 ht r).
      econstructor 2.
      econstructor; tea.
      eapply IHX; tea.
    - pose proof (isType_red1 hu r).
      econstructor 3; eauto.
      econstructor; tea.
  Qed.
End wtcumul.

Lemma trans_cumul {cf} {Σ : PCUICEnvironment.global_env_ext} {Γ T U} {wfΣ : PCUICTyping.wf Σ} :
  wf (trans_global_decls Σ.1) ->
  wt_cumul Σ Γ T U ->
  cumul (trans_global Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ'; induction 1. 
  - constructor; auto.
    eapply trans_leq_term in l.
    now rewrite -trans_global_ext_constraints.
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto. 2:destruct ht as [s hs]; now eexists.
    intros. 
    eapply red_cumul_cumul; tea. 
  - destruct w as [r ht hv].
    apply trans_red1 in r; eauto. 2:destruct ht as [s hs]; now eexists.
    eapply red_cumul_cumul_inv; tea.
Qed.

Definition TTwf_local {cf} Σ Γ := TT.All_local_env (TT.lift_typing TT.typing Σ) Γ.

Lemma trans_wf_local' {cf} :
  forall (Σ : SE.global_env_ext) Γ (wfΓ : wf_local Σ Γ),
    let P :=
        (fun Σ0 Γ0 _ (t T : PCUICAst.term) _ =>
           TT.typing (trans_global Σ0) (trans_local Γ0) (trans t) (trans T))
    in
    ST.All_local_env_over ST.typing P Σ Γ wfΓ ->
    TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct tu. exists x. eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x. auto.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : SE.global_env_ext) Γ b ty =>
              wf (trans_global Σ) ->
              ST.typing Σ Γ b ty × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
        Γ ->
  wf (trans_global Σ) ->
  TTwf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct t0. exists x. now eapply p.
  - simpl. constructor; auto. red. destruct t0. exists x. intuition auto.
    red. red in t1. destruct t1 => //.
Qed.

Lemma trans_branches {cf} Σ Γ brs btys ps:
  All2
    (fun br bty : nat × PCUICAst.term =>
      (((br.1 = bty.1 × ST.typing Σ Γ br.2 bty.2)
        × TT.typing (trans_global Σ) (trans_local Γ) (trans br.2) (trans bty.2))
      × ST.typing Σ Γ bty.2 (PCUICAst.tSort ps))
      × TT.typing (trans_global Σ) (trans_local Γ) (trans bty.2)
        (trans (PCUICAst.tSort ps))) brs btys ->
  All2
    (fun br bty : nat × term =>
    (br.1 = bty.1 × TT.typing (trans_global Σ) (trans_local Γ) br.2 bty.2)
    × TT.typing (trans_global Σ) (trans_local Γ) bty.2 (tSort ps))
    (map (on_snd trans) brs) (map (fun '(x, y) => (x, trans y)) btys).
Proof.
  induction 1;cbn.
  - constructor.
  - constructor.
    + destruct r as [[[[] ] ] ].
      destruct x,y.
      cbn in *.
      repeat split;trivial.
    + apply IHX.
Qed.

Lemma trans_mfix_All {cf} Σ Γ mfix idx :
  is_open_term Γ (tFix mfix idx) ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ : SE.global_env_ext)
          (Γ : SE.context) (b ty : PCUICAst.term) =>
        ST.typing Σ Γ b ty
        × TT.typing (trans_global Σ) (trans_local Γ) (trans b) (trans ty)) Σ)
    (SE.app_context Γ (SE.fix_context mfix)) ->
  TTwf_local (trans_global Σ)
    (trans_local Γ ,,, fix_context (map (map_def trans trans) mfix)).
Proof.
  intros clfix ?.
  rewrite -(trans_fix_context (shiftnP #|Γ| xpred0) _ idx) //.
  match goal with
  |- TTwf_local _ ?A =>
      replace A with (trans_local (SE.app_context Γ (SE.fix_context mfix)))
  end.
  2: {
    unfold trans_local, SE.app_context.
    now rewrite map_app.
  }

  induction X;cbn;constructor;auto;cbn in *.
  - destruct t0 as (?&?&?).
    exists x.
    apply t1.
  - destruct t0 as (?&?&?).
    eexists;eassumption.
  - destruct t1.
    assumption.  
Qed.

(* Lemma trans_mfix_All2 {cf} Σ Γ mfix (idx : nat) xfix:
  is_open_term Γ (tFix xfix idx) ->
  All
  (fun d : def PCUICAst.term =>
    (ST.typing Σ (SE.app_context Γ (SE.fix_context xfix))
    (dbody d)
    (S.lift0 #|SE.fix_context xfix| (dtype d)))
    × TT.typing (trans_global Σ)
      (trans_local (SE.app_context Γ (SE.fix_context xfix)))
      (trans (dbody d))
      (trans
          (S.lift0 #|SE.fix_context xfix|
            (dtype d)))) mfix ->
  All
    (fun d : def term =>
    TT.typing (trans_global Σ)
    (trans_local Γ ,,, fix_context (map (map_def trans trans) xfix)) 
    (dbody d) (T.lift0 #|fix_context (map (map_def trans trans) xfix)| (dtype d))) 
    (map (map_def trans trans) mfix).
Proof.
  intros hfix; induction 1.
  - constructor.
  - simpl; constructor.
    + destruct p as [].
      unfold app_context, SE.app_context in *.
      unfold trans_local in t0.
      rewrite map_app (trans_fix_context (shiftnP #|Γ| xpred0) _ idx) // in t0.
      rewrite trans_dbody (trans_lift _ (shiftnP #|Γ| xpred0)) in t0.
      replace(#|SE.fix_context xfix|) with
          (#|TT.fix_context (map(map_def trans trans) xfix)|) in t0.
        2:now rewrite TT.fix_context_length map_length fix_context_length.
        now destruct x.
    + auto.
Qed. *)

Lemma All_over_All {cf} Σ Γ wfΓ :
  ST.All_local_env_over ST.typing
    (fun (Σ : SE.global_env_ext) (Γ : SE.context)
      (_ : wf_local Σ Γ) (t T : PCUICAst.term)
      (_ : ST.typing Σ Γ t T) =>
      wf (trans_global Σ) ->
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)) Σ Γ wfΓ ->
  ST.All_local_env
    (ST.lift_typing
      (fun (Σ0 : SE.global_env_ext) (Γ0 : SE.context)
          (b ty : PCUICAst.term) =>
          wf (trans_global Σ) ->

        ST.typing Σ0 Γ0 b ty
        × TT.typing (trans_global Σ0) (trans_local Γ0) (trans b) (trans ty)) Σ) Γ.
Proof.
  intros H.
  induction H;cbn.
  - constructor.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;auto; assumption.
  - constructor.
    + apply IHAll_local_env_over.
    + cbn in *.
      destruct tu.
      eexists;split;auto;eassumption.
    + cbn in *.
      split;auto;eassumption.
Qed.

Lemma trans_decompose_prod_assum :
  forall Γ t,
    let '(Δ, c) := decompose_prod_assum Γ t in
    decompose_prod_assum (trans_local Γ) (trans t) = (trans_local Δ, trans c).
Proof.
  intros Γ t.
  destruct decompose_prod_assum as [Δ c] eqn:e.
  induction t in Γ, Δ, c, e |- *.
  all: simpl in *.
  all: try solve [ inversion e ; subst ; reflexivity ].
  - eapply IHt2 in e as e'. apply e'.
  - eapply IHt3 in e as e'. assumption.
Qed.

Lemma trans_isApp t : PCUICAst.isApp t = false -> isApp (trans t) = false.
Proof.
  destruct t => //.
Qed.

Lemma trans_nisApp t : ~~ PCUICAst.isApp t -> ~~ isApp (trans t).
Proof.
  destruct t => //.
Qed.

Lemma trans_destInd t : ST.destInd t = TT.destInd (trans t).
Proof.
  destruct t => //.
Qed.

Lemma trans_decompose_app t : 
  let '(hd, args) := decompose_app t in 
  decompose_app (trans t) = (trans hd, map trans args).
Proof.
  destruct (decompose_app t) eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  eapply decompose_app_rec_inv in da. simpl in da. subst t.
  rewrite trans_mkApps.
  apply decompose_app_mkApps.
  now rewrite trans_isApp.
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B'} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') l t,
    (forall i x t, f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' f g' g l t.
  unfold mapi. generalize 0.
  intros n h e.
  induction l in n, e, t |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n a) eqn:e'. 2: discriminate.
    eapply h in e' as h'.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHl in e''. rewrite e''. now noconf e.
Qed.

Lemma on_free_vars_it_mkProd_or_LetIn {P Δ t} : 
  on_free_vars P (it_mkProd_or_LetIn Δ t) = 
    on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
Proof.
  move: P. induction Δ using rev_ind => P.
  - cbn. now rewrite shiftnP0.
  - destruct x as [na [b|] ty]; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite on_free_vars_ctx_app /= IHΔ !plengths /= shiftnP_add on_free_vars_ctx_tip /= 
      /on_free_vars_decl /test_decl /=. ring.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /= 
     /on_free_vars_decl /test_decl /=. ring.
Qed.

Lemma trans_check_one_fix n p def :
  test_def (on_free_vars p) (on_free_vars (shiftnP n p)) def ->
  TT.check_one_fix (map_def trans trans def) = ST.check_one_fix def.
Proof.
  unfold ST.check_one_fix, TT.check_one_fix.
  destruct def as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p'] eqn:decty => /= ->.
  rewrite /test_def /=. move/andP => [] onty onarg.
  eapply decompose_prod_assum_it_mkProd_or_LetIn in decty. cbn in decty.
  subst ty.
  move: onty; rewrite on_free_vars_it_mkProd_or_LetIn => /andP[] onctx onp'.
  rewrite -(trans_smash_context p []) /trans_local //.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error => /= //.
  move: (trans_decompose_app (decl_type c)).
  destruct decompose_app => /=.
  simpl. destruct c. simpl. intros ->.
  now rewrite -trans_destInd.
Qed.

Definition on_free_vars_mfix p n mfix :=
 forallb (test_def (on_free_vars p) (on_free_vars (shiftnP n p))) mfix.

Lemma map_option_out_check_one_fix {p n mfix} :
  on_free_vars_mfix p n mfix ->
  map (fun x => TT.check_one_fix (map_def trans trans x)) mfix = 
  map ST.check_one_fix mfix.
Proof.
  move/forallb_All => hmfix. eapply All_map_eq, All_impl; tea; cbv beta.
  apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix mfix :
  TT.check_one_cofix (map_def trans trans mfix) = ST.check_one_cofix mfix.
Proof.
  unfold ST.check_one_cofix, TT.check_one_cofix.
  destruct mfix as [na ty arg rarg] => /=.
  move: (trans_decompose_prod_assum [] ty).
  destruct decompose_prod_assum as [ctx p] => -> /=.
  move: (trans_decompose_app p).
  destruct decompose_app => /= ->.
  now rewrite -trans_destInd.
Qed.

Lemma map_option_out_check_one_cofix mfix :
  map (fun x => TT.check_one_cofix (map_def trans trans x)) mfix = 
  map ST.check_one_cofix mfix.
Proof.
  eapply map_ext => x. apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind Σ k f :
  ST.check_recursivity_kind Σ k f = TT.check_recursivity_kind (trans_global_decls Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, TT.check_recursivity_kind.
  rewrite trans_lookup.
  destruct SE.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ p n mfix :
  on_free_vars_mfix p n mfix ->
  TT.wf_fixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix) = 
  ST.wf_fixpoint Σ mfix.
Proof.
  intros hmfix.
  unfold ST.wf_fixpoint, TT.wf_fixpoint.
  rewrite map_map_compose.
  rewrite (map_option_out_check_one_fix hmfix).
  destruct map_option_out as [[]|] => //.
  now rewrite (trans_check_rec_kind Σ).
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  TT.wf_cofixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix) = 
  ST.wf_cofixpoint Σ mfix.
Proof.
  unfold ST.wf_cofixpoint, TT.wf_cofixpoint.
  rewrite map_map_compose.
  rewrite map_option_out_check_one_cofix.
  destruct map_option_out as [[]|] => //.
  now rewrite (trans_check_rec_kind Σ).
Qed.

Lemma type_mkApps_napp `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ f u T T' :
  ~~ isApp f ->
  TT.typing Σ Γ f T ->
  typing_spine Σ Γ T u T' ->
  TT.typing Σ Γ (mkApps f u) T'.
Proof.
  intros hf hty hsp.
  depelim hsp. simpl; auto.
  eapply type_equality; tea.
  eapply type_mkApps; tea.
  econstructor; tea.
Qed.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    TT.fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
  ST.cofix_guard Σ Γ mfix ->
  TT.cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Lemma trans_it_mkLambda_or_LetIn Γ T : 
  trans (it_mkLambda_or_LetIn Γ T) = it_mkLambda_or_LetIn (trans_local Γ) (trans T).
Proof.
  induction Γ using rev_ind.
  * cbn; auto.
  * rewrite /=. rewrite PCUICAstUtils.it_mkLambda_or_LetIn_app [trans_local _]map_app
      it_mkLambda_or_LetIn_app.
    destruct x as [na [b|] ty] => /=; cbn; now f_equal.
Qed.

Lemma All2i_All2_mapi {A B C D} P (f : nat -> A -> B) (g : nat -> C -> D) l l' : 
  All2i (fun i x y => P (f i x) (g i y)) 0 l l' ->  
  All2 P (mapi f l) (mapi g l').
Proof.
  rewrite /mapi. generalize 0.
  induction 1; constructor; auto.
Qed.

Lemma All2i_sym {A B} (P : nat -> A -> B -> Type) n l l' :
  All2i (fun i x y => P i y x) n l' l ->
  All2i P n l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma eq_names_subst_context_pcuic nas Γ s k : 
  eq_names nas Γ ->
  eq_names nas (subst_context s k Γ).
Proof.
  induction 1.
  * rewrite subst_context_nil. constructor.
  * rewrite subst_context_snoc. constructor; auto.
Qed.

Lemma eq_names_subst_instance_pcuic nas (Γ : context) u : 
  eq_names nas Γ ->
  eq_names nas (subst_instance u Γ).
Proof.
  induction 1.
  * cbn; auto.
  * rewrite /subst_instance /=. constructor; auto.
Qed.

Lemma map_expand_lets_lift_cancel Γ n ts : 
  n = #|Γ| ->
  map (expand_lets Γ) (map (lift0 n) ts) =
  map (lift0 (context_assumptions Γ)) ts.
Proof.
  intros ->. solve_all. eapply All_refl.
  intros x. now rewrite expand_lets_lift_cancel.
Qed.

Lemma expand_lets_k_subst_comm Δ k s T : 
  expand_lets_k Δ k (subst s k T) = 
  subst (map (expand_lets Δ) s) k (expand_lets_k Δ (#|s| + k) T).
Proof.
  rewrite /expand_lets_k.
  rewrite distr_lift_subst_rec.
  rewrite -{1}(Nat.add_0_r k).
  rewrite distr_subst_rec (Nat.add_comm #|s|). len.
  rewrite map_map_compose. reflexivity.
Qed.

Lemma context_assumptions_set_binder_name nas Γ : 
  #|nas| = #|Γ| ->
  context_assumptions (map2 set_binder_name nas Γ) = context_assumptions Γ.
Proof.
  induction nas in Γ |- *; destruct Γ; cbn => //.
  intros [=]. destruct c as [na [b|] ty]; cbn; auto.
  rewrite IHnas //.
Qed.
  
Lemma extended_subst_set_binder_name nas Γ k : 
  #|nas| = #|Γ| ->
  extended_subst (map2 set_binder_name nas Γ) k = 
  extended_subst Γ k.
Proof.
  induction nas in Γ, k |- *; destruct Γ; cbn => //.
  intros [=]. destruct c as [na [b|] ty]; cbn; f_equal; eauto.
  len. rewrite map2_length //. rewrite H0.
  rewrite IHnas //. rewrite context_assumptions_set_binder_name //.
Qed.

Lemma expand_lets_set_binder_name nas Γ t : 
  #|nas| = #|Γ| ->
  expand_lets (map2 set_binder_name nas Γ) t = expand_lets Γ t.
Proof.
  induction nas in Γ |- *; destruct Γ; cbn => //.
  intros [=]. rewrite /expand_lets /expand_lets_k.
  destruct c as [na [b|] ty]; cbn; try len;
  rewrite extended_subst_set_binder_name // map2_length // H0
    !context_assumptions_set_binder_name //.
Qed.

Lemma expand_lets_k_lift n k k' Γ t : 
  expand_lets_k (lift_context n k Γ) k' (lift n (#|Γ| + k + k') t) =
  lift n (k + k' + context_assumptions Γ) (expand_lets_k Γ k' t).
Proof.
  rewrite /expand_lets /expand_lets_k /=.
  rewrite extended_subst_lift_context Nat.add_0_r.
  epose proof (distr_lift_subst_rec _ _ _ k' (k + context_assumptions Γ)).
  len. rewrite permute_lift. lia. rewrite !Nat.add_assoc /= in H.
  rewrite (Nat.add_comm _ k') Nat.add_assoc.
  relativize #|Γ|. erewrite <- H. 2:now len.
  now len.
Qed.

Lemma lift_expand_lets_k Δ Γ t : 
  closed_ctx Γ ->
  on_free_vars (shiftnP (#|Γ| + #|Δ|) xpred0) t ->
  lift (context_assumptions Δ) #|Δ| (expand_lets_k Γ #|Δ| t) =
  expand_lets_k Γ (#|Δ| + context_assumptions Δ) (lift (context_assumptions Δ) #|Δ| t).
Proof.
  intros cl ont.
  rewrite {1}/expand_lets_k.
  rewrite -{1}(Nat.add_0_r #|Δ|).
  rewrite /expand_lets_k.
  rewrite (lift_closed _ _ (lift (context_assumptions Δ) #|Δ| t) _).
  rewrite on_free_vars_closedn.
  rewrite (Nat.add_comm #|Δ|).
  rewrite -shiftnP_add.
  eapply on_free_vars_lift_impl; rewrite shiftnP_add Nat.add_comm //.
  rewrite (lift_closed _ _ t).
  rewrite on_free_vars_closedn Nat.add_comm //.
  rewrite distr_lift_subst_rec. len.
  rewrite (lift_closed _ _ t).
  rewrite on_free_vars_closedn Nat.add_comm //.
  rewrite closed_subst_map_lift. len.
  rewrite on_free_vars_closedn //. rewrite Nat.add_comm //.
Qed.

Lemma expand_lets_comm Γ Δ t :
  closed_ctx Γ ->
  on_free_vars (shiftnP (#|Γ| + #|Δ|) xpred0) t ->
  expand_lets (expand_lets_ctx Γ Δ) (expand_lets_k Γ #|Δ| t) =
  expand_lets_k Γ (context_assumptions Δ) (expand_lets Δ t).
Proof.
  intros clΓ ont.
  rewrite {2}/expand_lets {3}/expand_lets_k.
  rewrite PCUICInductives.expand_lets_k_subst_comm.
  len. cbn.
  rewrite {1}/expand_lets {1}/expand_lets_k.
  len. f_equal.
  - rewrite /expand_lets_k /expand_lets_ctx /expand_lets_k_ctx subst_extended_subst; len.
    rewrite extended_subst_lift_context; try len. cbn.
    rewrite !map_map_compose. apply map_ext => x.
    now rewrite Nat.add_comm.
  - rewrite lift_expand_lets_k //.
Qed.

Lemma to_extended_list_smash_context_eq Δ Δ' k :
  #|Δ| = #|Δ'| ->
  assumption_context Δ ->
  assumption_context Δ' ->
  to_extended_list_k Δ k =
  to_extended_list_k Δ' k.
Proof.
  induction Δ in Δ', k |- *; cbn; destruct Δ' => /= //.
  intros [=].
  intros ass ass'. destruct a as [na [b|] ty]. elimtype False; depelim ass.
  destruct c as [na' [b'|] ty']; cbn. elimtype False; depelim ass'.
  rewrite !(reln_acc [_]). f_equal. eapply IHΔ => //.
  now depelim ass. now depelim ass'.
Qed.

(* Lemma on_free_vars_expand_lets_k P Γ n t : 
  on_free_vars_ctx P Γ ->
  on_free_vars (shiftnP #|Γ| P) t ->
  on_free_vars (shiftnP n P) (expand_lets_k Γ 0 t).
Proof.
  intros HΓ Ht.
  rewrite /expand_lets_k /=.
  eapply on_free_vars_impl; cycle 1.
  - eapply on_free_vars_subst_gen.
    1:eapply on_free_vars_extended_subst; eauto.
    rewrite -> on_free_vars_lift. eauto.
  - len. rewrite /substP /= /strengthenP /=.
    intros i. simpl. rewrite /shiftnP.
    repeat nat_compare_specs => /= //.
    rewrite Nat.sub_0_r. rewrite /orP.
    replace (i + #|Γ| - context_assumptions Γ - #|Γ|) with (i - context_assumptions Γ) by lia.
    rewrite /occ_betweenP. repeat nat_compare_specs => /= //.
    rewrite orb_false_r Nat.sub_0_r.
    now rewrite orb_diag.
Qed. *)

Lemma on_free_vars_subst_k s k t : 
  forallb (on_free_vars xpred0) s -> 
  on_free_vars (shiftnP (#|s| + k) xpred0) t ->
  on_free_vars (shiftnP k xpred0) (subst s k t).
Proof.
  intros ons ont.
  eapply on_free_vars_impl; [|eapply on_free_vars_subst_gen]; tea.
  intros i. rewrite /substP /shiftnP.
  repeat nat_compare_specs; cbn; auto.
  nat_compare_specs => //.
Qed.

Lemma on_free_vars_expand_lets_k P Γ k t : 
  on_free_vars_ctx P Γ ->
  on_free_vars (shiftnP (k + #|Γ|) P) t ->
  on_free_vars (shiftnP (k + context_assumptions Γ) P) (expand_lets_k Γ k t).
Proof.
  intros HΓ Ht.
  rewrite /expand_lets_k /=.
  eapply on_free_vars_impl; cycle 1.
  - eapply on_free_vars_subst_gen.
    1:eapply on_free_vars_extended_subst; eauto.
    rewrite -> on_free_vars_lift. eauto.
  - len. rewrite /substP /= /strengthenP /=.
    intros i. simpl. rewrite /shiftnP.
    repeat nat_compare_specs => /= //.
    rewrite Nat.sub_0_r. 
    replace (i + #|Γ| - context_assumptions Γ - (k + #|Γ|)) with (i - context_assumptions Γ - k) by lia.
    rewrite /occ_betweenP. repeat nat_compare_specs => /= //.
    rewrite orb_false_r.
    replace (i - context_assumptions Γ - k) with (i - k - context_assumptions Γ) by lia.
    rewrite orb_diag.
    now replace (i - k - context_assumptions Γ) with (i - (k + context_assumptions Γ)) by lia.
Qed.

Lemma on_free_vars_case_predicate_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {P ind mdecl idecl p} :
   let pctx := case_predicate_context ind mdecl idecl p in
   declared_inductive Σ ind mdecl idecl ->
   wf_predicate mdecl idecl p ->
   forallb (on_free_vars P) (pparams p) ->
   on_free_vars_ctx P pctx.
Proof.
  intros pctx decli wfp onps.
  rewrite /pctx /case_predicate_context /case_predicate_context_gen.
  eapply alpha_eq_on_free_vars_ctx. symmetry.
  eapply eq_binder_annots_eq.
  eapply (wf_pre_case_predicate_context_gen wfp).
  rewrite /pre_case_predicate_context_gen.
  eapply on_free_vars_ctx_inst_case_context; tea. reflexivity.
  rewrite test_context_k_closed_on_free_vars_ctx.
  rewrite (wf_predicate_length_pars wfp).
  rewrite (declared_minductive_ind_npars decli).
  exact (on_free_vars_ind_predicate_context (ind:=ind) decli).
Qed.

Lemma trans_case_branch_type {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : context} {ci : case_info} {mdecl idecl cdecl i p br} :
  declared_constructor Σ (ci, i) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  All2 (compare_decls eq eq) (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  All2 (compare_decls eq eq) (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
  on_free_vars_terms (shiftnP #|Γ| xpred0) p.(pparams) ->
  on_free_vars (shiftnP (S #|ind_indices idecl|) (shiftnP #|Γ| xpred0)) (preturn p) ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  let p' := map_predicate id trans trans (map_context trans) p in
  let br' :=  (trans_branch p' (map_branch trans (map_context trans) br)) in
  let cbctx := case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl in
  let cbt' := case_branch_type ci (trans_minductive_body mdecl)
    (trans_one_ind_body mdecl (inductive_ind ci) idecl) p' br'
  (it_mkLambda_or_LetIn
    (trans_local (case_predicate_context ci mdecl idecl p))
    (preturn
        (map_predicate id trans trans (map_context trans) p)))
  i (trans_constructor_body (inductive_ind ci) mdecl cdecl) in
  (cbt'.1 = trans_local (smash_context [] cbctx)) *
  (cbt'.2 = trans (expand_lets cbctx (case_branch_type ci mdecl idecl p br ptm i cdecl).2)).
Proof.
  intros declc cu wfp wfbr wfpctx wfbctx onps ptm p' br'.
  have wfbr' : wf_branch cdecl (map_branch trans (map_context trans) br).
  { move: wfbr. rewrite /wf_branch /wf_branch_gen /=.
    intros h. now rewrite forget_types_map_context. }
  rewrite /case_branch_type /case_branch_type_gen /=.
  set (brctx' := case_branch_context_gen _ _ _ _ _ _).
  have eqbrctx' : brctx' = trans_local (smash_context [] 
    (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)).
  { rewrite /brctx' [case_branch_context_gen _ _ _ _ _ _](trans_inst_case_branch_context
      (Γ := Γ)
      (br := br) wfp wfbr declc) => //.
    erewrite <- PCUICCasesContexts.inst_case_branch_context_eq => //. }
  split => //.
  rewrite expand_lets_mkApps trans_mkApps !lengths /=.
  rewrite !map_app (map_map_compose _ _ _ _ trans).
  f_equal.
  { relativize #|cstr_args cdecl|. erewrite expand_lets_lift_cancel. 2:rewrite case_branch_context_length_args //.
    rewrite case_branch_context_assumptions //. 
    rewrite context_assumptions_map.
    rewrite (trans_lift _ (shiftnP #|Γ| xpred0)).
    { rewrite /ptm on_free_vars_it_mkLambda_or_LetIn.
      apply/andP; split.
      eapply (on_free_vars_case_predicate_context declc wfp) => //.
      rewrite (case_predicate_context_length_indices wfp) => //. }
    rewrite -trans_it_mkLambda_or_LetIn //. }
  have onfvsargs : on_free_vars_ctx (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)
    (cstr_args cdecl).
  { pose proof (declared_constructor_closed_args declc).
    now eapply closedn_ctx_on_free_vars. }
  f_equal.
  rewrite !map_map_compose /id. 
  pose proof (declared_constructor_closed_indices declc).
  eapply forallb_All in H.
  eapply All_map_eq. eapply All_impl; tea; cbv beta.
  intros x cl.
  { rewrite -(trans_expand_lets (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)) //.
    rewrite shiftnP_add.
    eapply closedn_on_free_vars. red in cl. red. rewrite -cl.
    f_equal. lia.
    rewrite -trans_inds. 
    rewrite -trans_subst_instance.
    have fvsexpx : on_free_vars
      (shiftnP (context_assumptions (cstr_args cdecl))
         (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0))
          (expand_lets (cstr_args cdecl) x)@[puinst p].
    { eapply (@closedn_on_free_vars xpred0) in cl.
      rewrite on_free_vars_subst_instance.
      eapply (on_free_vars_expand_lets_k _ _ 0) => //.
      rewrite shiftnP_add. red; rewrite -cl.
      f_equal. f_equal. lia. }
    rewrite -(trans_subst (shiftnP (context_assumptions (cstr_args cdecl)) (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)) xpred0) //.
    eapply (inds_is_open_terms []).
    rewrite -trans_subst_instance_ctx.
    have fvssi : on_free_vars
      (shiftnP #|(ind_params mdecl)@[puinst p]|
        (shiftnP (context_assumptions (cstr_args cdecl)) xpred0))
      (S.subst (inds (inductive_mind ci) (puinst p) (SE.ind_bodies mdecl))
        (#|ind_params mdecl| +
          context_assumptions (trans_local (cstr_args cdecl)))
        (expand_lets (cstr_args cdecl) x)@[puinst p]).
    { len. rewrite shiftnP_add.
      rewrite context_assumptions_map.
      eapply on_free_vars_subst_k. eapply (inds_is_open_terms []).
      len. rewrite shiftnP_add in fvsexpx.
      red; rewrite -fvsexpx. f_equal. f_equal. lia. }
    rewrite -(trans_expand_lets_k (shiftnP (context_assumptions (cstr_args cdecl)) xpred0)) //.
    rewrite on_free_vars_ctx_subst_instance. eapply on_free_vars_ctx_impl. 2:pcuic.
    { intros i'. rewrite shiftnP0 //. }
    rewrite -map_rev.
    rewrite -(trans_subst (shiftnP (context_assumptions (cstr_args cdecl) + context_assumptions (ind_params mdecl))
      xpred0) (shiftnP #|Γ| xpred0)).
    { rewrite context_assumptions_map.
      relativize (context_assumptions (ind_params mdecl)).
      eapply on_free_vars_expand_lets_k => //. rewrite on_free_vars_ctx_subst_instance; pcuic.
      2:now len.
      rewrite shiftnP_add in fvssi. len in fvssi. len.
      rewrite Nat.add_comm context_assumptions_map in fvssi => //. }
    { rewrite forallb_rev. eapply forallb_All in onps. solve_all. }
    f_equal.
    rewrite /case_branch_context /case_branch_context_gen.
    rewrite expand_lets_set_binder_name. len.
    { eapply All2_length in wfbctx.
      now rewrite cstr_branch_context_length in wfbctx. }
    rewrite /pre_case_branch_context_gen /inst_case_context.
    relativize #|cstr_args cdecl|.
    erewrite expand_lets_subst_comm. 2:now len.
    rewrite !context_assumptions_map !context_assumptions_subst_instance.
    rewrite cstr_branch_context_assumptions Nat.add_0_r.
    f_equal.
    rewrite /cstr_branch_context; len.
    rewrite Nat.add_comm.
    rewrite expand_lets_subst_instance.
    relativize (SE.context_assumptions _).
    erewrite <-expand_lets_subst_comm. len.
    rewrite subst_instance_expand_lets_ctx.
    relativize #|cstr_args cdecl|.
    erewrite expand_lets_comm. len.
    rewrite subst_instance_subst_context.
    rewrite instantiate_inds //. exact declc. 4:now len.
    4:now len. now rewrite Nat.add_comm. rewrite closedn_subst_instance_context. pcuic.
    len. eapply on_free_vars_subst_k. eapply (inds_is_open_terms []).
    len. rewrite on_free_vars_subst_instance. 
    eapply closedn_on_free_vars. rewrite Nat.add_assoc //. }
  cbn. f_equal.
  rewrite context_assumptions_map.
  rewrite -(trans_smash_context (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) []) //.
  rewrite expand_lets_mkApps /= map_app trans_mkApps /=.
  f_equal. f_equal; rewrite map_app. f_equal.
  rewrite map_expand_lets_lift_cancel. now rewrite (case_branch_context_length_args wfbr).
  rewrite (case_branch_context_assumptions wfbr).
  rewrite !map_map_compose.
  eapply forallb_All in onps. eapply All_map_eq, All_impl; tea; cbv beta.
  intros x op. rewrite (trans_lift _ (shiftnP #|Γ| xpred0)) //.
  rewrite -(to_extended_list_case_branch_context ci mdecl p _ _ (Forall2_All2 _ _ wfbr)).
  rewrite map_expand_lets_to_extended_list.
  rewrite -[to_extended_list _]trans_to_extended_list.
  f_equal. eapply to_extended_list_smash_context_eq; pcuic; len.
  now rewrite (case_branch_context_assumptions wfbr).
Qed.

Lemma untyped_subslet_inds Γ ind u u' mdecl :
  untyped_subslet Γ (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance u' (arities_context (ind_bodies mdecl))).
Proof.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4.
  unfold inds.
  induction l using rev_ind; simpl; first constructor.
  simpl. rewrite app_length /= => Hlen.
  unfold arities_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=. 
  rewrite /= Nat.add_1_r /=.
  constructor.
  rewrite -rev_map_spec. apply IHl. lia.
Qed.

Lemma equality_it_mkProd_or_LetIn_smash {cf} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ T : 
  is_closed_context Γ -> is_open_term Γ (it_mkProd_or_LetIn Δ T) ->
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn Δ T = it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
Proof.
  intros hfvΓ hfv.
  eapply into_equality. 1-3:fvs.
  2:{ move: hfv.
      rewrite !on_free_vars_it_mkProd_or_LetIn.
      move/andP=> [] onΔ onT.
      rewrite on_free_vars_ctx_smash // /=.
      len. cbn.
      eapply (on_free_vars_expand_lets_k _ _ 0) => //. }
  eapply red_conv_conv; [|reflexivity].
  clear hfvΓ hfv.
  induction Δ in Γ, T |- * using ctx_length_rev_ind.
  - cbn. rewrite expand_lets_nil. reflexivity.
  - rewrite it_mkProd_or_LetIn_app.
    destruct d as [na [b|] ty]; cbn; [rewrite smash_context_app_def expand_lets_vdef|rewrite smash_context_app_ass expand_lets_vass]. 
    * etransitivity.
      eapply red1_red. constructor.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
      eapply X. now len.
    * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      eapply red_prod. reflexivity.
      now eapply X.
Qed.
  
Lemma map_expand_lets_to_extended_list_k_above Γ Δ : 
  map (expand_lets Γ) (to_extended_list_k Δ #|Γ|) = to_extended_list_k Δ (context_assumptions Γ).
Proof.
  unfold to_extended_list_k.
  rewrite -(Nat.add_0_r #|Γ|).
  rewrite reln_lift.
  rewrite map_map_compose.
  setoid_rewrite expand_lets_lift_cancel.
  rewrite -reln_lift Nat.add_0_r //.
Qed.

Lemma on_free_vars_to_extended_list_k P ctx k : 
  forallb (on_free_vars (shiftnP (k + #|ctx|) P)) (to_extended_list_k ctx k).
Proof.
  rewrite /to_extended_list /to_extended_list_k.
  have: (forallb (on_free_vars (shiftnP (k + #|ctx|) P)) []) by easy.
  generalize (@nil term).
  induction ctx in k |- *; intros l Hn.
  - simpl; auto.
  - simpl.
    destruct a as [? [?|] ?].
    * rewrite /= Nat.add_succ_r in Hn.
      specialize (IHctx (S k) l Hn).
      now rewrite Nat.add_succ_r Nat.add_1_r.
    * rewrite Nat.add_succ_r Nat.add_1_r. eapply (IHctx (S k)).
      rewrite -[_ + _](Nat.add_succ_r k #|ctx|) /= Hn.
      rewrite /shiftnP.
      nat_compare_specs => /= //.
Qed.

Lemma trans_type_of_constructor {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {wfΣ' : wf (trans_global Σ)} {mdecl idecl cdecl ind i u} :
  declared_constructor Σ (ind, i) mdecl idecl cdecl ->
  consistent_instance_ext (trans_global Σ)
    (ind_universes (trans_minductive_body mdecl)) u ->
  trans_global Σ ;;; [] ⊢ trans (ST.type_of_constructor mdecl cdecl (ind, i) u) =
  TT.type_of_constructor 
    (trans_minductive_body mdecl) 
    (trans_constructor_body (inductive_ind ind) mdecl cdecl)
    (ind,i)
    u.
Proof.
  intros oncstr onu.
  unfold ST.type_of_constructor.
  rewrite (trans_subst (shiftnP #|ind_bodies mdecl| xpred0) xpred0).
  eapply declared_constructor_closed_gen_type in oncstr.
  len in oncstr. eapply closedn_on_free_vars. now rewrite closedn_subst_instance.
  eapply (inds_is_open_terms []).
  unfold TT.type_of_constructor.
  rewrite trans_inds.
  eapply (untyped_substitution_equality (le:=false) (Γ := []) (Γ'' := [])).
  eapply untyped_subslet_inds.
  eapply (inds_is_open_terms []). instantiate (1:=u).
  simpl. rewrite app_context_nil_l.
  pose proof (on_declared_constructor oncstr) as [[onmind onind] [cs [hnth onc]]].
  rewrite (cstr_eq onc).
  rewrite !subst_instance_it_mkProd_or_LetIn.
  rewrite !trans_it_mkProd_or_LetIn.
  have clctx : is_closed_context
  ((arities_context (mapi (trans_one_ind_body mdecl) (ind_bodies mdecl)))@[u],,,
   trans_local (ind_params mdecl)@[u]).
  { pose proof (trans_declared_constructor _ _ _ _ _ oncstr).
    epose proof (declared_inductive_closed_params (Σ := trans_global Σ) H).
    rewrite on_free_vars_ctx_app !on_free_vars_ctx_subst_instance.
    len.
    rewrite closedn_ctx_on_free_vars.
    rewrite trans_subst_instance_ctx.
    rewrite closedn_subst_instance_context.
    eapply closedn_ctx_upwards; tea. lia.
    rewrite andb_true_r. apply closed_ctx_on_free_vars.
    epose proof (declared_minductive_closed_arities (proj1 (proj1 H))).
    apply H1. }
  epose proof (declared_constructor_closed oncstr).
  rewrite /closed_constructor_body in H.
  move/andP: H => [] /andP[] clargs cli clty.
  have clterm : is_open_term
    ((arities_context (mapi (trans_one_ind_body mdecl) (ind_bodies mdecl)))@[u],,,
    map trans_decl (ind_params mdecl)@[u])
    (it_mkProd_or_LetIn (map trans_decl (cstr_args cdecl)@[u])
      (trans (cstr_concl mdecl (inductive_ind (ind, i).1) cdecl)@[u])).
  { rewrite -trans_it_mkProd_or_LetIn.
    eapply trans_on_free_vars. len.
    rewrite on_free_vars_it_mkProd_or_LetIn.
    apply/andP; split. rewrite on_free_vars_ctx_subst_instance.
    eapply closedn_ctx_on_free_vars. now rewrite Nat.add_comm.
    rewrite shiftnP_add. len. rewrite /cstr_concl.
    rewrite subst_instance_mkApps on_free_vars_mkApps /=.
    rewrite forallb_map forallb_app. apply/and3P; split.
    rewrite /shiftnP orb_false_r. apply Nat.ltb_lt. 
    assert (#|ind_bodies mdecl| > 0).
    { destruct oncstr as [[] ?]. clear hnth. eapply nth_error_Some_length in e. lia. }
    lia.
    eapply forallb_impl. 2:eapply on_free_vars_to_extended_list_k.
    intros x hx. rewrite on_free_vars_subst_instance.
    rewrite Nat.add_assoc. rewrite -[shiftnP (_ + #|ind_bodies mdecl|) _]shiftnP_add.
    intros H; exact H. solve_all.
    rewrite on_free_vars_subst_instance. eapply closedn_on_free_vars in H.
    now rewrite Nat.add_comm (Nat.add_comm _ #|ind_params mdecl|) Nat.add_assoc. }
  eapply equality_it_mkProd_or_LetIn.
  { eapply context_equality_rel_app.
    rewrite -trans_subst_instance_ctx.
    now eapply context_equality_refl. }
  etransitivity.
  eapply equality_it_mkProd_or_LetIn_smash => //.
  have <-: (expand_lets (map trans_decl (cstr_args cdecl)@[u])
    (trans (cstr_concl mdecl (inductive_ind (ind, i).1) cdecl)@[u])) =
    (trans_cstr_concl mdecl (inductive_ind ind)
    (smash_context [] (trans_local (cstr_args cdecl)))
    (map (expand_lets (trans_local (cstr_args cdecl)))
       (map trans (cstr_indices cdecl))))@[u].
  { rewrite /cstr_concl /trans_cstr_concl.
    rewrite !subst_instance_mkApps !trans_mkApps.
    rewrite expand_lets_mkApps. f_equal.
    rewrite /trans_cstr_concl_head. len.
    rewrite /cstr_concl_head /=. 
    relativize #|cstr_args cdecl|. erewrite expand_lets_tRel. 
    cbn. rewrite !context_assumptions_map context_assumptions_subst_instance //.
    now len.
    rewrite !map_app. f_equal.
    rewrite !subst_instance_to_extended_list_k. len; cbn.
    rewrite trans_to_extended_list.
    relativize #|cstr_args cdecl|. erewrite map_expand_lets_to_extended_list_k_above.
    rewrite trans_subst_instance_ctx.
    rewrite [map _ _]trans_subst_instance_ctx.
    rewrite context_assumptions_subst_instance //.
    now len.
    rewrite [map trans_decl _]trans_subst_instance_ctx.
    rewrite (map_map_compose _ _ _ _ trans).
    setoid_rewrite trans_subst_instance.
    rewrite -(map_map_compose _ _ _ trans).
    rewrite !map_map_compose.
    now setoid_rewrite subst_instance_expand_lets. }
  rewrite ![map trans_decl _ ]trans_subst_instance_ctx.
  rewrite subst_instance_smash.
  eapply equality_refl => //.
  now rewrite -trans_subst_instance_ctx.
  rewrite -trans_subst_instance_ctx.
  rewrite on_free_vars_it_mkProd_or_LetIn. len.
  cbn.
  rewrite on_free_vars_ctx_smash //.
  rewrite -closedP_shiftnP. 
  rewrite on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_trans. eapply closedn_ctx_on_free_vars.
  now rewrite Nat.add_comm.
  cbn. 
  eapply PCUICOnFreeVars.on_free_vars_expand_lets_k.
  now rewrite context_assumptions_subst_instance.
  rewrite Nat.add_comm on_free_vars_ctx_subst_instance.
  eapply on_free_vars_ctx_trans.
  now eapply closedn_ctx_on_free_vars.
  move: clterm. len.
  rewrite on_free_vars_it_mkProd_or_LetIn.
  move/andP => [] _. now len.
Qed.

Lemma trans_eq_annots (Γ : list aname) Δ : 
  eq_annots Γ Δ ->
  eq_annots Γ (trans_local Δ).
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma trans_wf_predicate ci mdecl idecl p :
  wf_predicate mdecl idecl p ->
  wf_predicate (trans_minductive_body mdecl)
    (trans_one_ind_body mdecl (inductive_ind ci) idecl)
    (map_predicate id trans trans trans_local p).
Proof.
  move=> [] eqps eqanns.
  split. cbn.
  now rewrite map_length //.
  rewrite forget_types_map_context.
  move: eqanns; rewrite /idecl_binder /= => eqanns.
  depelim eqanns. rewrite H0.
  constructor. cbn. auto.
  now apply trans_eq_annots.
Qed.
 
Lemma extends_trans {Σ Σ'} : extends Σ Σ' -> extends (trans_global_decls Σ) (trans_global_decls Σ').
Proof.
  intros [? ->]. exists (trans_global_decls x).
  rewrite /trans_global_decls map_app //.
Qed.

Lemma weaken_prop {cf} : weaken_env_prop
  (lift_typing
   (λ (Σ : global_env_ext) (Γ : context) (t T : term),
      wf (trans_global Σ)
      → trans_global Σ;;; trans_local Γ |- trans t : trans T)).
Proof.
  intros Σ Σ' u wf ext Γ t T.
  unfold lift_typing. destruct T.
  - intros Ht Hw. 
    pose proof (extends_trans ext).
    pose proof (wf_extends Hw X). 
    specialize (Ht X0).
    eapply (weakening_env (trans_global (Σ, u))); eauto.
  - intros [s Hs]. exists s. intros Hw.
    pose proof (extends_trans ext).
    pose proof (wf_extends Hw X). 
    specialize (Hs X0).
    eapply (weakening_env (trans_global (Σ, u))); eauto.
Qed.

Lemma trans_arities_context mdecl :
  arities_context (ind_bodies (trans_minductive_body mdecl)) = 
  trans_local (arities_context (ind_bodies mdecl)).
Proof.
  rewrite /arities_context.
  rewrite !rev_map_spec -map_rev -map_rev.
  cbn. rewrite rev_mapi /trans_local map_map_compose map_mapi. cbn.
  rewrite mapi_cst_map. solve_all.
  eapply All_refl. intros; cbn. reflexivity.
Qed.

Lemma trans_subst_telescope p q s n Γ :
  on_free_vars_terms p s -> on_free_vars_ctx q (List.rev Γ) ->
  trans_local (subst_telescope s n Γ) = 
  subst_telescope (map trans s) n (trans_local Γ).
Proof.
  induction Γ in s, n, q|- *.
  - cbn; auto.
  - intros ons; rewrite /= on_free_vars_ctx_app => /andP[] /= ona onΓ.
    f_equal; eauto. rewrite!PCUICContextSubst.subst_telescope_cons /=.
    rewrite (trans_subst_decl p q) //. move/andP: ona. now rewrite shiftnP0.
    f_equal. rewrite mapi_rec_Sk. rewrite -(IHΓ (shiftnP 1 q)) //.
    rewrite /subst_telescope. f_equal. unfold mapi.
    apply mapi_rec_ext. intros. now rewrite Nat.add_succ_r.
Qed.

Lemma All2i_All2 {A B} {P : nat -> A -> B -> Type} {Q} n l l' :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q x y) ->
  All2 Q l l'.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma eq_annots_expand_lets_ctx (Γ : list aname) (Δ Δ' : context) :
  eq_annots Γ (expand_lets_ctx Δ Δ') <-> eq_annots Γ Δ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  etransitivity. eapply eq_annots_subst_context.
  eapply eq_annots_lift_context.
Qed.

(** We need to go through the intermediate definition which just maps the translation 
    on inductive declarations but does not perform smashing of the arguments contexts. *)

Definition map_trans_constructor_body (d : PCUICEnvironment.constructor_body) :=
  let args := trans_local d.(cstr_args) in
  let indices := map trans d.(cstr_indices) in
  {| cstr_name := d.(PCUICEnvironment.cstr_name);     
     cstr_args := args;
     cstr_indices := indices;
     cstr_type := trans d.(cstr_type);
     cstr_arity := d.(PCUICEnvironment.cstr_arity) |}.
      
Definition map_trans_one_ind_body (d : PCUICEnvironment.one_inductive_body) :=
  {| ind_name := d.(PCUICEnvironment.ind_name);
     ind_relevance := d.(PCUICEnvironment.ind_relevance);
     ind_indices := trans_local d.(PCUICEnvironment.ind_indices);
     ind_type := trans d.(PCUICEnvironment.ind_type);
     ind_sort := d.(PCUICEnvironment.ind_sort);
     ind_kelim := d.(PCUICEnvironment.ind_kelim);
     ind_ctors := List.map map_trans_constructor_body d.(PCUICEnvironment.ind_ctors);
     ind_projs := List.map (fun '(x, y) => (x, trans y)) d.(PCUICEnvironment.ind_projs) |}.

Definition map_trans_minductive_body md :=
  {| ind_finite := md.(PCUICEnvironment.ind_finite);
     ind_npars := md.(PCUICEnvironment.ind_npars);
     ind_params := trans_local md.(PCUICEnvironment.ind_params);
     ind_bodies := map map_trans_one_ind_body md.(PCUICEnvironment.ind_bodies);
     ind_universes := md.(PCUICEnvironment.ind_universes);
     ind_variance := md.(PCUICEnvironment.ind_variance)
  |}.

Lemma trans_case_branch_context {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {ci c mdecl idecl cdecl p br} {Γ : context} :
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  All2 (compare_decls eq eq) (bcontext br)	(cstr_branch_context ci mdecl cdecl) ->
  on_free_vars_terms (shiftnP #|Γ| xpred0) p.(pparams) ->
  let p' := map_predicate id trans trans (map_context trans) p in
  let br' := map_branch trans (map_context trans) br in
  trans_local (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) =
  inst_case_branch_context p' br'.
Proof.
  intros declc wfp wfbr onbctx onpars.
  intros p' br'.
  have onfvsargs : on_free_vars_ctx (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0)
  (cstr_args cdecl).
  { pose proof (declared_constructor_closed_args declc).
    now eapply closedn_ctx_on_free_vars. }
  have fvssi : on_free_vars_ctx
    (shiftnP #|ind_params mdecl| xpred0)
    (subst_context
      (inds (inductive_mind ci) (abstract_instance (ind_universes mdecl))
        (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)).
    { eapply on_free_vars_ctx_subst_context. len.
      now rewrite Nat.add_comm. eapply (inds_is_open_terms []). }
  erewrite <-(PCUICCasesContexts.inst_case_branch_context_eq
    (ind := ci) (mdecl := map_trans_minductive_body mdecl)
    (cdecl := map_trans_constructor_body cdecl)).
  rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context_gen.
  rewrite trans_local_set_binder. f_equal.
  rewrite /br' /=.
  now rewrite forget_types_map_context.
  rewrite /inst_case_context.
  rewrite (trans_subst_context (shiftnP (context_assumptions (ind_params mdecl)) xpred0) (shiftnP #|Γ| xpred0)).
  { rewrite on_free_vars_ctx_subst_instance.
    eapply (on_free_vars_ctx_cstr_branch_context (c := (ci, c)) declc). }
  rewrite [on_free_vars_terms _ _]forallb_rev //.
  rewrite map_rev. f_equal.
  rewrite /cstr_branch_context.
  rewrite trans_subst_instance_ctx.
  rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)); pcuic.
  f_equal. f_equal.
  rewrite (trans_subst_context 
    (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) xpred0) //.
  eapply (inds_is_open_terms []). 
  f_equal. rewrite trans_inds //. cbn. now len. now len.
  rewrite /br'. cbn [bcontext map_branch].
  eapply alpha_eq_trans in onbctx.
  etransitivity; tea.
  rewrite /cstr_branch_context.
  rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)) //. pcuic.
  rewrite (trans_subst_context (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) xpred0) //.
  eapply (inds_is_open_terms []). 
  rewrite trans_inds. len.
  cbn [cstr_args map_trans_constructor_body].
  cbn [ind_params map_trans_minductive_body].
  cbn [ind_universes map_trans_minductive_body].
  rewrite /inds. len. reflexivity.
Qed.
  
Theorem pcuic_expand_lets {cf} (Σ : SE.global_env_ext) Γ t T :
  wf Σ ->
  typing Σ Γ t T ->
  wf (trans_global Σ) -> 
  typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros X X0.
  revert Σ X Γ t T X0.
  apply (typing_ind_env (fun Σ Γ t T =>
    wf (trans_global Σ) ->
    TT.typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type
    (fun Σ Γ => 
    wf (trans_global Σ) ->
    TT.All_local_env (TT.lift_typing TT.typing (trans_global Σ)) (trans_local Γ))
  );intros.
  - now eapply trans_wf_local_env => //; eapply All_over_All.
  - rewrite (trans_lift _ (shiftnP #|skipn (S n) Γ| xpred0)).
    eapply closed_wf_local in wfΓ; tea.
    eapply closedn_ctx_decl in wfΓ; tea.
    move/andP: wfΓ=> /= [] _ cl.
    rewrite skipn_length. eapply nth_error_Some_length in H. lia. 
    now apply closedn_on_free_vars.
    rewrite trans_decl_type.
    eapply type_Rel; eauto.
    now apply map_nth_error.
  - econstructor; eauto.
    destruct u; auto. simpl in H |- *.
    intros l inl. now rewrite <-trans_global_ext_levels.
  - eapply TT.type_Prod;auto.
  - eapply TT.type_Lambda;eauto.
  - eapply TT.type_LetIn;eauto.
  - simpl. rewrite (trans_subst10 _ (shiftnP (S #|Γ|) xpred0) (shiftnP #|Γ| xpred0)); pcuic.
    eapply type_is_open_term in X2.
    move: X2 => /= /andP[]. rewrite shiftnP_add //.
    now eapply subject_is_open_term in X4.
    eapply type_App; tea.
  - rewrite trans_subst_instance.
    rewrite trans_cst_type.
    eapply TT.type_Const; eauto.
    + now apply trans_declared_constant.
    + now apply trans_consistent_instance_ext.
  - rewrite trans_subst_instance.
    rewrite (trans_ind_type mdecl (inductive_ind ind)).
    eapply TT.type_Ind; eauto.
    + now apply trans_declared_inductive.
    + now apply trans_consistent_instance_ext.
  - eapply (type_equality (le:=false)).
    eapply TT.type_Construct; eauto.
    + eapply trans_declared_constructor; tea. 
    + now apply trans_consistent_instance_ext.
    + epose proof (declared_constructor_inv weaken_prop _ X isdecl) as [cs [hnth onc]].
      destruct onc. red in on_ctype.
      destruct on_ctype as [s Hs].
      rewrite /type_of_constructor. forward Hs. eauto.
      exists (s@[u]). red.
      rewrite (trans_subst (shiftnP #|ind_bodies mdecl| xpred0) (shiftnP 0 xpred0)).
      pose proof (declared_constructor_closed_gen_type isdecl).
      eapply closedn_on_free_vars. len in H0. now rewrite closedn_subst_instance.
      eapply (inds_is_open_terms []).
      eapply (substitution (Γ := trans_local Γ) (Δ := []) (T:=tSort s@[u])).
      rewrite trans_inds. eapply (weaken_subslet (Γ := trans_local Γ) (Γ' := [])); pcuic.
      eapply subslet_inds. eapply (trans_declared_inductive _ _ _ _ isdecl).
      now eapply trans_consistent_instance_ext.
      rewrite trans_arities_context /=.
      rewrite -trans_subst_instance_ctx.
      eapply weaken_ctx; eauto.
      clear hnth. eapply trans_declared_constructor in isdecl.
      epose proof (typing_subst_instance_decl (trans_global Σ)
        _ _ _ _ _ _ _ (proj1 (proj1 isdecl)) Hs).
      forward X2. now eapply trans_consistent_instance_ext.
      now rewrite trans_subst_instance_ctx trans_subst_instance.
    + symmetry. cbn.
      eapply (weaken_equality (Γ := []) (trans_local Γ)).
      now eapply wf_local_closed_context in X0.
      eapply (trans_type_of_constructor isdecl).
      now eapply trans_consistent_instance_ext.
  - rewrite trans_mkApps map_app.
    simpl.
    rewrite /ptm trans_it_mkLambda_or_LetIn.
    rewrite /predctx.
    have hty := validity X7.
    eapply isType_mkApps_Ind_smash in hty as []; tea.
    erewrite <- (trans_case_predicate_context (Σ := Σ)); tea.
    2:{ eapply (wf_predicate_length_pars H0). }
    eapply TT.type_Case; auto.
    + now apply trans_declared_inductive.
    + cbn. rewrite -trans_ind_predicate_context. pcuic. pcuic.
      now eapply alpha_eq_trans.
    + now eapply trans_wf_predicate.
    + cbn. rewrite /id.
      now apply trans_consistent_instance_ext.
    + cbn [pparams pcontext].
      rewrite (trans_case_predicate_context (Σ := Σ) (Γ := Γ)); tea.
      now rewrite -trans_local_app. 
    + rewrite (trans_case_predicate_context (Σ := Σ) (Γ := Γ)); tea.
      rewrite -trans_local_app. now eapply X3.
    + rewrite <- trans_global_ext_constraints.
      eassumption.
    + move: X5 X6. cbn.
      have wfctx : wf_local Σ (Γ ,,, (ind_params mdecl,,, ind_indices idecl)@[puinst p]).
      { eapply PCUICWeakening.weaken_wf_local; tea. eapply on_minductive_wf_params_indices_inst; tea. }
      move: wfctx.
      clear -wfΣ X10.
      rewrite -map_app -[trans_local _ ++ _]trans_local_app.
      rewrite -[map _ (trans_local _)]trans_subst_instance_ctx /id.
      rewrite -[List.rev (trans_local _)]map_rev.
      generalize (pparams p ++ indices).
      change T.PCUICEnvironment.subst_instance_context with subst_instance_context.
      rewrite -/context.
      generalize (ind_params mdecl ,,, ind_indices idecl)@[puinst p] as Δ.
      intros c; revert Γ. induction c using ctx_length_rev_ind.
      * intros Γ l wf.
        intros c; depelim c. constructor.
      * intros Δ. rewrite app_context_assoc.
        rewrite List.rev_app_distr /=. 
        move=> l wfctx.
        intros H. depelim H.
        { depelim X6.
          cbn; constructor. now apply t2.
          unshelve epose proof (substitution_wf_local (Γ':=[vass na t]) _ wfctx). shelve.
          { now eapply subslet_ass_tip. }
          rewrite subst_telescope_subst_context in H.
          specialize (X (subst_context [i] 0 Γ) ltac:(now len) _ _ X0 H).
          rewrite subst_telescope_subst_context in X6.
          specialize (X X6).
          rewrite -subst_telescope_subst_context in X.
          rewrite [map trans_decl _](trans_subst_telescope (shiftnP #|Δ| xpred0) 
            (shiftnP (S #|Δ|) xpred0)) in X.
          cbn. rewrite (subject_is_open_term t0) //. rewrite List.rev_involutive.
          eapply wf_local_closed_context in wfctx.
          now move: wfctx; rewrite on_free_vars_ctx_app /= => /andP[].
          exact X. }
        { intros c; depelim c. 
          constructor. 
          destruct (wf_local_app_inv wfctx) as [w _]. depelim w.
          unshelve epose proof (substitution_wf_local (Γ':=[vdef na b t]) _ wfctx). shelve.
          { now eapply subslet_def_tip. }
          rewrite subst_telescope_subst_context in H.
          specialize (X (subst_context [b] 0 Γ) ltac:(now len) _ _ X0 H).
          rewrite subst_telescope_subst_context in c.
          specialize (X c).
          rewrite -subst_telescope_subst_context in X.
          rewrite [map trans_decl _](trans_subst_telescope (shiftnP #|Δ| xpred0) 
            (shiftnP (S #|Δ|) xpred0)) in X.
          cbn. rewrite (subject_is_open_term l1) //. rewrite List.rev_involutive.
          eapply wf_local_closed_context in wfctx.
          now move: wfctx; rewrite on_free_vars_ctx_app /= => /andP[].
          exact X. }
    + rewrite trans_mkApps map_app in X8. now eapply X8.
    + red. eapply Forall2_map_right, Forall2_map.
      eapply Forall2_All2 in H4.
      eapply All2i_All2_mix_left in X9; tea.
      eapply All2i_nth_hyp in X9.
      eapply All2_Forall2. eapply All2i_All2; tea; cbv beta.
      intros i cdecl br [hnth [wfbr [cd _]]].
      have declc : declared_constructor Σ (ci, i) mdecl idecl cdecl.
      { split; tea. }
      move: wfbr; rewrite /wf_branch /wf_branch_gen. cbn.
      apply compare_decls_eq_context in cd.
      rewrite /cstr_branch_context in cd.
      eapply trans_eq_context_gen in cd.
      eapply eq_context_gen_smash_context in cd.
      intros eqann.
      eapply (eq_annots_subst_context _ (map trans (inds (inductive_mind ci) (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl))) #|ind_params mdecl|).
      eapply (eq_annots_expand_lets_ctx _ (trans_local (ind_params mdecl))).
      rewrite -(smash_context_subst []) /= subst_context_nil.
      rewrite (expand_lets_smash_context _ []) /=. len; rewrite expand_lets_k_ctx_nil.
      rewrite (trans_expand_lets_ctx xpred0 (shiftnP #|ind_params mdecl| xpred0)) in cd. pcuic.
      { eapply on_free_vars_ctx_subst_context. len.
        apply closedn_ctx_on_free_vars.
        generalize (declared_constructor_closed_args declc).
        now rewrite Nat.add_comm.
        eapply (inds_is_open_terms []). }
      rewrite (trans_subst_context (shiftnP (#|ind_bodies mdecl| + #|ind_params mdecl|) xpred0) xpred0) in cd.
      { apply closedn_ctx_on_free_vars.
        apply (declared_constructor_closed_args declc). }
      apply (inds_is_open_terms []).
      now eapply eq_context_gen_binder_annot in cd.
    + eapply All2i_map. eapply All2i_map_right.
      eapply Forall2_All2 in H4.
      eapply All2i_nth_hyp in X9.
      eapply All2i_All2_mix_left in X9; tea.
      eapply All2i_impl ; tea.
      intros i cdecl br. cbv beta.
      set (cbt := case_branch_type _ _ _ _ _ _ _ _).
      intros (wf & hnth & eqctx & Hbctx & Hb & IHb & Hbty & IHbty).
      have declc : declared_constructor Σ (ci, i) mdecl idecl cdecl.
      { split; tea. }
      have clargs : on_free_vars_ctx (shiftnP (#|ind_params mdecl| + #|ind_bodies mdecl|) xpred0)
        (cstr_args cdecl).
      { apply closedn_ctx_on_free_vars.
        generalize (declared_constructor_closed_args declc). now rewrite Nat.add_comm. }
      split. rewrite -(trans_cstr_branch_context xpred0); auto. pcuic.
      cbn. now eapply alpha_eq_smash_context, alpha_eq_trans.
      rewrite (trans_case_predicate_context declc H1 s H0).
      intros brctxty.
      have trbr := !! (trans_case_branch_type (Γ := Γ) declc H1 H0 wf X1 eqctx).
      forward_keep trbr. 
      { eapply ctx_inst_open_terms in X5.
        eapply All_app in X5 as [].
        now eapply All_forallb, All_impl; tea. }
      forward trbr.
      { eapply subject_is_open_term in pret. move: pret.
        rewrite /predctx; len. rewrite (case_predicate_context_length_indices H0).
        now rewrite shiftnP_add. }
      rewrite -/ptm  in trbr.
      set (p' := map_predicate _ _ _ _ _) in *.
      cbv zeta in trbr.
      set (br' := trans_branch _ _) in *.
      set (cbctx := case_branch_context _ _ _ _ _) in trbr.
      set (brctxty' := case_branch_type _ _ _ _ _ _ _ _) in trbr.
      change brctxty with brctxty'. clear brctxty.
      destruct trbr as [eqbrctx' eqbrty'].
      specialize (IHb X10). specialize (IHbty X10). specialize (Hbctx X10).
      have fvs_cbctx : on_free_vars_ctx (shiftnP #|Γ| xpred0) cbctx.
      { eapply typing_closed_ctx in Hb; eauto.
        now move: Hb; rewrite on_free_vars_ctx_app => /andP[]. }
      repeat split.
      * rewrite eqbrctx'.
        rewrite trans_local_app in Hbctx.
        eapply wf_local_smash_end in Hbctx.
        rewrite (trans_smash_context (shiftnP #|Γ| xpred0)) //.
      * rewrite eqbrctx' eqbrty'.
        rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
        eapply subject_is_open_term in Hbty.
        move: Hbty. rewrite /cbt. len.
        now rewrite shiftnP_add.
        rewrite (trans_smash_context (shiftnP #|Γ| xpred0)) //.
        assert (bbody br' = expand_lets (trans_local cbctx) (trans (bbody br))) as ->.
        { rewrite /br' /trans_branch; cbn [bbody].
          rewrite -/(inst_case_context (pparams p') (puinst p') _).
          cbn -[inst_case_context expand_lets].
          f_equal. rewrite /cbctx.
          rewrite (trans_case_branch_context (Γ := Γ) declc) //. }   
        eapply (typing_expand_lets (Σ := trans_global Σ)).
        now rewrite trans_local_app in IHb.
      * rewrite eqbrctx' eqbrty'.
        rewrite (trans_expand_lets (shiftnP #|Γ| xpred0)) //.
        eapply subject_is_open_term in Hbty.
        move: Hbty. rewrite /cbt. len.
        now rewrite shiftnP_add.
        rewrite (trans_smash_context (shiftnP #|Γ| xpred0)) //.
        eapply (typing_expand_lets (Σ := trans_global Σ) _ _ _ (tSort ps)).
        now rewrite trans_local_app in IHbty.

  - rewrite (trans_subst (shiftnP #|projection_context p.1.1 mdecl idecl u| xpred0) (shiftnP #|Γ| xpred0)).
    { rewrite /projection_context /=; len. cbn.
      destruct (declared_projection_type_and_eq _ isdecl) as [[] ?].
      eapply isType_is_open_term in i. cbn in i; len in i.
      rewrite on_free_vars_subst_instance //. }
    { generalize (subject_is_open_term X1). move/type_is_open_term: X1.
      now rewrite on_free_vars_mkApps /= forallb_rev => -> ->. }
    rewrite trans_subst_instance /= map_rev.
    change (trans ty) with ((on_snd trans pdecl).2).
    eapply type_Proj.
    + now apply trans_declared_projection.
    + rewrite trans_mkApps in X2; eauto.
    + rewrite map_length H. now destruct mdecl.
  - rewrite trans_dtype /=.
    assert (is_open_term Γ (tFix mfix n)).
    { eapply (subject_is_open_term (Σ := Σ)). econstructor; tea. solve_all.
      destruct a as [s Hs]. exists s; intuition eauto.
      solve_all. }
    eapply TT.type_Fix; auto.
    + now rewrite fix_guard_trans.
    + erewrite map_nth_error. 
      2: apply H0.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + eapply All_map, (All_impl X0).
      intuition auto. destruct X as [s [? ?]].
      exists s; intuition auto.
    + fold trans.
      subst types.
      eapply All_map.
      eapply All_prod in X0; tea. clear X1.
      eapply All_impl; tea. intros d [[Hdb IHdb] [hs [hdty ihdty]]].
      len. rewrite -(trans_fix_context _ _ _ H2).
      rewrite -trans_local_app.
      rewrite (trans_lift _ (shiftnP #|Γ| xpred0)) in IHdb.
      eapply (subject_is_open_term (Σ := Σ)); tea.
      len in IHdb. eauto.
    + rewrite (trans_wf_fixpoint _ (shiftnP #|Γ| xpred0) #|mfix|) //.

  - rewrite trans_dtype. simpl.
    assert (is_open_term Γ (tCoFix mfix n)).
    { eapply (subject_is_open_term (Σ := Σ)). econstructor; tea. solve_all.
      destruct a as [s Hs]. exists s; intuition eauto.
      solve_all. }
    eapply TT.type_CoFix; auto.
    + now eapply cofix_guard_trans.
    + erewrite map_nth_error. 
      2: eassumption.
      destruct decl.
      unfold map_def.
      reflexivity.
    + rewrite /trans_local map_app in X.
      now eapply TT.All_local_env_app_inv in X as [].
    + fold trans.
      eapply All_map, (All_impl X0).
      intros x [s ?]; exists s; intuition auto.
    + fold trans;subst types.        
      eapply All_map.
      eapply All_prod in X0; tea. clear X1.
      eapply All_impl; tea. intros d [[Hdb IHdb] [hs [hdty ihdty]]].
      len. rewrite -(trans_fix_context _ _ _ H2). exact 0.
      rewrite -trans_local_app.
      rewrite (trans_lift _ (shiftnP #|Γ| xpred0)) in IHdb.
      eapply (subject_is_open_term (Σ := Σ)); tea.
      len in IHdb. eauto.
    + rewrite trans_wf_cofixpoint //.
  - eapply (type_equality (le:=true)).
    + eauto.
    + now exists s.
    + eapply cumul_decorate in X4; tea.
      2:eapply validity; tea.
      2:now exists s.
      eapply into_equality.
      eapply (trans_cumul (Σ := Σ)); eauto.
      fvs. specialize (X1 X5).
      now eapply type_is_open_term in X1.
      now eapply subject_is_open_term in X3.
Qed.

Print Assumptions pcuic_expand_lets.
