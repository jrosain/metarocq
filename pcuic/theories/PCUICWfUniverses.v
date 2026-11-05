(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICSigmaCalculus PCUICTyping PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICUnivSubst PCUICUnivSubstitutionConv.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

From MetaRocq.PCUIC Require Import PCUICInduction.

Lemma test_primu_mapu {term term'} pu pt fu (ft : term -> term') p :
  test_primu pu pt (mapu_prim fu ft p) =
  test_primu (pu ∘ fu) (pt ∘ ft) p.
Proof.
  destruct p as [? []] => //=. cbn.
  now rewrite forallb_map.
Qed.

Lemma test_primu_primProp {term} P pu (pt : term -> bool) pu' (pt' : term -> bool) p :
  tPrimProp P p ->
  (forall x, pu x = pu' x) ->
  (forall x, P x -> pt x = pt' x) ->
  test_primu pu pt p = test_primu pu' pt' p.
Proof.
  destruct p as [? []] => //=. cbn.
  intuition eauto. do 3 f_equal; eauto.
  solve_all.
Qed.

Section CheckerFlags.
  Context {cf:checker_flags}.

  Lemma wf_univ_type0 Σ : wf_univ Σ Universe.type0.
  Proof using Type.
    simpl.
    intros l hin%LevelExprSet.singleton_spec.
    subst l. simpl.
    apply global_ext_levels_InSet.
  Qed.

  Lemma wf_univ_type1 Σ : wf_univ Σ Universe.type1.
  Proof using Type.
    simpl.
    intros l hin%LevelExprSet.singleton_spec.
    subst l. simpl.
    apply global_ext_levels_InSet.
  Qed.

  Lemma wf_univ_super {Σ u} : wf_univ Σ u -> wf_univ Σ (Universe.super u).
  Proof using Type.
    destruct u as [[| |] u]; cbn.
    1-2:intros _ l hin%LevelExprSet.singleton_spec; subst l; apply wf_univ_type1;
     now apply LevelExprSet.singleton_spec.
    intros Hl.
    intros l hin.
    eapply Universes.spec_map_succ in hin as [x' [int ->]].
    simpl. now specialize (Hl _ int).
  Qed.

  Lemma wf_univ_sup {Σ u u'} : wf_univ Σ u -> wf_univ Σ u' ->
    wf_univ Σ (Universe.sup u u').
  Proof using Type.
    destruct u as [[| |] u], u' as [[| |] u']; cbn; auto.
    all: unfold wf_univ; cbn.
    all: try (intros ??; apply wf_ulvl_type0).
    intros Hu Hu' l [Hl|Hl]%LevelExprSet.union_spec.
    now apply (Hu _ Hl).
    now apply (Hu' _ Hl).
  Qed.

  Lemma wf_univ_product {Σ s s'} : wf_univ Σ s -> wf_univ Σ s' ->
    wf_univ Σ (Universe.univ_of_product s s').
  Proof using Type.
    intros Hu Hu'.
    destruct s' as [[| |] u'] => //=.
    now apply wf_univ_sup.
  Qed.

  Lemma wf_univ_wf_ulvl {Σ u} :
    wf_univ Σ u -> wf_ulvl Σ (ulvl u).
  Proof. by intro. Qed.

  Hint Resolve wf_univ_type1 wf_univ_super wf_univ_sup wf_univ_product wf_univ_wf_ulvl : pcuic.


  Definition wf_levelb Σ l :=
    LevelSet.mem l (global_ext_levels Σ).

  Definition wf_level Σ l :=
    LevelSet.In l (global_ext_levels Σ).

  Definition wf_instance Σ u :=
    Forall (wf_level Σ) u.

  Definition wf_instanceb Σ u :=
    forallb (wf_levelb Σ) u.

  Lemma wf_levelP {Σ l} : reflect (wf_level Σ l) (wf_levelb Σ l).
  Proof using Type.
    unfold wf_level, wf_levelb.
    destruct LevelSet.mem eqn:ls; constructor.
    now apply LevelSet.mem_spec in ls.
    intros hin.
    now apply LevelSet.mem_spec in hin.
  Qed.

  Lemma wf_instanceP {Σ u} : reflect (wf_instance Σ u) (wf_instanceb Σ u).
  Proof using Type.
    unfold wf_instance, wf_instanceb.
    apply forallbP. intros x; apply wf_levelP.
  Qed.

  Lemma wf_ulvl_subst_instance_univ_lvl (Σ : global_env_ext) ulvls ui u :
    wf Σ ->
    wf_ulvl Σ u ->
    wf_instance (Σ.1, ulvls) ui ->
    wf_ulvl (Σ.1, ulvls) (subst_instance ui u).
  Proof using Type.
    intros wfΣ Hl Hu e [[l n] [inl ->]]%In_subst_instance.
    destruct l as [|s|n']; simpl; auto.
    - apply global_ext_levels_InSet.
    - specialize (Hl (Level.level s, n) inl).
      simpl in Hl.
      apply monomorphic_level_in_global_ext in Hl.
      eapply LS.union_spec. now right.
    - specialize (Hl (Level.lvar n', n) inl).
      eapply LS.union_spec in Hl as [Hl|Hl].
      + red in Hu.
        unfold levels_of_udecl in Hl.
        destruct Σ.2.
        * simpl in Hu. simpl in *.
          unfold subst_instance; simpl.
          destruct nth_error eqn:hnth; simpl.
          eapply nth_error_forall in Hu; eauto.
          apply global_ext_levels_InSet.
        * unfold subst_instance. simpl.
          destruct (nth_error ui n') eqn:hnth.
          2:{ simpl. rewrite hnth. apply global_ext_levels_InSet. }
          eapply nth_error_forall in Hu. 2:eauto.
          change (nth_error ui n') with (nth_error ui n') in *.
          rewrite -> hnth. simpl. apply Hu.
      + now apply not_var_global_levels in Hl.
  Qed.

  Lemma wf_univ_subst_instance_univ (Σ : global_env_ext) ulvls u s :
    wf Σ ->
    wf_univ Σ s ->
    wf_instance (Σ.1, ulvls) u ->
    wf_univ (Σ.1, ulvls) (subst_instance u s).
  Proof using Type.
    destruct s as [[| |] t]; cbnr.
    all: apply wf_ulvl_subst_instance_univ_lvl.
  Qed.

  Lemma wf_univ_instantiate Σ ulvls s u φ :
    wf Σ ->
    wf_univ (Σ, ulvls) s ->
    wf_instance (Σ, φ) u ->
    wf_univ (Σ, φ) (subst_instance_univ u s).
  Proof using Type.
    intros wfΣ Hs.
    apply (wf_univ_subst_instance_univ (Σ, ulvls) φ); auto.
  Qed.

  Lemma subst_instance_empty u :
    forallb (fun x => ~~ Level.is_var x) u ->
    subst_instance [] u = u.
  Proof using Type.
    induction u; simpl; intros Hu; auto.
    rewrite subst_instance_cons.
    move/andP: Hu => [] isv Hf.
    rewrite IHu //.
    now destruct a => /= //; auto.
  Qed.

  Lemma wf_level_mono Σ u :
    wf Σ ->
    on_udecl_prop Σ (Monomorphic_ctx) ->
    Forall (wf_level (Σ, Monomorphic_ctx)) u ->
    forallb (fun x => ~~ Level.is_var x) u.
  Proof using Type.
    intros wf uprop.
    induction 1 => /= //.
    destruct x eqn:isv => /= //.
    apply LS.union_spec in H as [H|H]; simpl in H.
    epose proof (@udecl_prop_in_var_poly _ (Σ, _) _ uprop H) as [ctx' eq].
    discriminate.
    now pose proof (not_var_global_levels wf _ H).
  Qed.

  Lemma wf_level_sub Σ univs u :
    wf_level (Σ, Monomorphic_ctx) u ->
    wf_level (Σ, univs) u.
  Proof using cf.
    intros wfx.
    red in wfx |- *.
    eapply LevelSet.union_spec in wfx; simpl in *.
    destruct wfx as [wfx|wfx]. lsets.
    eapply LevelSet.union_spec. now right.
  Qed.

  Lemma wf_instance_sub Σ univs u :
    wf_instance (Σ, Monomorphic_ctx) u ->
    wf_instance (Σ, univs) u.
  Proof using cf.
    intros wfu.
    red in wfu |- *.
    eapply Forall_impl; eauto.
    intros. red in H. cbn in H. eapply wf_level_sub; eauto.
  Qed.

  Lemma In_Level_global_ext_poly s Σ cst :
    LS.In (Level.level s) (global_ext_levels (Σ, Polymorphic_ctx cst)) ->
    LS.In (Level.level s) (global_levels Σ).
  Proof using Type.
    intros [hin|hin]%LS.union_spec.
    simpl in hin.
    now apply monomorphic_level_notin_AUContext in hin.
    apply hin.
  Qed.

  Lemma Forall_In (A : Type) (P : A -> Prop) (l : list A) :
    Forall P l -> (forall x : A, In x l -> P x).
  Proof using Type.
    induction 1; simpl; auto.
    intros x' [->|inx]; auto.
  Qed.

  Lemma wf_instance_In {Σ u} : wf_instance Σ u <->
    (forall l, In l u -> LS.In l (global_ext_levels Σ)).
  Proof using Type.
    unfold wf_instance.
    split; intros. eapply Forall_In in H; eauto.
    apply In_Forall. auto.
  Qed.

  Lemma in_subst_instance l u u' :
    In l (subst_instance u u') ->
    In l u \/ In l u' \/ l = Level.lzero.
  Proof using Type.
    induction u'; simpl; auto.
    intros [].
    destruct a; simpl in *; subst; auto.
    destruct (nth_in_or_default n u Level.lzero); auto.
    specialize (IHu' H). intuition auto.
  Qed.

  Lemma wf_instance_subst_instance Σ univs u u' φ :
    wf Σ ->
    on_udecl_prop Σ univs ->
    wf_instance (Σ, univs) u' ->
    wf_instance (Σ, φ) u ->
    wf_instance (Σ, φ) (subst_instance u u').
  Proof using Type.
    intros wfΣ onup Hs cu.
    destruct univs.
    - red in Hs |- *.
      unshelve epose proof (wf_level_mono _ _ _ _ Hs); eauto.
      eapply forallb_Forall in H. apply Forall_map.
      solve_all. destruct x; simpl => //.
      red. apply global_ext_levels_InSet.
      eapply wf_level_sub; eauto.
    - clear onup.
      red in Hs |- *.
      eapply Forall_map, Forall_impl; eauto.
      intros x wfx.
      red in wfx. destruct x => /= //.
      { red. apply global_ext_levels_InSet. }
      eapply In_Level_global_ext_poly in wfx.
      apply LS.union_spec; now right.
      eapply in_var_global_ext in wfx; simpl in wfx; auto.
      unfold AUContext.levels, AUContext.repr in wfx.
      destruct cst as [? cst].
      rewrite mapi_unfold in wfx.
      eapply (proj1 (LevelSetProp.of_list_1 _ _)) in wfx.
      apply SetoidList.InA_alt in wfx as [? [<- wfx]]. simpl in wfx.
      eapply In_unfold_inj in wfx; [|congruence].
      destruct (nth_in_or_default n u (Level.lzero)).
      red in cu. eapply Forall_In in cu; eauto. rewrite e.
      red. apply global_ext_levels_InSet.
  Qed.

  Section WfUlvls.
    Context (Σ : global_env_ext).

    Definition wf_ulvlb (u : UnivLvl.t) : bool :=
      LevelExprSet.for_all (fun l => LevelSet.mem (LevelExpr.get_level l) (global_ext_levels Σ)) u.

    Lemma wf_ulvl_reflect {u : UnivLvl.t} :
      reflect (wf_ulvl Σ u) (wf_ulvlb u).
    Proof using Type.
      eapply iff_reflect.
      rewrite LevelExprSet.for_all_spec.
      split; intros.
      - intros l Hl; specialize (H l Hl).
        now eapply LS.mem_spec.
      - intros l Hl. specialize (H l Hl).
        now eapply LS.mem_spec in H.
    Qed.

    Fixpoint on_ulvls fu fc t :=
      match t with
      | tUniv s => fu (ulvl s)
      | tApp t u
      | tProd _ t u
      | tLambda _ t u => on_ulvls fu fc t && on_ulvls fu fc u
      | tCase _ p c brs =>
        [&&
        forallb fu (map UnivLvl.make' p.(puinst)) ,
        forallb (on_ulvls fu fc) p.(pparams) ,
        test_context (fc #|p.(puinst)|) p.(pcontext) ,
        on_ulvls fu fc p.(preturn) ,
        on_ulvls fu fc c &
        forallb (test_branch (fc #|p.(puinst)|) (on_ulvls fu fc)) brs ]
      | tLetIn _ t t' u =>
        [&& on_ulvls fu fc t , on_ulvls fu fc t' & on_ulvls fu fc u]
      | tProj _ t => on_ulvls fu fc t
      | tFix mfix _ | tCoFix mfix _ =>
        forallb (fun d => on_ulvls fu fc d.(dtype) && on_ulvls fu fc d.(dbody)) mfix
      | tConst _ u | tInd _ u | tConstruct _ _ u =>
          forallb fu (map UnivLvl.make' u)
      | tEvar _ args => forallb (on_ulvls fu fc) args
      | tPrim p => test_primu (fun x => fu (UnivLvl.make' x)) (on_ulvls fu fc) p
      | _ => true
      end.

    Definition wf_ulvls t := on_ulvls wf_ulvlb closedu t.
    Definition wf_univb (s : Universe.t) := wf_ulvlb (ulvl s).

    Lemma wf_univ_reflect {s : Universe.t} :
      reflect (wf_univ Σ s) (wf_univb s).
    Proof using Type.
      destruct s as [[| |] u] => //=; repeat constructor; cbn;apply wf_ulvl_reflect.
    Qed.

    Lemma wf_ulvlb_instance_forall u :
      forallb wf_ulvlb (map UnivLvl.make' u) = wf_instanceb Σ u.
    Proof using Type.
      induction u => //=.
      rewrite IHu.
      f_equal.
      cbn.
      now rewrite if_true_false.
    Qed.

    (* Lemma All_forallb {A} (P : A -> Type) l (H : All P l) p p' : (forall x, P x -> p x = p' x) -> forallb p l = forallb p' l.
    Proof.
      intros; induction H; simpl; auto.
      now rewrite IHAll H0.
    Qed. *)

    Lemma test_context_mapi (p : term -> bool) f (ctx : context) k :
  test_context p (mapi_context (shiftf f k) ctx) = test_context_k (fun k => p ∘ f k) k ctx.
Proof using Type.
  induction ctx; simpl; auto.
  rewrite IHctx. f_equal.
  now rewrite test_decl_map_decl.
Qed.
Hint Rewrite test_context_mapi : map.

Lemma test_context_k_ctx (p : term -> bool) (ctx : context) k :
  test_context p ctx = test_context_k (fun k => p) k ctx.
Proof using Type.
  induction ctx; simpl; auto.
Qed.

    Lemma on_ulvls_lift pu pc n k t : on_ulvls pu pc (lift n k t) = on_ulvls pu pc t.
    Proof using Type.
      induction t in n, k |- * using term_forall_list_ind; simpl ; auto ; try
        rewrite ?IHt1 ?IHt2 ?IHt3; auto.
      - solve_all.
      - destruct X as [? [? ?]]. solve_all.
        rewrite IHt.
        f_equal.
        f_equal ; [now solve_all|..].
        f_equal.
        f_equal ; [now rewrite /id e|..].
        f_equal.
        solve_all.
        rewrite /test_branch. rewrite b. f_equal.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite test_primu_mapu; eapply test_primu_primProp; tea; eauto.
    Qed.

    Corollary wf_ulvls_lift n k t : wf_ulvls (lift n k t) = wf_ulvls t.
    Proof using Type.
      by apply on_ulvls_lift.
    Qed.

    Lemma on_ulvls_subst s k pu pc t :
      All (on_ulvls pu pc) s ->
      on_ulvls pu pc (subst s k t) = on_ulvls pu pc t.
    Proof using Type.
      intros Hs.
      induction t in k |- * using term_forall_list_ind; simpl; auto; try
        rewrite ?IHt1 ?IHt2 ?IHt3; auto.
      - destruct (Nat.leb_spec k n); auto.
        destruct nth_error eqn:nth; simpl; auto.
        eapply nth_error_all in nth; eauto.
        simpl in nth. intros. now rewrite on_ulvls_lift.
      - solve_all.
      - destruct X as [? [? ?]]. solve_all.
        rewrite IHt.
        f_equal.
        f_equal ; [now solve_all|..].
        f_equal.
        f_equal ; [now rewrite /id e|..].
        f_equal.
        solve_all.
        rewrite /test_branch. rewrite b. f_equal.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite forallb_map.
        eapply All_forallb_eq_forallb; eauto. simpl; intros [].
        simpl. intros. cbn. now rewrite H.
      - rewrite test_primu_mapu; eapply test_primu_primProp; tea; eauto.
    Qed.

    Corollary wf_ulvls_subst s k t :
      All wf_ulvls s ->
      wf_ulvls (subst s k t) = wf_ulvls t.
    Proof using Type.
      by apply on_ulvls_subst.
    Qed.

  End WfUlvls.
  Arguments wf_ulvl_reflect {Σ u}.

  Ltac to_prop :=
    repeat match goal with
    | [ H: is_true (?x && ?y) |- _ ] =>
     let x := fresh in let y := fresh in move/andP: H; move=> [x y]; rewrite ?x ?y; simpl
    end.

  Ltac to_wfu :=
    repeat match goal with
    | [ H: is_true (wf_ulvlb _ ?x) |- _ ] => apply (elimT (@wf_ulvl_reflect _ x)) in H
    | [ |- is_true (wf_ulvlb _ ?x) ] => apply (introT (@wf_ulvl_reflect _ x))
    | [ H: is_true (wf_univb _ ?x) |- _ ] => apply (elimT (@wf_univ_reflect _ x)) in H
    | [ |- is_true (wf_univb _ ?x) ] => apply (introT (@wf_univ_reflect _ x))
    end.

  Lemma wf_ulvls_inst {Σ : global_env_ext} univs t u :
    wf Σ ->
    on_udecl_prop Σ.1 univs ->
    wf_instance Σ u  ->
    wf_ulvls (Σ.1, univs) t ->
    wf_ulvls Σ (subst_instance u t).
  Proof using Type.
    intros wfΣ onudecl cu wft.
    induction t using term_forall_list_ind; simpl in *; auto; try to_prop;
      try apply /andP; intuition eauto 4.

    all:cbn -[UnivLvl.make'] in * ; to_wfu; autorewrite with map; repeat (f_equal; solve_all).

    - destruct Σ as [Σ univs']. simpl in *.
      eapply (wf_univ_subst_instance_univ (Σ, univs)); auto.

    - apply forallb_All.
      rewrite -forallb_map wf_ulvlb_instance_forall.
      apply All_forallb in wft.
      rewrite -forallb_map wf_ulvlb_instance_forall in wft.
      apply/wf_instanceP.
      eapply wf_instance_subst_instance; eauto.
      destruct Σ; simpl in *.
      now move/wf_instanceP: wft.
    - apply forallb_All.
      rewrite -forallb_map wf_ulvlb_instance_forall.
      apply All_forallb in wft.
      rewrite -forallb_map wf_ulvlb_instance_forall in wft.
      apply/wf_instanceP.
      eapply wf_instance_subst_instance; eauto.
      destruct Σ; simpl in *.
      now move/wf_instanceP: wft.
    - apply forallb_All.
      rewrite -forallb_map wf_ulvlb_instance_forall.
      apply All_forallb in wft.
      rewrite -forallb_map wf_ulvlb_instance_forall in wft.
      apply/wf_instanceP.
      eapply wf_instance_subst_instance; eauto.
      destruct Σ; simpl in *.
      now move/wf_instanceP: wft.

    - apply forallb_All.
      rewrite -forallb_map wf_ulvlb_instance_forall.
      apply All_forallb in H.
      rewrite -forallb_map wf_ulvlb_instance_forall in H.
      apply/wf_instanceP.
      eapply wf_instance_subst_instance; eauto.
      destruct Σ ; simpl in *.
      now move/wf_instanceP: H.

    - now len.
    - rewrite /test_branch. rtoProp.
      move/andP: a => [] tctx wfu.
      split; auto. simpl.
      solve_all. now len.
    - rewrite -subst_instance_ulvl_make. to_wfu.
      eapply (wf_ulvl_subst_instance_univ_lvl (Σ.1, univs)) => //.
  Qed.

  Lemma weaken_wf_ulvl Σ Σ' t : wf Σ' -> extends Σ.1 Σ' ->
    wf_ulvl Σ t ->
    wf_ulvl (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ ext.
    intros Hl l inl; specialize (Hl l inl).
    apply LS.union_spec. apply LS.union_spec in Hl as [Hl|Hl]; simpl.
    left; auto.
    right. now eapply global_levels_sub; [apply ext|].
  Qed.

  Lemma weaken_wf_level {Σ : global_env_ext} Σ' t : wf Σ -> wf Σ' -> extends Σ Σ' ->
    wf_level Σ t ->
    wf_level (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    unfold wf_level.
    destruct t; simpl; auto using global_ext_levels_InSet;
    intros; apply LS.union_spec.
    - eapply LS.union_spec in H as [H|H].
      left; auto.
      right; auto. simpl.
      eapply global_levels_sub. apply ext. apply H.
    - cbn. eapply in_var_global_ext in H; eauto.
  Qed.

  Lemma weaken_wf_instance {Σ : global_env_ext} Σ' t : wf Σ -> wf Σ' -> extends Σ.1 Σ' ->
    wf_instance Σ t ->
    wf_instance (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    unfold wf_instance.
    intros H; eapply Forall_impl; eauto.
    intros. now eapply weaken_wf_level.
  Qed.

  Arguments UnivLvl.make' : simpl never.
  Lemma test_primu_test_primu_tPrimProp {P : term -> Type} {pu put} {pu' : Level.t -> bool} {put' : term -> bool} p :
    tPrimProp P p -> test_primu pu put p ->
    (forall u, pu u -> pu' u) ->
    (forall t, P t -> put t -> put' t) ->
    test_primu pu' put' p.
  Proof.
    intros hp ht hf hg.
    destruct p as [? []]; cbn => //.
    destruct a; destruct hp; cbn in *.
    rtoProp. destruct p0. intuition eauto.
    eapply forallb_All in H2. eapply All_prod in a; tea.
    eapply All_forallb, All_impl; tea. intuition eauto. apply hg; intuition auto.
  Qed.

  Lemma weaken_wf_ulvls {Σ : global_env_ext} Σ' t : wf Σ -> wf Σ' -> extends Σ.1 Σ' ->
    wf_ulvls Σ t ->
    wf_ulvls (Σ', Σ.2) t.
  Proof using Type.
    intros wfΣ wfΣ' ext.
    induction t using term_forall_list_ind; cbn in *; auto; intros; to_prop;
    try apply /andP; to_wfu; intuition eauto 4.

  - solve_all.
  - move: H. destruct s => //=.
    now apply weaken_wf_ulvl.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_ulvl_reflect /weaken_wf_ulvl /wf_ulvl_reflect.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_ulvl_reflect /weaken_wf_ulvl /wf_ulvl_reflect.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_ulvl_reflect /weaken_wf_ulvl /wf_ulvl_reflect.
  - eapply forallb_impl ; tea.
    now move => ? _ /wf_ulvl_reflect /weaken_wf_ulvl /wf_ulvl_reflect.
  - red in X.
    solve_all.
    rewrite /test_branch in b |- *.
    rtoProp.
    intuition.
  - red in X; solve_all.
  - red in X. solve_all.
  - eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
    intros; to_wfu; now eapply weaken_wf_ulvl.
  Qed.

  Lemma wf_ulvls_weaken_full :
    weaken_env_prop_full cumulSpec0 (lift_typing typing)
      (fun Σ _ t T => wf_ulvls Σ t && wf_ulvls Σ T).
  Proof using Type.
    do 2 red. intros.
    to_prop; apply /andP; split; now apply weaken_wf_ulvls.
  Qed.

  Lemma wf_ulvls_weaken :
    weaken_env_prop cumulSpec0 (lift_typing typing)
      (fun Σ _ j => option_default (wf_ulvls Σ) (j_term j) true && wf_ulvls Σ (j_typ j) && option_default (wf_univb Σ) (j_univ j) true).
  Proof using Type.
    intros Σ Σ' φ wfΣ wfΣ' Hext _ j Hj.
    pose proof (fun t => @weaken_wf_ulvls (Σ, φ) Σ' t wfΣ wfΣ' Hext).
    rtoProp; repeat split; auto.
    1: destruct j_term => //; cbn in *; auto.
    1: destruct j_univ => //; cbn in *; now apply (H (tUniv _)).
  Qed.

  Lemma wf_ulvls_inds Σ mind u bodies :
    wf_instance Σ u ->
    All (fun t : term => wf_ulvls Σ t) (inds mind u bodies).
  Proof using Type.
    intros wfu.
    unfold inds.
    generalize #|bodies|.
    induction n; simpl; auto.
    constructor; auto.
    cbn.
    rewrite wf_ulvlb_instance_forall.
    now apply /wf_instanceP.
  Qed.

  Lemma wf_ulvls_mkApps Σ f args :
    wf_ulvls Σ (mkApps f args) = wf_ulvls Σ f && forallb (wf_ulvls Σ) args.
  Proof using Type.
    induction args using rev_ind; simpl; auto. now rewrite andb_true_r.
    now rewrite mkApps_app forallb_app /= andb_true_r andb_assoc -IHargs.
  Qed.

  Lemma type_local_ctx_wf Σ Γ Δ s : type_local_ctx (fun Σ _ => lift_wf_term (fun t => wf_ulvls Σ t)) Σ Γ Δ s ->
      All (fun d => option_default (wf_ulvls Σ) (decl_body d) true && wf_ulvls Σ (decl_type d)) Δ.
  Proof using Type.
    induction Δ as [|[na [b|] ty] ?]; simpl.
    1: constructor.
    all: intros [X [Hb Ht]]; constructor; cbn; auto.
  Qed.

  Lemma consistent_instance_ext_wf Σ univs u : consistent_instance_ext Σ univs u ->
    wf_instance Σ u.
  Proof using Type.
    destruct univs; simpl.
    - destruct u => // /=.
      intros _. constructor.
    - intros [H%forallb_Forall [H' H'']].
      eapply Forall_impl; eauto.
      simpl; intros. now eapply LS.mem_spec in H0.
  Qed.

  Ltac specIH :=
    repeat match goal with
    | [ H : on_udecl _ _, H' : on_udecl _ _ -> _ |- _ ] => specialize (H' H)
    end.

  Local Lemma wf_ulvls_local_ctx_smash (Σ : global_env_ext) mdecl args univs :
    univs_local_ctx (fun Σ _ => lift_wfbu_term (fun t => wf_ulvls Σ t) (wf_univb Σ))
      (Σ.1, ind_ulvls mdecl) (arities_context (ind_bodies mdecl),,, ind_params mdecl) args univs ->
    univs_local_ctx (fun Σ _ => lift_wfbu_term (fun t => wf_ulvls Σ t) (wf_univb Σ))
      (Σ.1, ind_ulvls mdecl) (arities_context (ind_bodies mdecl),,, ind_params mdecl) (smash_context [] args) univs.
  Proof using Type.
    induction args as [|[na [b|] ty] args] in univs |- *; simpl; auto.
    intros [X Hj].
    rewrite subst_context_nil. auto.
    destruct univs as [|u]; auto.
    intros [X Hj].
    rewrite smash_context_acc /=. split. eauto.
    apply lift_wfbu_term_f_impl with (f := fun t => _ (_ t)) (1 := Hj) (fu := id) => // t Ht.
    rewrite wf_ulvls_subst.
    clear -X. generalize 0.
    induction args as [|[na [b|] ty] args] in univs, X |- *; simpl in *; auto.
    - destruct X as [? Hj].
      constructor; eauto.
      rewrite wf_ulvls_subst. eapply IHargs; eauto.
      move: Hj => /andP[] /andP[] /= Htm _ _.
      now rewrite wf_ulvls_lift.
    - destruct univs => //. destruct X.
      constructor => //. eapply IHargs; eauto.
    - now rewrite wf_ulvls_lift.
  Qed.

  Lemma wf_ulvls_local_ctx_nth_error Σ P Pu Γ Δ s n d :
    univs_local_ctx (fun Σ _ => lift_wfbu_term (P Σ) (Pu Σ)) Σ Γ Δ s ->
    nth_error Δ n = Some d ->
    P Σ (decl_type d).
  Proof using Type.
    induction Δ as [|[na [b|] ty] Δ] in n, s |- *; simpl; auto.
    - now rewrite nth_error_nil.
    - move => [] h /andP[] /andP[] _ h' _.
      destruct n. simpl. move=> [= <-] //=.
      now simpl; eapply IHΔ.
    - destruct s => //. move => [] h /andP[] /andP[] _ h' _.
      destruct n. simpl. move=> [= <-] //=.
      now simpl; eapply IHΔ.
  Qed.

  Lemma In_unfold_var x n : In x (unfold n Level.lvar) <-> exists k, k < n /\ (x = Level.lvar k).
  Proof using Type.
    split.
    - induction n => /= //.
      intros [hin|hin]%in_app_or.
      destruct (IHn hin) as [k [lt eq]].
      exists k; auto.
      destruct hin => //. subst x.
      eexists; eauto.
    - intros [k [lt ->]].
      induction n in k, lt |- *. lia.
      simpl. apply in_or_app.
      destruct (lt_dec k n). left; auto.
      right. left. f_equal. lia.
  Qed.

  Lemma wf_abstract_instance Σ decl :
    wf_instance (Σ, decl) (abstract_instance decl).
  Proof using Type.
    destruct decl as [|[u cst]]=> /=.
    red. constructor.
    rewrite /UContext.instance /AUContext.repr /=.
    rewrite mapi_unfold.
    red. eapply In_Forall.
    intros x hin. eapply In_unfold_var in hin as [k [lt eq]].
    subst x. red.
    eapply LS.union_spec; left. simpl.
    rewrite /AUContext.levels /= mapi_unfold.
    eapply (proj2 (LevelSetProp.of_list_1 _ _)).
    apply SetoidList.InA_alt. eexists; split; eauto.
    eapply In_unfold_var. exists k; split; eauto.
  Qed.

  Definition on_decl_ulvls (fu : UnivLvl.t -> bool) (fc : nat -> term -> bool) d :=
      option_default (on_ulvls fu fc) d.(decl_body) true &&
      on_ulvls fu fc d.(decl_type).

  Definition wf_decl_ulvls Σ := on_decl_ulvls (wf_ulvlb Σ) closedu.

  Definition on_ctx_ulvls (fu : UnivLvl.t -> bool) (fc : nat -> term -> bool) Γ :=
    forallb (on_decl_ulvls fu fc) Γ.

  Definition wf_ctx_ulvls Σ Γ :=
    forallb (wf_decl_ulvls Σ) Γ.

  Lemma wf_ulvls_it_mkProd_or_LetIn {Σ Γ T} :
    wf_ulvls Σ (it_mkProd_or_LetIn Γ T) = wf_ctx_ulvls Σ Γ && wf_ulvls Σ T.
  Proof using Type.
    induction Γ as [ |[na [b|] ty] Γ] using rev_ind ; simpl; auto;
    rewrite it_mkProd_or_LetIn_app {1}/wf_ulvls /=
    -!/(wf_ulvls _ _) IHΓ /wf_ctx_ulvls forallb_app /=
    {3}/wf_decl_ulvls -!/(wf_ulvls _ _) / on_decl_ulvls /= /wf_ulvls;
    repeat bool_congr.

  Qed.

  Lemma wf_ulvls_it_mkLambda_or_LetIn {Σ Γ T} :
    wf_ulvls Σ (it_mkLambda_or_LetIn Γ T) = test_context (wf_ulvls Σ) Γ && wf_ulvls Σ T.
  Proof using Type.
    induction Γ as [ |[na [b|] ty] Γ] using rev_ind; simpl; auto;
    now rewrite it_mkLambda_or_LetIn_app {1}/wf_ulvls
      /= -!/(wf_ulvls _ _) IHΓ test_context_app /= /test_decl /= ;
    repeat bool_congr.
  Qed.

  Lemma wf_projs Σ ind npars p :
    All (fun t : term => wf_ulvls Σ t) (projs ind npars p).
  Proof using Type.
    induction p; simpl; auto.
  Qed.

  Lemma wf_extended_subst Σ Γ n :
    wf_ctx_ulvls Σ Γ ->
    All (fun t : term => wf_ulvls Σ t) (extended_subst Γ n).
  Proof using Type.
    induction Γ as [|[na [b|] ty] Γ] in n |- *; simpl; auto.
    move=> /andP []; rewrite /wf_decl_ulvls /= => /andP [] wfb wfty wfΓ.
    constructor; eauto. rewrite wf_ulvls_subst //. now apply IHΓ.
    now rewrite wf_ulvls_lift. eauto.
    move=> /andP []; rewrite /wf_decl_ulvls /= => wfty wfΓ.
    constructor; eauto.
  Qed.

  Lemma closedu_compare_decls k Γ Δ :
    PCUICEquality.eq_context_upto_names Γ Δ ->
    test_context (closedu k) Γ = test_context (closedu k) Δ.
  Proof using Type.
    induction 1; cbn; auto.
    f_equal; auto. destruct r; subst; auto.
  Qed.

  Lemma closedu_mkApps k f args : closedu k (mkApps f args) = closedu k f && forallb (closedu k) args.
  Proof using Type.
    induction args in f |- *; cbn; auto. ring.
    rewrite IHargs /=. ring.
  Qed.

  Lemma closedu_abstract_instance univs : closedu_instance #|abstract_instance univs| (abstract_instance univs).
  Proof using Type.
    destruct univs as [|[l csts]] => // /=.
    rewrite /UContext.instance /AUContext.repr.
    rewrite /closedu_instance forallb_mapi //.
    intros i hi. cbn; len. now eapply Nat.ltb_lt.
  Qed.

  Notation closedu_ctx k := (test_context (closedu k)).

  Lemma closedu_lift k n k' t :
    closedu k (lift n k' t) = closedu k t.
  Proof using Type.
    induction t in k' |- * using term_forall_list_ind; cbn; auto; intros; solve_all.
    - rewrite IHt.
      rewrite /map_predicate_k /= /test_predicate /test_predicate_ku /= /id.
      f_equal. f_equal. rewrite e. f_equal. f_equal. f_equal.
      solve_all.
      solve_all.
      rewrite /map_branch_k /test_branch /=. f_equal.
      now rewrite b.
    - rewrite /test_def /map_def /=. now rewrite a b.
    - rewrite /test_def /map_def /=. now rewrite a b.
    - rewrite test_primu_mapu; eapply test_primu_primProp; tea; eauto.
  Qed.

  Ltac try_hyp :=
    multimatch goal with H : _ |- _ => eapply H end.

  Ltac crush := repeat (solve_all; try try_hyp; cbn).


  Lemma closedu_subst k s k' t :
    forallb (closedu k) s && closedu k t ->
    closedu k (subst s k' t).
  Proof using Type.
    Ltac t := repeat (solve_all; try try_hyp).
    induction t in k' |- * using term_forall_list_ind; cbn; auto; intros;
      try solve [t].
    - destruct Nat.leb => //.
      destruct nth_error eqn:eq => //.
      rewrite closedu_lift.
      eapply nth_error_forallb in eq; tea. solve_all.
    - unfold test_predicate_ku in *. unfold test_branch in *. crush.
    - unfold test_def in *; crush.
    - unfold test_def in *; crush.
  Qed.

  Lemma closedu_subst_context k s k' Γ :
    forallb (closedu k) s && closedu_ctx k Γ ->
    closedu_ctx k (subst_context s k' Γ).
  Proof using Type.
    rewrite /subst_context.
    induction Γ.
    * cbn; auto.
    * rtoProp. intros []. cbn in H0. rtoProp.
      rewrite fold_context_k_snoc0 /= IHΓ //. crush.
      unfold test_decl in *. crush.
      destruct decl_body eqn:heq => /= //.
      rewrite closedu_subst //. crush.
      rewrite closedu_subst //. crush.
  Qed.

  Lemma closedu_lift_context k n k' Γ :
    closedu_ctx k (lift_context n k' Γ) = closedu_ctx k Γ.
  Proof using Type.
    rewrite /lift_context.
    induction Γ.
    * cbn; auto.
    * rtoProp.
      rewrite fold_context_k_snoc0 /= IHΓ //.
      unfold test_decl in *.
      cbn.
      rewrite closedu_lift.
      destruct (decl_body a) => /= //.
      rewrite closedu_lift //.
  Qed.

  Lemma closedu_extended_subst k Γ k' :
    closedu_ctx k Γ ->
    forallb (closedu k) (extended_subst Γ k').
  Proof using Type.
    induction Γ in k' |- *; cbn; auto. destruct a as [na [b|] ty] => /= //.
    unfold test_decl; move/andP=> [] clΓ /= cld. apply/andP. split.
    eapply closedu_subst. rewrite IHΓ // /= closedu_lift. crush.
    now rewrite IHΓ.
    unfold test_decl; move/andP=> [] clΓ /= cld. now apply IHΓ.
  Qed.

  Lemma closedu_expand_lets_ctx k Γ Δ :
    closedu_ctx k Γ && closedu_ctx k Δ ->
    closedu_ctx k (expand_lets_ctx Γ Δ).
  Proof using Type.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    move/andP => [] clΓ clΔ.
    apply closedu_subst_context.
    rewrite closedu_extended_subst // /= closedu_lift_context //.
  Qed.

  Lemma closedu_smash_context_gen k Γ Δ :
    closedu_ctx k Γ -> closedu_ctx k Δ ->
    closedu_ctx k (smash_context Γ Δ).
  Proof using Type.
    induction Δ in Γ |- *; cbn; auto.
    move=> clΓ /andP[] clΔ cla.
    destruct a as [na [b|] ty] => //.
    - apply IHΔ => //. apply closedu_subst_context => /= //.
      now move/andP: cla => [] /= -> clty.
    - apply IHΔ => //.
      now rewrite test_context_app clΓ /= andb_true_r.
  Qed.

  Lemma closedu_smash_context k Δ :
    closedu_ctx k Δ ->
    closedu_ctx k (smash_context [] Δ).
  Proof using Type.
    apply closedu_smash_context_gen => //.
  Qed.

  Lemma wf_level_closed {Σ : global_env} {wfΣ : wf Σ} univs l :
    on_udecl_prop Σ univs ->
    wf_level (Σ, univs) l -> closedu_level #|polymorphic_instance univs| l.
  Proof using Type.
    intros ond Ht; destruct l => //.
    cbn in Ht. unfold closedu_level.
    cbn. red in Ht.
    eapply in_var_global_ext in Ht => //.
    cbn in Ht.
    destruct (udecl_prop_in_var_poly (Σ := (Σ, univs)) ond Ht) as [ctx eq].
    cbn in eq. subst univs.
    cbn in Ht. cbn. unfold AUContext.levels in Ht.
    eapply (proj1 (LevelSetProp.of_list_1 _ _)) in Ht.
    eapply InA_In_eq in Ht.
    destruct ctx as [names cstrs].
    unfold AUContext.repr in Ht |- *. cbn in *. len.
    rewrite mapi_unfold in Ht. eapply In_unfold_var in Ht as [k []].
    eapply Nat.leb_le. noconf H0. lia.
  Qed.

  Lemma wf_ulvl_closed {Σ : global_env} {wfΣ : wf Σ} univs u :
    on_udecl_prop Σ univs ->
    wf_ulvl (Σ, univs) u -> closedu_univ_lvl #|polymorphic_instance univs| u.
  Proof using Type.
    intros ond Ht.
    cbn in Ht. unfold closedu_univ_lvl.
    eapply LevelExprSet.for_all_spec.
    intros x y ?; subst; auto.
    intros i hi. specialize (Ht i hi).
    unfold closedu_level_expr.
    apply wf_level_closed => //.
  Qed.

  Lemma wf_univ_closed {Σ : global_env} {wfΣ : wf Σ} univs s :
    on_udecl_prop Σ univs ->
    wf_univ (Σ, univs) s -> closedu_universe #|polymorphic_instance univs| s.
  Proof using Type.
    destruct s => //=.
    apply wf_ulvl_closed.
  Qed.

  Lemma wf_instance_closed {Σ : global_env} {wfΣ : wf Σ} {univs u} :
    on_udecl_prop Σ univs ->
    wf_instance (Σ, univs) u ->
    closedu_instance #|polymorphic_instance univs| u.
  Proof using Type.
    intros ond Ht.
    red in Ht. unfold closedu_instance. solve_all.
    now eapply wf_level_closed.
  Qed.

  Lemma wf_ulvl_make Σ u : wf_ulvl Σ (UnivLvl.make' u) -> wf_level Σ u.
  Proof.
    rewrite /wf_ulvl /= => hl; rewrite /wf_level.
    apply (hl (u, 0)). lsets.
  Qed.

  Lemma wf_ulvls_closedu {Σ : global_env} {wfΣ : wf Σ} {univs t} :
    on_udecl_prop Σ univs ->
    wf_ulvls (Σ, univs) t -> closedu #|polymorphic_instance univs| t.
  Proof using Type.
    intros ond. induction t using term_forall_list_ind; cbn => //; solve_all.
    - apply wf_univ_closed => //.
      destruct s => //=.
      now move/wf_ulvl_reflect: H.
    - eapply wf_instance_closed => //.
      apply All_forallb in H.
      rewrite -forallb_map wf_ulvlb_instance_forall in H.
      now move/wf_instanceP: H.
    - eapply wf_instance_closed => //.
      apply All_forallb in H.
      rewrite -forallb_map wf_ulvlb_instance_forall in H.
      now move/wf_instanceP: H.
    - eapply wf_instance_closed => //.
      apply All_forallb in H.
      rewrite -forallb_map wf_ulvlb_instance_forall in H.
      now move/wf_instanceP: H.
    - unfold test_predicate_ku in *; solve_all.
      eapply wf_instance_closed => //.
      apply All_forallb in H0.
      rewrite -forallb_map wf_ulvlb_instance_forall in H0.
      now move/wf_instanceP: H0.
    - unfold test_branch in *; solve_all.
    - unfold test_def in *; solve_all.
    - unfold test_def in *; solve_all.
    - eapply test_primu_test_primu_tPrimProp; tea; cbn; eauto.
      intros. to_wfu. eapply wf_level_closed; tea.
      now apply wf_ulvl_make.
  Qed.

  Lemma wf_ctx_ulvls_closed {Σ} {wfΣ : wf Σ} {univs ctx} :
    on_udecl_prop Σ univs ->
    wf_ctx_ulvls (Σ, univs) ctx ->
    closedu_ctx #|polymorphic_instance univs| ctx.
  Proof using Type.
    intros ond. induction ctx => //.
    rewrite /wf_ctx_ulvls /= => /andP[] wfa wfctx.
    rewrite IHctx // /=.
    unfold wf_decl_ulvls, test_decl in *.
    destruct a as [na [b|] ty]; cbn in *.
    move/andP: wfa => [].
    now do 2 move/(wf_ulvls_closedu ond) => ->.
    now move/(wf_ulvls_closedu ond): wfa => ->.
  Qed.


  Lemma closedu_reln k Γ k' acc :
    closedu_ctx k Γ ->
    forallb (closedu k) acc ->
    forallb (closedu k) (reln acc k' Γ).
  Proof using Type.
    induction Γ in acc, k' |- *; cbn; auto.
    destruct a as [na [b|] ty] => /= //.
    - unfold test_decl; move/andP=> [] clΓ /= cld. now eapply IHΓ.
    - unfold test_decl; move/andP=> [] clΓ /= cld clacc; now apply IHΓ => //.
  Qed.

  Lemma closedu_to_extended_list_k k Γ k' :
    closedu_ctx k Γ ->
    forallb (closedu k) (to_extended_list_k Γ k').
  Proof using Type.
    intros clΓ. apply closedu_reln => //.
  Qed.

  Lemma closed_ind_predicate_context {Σ ind mdecl idecl} {wfΣ : wf Σ} :
    declared_inductive Σ ind mdecl idecl ->
    closedu_ctx #|polymorphic_instance (ind_ulvls mdecl)|
        (ind_params mdecl) ->
    closedu_ctx #|polymorphic_instance (ind_ulvls mdecl)|
            (ind_indices idecl) ->
    test_context (closedu #|abstract_instance (ind_ulvls mdecl)|) (ind_predicate_context ind mdecl idecl).
  Proof using Type.
    intros decli.
    rewrite /ind_predicate_context; cbn.
    rewrite closedu_mkApps /=.
    rewrite closedu_abstract_instance /= => clpars clinds.
    apply/andP; split.
    * apply closedu_expand_lets_ctx. now rewrite clpars clinds.
    * apply closedu_to_extended_list_k.
      rewrite test_context_app.
      rewrite (closedu_smash_context _ _ clpars).
      apply closedu_expand_lets_ctx => //.
      now rewrite clpars.
  Qed.

  Lemma closedu_inds {Σ ind mdecl} {wfΣ : wf Σ} :
    forallb (closedu #|abstract_instance (ind_ulvls mdecl)|)
      (inds ind (abstract_instance (ind_ulvls mdecl)) (ind_bodies mdecl)).
  Proof using Type.
    rewrite /inds.
    induction #|ind_bodies mdecl|; cbn; auto.
    rewrite IHn andb_true_r.
    eapply closedu_abstract_instance.
  Qed.

  Theorem wf_types :
    env_prop (fun Σ Γ t T => wf_ulvls Σ t && wf_ulvls Σ T)
      (fun Σ _ j => lift_wfbu_term (wf_ulvls Σ) (wf_univb Σ) j)
      (fun Σ Γ => wf_ctx_ulvls Σ Γ).
  Proof using Type.
    apply typing_ind_env; unfold lift_wfbu_term; intros; rename_all_hyps; cbn; rewrite -!/(wf_ulvls _ _) ;
    specIH; to_prop;
    cbn; auto.

    - eapply MRReflect.introT. 1: apply lift_wfu_wfbu_term.
      apply lift_typing_subjtyp with (1 := X) => //= t T [] _ /andP[] //.

    - apply All_local_env_cst, All_forallb in X0.
      apply forallb_impl with (2 := X0) => [] [na bo ty] _ //= /andP[] //=.

    - rewrite wf_ulvls_lift.
      eapply forallb_nth_error with (n := n) in H0. rewrite heq_nth_error /= in H0.
      now move/andP: H0.

    - apply/andP; split; to_wfu; cbn; eauto with pcuic.

    - cbn in *; to_wfu ; eauto with pcuic.
    - rewrite wf_ulvls_subst. constructor. to_wfu; auto. constructor.
      now move/andP: H1 => [].

    - apply/andP; split.
      { rewrite wf_ulvlb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constant_inv _ _ _ _ wf_ulvls_weaken wf X H0) as [[_ X0]%andb_and _]%andb_and.
      unshelve eapply declared_constant_to_gen in H0; eauto.
      epose proof (weaken_lookup_on_global_env' Σ.1 _ _ wf H0).
      eapply wf_ulvls_inst. 2:eauto. all:eauto.
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_ulvlb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_inductive_inv wf_ulvls_weaken wf X isdecl).
      move/onArity : X0 => /andP[] /andP[] /= _ Hind _.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      eapply wf_ulvls_inst; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 isdecl)).
      now eapply consistent_instance_ext_wf.

    - apply/andP; split.
      { rewrite wf_ulvlb_instance_forall.
        apply/wf_instanceP.
        eapply consistent_instance_ext_wf; eauto. }
      pose proof (declared_constructor_inv wf_ulvls_weaken wf X isdecl) as [sc [nthe onc]].
      unfold type_of_constructor.
      rewrite wf_ulvls_subst.
      { apply wf_ulvls_inds.
        now eapply consistent_instance_ext_wf. }
      move/on_ctype : onc => /andP[] /andP[] /= _ onc _.
      clear nthe. unshelve eapply declared_constructor_to_gen in isdecl; eauto.
      eapply wf_ulvls_inst; eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 isdecl))).
      now eapply consistent_instance_ext_wf.

    - rewrite wf_ulvls_mkApps in H6.
      move/andP: H6 => /= [] wfu; rewrite forallb_app.
      move/andP=> [] wfpars wfinds.
      cbn in wfu.
      rewrite wfu /= wfpars wf_ulvls_mkApps /=
        forallb_app wfinds /= H0 /= !andb_true_r.
      pose proof (declared_inductive_inv wf_ulvls_weaken wf X isdecl).
      move:(onArity X3) => /andP[] /andP[] /= _ hty _.
      rewrite (ind_arity_eq X3) in hty.
      rewrite !wf_ulvls_it_mkProd_or_LetIn in hty.
      move/and3P: hty => [] wfp wfindis wfiuniv.
      have ond : on_udecl_prop Σ (ind_ulvls mdecl).
      { eapply (weaken_lookup_on_global_env' _ _ (InductiveDecl mdecl)); eauto.
      unshelve eapply declared_inductive_to_gen in isdecl; eauto.
      }
      eapply wf_ctx_ulvls_closed in wfp => //.
      eapply wf_ctx_ulvls_closed in wfindis => //.
      rewrite (consistent_instance_length H2).
      erewrite closedu_compare_decls; tea.
      rewrite closed_ind_predicate_context // /=.
      unfold test_branch.
      apply/andP; split.
      * have wfbrctx : All (fun cdecl =>
          closedu_ctx #|polymorphic_instance (ind_ulvls mdecl)| (cstr_args cdecl))
          (ind_ctors idecl).
        { pose proof (onConstructors := onConstructors X3).
          clear -wf ond onConstructors.
          red in onConstructors. solve_all. destruct X.
          move : on_ctype => /andP[] /andP[] /= _ wfty _.
          rewrite cstr_eq in wfty.
          rewrite !wf_ulvls_it_mkProd_or_LetIn in wfty.
          move/and3P: wfty => [] _ clargs _.
          apply wf_ctx_ulvls_closed in clargs => //. }
        solve_all.
        erewrite closedu_compare_decls; [|tea].
        rewrite /cstr_branch_context.
        eapply closedu_expand_lets_ctx.
        rewrite wfp. eapply closedu_subst_context.
        rewrite a.
        now rewrite closedu_inds.
      * rewrite wf_ulvls_it_mkLambda_or_LetIn H7 andb_true_r.
        move: H4.
        rewrite /wf_ctx_ulvls forallb_app => /andP[hctx _].
        apply (MRReflect.introT onctxP).
        solve_all. unfold ondecl, wf_decl_ulvls, on_decl_ulvls in *.
        move/andP:H3 => [Hb Ht] //; split; tas.
        now destruct decl_body.

    - rewrite /subst1. rewrite wf_ulvls_subst.
      constructor => //. eapply All_rev.
      rewrite wf_ulvls_mkApps in H2.
      move/andP: H2 => [].
      now intros _ hargs%forallb_All.
      pose proof (declared_projection_inv wf_ulvls_weaken wf X isdecl).
      destruct (declared_inductive_inv); simpl in *.
      destruct ind_ctors as [|cs []] => //.
      destruct ind_cunivs as [|cunivs []] => //;
      destruct X0 as [[[? ?] ?] ?] => //.
      red in o0.
      destruct nth_error eqn:heq => //.
      destruct o0  as [_ ->].
      rewrite wf_ulvls_mkApps {1}/wf_ulvls /= -!/(wf_ulvls _ _)
        wf_ulvlb_instance_forall in H2.
      move/andP: H2 => [/wf_instanceP wfu wfargs].
      unshelve eapply declared_projection_to_gen in isdecl; eauto.
      eapply (wf_ulvls_inst (ind_ulvls mdecl)); eauto.
      exact (weaken_lookup_on_global_env' Σ.1 _ _ wf (proj1 (proj1 (proj1 isdecl)))).
      rewrite wf_ulvls_subst.
      eapply wf_ulvls_inds; eauto.
      eapply wf_abstract_instance.
      rewrite wf_ulvls_subst. apply wf_projs.
      rewrite wf_ulvls_lift.
      rewrite smash_context_app smash_context_acc in heq.
      autorewrite with len in heq. rewrite nth_error_app_lt in heq.
      autorewrite with len. lia.
      rewrite nth_error_subst_context in heq.
      autorewrite with len in heq. simpl in heq.
      epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl)) _ _).
      autorewrite with len in H0. simpl in H0. rewrite -> H0 in heq. clear H0.
      autorewrite with len in heq.
      simpl in heq.
      destruct nth_error eqn:hnth; simpl in * => //.
      noconf heq. simpl.
      rewrite wf_ulvls_subst.
      apply wf_extended_subst.
      rewrite ind_arity_eq in onArity. move:onArity => /andP[] /andP[] /= _ Hs _.
      rewrite !wf_ulvls_it_mkProd_or_LetIn in Hs.
      now move/andP: Hs => /andP /andP [].
      rewrite wf_ulvls_lift.
      eapply wf_ulvls_local_ctx_smash in u0.
      eapply wf_ulvls_local_ctx_nth_error in u0; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - clear X X1. unfold on_def_type, on_def_body in *; cbn in *.
      apply/andP; split; auto.
      solve_all.
      eapply nth_error_all in X0 as (? & _)%andb_and; eauto.

    - apply/andP; split; eauto.
      destruct X0; cbn => //.
      rtoProp; intuition eauto. solve_all.
      destruct X0; cbn => //.
      simp prim_type. cbn. rtoProp; intuition.
Qed.

  Lemma typing_wf_ulvls {Σ : global_env_ext} {Γ t T} :
    wf Σ ->
    Σ ;;; Γ |- t : T -> wf_ulvls Σ t && wf_ulvls Σ T.
  Proof using Type.
    intros wfΣ Hty.
    exact (env_prop_typing wf_types _ wfΣ _ _ _ Hty).
  Qed.

  Lemma typing_wf_univ {Σ : global_env_ext} {Γ t s} :
    wf Σ ->
    Σ ;;; Γ |- t : tUniv s -> wf_univ Σ s.
  Proof using Type.
    intros wfΣ Hty.
    apply typing_wf_ulvls in Hty as [_ wfs]%andb_and; auto.
    cbn in wfs. now to_wfu.
  Qed.

  Lemma isType_wf_ulvls {Σ Γ T} : wf Σ.1 -> isType Σ Γ T -> wf_ulvls Σ T.
  Proof using Type.
    intros wfΣ (_ & s & Hs & _). now eapply typing_wf_ulvls in Hs as [HT _]%andb_and.
  Qed.

End CheckerFlags.

Arguments wf_ulvl_reflect {Σ u}.
#[global] Hint Resolve wf_univ_type1 wf_univ_super wf_univ_sup wf_univ_product : pcuic.

#[global]
Hint Extern 4 (wf_univ _ ?u) =>
  match goal with
  [ H : typing _ _ _ (tUniv u) |- _ ] => apply (typing_wf_univ _ H)
  end : pcuic.
