From Stdlib Require Import OrdersAlt MSetList MSetAVL MSetFacts MSetProperties MSetDecide FMapAVL.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils MRMSets MRFSets.
From MetaRocq.Common Require Import BasicAst config Levels Sorts.
From Stdlib Require Import ssreflect.

Local Open Scope nat_scope.
Local Open Scope string_scope2.

Implicit Types (cf : checker_flags).

Module Universe.
  (** A Universe is a product of a sort with a universe level.

  	  Universes are quotiented at conversion so that every impredicative sorts (e.g., [sSProp] or [sProp])
	  at level i and j are convertible. *)
  Record t_ {sort} {ulvl} :=
    mk
	{ s : sort
  	; l : ulvl }.
  Arguments t_ : clear implicits.
  Arguments mk {_ _} _ _.

  Definition eq_ {sort} {ulvl} eq_sort eq_ulvl (u u' : t_ sort ulvl) :=
    eq_sort (u.(s)) (u'.(s)) /\ eq_ulvl (u.(l)) (u'.(l)).

  Definition t := t_ Sort.t UnivLvl.t.

  Lemma univ_eq :
    forall (u u' : t),
	  u.(s) = u'.(s) ->
	  u.(l) = u'.(l) ->
	  u = u'.
  Proof. intros [] []; cbn in *; now intros -> ->. Qed.

  Definition eqb {sort} {univ} `{ReflectEq sort} `{ReflectEq univ} (u1 u2 : t_ sort univ) : bool :=
    eqb u1.(s) u2.(s) &&
	eqb u1.(l) u2.(l).

  #[global, program] Instance reflect_eq_univ_ {sort} {ulvl} `{ReflectEq sort} `{ReflectEq ulvl} : ReflectEq (t_ sort ulvl) :=
    { eqb := eqb }.
  Next Obligation.
    destruct x as [s l], y as [s' l']; unfold eqb; cbn.
	destruct (eqb_spec s s'); destruct (eqb_spec l l').
	all: cbn; constructor; easy.
  Qed.

  #[global] Instance eq_dec_univ {sort} {ulvl} `{EqDec sort} `{EqDec ulvl} : EqDec (t_ sort ulvl) :=
    ltac:(intros s s'; decide equality).

  Definition map {sort sort'} {ulvl ulvl'} (fs : sort -> sort') (fl : ulvl -> ulvl') u :=
    mk (fs u.(s)) (fl u.(l)).

  Definition maps {sort sort'} {ulvl} (f : sort -> sort') u :=
    map f (fun (x : ulvl) => x) u.

  Definition mapl {sort} {ulvl ulvl'} (f : ulvl -> ulvl') u :=
    map (fun (x : sort) => x) f u.

  Definition on_sort {ulvl} {T} (P: ulvl -> T) (def: T) (u : t_ Sort.t ulvl) :=
    match u.(s) with
    | sProp | sSProp => def
    | sType => P u.(l)
    end.

  (** Test if the universe is a lub of levels or contains +n's. *)
  Definition is_levels (u : t) : bool :=
    match u.(s) with
    | sSProp | sProp => true
    | sType => UnivLvl.is_levels u.(l)
    end.

  (** Test if the universe is a level or an algebraic universe. *)
  Definition is_level (u : t) : bool :=
    match u.(s) with
    | sSProp | sProp => true
    | sType => UnivLvl.is_level u.(l)
    end.

  Definition is_sprop {ulvl} (u : t_ Sort.t ulvl) : bool :=
    match u.(s) with
      | sSProp => true
      | _ => false
    end.

  Definition is_prop {ulvl} (u : t_ Sort.t ulvl) : bool :=
    match u.(s) with
      | sProp => true
      | _ => false
    end.

  Definition is_propositional {ulvl} (u : t_ Sort.t ulvl) : bool :=
    match u.(s) with
      | sProp | sSProp => true
      | _ => false
    end.

  Lemma is_prop_propositional {ulvl} (u : t_ Sort.t ulvl) :
    is_prop u -> is_propositional u.
  Proof. destruct u as [s l]; now destruct s. Qed.
  Lemma is_sprop_propositional {ulvl} (u : t_ Sort.t ulvl) :
    is_sprop u -> is_propositional u.
  Proof. destruct u as [s l]; now destruct s. Qed.

  Definition is_type_sort {ulvl} (u : t_ Sort.t ulvl) : bool :=
    match u.(s) with
      | sType => true
      | _ => false
    end.

  Definition type0 : t := mk sType UnivLvl.type0.
  Definition type1 : t := mk sType UnivLvl.type1.

  Definition of_levels (l : PropLevel.t + Level.t) : t :=
    match l with
    | inl PropLevel.lSProp => mk sSProp UnivLvl.type0
    | inl PropLevel.lProp => mk sProp UnivLvl.type0
    | inr l => mk sType (UnivLvl.make' l)
    end.

  (** The universe strictly above FOR TYPING (not cumulativity) *)

  Definition super_ {ulvl} type1 usucc (u : t_ Sort.t ulvl) : t_ Sort.t ulvl :=
    match u.(s) with
    | sSProp | sProp => mk sType type1
    | sType => mk sType (usucc u.(l))
    end.
  Definition super : t -> t := super_ UnivLvl.type1 UnivLvl.succ.
  Definition csuper := super_ 1 S.

  Definition sup_ {ulvl} type0 univ_sup (u u' : t_ Sort.t ulvl) : t_ Sort.t ulvl :=
    match u.(s), u'.(s) with
    | sSProp, sSProp => mk sSProp type0
    | sSProp, sProp | sProp, sSProp => mk sProp type0
    | sSProp, _ => u'
    | _, sSProp => u
    | sProp, sProp => mk sProp type0
    | sProp, _ => u'
    | _, sProp => u
    | sType, sType => mk sType (univ_sup u.(l) u'.(l))
    end.
  Definition sup : t -> t -> t := sup_ UnivLvl.type0 UnivLvl.sup.
  Definition csup := sup_ 0 Nat.max.

  (** Type of a product *)
  Definition univ_of_product_ {ulvl} type0 usup (dom codom : t_ Sort.t ulvl) : t_ Sort.t ulvl :=
    match codom.(s) with
    | sSProp | sProp => codom
    (* Prop and SProp impredicativity *)
    | _ => sup_ type0 usup dom codom
    end.
  Definition univ_of_product : t -> t -> t := univ_of_product_ UnivLvl.type0 UnivLvl.sup.
  Definition cuniv_of_product := univ_of_product_ 0 Nat.max.

  Definition get_is_level (u : t) : option Level.t :=
    match u.(s) with
    | sSProp => None
    | sProp => None
    | sType => UnivLvl.get_is_level u.(l)
    end.

  Definition to_family {sort ulvl} (u : t_ sort ulvl) := u.(s).

  Definition to_csort v (u : t) := mk u.(s) (val v u.(l)).

  Lemma to_family_to_csort u v :
    to_family (to_csort v u) = to_family u.
  Proof.
    destruct u as [s l]; unfold to_csort; destruct s; cbnr.
  Qed.

  Lemma sType_super_ {ulvl type1 usucc} (u : t_ Sort.t ulvl) :
    to_family (super_ type1 usucc u) = sType.
  Proof. destruct u as [s l]; now destruct s. Qed.

  Lemma sType_super (s : t) :
    to_family (super s) = sType.
  Proof. apply sType_super_. Qed.

  Definition lt_ {sort ulvl} slt eqs ult (u v : t_ sort ulvl) : Prop :=
    slt u.(s) v.(s) \/
	(eqs u.(s) v.(s) /\ ult u.(l) v.(l)).

  Definition lt := lt_ Sort.lt eq UnivLvl.lt.
  Definition clt := lt_ Sort.lt eq Nat.lt.

  Module OT <: OrderedType.
    Definition t := t.
    #[local] Definition eq : t -> t -> Prop := eq.
    #[local] Definition eq_equiv : Equivalence eq := _.
    Definition lt := lt.
    #[local] Instance lt_strorder : StrictOrder lt.
    Proof.
      constructor.
      - intros [s l] [contra | [_ contra]]; cbn in *;
	    by apply irreflexivity in contra.
	  - intros [s1 l1] [s2 l2] [s3 l3] [hslt | [he hlt]] [hslt' | [he' hlt']]; cbn in *.
	    + left. etransitivity; eauto.
		+ left. by rewrite -he'. 
		+ left. by rewrite he.
		+ right; split; cbn.
		  * congruence.
		  * etransitivity; eauto.
    Qed.

    Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      intros x y e z t e'. hnf in * |- ; subst. reflexivity.
    Qed.
	
    Definition compare (u v : t) : comparison :=
	  match Sort.compare u.(s) v.(s) with
	  | Eq => LevelExprSet.compare u.(l) v.(l)
	  | _ as c => c
	  end.

    Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
    Proof.
	  destruct x as [s l], y as [s' l']; cbv [compare eq]; cbn.
	  destruct (Sort.compare_spec s s').
	  (* Only the case Eq needs more justification. *)
	  2,3: constructor; cbv[lt Universe.lt lt_]; now left.
	  subst; destruct (LevelExprSet.compare_spec l l'); cbn; constructor.
	  - apply univ_eq; cbn; auto.
	    apply NonEmptySetFacts.eq_univ', H.
	  - cbv[lt Universe.lt lt_]; cbn.
	    right; split; auto.
	  - cbv[lt Universe.lt lt_]; cbn.
	    right; split; auto.
    Qed.

    Definition eq_dec (x y : t) : {x = y} + {x <> y}.
    Proof. repeat decide equality. apply UnivLvl.eq_dec_univ0. Defined.
  End OT.
  Module OTOrig <: OrderedTypeOrig := Backport_OT OT.
End Universe.


Module UnivMap := FMapAVL.Make Universe.OTOrig.
Module UnivMapFact := FMapFacts.WProperties UnivMap.
Module UnivMapExtraFact := FSets.WFactsExtra_fun Universe.OTOrig UnivMap UnivMapFact.F.
Module UnivMapDecide := FMapAVL.Decide Universe.OTOrig UnivMap.

Notation usort := Universe.s.
Notation ulvl := Universe.l.

Notation "⟦ u ⟧_ v" := (Universe.to_csort v u) (at level 0, format "⟦ u ⟧_ v", v name) : univ_scope.


Lemma val_sort_sup v u1 u2 :
  Universe.to_csort v (Universe.sup u1 u2) =
  Universe.csup (Universe.to_csort v u1) (Universe.to_csort v u2).
Proof.
  destruct u1 as [[| |] l1], u2 as [[| |] l2]; cbv[Universe.to_csort]; cbnr; f_equal.
  all: apply val_sup.
Qed.

Lemma is_prop_val u :
  Universe.is_prop u -> forall v, Universe.to_csort v u = Universe.mk sProp (val v (ulvl u)).
Proof. destruct u as [[| |] l] => //. Qed.

Lemma is_sprop_val u :
  Universe.is_sprop u -> forall v, Universe.to_csort v u = Universe.mk sSProp (val v (ulvl u)).
Proof. destruct u as [[| |] l] => //. Qed.

Lemma val_is_prop u v :
  Universe.to_csort v u = Universe.mk sProp (val v (ulvl u)) <-> Universe.is_prop u.
Proof. destruct u as [[| |] l] => //. Qed.

Lemma val_is_sprop u v :
  Universe.to_csort v u = Universe.mk sSProp (val v (ulvl u)) <-> Universe.is_sprop u.
Proof. destruct u as [[| |] l] => //. Qed.

Lemma is_prop_and_is_sprop_val_false u :
  Universe.is_prop u = false -> Universe.is_sprop u = false ->
  forall v, ∑ n, Universe.to_csort v u = Universe.mk sType n.
Proof.
  intros Hp Hsp v.
  destruct u as [[| |] l] => //; cbv[Universe.to_csort]. eexists; eauto.
Qed.

Lemma val_is_prop_false u v n :
  Universe.to_csort v u = Universe.mk sType n -> Universe.is_prop u = false.
Proof. destruct u as [[| |] l] => //. Qed.

Lemma get_is_level_correct u l :
  Universe.get_is_level u = Some l -> u = Universe.mk sType (UnivLvl.make' l).
Proof.
  intro H; destruct u as [[| |] l'] => //.
  f_equal; now apply ulvl_get_is_level_correct.
Qed.

Lemma eqb_true_iff (u u' : Universe.t) :
  eqb u u' <-> u = u'.
Proof.
  split. apply /eqb_spec. eapply introP. apply /eqb_spec.
Qed.

Lemma sup_comm u1 u2 :
  Universe.sup u1 u2 = Universe.sup u2 u1.
Proof.
  destruct u1 as [[| |] l1], u2 as [[| |] l2]; cbnr.
  all: f_equal; apply sup0_comm.
Qed.

Lemma is_not_prop_and_is_not_sprop {univ} (u : Universe.t_ Sort.t univ) :
  Universe.is_prop u = false -> Universe.is_sprop u = false ->
  ∑ l, u = Universe.mk sType l.
Proof.
  intros Hp Hsp.
  destruct u as [[| |] l] => //. now eexists.
Qed.

Lemma is_prop_sort_sup u1 u2 :
  Universe.is_prop (Universe.sup u1 u2)
  -> Universe.is_prop u2 \/ Universe.is_sprop u2 .
Proof. destruct u1 as [[| |] l1], u2 as [[| |] l2]; auto. Qed.

Lemma is_prop_sort_sup' u1 u2 :
  Universe.is_prop (Universe.sup u1 u2)
  -> Universe.is_prop u1 \/ Universe.is_sprop u1 .
Proof. destruct u1 as [[| |] l1], u2 as [[| |] l2]; auto. Qed.

Lemma is_prop_or_sprop_sort_sup u1 u2 :
  Universe.is_sprop (Universe.sup u1 u2) -> Universe.is_sprop u2.
Proof. destruct u1 as [[| |] l1], u2 as [[| |] l2]; auto. Qed.

Lemma is_prop_sort_sup_prop u1 u2 :
  Universe.is_prop u1 && Universe.is_prop u2 ->
  Universe.is_prop (Universe.sup u1 u2).
Proof. destruct u1 as [[| |] l1], u2 as [[| |] l2]; auto. Qed.

Lemma is_prop_or_sprop_sort_sup_prop u1 u2 :
  Universe.is_sprop u1 && Universe.is_sprop u2 ->
  Universe.is_sprop (Universe.sup u1 u2).
Proof. destruct u1 as [[| |] l1], u2 as [[| |] l2]; auto. Qed.

Lemma is_prop_sup u1 u2 :
  Universe.is_prop (Universe.sup u1 u2) ->
  Universe.is_propositional u1 /\ Universe.is_propositional u2.
Proof. destruct u1 as [[| |] l1], u2 as [[| |] l2]; auto. Qed.

Lemma is_sprop_sup_iff u1 u2 :
  Universe.is_sprop (Universe.sup u1 u2) <->
  (Universe.is_sprop u1 /\ Universe.is_sprop u2).
Proof. split; destruct u1 as [[| |] l1], u2 as [[| |] l2] => //=; intuition. Qed.

Lemma is_type_sup_r u1 u2 :
  Universe.is_type_sort u2 ->
  Universe.is_type_sort (Universe.sup u1 u2).
Proof. destruct u2 as [[| |] l2]; try absurd; destruct u1 as [[| |] l1]; cbnr; intros; absurd. Qed.

Lemma is_prop_univ_prod u1 u2 :
  Universe.is_prop (Universe.univ_of_product u1 u2)
  -> Universe.is_prop u2.
Proof.
  unfold Universe.univ_of_product.
  destruct u2 as [[| |] l2]; cbn; auto.
  intros; simpl in *; destruct u1 as [[| |] l1]; auto.
Qed.

Lemma is_sprop_univ_prod u1 u2 :
  Universe.is_sprop (Universe.univ_of_product u1 u2)
  -> Universe.is_sprop u2.
Proof.
  unfold Universe.univ_of_product.
  destruct u2 as [[| |] l2]; cbn; auto.
  intros; simpl in *; destruct u1 as [[| |] l1]; auto.
Qed.

Section UnivCompare.
  Context {cf}.
  Definition leq_univ_n_ {univ} (leq_universe_n : Z -> univ -> univ -> Prop) n u u' : Prop :=
    match usort u, usort u' with
    | sProp,   sProp
    | sSProp,  sSProp => (n = 0)%Z
    | sType, sType => leq_universe_n n (ulvl u) (ulvl u')
    | sProp,   sType => prop_sub_type
    | _, _ => False
    end.

  Definition leq_univ_n n φ := leq_univ_n_ (fun n => leq_ulvl_n n φ) n.
  Definition lt_univ := leq_univ_n 1.
  Definition leq_univ := leq_univ_n 0.

  Definition leqb_univ_n_ {univ} (leqb_universe_n : bool -> univ -> univ -> bool) b u u' : bool :=
    match usort u, usort u' with
    | sProp,   sProp
    | sSProp,  sSProp => negb b
    | sType, sType => leqb_universe_n b (ulvl u) (ulvl u')
    | sProp,   sType => prop_sub_type
    | _, _ => false
    end.

  Definition eq_univ_ {univ} (eq_universe : univ -> univ -> Prop) u u' : Prop :=
    match usort u, usort u' with
    | sProp,   sProp
    | sSProp,  sSProp => True
    | sType, sType => eq_universe (ulvl u) (ulvl u')
    | _, _ => False
    end.

  Definition eq_univ φ := eq_univ_ (eq_ulvl φ).

  Definition eqb_univ_ {univ} (eqb_universe : univ -> univ -> bool) u u' : bool :=
    match usort u, usort u' with
    | sProp,   sProp
    | sSProp,  sSProp => true
    | sType, sType => eqb_universe (ulvl u) (ulvl u')
    | _, _ => false
    end.

  Definition compare_univ φ (pb : conv_pb) :=
    match pb with
    | Conv => eq_univ φ
    | Cumul => leq_univ φ
    end.

  Lemma leq_univ_leq_univ_n (φ : ConstraintSet.t) u u' :
    leq_univ φ u u' <-> leq_univ_n 0 φ u u'.
  Proof. intros. reflexivity. Qed.

  Lemma compare_univ_type φ pb l l' :
    compare_univ φ pb (Universe.mk sType l) (Universe.mk sType l') = compare_ulvl φ pb l l'.
  Proof. now destruct pb. Qed.

  Section GeneralLemmas.
    Context {univ} {leq_universe_n : Z -> univ -> univ -> Prop} {eq_universe : univ -> univ -> Prop}.

    Let leq_univ_n := leq_univ_n_ leq_universe_n.
    Let lt_univ := leq_univ_n_ leq_universe_n 1.
    Let leq_univ := leq_univ_n_ leq_universe_n 0.
    Let eq_univ := eq_univ_ eq_universe.
    Notation "x <_ n  y" := (leq_univ_n n x y) (at level 10, n name).
    Notation "x < y" := (lt_univ x y).
    Notation "x <= y" := (leq_univ x y).

    Lemma univ_le_prop_inv u l : u <= Universe.mk sProp l -> usort u = sProp.
    Proof using Type. destruct u as [[| |] l'] => //. Qed.

    Lemma univ_le_sprop_inv u l : u <= Universe.mk sSProp l -> usort u = sSProp.
    Proof using Type. destruct u as [[| |] l'] => //. Qed.

    Lemma univ_prop_le_inv u l : Universe.mk sProp l <= u ->
      (usort u = sProp \/ (prop_sub_type /\ exists n, u = Universe.mk sType n)).
    Proof using Type.
      destruct u as [[| |] l'] => //= Hle.
      - now left.
      - right; split => //; now eexists.
    Qed.

    Lemma univ_sprop_le_inv u l : Universe.mk sSProp l <= u -> usort u = sSProp.
    Proof using Type. destruct u as [[| |] l'] => //. Qed.

    Global Instance leq_univ_refl `{Reflexive univ (leq_universe_n 0)} : Reflexive leq_univ.
    Proof using Type. intros [[| |] l]; cbnr. Qed.

    Global Instance eq_univ_refl `{Reflexive univ eq_universe} : Reflexive eq_univ.
    Proof using Type. intros [[| |] l]; cbnr. Qed.

    Global Instance eq_univ_sym `{Symmetric univ eq_universe} : Symmetric eq_univ.
    Proof using Type. intros [[| |] l] [[| |] l'] => //=. apply H. Qed.

    Global Instance leq_univ_n_trans n `{Transitive univ (leq_universe_n n)} : Transitive (leq_univ_n n).
    Proof using Type.
      intros [[| |] l1] [[| |] l2] [[| |] l3] => //=. apply H.
    Qed.

    Global Instance leq_univ_trans `{Transitive univ (leq_universe_n 0)} : Transitive leq_univ.
    Proof using Type. apply (leq_univ_n_trans 0). Qed.

    Global Instance lt_univ_trans `{Transitive univ (leq_universe_n 1)} : Transitive lt_univ.
    Proof using Type. apply (leq_univ_n_trans 1). Qed.

    Global Instance eq_univ_trans `{Transitive univ eq_universe} : Transitive eq_univ.
    Proof using Type.
      intros [[| |] l1] [[| |] l2] [[| |] l3] => //=. apply H.
    Qed.

    Global Instance leq_univ_preorder `{PreOrder univ (leq_universe_n 0)} : PreOrder leq_univ :=
      Build_PreOrder _ _ _.

    (* Can't be a global instance since it can lead to infinite search *)
    Lemma lt_univ_irrefl : Irreflexive (leq_universe_n 1) -> Irreflexive lt_univ.
    Proof using Type.
      intros H [[| |] l]; unfold complement; cbnr. 1,2: lia. apply H.
    Qed.

    Global Instance lt_univ_str_order `{StrictOrder univ (leq_universe_n 1)} : StrictOrder lt_univ :=
      Build_StrictOrder _ (lt_univ_irrefl _) _.

    Global Instance eq_leq_univ `{subrelation univ eq_universe (leq_universe_n 0)}: subrelation eq_univ leq_univ.
    Proof using Type.
      intros [[| |] l1] [[| |] l2] => //=. apply H.
    Qed.

    Global Instance eq_univ_equivalence `{Equivalence univ eq_universe} : Equivalence eq_univ := Build_Equivalence _ _ _ _.

    Global Instance leq_univ_antisym `{Antisymmetric _ eq_universe (leq_universe_n 0)} : Antisymmetric _ eq_univ leq_univ.
    Proof using Type.
      intros [[| |] l1] [[| |] l2] => //=. apply H.
    Qed.

    Global Instance leq_univ_partial_order `{PartialOrder _ eq_universe (leq_universe_n 0)}: PartialOrder eq_univ leq_univ.
    Proof.
      assert (subrelation eq_universe (leq_universe_n 0)).
      { intros u u' Hu. specialize (H u u'); cbn in H. apply H in Hu. apply Hu. }
      assert (subrelation eq_universe (flip (leq_universe_n 0))).
      { intros u u' Hu. specialize (H u u'); cbn in H. apply H in Hu. apply Hu. }
      intros s s'. split.
      - intro Heq. split.
        + now eapply eq_leq_univ.
        + now eapply eq_leq_univ.
      - intros [Hle Hge]. now eapply leq_univ_antisym.
    Qed.

  End GeneralLemmas.

  (** Universes with linear hierarchy *)
  Definition concrete_univ := Universe.t_ Sort.t nat.

  (** u + n <= u' *)
  Definition leq_cuniv_n : Z -> concrete_univ -> concrete_univ -> Prop :=
    leq_univ_n_ (fun n u u' => (Z.of_nat u <= Z.of_nat u' - n)%Z).

  Definition leq_cuniv := leq_cuniv_n 0.
  Definition lt_cuniv := leq_cuniv_n 1.

  Notation "x <_ n  y" := (leq_univ_n n x y) (at level 10, n name) : univ_scope.
  Notation "x < y" := (lt_cuniv x y) : univ_scope.
  Notation "x <= y" := (leq_cuniv x y) : univ_scope.

  Definition is_propositional_or_set u :=
    match usort u with
	| sSProp | sProp => true
	| sType => eqb (ulvl u) 0
	end.

  Lemma cuniv_sup_comm u u' : Universe.csup u u' = Universe.csup u' u.
  Proof using Type.
    destruct u as [[| |] n], u' as [[| |] m] => //=; cbnr; f_equal; lia.
  Qed.

  Lemma cuniv_sup_not_uproplevel u u' :
    ~ Universe.is_propositional u -> ∑ n, Universe.csup u u' = Universe.mk sType n.
  Proof using Type.
    destruct u as [[| |] n] => //=.
    destruct u' as [[| |] m]; now eexists.
  Qed.

  Lemma cuniv_sup_mon u0 u' l l' : (u0 <= u')%u -> (Universe.mk sType l <= Universe.mk sType l')%u ->
    (Universe.csup u0 (Universe.mk sType l) <= Universe.csup u' (Universe.mk sType l'))%u.
  Proof using Type.
    destruct u0 as [[| |] l0], u' as [[| |] l0'] => //=; cbn; intros Hle Hle'; lia.
  Qed.

  Lemma leq_cuniv_of_product_mon u u' v v' :
    (u <= u')%u ->
    (v <= v')%u ->
    (Universe.cuniv_of_product u v <= Universe.cuniv_of_product u' v')%u.
  Proof using Type.
    intros Hle1 Hle2.
    destruct v as [[| |] l], v' as [[| |] l']; cbn in Hle2 |- *; auto.
    - destruct u' as [[| |] l'']; cbn; assumption.
    - apply cuniv_sup_mon; assumption.
  Qed.

  Lemma impredicative_cuniv_product {ulvl} {type0} {univ_sup} {l u} :
    Universe.is_propositional u ->
    Universe.univ_of_product_ (ulvl := ulvl) type0 univ_sup l u = u.
  Proof using Type. now destruct u as [[| |] l0]. Qed.

  Lemma leq_univ_sup_l φ u1 s2 :
    let s1 := Universe.mk sType u1 in
    leq_univ φ s1 (Universe.sup s1 s2).
  Proof using Type.
    destruct s2 as [[| |] u2]; cbnr.
    apply leq_ulvl_sup_l.
  Qed.

  Lemma leq_univ_sup_r φ s1 u2 :
    let s2 := Universe.mk sType u2 in
    leq_univ φ s2 (Universe.sup s1 s2).
  Proof using Type.
    destruct s1 as [[| |] u1]; cbnr.
    apply leq_ulvl_sup_r.
  Qed.

  Lemma leq_univ_product φ (s1 s2 : Universe.t)
    : leq_univ φ s2 (Universe.univ_of_product s1 s2).
  Proof using Type.
    destruct s2 as [[| |] u2] => //.
    apply leq_univ_sup_r.
  Qed.
  (* Rk: [leq_universe φ s1 (univ_of_product s1 s2)] does not hold due to
      impredicativity. *)

  Global Instance lt_univ_irrefl' {c: check_univs} φ (H: consistent φ) : Irreflexive (lt_univ φ).
  Proof.
    unshelve eapply lt_univ_irrefl.
    now unshelve eapply lt_ulvl_irrefl.
  Qed.

  Global Instance lt_univ_str_order' {c: check_univs} φ (H: consistent φ) : StrictOrder (lt_univ φ).
  Proof using Type.
    unshelve eapply lt_univ_str_order.
    now unshelve eapply lt_ulvl_str_order.
  Qed.

  Global Instance compare_univ_subrel φ pb : subrelation (eq_univ φ) (compare_univ φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_sort_refl φ pb : Reflexive (compare_univ φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_sort_trans φ pb : Transitive (compare_univ φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Global Instance compare_sort_preorder φ pb : PreOrder (compare_univ φ pb).
  Proof using Type.
    destruct pb; tc.
  Qed.

  Definition eq_leq_univ' φ leq_universe eq_universe Hsub u u'
    := @eq_leq_univ φ leq_universe eq_universe Hsub u u'.
  Definition leq_univ_refl' φ leq_universe leq_refl u
    := @leq_univ_refl φ leq_universe leq_refl u.

  Hint Resolve eq_leq_ulvl' leq_ulvl_refl' : core.

  Lemma cmp_univ_subset φ φ' pb t u
    : ConstraintSet.Subset φ φ'
      -> compare_univ φ pb t u -> compare_univ φ' pb t u.
  Proof using Type.
    intros Hctrs.
    destruct pb, t as [[| |] l], u as [[| |] l']; cbnr; trivial.
    all: intros H; unfold_ulvl_rel;
    apply H.
    all: eapply satisfies_subset; eauto.
  Qed.

  Lemma eq_univ_subset ctrs ctrs' t u
    : ConstraintSet.Subset ctrs ctrs'
      -> eq_univ ctrs t u -> eq_univ ctrs' t u.
  Proof using Type. apply cmp_univ_subset with (pb := Conv). Qed.

  Lemma leq_univ_subset ctrs ctrs' t u
    : ConstraintSet.Subset ctrs ctrs'
      -> leq_univ ctrs t u -> leq_univ ctrs' t u.
  Proof using Type. apply cmp_univ_subset with (pb := Cumul). Qed.
End UnivCompare.

Definition relevance_of_family (s : Sort.t) :=
  match s with
  | sSProp => Irrelevant
  | _ => Relevant
  end.

#[global] Opaque relevance_of_family.

Notation rel_of_Type := (relevance_of_family sType).
Notation relevance_of_univ s := (relevance_of_family (Universe.to_family s)).

Notation isUnivRel s rel := (relevance_of_univ s = rel).
Notation isUnivRelOpt s relopt :=
  (option_default (fun rel => isUnivRel s rel) relopt True).

(** Elimination restriction *)

(** This inductive classifies which eliminations are allowed for inductive types
  in various sorts. *)
Inductive allowed_eliminations : Set :=
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny.
Derive NoConfusion EqDec for allowed_eliminations.

Definition is_allowed_elimination_cuniv (allowed : allowed_eliminations) : concrete_univ -> bool :=
  match allowed with
  | IntoSProp => Universe.is_sprop
  | IntoPropSProp => Universe.is_propositional
  | IntoSetPropSProp => is_propositional_or_set
  | IntoAny => fun _ => true
  end.

Definition is_lSet {cf} φ s := eq_univ φ s Universe.type0.
  (* Unfolded definition :
  match s with
  | Universe.sType u =>
    if check_univs then forall v, satisfies v φ -> val v u = 0 else true
  | _ => false
  end. *)

Definition is_allowed_elimination {cf} φ allowed : Universe.t -> Prop :=
  match allowed with
  | IntoSProp => Universe.is_sprop
  | IntoPropSProp => Universe.is_propositional
  | IntoSetPropSProp => fun s => Universe.is_propositional s \/ is_lSet φ s
  | IntoAny => fun s => true
  end.

(* Is [a] a subset of [a']? *)
Definition allowed_eliminations_subset (a a' : allowed_eliminations) : bool :=
  match a, a' with
  | IntoSProp, _
  | IntoPropSProp, (IntoPropSProp | IntoSetPropSProp | IntoAny)
  | IntoSetPropSProp, (IntoSetPropSProp | IntoAny)
  | IntoAny, IntoAny => true
  | _, _ => false
  end.

Lemma allowed_eliminations_subset_impl {cf} φ a a' s
  : allowed_eliminations_subset a a' ->
    is_allowed_elimination φ a s -> is_allowed_elimination φ a' s.
Proof using Type.
  destruct a, a'; cbnr; trivial;
  destruct s as [[| |] l]; cbnr; trivial;
  intros H1 H2; try absurd; constructor; trivial.
Qed.

Lemma is_allowed_elimination_monotone `{cf : checker_flags} Σ s1 s2 a :
  leq_univ Σ s1 s2 -> is_allowed_elimination Σ a s2 -> is_allowed_elimination Σ a s1.
Proof.
  destruct a, s2 as [[| |] u2], s1 as [[| |] u1] => //=. 1: now left.
  intros Hle [H|]; right => //.
  unfold_ulvl_rel; cbn in H, Hle |- *; rewrite H in Hle;
  unfold eq_ulvl; unfold leq_ulvl_n, leq0_ulvl_n in Hle; destruct check_univs; auto.
  all: intros v hsat; specialize (Hle v hsat); cbn in *; lia.
Qed.

Section UnivCF2.
  Context {cf1 cf2 : checker_flags}.

  Lemma valid_config_impl φ ctrs
    : config.impl cf1 cf2 -> @valid_constraints cf1 φ ctrs
      -> @valid_constraints cf2 φ ctrs.
  Proof using Type.
    unfold valid_constraints, config.impl, is_true.
    do 2 destruct check_univs; trivial; cbn => //.
  Qed.

  Lemma cmp_universe_config_impl ctrs pb t u
    : config.impl cf1 cf2
      -> @compare_ulvl cf1 ctrs pb t u -> @compare_ulvl cf2 ctrs pb t u.
  Proof using Type.
    unfold config.impl, compare_ulvl, leq_ulvl, eq_ulvl, leq_ulvl_n, is_true.
    destruct pb; do 2 destruct check_univs => //=.
  Qed.

  Lemma eq_universe_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @eq_ulvl cf1 ctrs t u -> @eq_ulvl cf2 ctrs t u.
  Proof using Type. apply cmp_universe_config_impl with (pb := Conv). Qed.

  Lemma leq_universe_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @leq_ulvl cf1 ctrs t u -> @leq_ulvl cf2 ctrs t u.
  Proof using Type. apply cmp_universe_config_impl with (pb := Cumul). Qed.

  Lemma cmp_univ_config_impl ctrs pb t u
    : config.impl cf1 cf2
      -> @compare_univ cf1 ctrs pb t u -> @compare_univ cf2 ctrs pb t u.
  Proof using Type.
    unfold compare_univ, leq_univ, eq_univ, eq_univ_, leq_univ_n, leq_univ_n_, is_true.
    destruct pb, t as [[| |] t1], u as [[| |] u1] => //=.
    - apply eq_universe_config_impl.
    - unfold config.impl. do 2 destruct check_univs, prop_sub_type; cbn => //=.
    - apply leq_universe_config_impl.
  Qed.

  Lemma eq_univ_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @eq_univ cf1 ctrs t u -> @eq_univ cf2 ctrs t u.
  Proof using Type. apply cmp_univ_config_impl with (pb := Conv). Qed.

  Lemma leq_univ_config_impl ctrs t u
    : config.impl cf1 cf2
      -> @leq_univ cf1 ctrs t u -> @leq_univ cf2 ctrs t u.
  Proof using Type. apply cmp_univ_config_impl with (pb := Cumul). Qed.

  (** Elimination restriction *)

  Lemma allowed_eliminations_config_impl φ a s
    : config.impl cf1 cf2 ->
      @is_allowed_elimination cf1 φ a s -> @is_allowed_elimination cf2 φ a s.
  Proof using Type.
    destruct a, s as [[| |] l]; cbnr; trivial.
    unfold eq_ulvl, config.impl, is_true.
    do 2 destruct check_univs; cbnr; auto => //.
  Qed.

End UnivCF2.


Ltac unfold_univ_rel :=
  unfold is_allowed_elimination, is_lSet, valid_constraints,
  compare_univ, eq_univ, leq_univ, lt_univ, leq_univ_n, leq_univ_n_, eq_univ_, leqb_univ_n_, eqb_univ_,
  compare_ulvl, leq_ulvl, eq_ulvl, leq_ulvl_n in *;
  destruct check_univs; [unfold_ulvl_rel0 | trivial].

Tactic Notation "unfold_univ_rel" "eqn" ":"ident(H) :=
  unfold is_allowed_elimination, is_lSet, valid_constraints,
  compare_univ, eq_univ, leq_univ, lt_univ, leq_univ_n, leq_univ_n_, eq_univ_, leqb_univ_n_, eqb_univ_,
  compare_ulvl, leq_ulvl, eq_ulvl, leq_ulvl_n in *;
  destruct check_univs eqn:H; [unfold_ulvl_rel0 | trivial].

(* Ltac prop_non_prop :=
  match goal with
  | |- context[ Universe.is_prop ?u || Universe.is_sprop ?u]  =>
    destruct (Universe.is_prop u || Universe.is_sprop u)
  | H : context[ Universe.is_prop ?u || Universe.is_sprop ?u] |- _ =>
    destruct (Universe.is_prop u || Universe.is_sprop u)
  end. *)

Ltac cong := intuition congruence.

Lemma leq_relevance_eq {cf φ} {s s'} :
  leq_univ φ s s' -> relevance_of_univ s = relevance_of_univ s'.
Proof.
  now destruct s as [[| |] l], s' as [[| |] l'].
Qed.

Lemma leq_relevance_opt {cf φ} {s s' rel} :
  leq_univ φ s s' -> isUnivRelOpt s rel -> isUnivRelOpt s' rel.
Proof.
  now destruct s as [[| |] l], s' as [[| |] l'].
Qed.

Lemma leq_relevance {cf φ} {s s' rel} :
  leq_univ φ s s' -> isUnivRel s rel -> isUnivRel s' rel.
Proof.
    now destruct s as [[| |] l], s' as [[| |] l'].
Qed.

Lemma geq_relevance {cf φ} {s s' rel} :
  leq_univ φ s' s -> isUnivRel s rel -> isUnivRel s' rel.
Proof.
  now destruct s as [[| |] l], s' as [[| |] l'].
Qed.

Lemma relevance_super s : relevance_of_univ (Universe.super s) = rel_of_Type.
Proof using Type.
  now destruct s as [[| |] l].
Qed.

Lemma leq_univ_product_mon {cf} ϕ s1 s1' s2 s2' :
  leq_univ ϕ s1 s1' ->
  leq_univ ϕ s2 s2' ->
  leq_univ ϕ (Universe.univ_of_product s1 s2) (Universe.univ_of_product s1' s2').
Proof.
  destruct s2 as [[| |] u2], s2' as [[| |] u2']; cbnr; try absurd;
  destruct s1 as [[| |] u1], s1' as [[| |] u1']; cbnr; try absurd; trivial.
  - intros _ H2; etransitivity; [apply H2 | apply leq_ulvl_sup_r].
  - apply leq_universe_sup_mon.
Qed.

Lemma impredicative_product {cf} {ϕ l u} :
  Universe.is_propositional u ->
  leq_univ ϕ (Universe.univ_of_product l u) u.
Proof.
  destruct u as [[| |] v] => //; reflexivity.
Qed.

Section UniverseLemmas.
  Context {cf: checker_flags}.

  Lemma univ_sup_idem s : Universe.sup s s = s.
  Proof using Type.
    apply eq_univ'; cbn.
    intro; rewrite !LevelExprSet.union_spec. intuition.
  Qed.

  Lemma sup_idem s : Universe.sup s s = s.
  Proof using Type.
    destruct s as [[| |] l]; cbn; auto.
    apply f_equal.
    apply univ_sup_idem.
  Qed.

  Lemma sort_of_product_idem s
    : Universe.sort_of_product s s = s.
  Proof using Type.
    unfold Universe.sort_of_product; destruct s; try reflexivity.
    apply sup_idem.
  Qed.

  Lemma univ_sup_assoc s1 s2 s3 :
    Universe.sup s1 (Universe.sup s2 s3) = Universe.sup (Universe.sup s1 s2) s3.
  Proof using Type.
    apply eq_univ'; cbn. symmetry; apply LevelExprSetProp.union_assoc.
  Qed.

  Instance proper_univ_sup_eq_univ φ :
    Proper (eq_univ φ ==> eq_univ φ ==> eq_univ φ) Universe.sup.
  Proof using Type.
    intros u1 u1' H1 u2 u2' H2.
    unfold_ulvl_rel.
    rewrite !val_sup. lia.
  Qed.

  Instance proper_sort_sup_eq_sort φ :
    Proper (eq_sort φ ==> eq_sort φ ==> eq_sort φ) Universe.sup.
  Proof using Type.
    intros [| | u1] [| |u1'] H1 [| |u2] [| |u2'] H2; cbn in *; try absurd; auto.
    now apply proper_univ_sup_eq_univ.
  Qed.

  Lemma sort_of_product_twice u s :
    Universe.sort_of_product u (Universe.sort_of_product u s)
    = Universe.sort_of_product u s.
  Proof using Type.
    destruct u,s; cbnr.
    now rewrite univ_sup_assoc univ_sup_idem.
  Qed.
End UniverseLemmas.


Section no_prop_leq_type.
  Context {cf: checker_flags}.
  Context (ϕ : ConstraintSet.t).

  Lemma succ_inj x y : LevelExpr.succ x = LevelExpr.succ y -> x = y.
  Proof using Type.
    unfold LevelExpr.succ.
    destruct x as [l n], y as [l' n']. simpl. congruence.
  Qed.

  Lemma spec_map_succ l x :
    LevelExprSet.In x (Universe.succ l) <->
    exists x', LevelExprSet.In x' l /\ x = LevelExpr.succ x'.
  Proof using Type.
    rewrite map_spec. reflexivity.
  Qed.

  Lemma val_succ v l : val v (LevelExpr.succ l) = val v l + 1.
  Proof using Type.
    destruct l as []; simpl. cbn. lia.
  Qed.

  Lemma val_map_succ v l : val v (Universe.succ l) = val v l + 1.
  Proof using Type.
    pose proof (spec_map_succ l).
    set (n := Universe.succ l) in *.
    destruct (val_In_max l v) as [max [inmax eqv]]. rewrite <-eqv.
    rewrite val_caract. split.
    intros.
    specialize (proj1 (H _) H0) as [x' [inx' eq]]. subst e.
    rewrite val_succ. eapply (val_In_le _ v) in inx'. rewrite <- eqv in inx'.
    simpl in *. unfold LevelExprSet.elt, LevelExpr.t in *. lia.
    exists (LevelExpr.succ max). split. apply H.
    exists max; split; auto.
    now rewrite val_succ.
  Qed.

  Lemma leq_sort_super s s' :
    leq_sort ϕ s s' ->
    leq_sort ϕ (Universe.super s) (Universe.super s').
  Proof using Type.
    destruct s as [| | u1], s' as [| | u1']; cbnr; try absurd;
    intros H; unfold_univ_rel;
    rewrite !val_map_succ; lia.
  Qed.

  Lemma leq_sort_prop_no_prop_sub_type s1 s2 :
    prop_sub_type = false ->
    leq_sort ϕ s1 s2 ->
    Universe.is_prop s1 -> Universe.is_prop s2.
  Proof using Type.
    intros ps.
    destruct s1; cbn; [ | absurd | absurd].
    rewrite ps.
    destruct s2; cbn; [ auto | absurd | absurd].
  Qed.

  Hint Resolve leq_sort_prop_no_prop_sub_type : univ_lemmas.

  Lemma leq_prop_is_propositonal {s1 s2} :
    prop_sub_type = false ->
    leq_sort ϕ s1 s2 ->
    Universe.is_propositional s1 <-> Universe.is_propositional s2.
  Proof using Type.
    intros ps.
    destruct s1, s2; cbn; try absurd; intros H; split; trivial.
    now rewrite ps in H.
  Qed.


End no_prop_leq_type.


(* This level is a hack used in plugings to generate fresh levels *)
Definition fresh_level : Level.t := Level.level     "__metarocq_fresh_level__".
(* This universe is a hack used in plugins to generate fresh universes *)
Definition fresh_universe : Universe.t := Universe.make' fresh_level.

(** * Universe substitution

  Substitution of universe levels for universe level lvariables, used to
  implement universe polymorphism. *)


(** Substitutable type *)

Class UnivSubst A := subst_instance : Instance.t -> A -> A.

Notation "x @[ u ]" := (subst_instance u x) (at level 3,
  format "x @[ u ]").

#[global] Instance subst_instance_level : UnivSubst Level.t :=
  fun u l => match l with
            Level.lzero | Level.level     _ => l
          | Level.lvar n => List.nth n u Level.lzero
          end.

#[global] Instance subst_instance_cstr : UnivSubst UnivConstraint.t :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

#[global] Instance subst_instance_cstrs : UnivSubst ConstraintSet.t :=
  fun u ctrs => ConstraintSet.fold (fun c => ConstraintSet.add (subst_instance_cstr u c))
                                ctrs ConstraintSet.empty.

#[global] Instance subst_instance_level_expr : UnivSubst LevelExpr.t :=
  fun u e => match e with
          | (Level.lzero, _)
          | (Level.level     _, _) => e
          | (Level.lvar n, b) =>
            match nth_error u n with
            | Some l => (l,b)
            | None => (Level.lzero, b)
            end
          end.

#[global] Instance subst_instance_universe : UnivSubst Universe.t :=
  fun u => map (subst_instance_level_expr u).

#[global] Instance subst_instance_sort : UnivSubst Universe.t :=
  fun u e => match e with
          | sProp | sSProp => e
          | sType u' => sType (subst_instance u u')
          end.

Lemma subst_instance_to_family s u :
  Universe.to_family s@[u] = Universe.to_family s.
Proof.
  destruct s => //.
Qed.

#[global] Instance subst_instance_instance : UnivSubst Instance.t :=
  fun u u' => List.map (subst_instance_level u) u'.


Theorem relevance_subst_eq u s : relevance_of_sort (subst_instance_sort u s) = relevance_of_sort s.
Proof.
  now destruct s.
Qed.

Theorem relevance_subst_opt u rel s :
  isSortRelOpt s rel -> isSortRelOpt (subst_instance_sort u s) rel.
Proof.
  now destruct s.
Qed.

Theorem relevance_subst u rel s :
  isSortRel s rel -> isSortRel (subst_instance_sort u s) rel.
Proof.
  now destruct s.
Qed.


(** Tests that the term is closed over [k] universe variables *)
Section Closedu.
  Context (k : nat).

  Definition closedu_level (l : Level.t) :=
    match l with
    | Level.lvar n => (n <? k)%nat
    | _ => true
    end.

  Definition closedu_level_expr (s : LevelExpr.t) :=
    closedu_level (LevelExpr.get_level s).

  Definition closedu_universe (u : Universe.t) :=
    LevelExprSet.for_all closedu_level_expr u.

  Definition closedu_sort (u : Universe.t) :=
    match u with
    | sSProp | sProp => true
    | sType l => closedu_universe l
    end.

  Definition closedu_instance (u : Instance.t) :=
    forallb closedu_level u.
End Closedu.

(** Universe-closed terms are unaffected by universe substitution. *)
Section UniverseClosedSubst.
  Lemma closedu_subst_instance_level u l
  : closedu_level 0 l -> subst_instance_level u l = l.
  Proof.
    destruct l; cbnr. discriminate.
  Qed.

  Lemma closedu_subst_instance_level_expr u e
    : closedu_level_expr 0 e -> subst_instance_level_expr u e = e.
  Proof.
    intros.
    destruct e as [t b]. destruct t;cbnr. discriminate.
  Qed.

  Lemma closedu_subst_instance_univ u s
    : closedu_sort 0 s -> subst_instance_sort u s = s.
  Proof.
    intro H.
    destruct s as [| | t]; cbnr.
    apply f_equal. apply eq_univ'.
    destruct t as [ts H1].
    unfold closedu_universe in *;cbn in *.
    intro e; split; intro He.
    - apply map_spec in He. destruct He as [e' [He' X]].
      rewrite closedu_subst_instance_level_expr in X.
      apply LevelExprSet.for_all_spec in H; proper.
      exact (H _ He').
      now subst.
    - apply map_spec. exists e; split; tas.
      symmetry; apply closedu_subst_instance_level_expr.
      apply LevelExprSet.for_all_spec in H; proper. now apply H.
  Qed.

  Lemma closedu_subst_instance u t
    : closedu_instance 0 t -> subst_instance u t = t.
  Proof.
    intro H. apply forall_map_id_spec.
    apply Forall_forall; intros l Hl.
    apply closedu_subst_instance_level.
    eapply forallb_forall in H; eassumption.
  Qed.

End UniverseClosedSubst.

#[global]
Hint Resolve closedu_subst_instance_level closedu_subst_instance_level_expr
     closedu_subst_instance_univ closedu_subst_instance : substu.

(** Substitution of a universe-closed instance of the right size
    produces a universe-closed term. *)
Section SubstInstanceClosed.
  Context (u : Instance.t) (Hcl : closedu_instance 0 u).

  Lemma subst_instance_level_closedu l
    : closedu_level #|u| l -> closedu_level 0 (subst_instance_level u l).
  Proof using Hcl.
    destruct l; cbnr.
    unfold closedu_instance in Hcl.
    destruct (nth_in_or_default n u Level.lzero).
    - intros _. eapply forallb_forall in Hcl; tea.
    - rewrite e; reflexivity.
  Qed.

  Lemma subst_instance_level_expr_closedu e :
    closedu_level_expr #|u| e -> closedu_level_expr 0 (subst_instance_level_expr u e).
  Proof using Hcl.
    destruct e as [l b]. destruct l;cbnr.
    case_eq (nth_error u n); cbnr. intros [] Hl X; cbnr.
    apply nth_error_In in Hl.
    eapply forallb_forall in Hcl; tea.
    discriminate.
  Qed.

  Lemma subst_instance_univ_closedu s
    : closedu_sort #|u| s -> closedu_sort 0 (subst_instance_sort u s).
  Proof using Hcl.
    intro H.
    destruct s as [| |t]; cbnr.
    destruct t as [l Hl].
    apply LevelExprSet.for_all_spec; proper.
    intros e He. eapply map_spec in He.
    destruct He as [e' [He' X]]; subst.
    apply subst_instance_level_expr_closedu.
    apply LevelExprSet.for_all_spec in H; proper.
    now apply H.
  Qed.

  Lemma subst_instance_closedu t :
    closedu_instance #|u| t -> closedu_instance 0 (subst_instance u t).
  Proof using Hcl.
    intro H. etransitivity. eapply forallb_map.
    eapply forallb_impl; tea.
    intros l Hl; cbn. apply subst_instance_level_closedu.
  Qed.
End SubstInstanceClosed.

#[global]
Hint Resolve subst_instance_level_closedu subst_instance_level_expr_closedu
     subst_instance_univ_closedu subst_instance_closedu : substu.


Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lzero => "Set"
  | Level.level     s => s
  | Level.lvar n => "lvar" ^ string_of_nat n
  end.

Definition string_of_level_expr (e : LevelExpr.t) : string :=
  let '(l, n) := e in string_of_level l ^ (if n is 0 then "" else "+" ^ string_of_nat n).

Definition string_of_sort (u : Universe.t) :=
  match u with
  | sSProp => "SProp"
  | sProp => "Prop"
  | sType l => "Type(" ^ string_of_list string_of_level_expr (LevelExprSet.elements l) ^ ")"
  end.

Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Inductive universes_entry :=
| Monomorphic_entry (ctx : ContextSet.t)
| Polymorphic_entry (ctx : UContext.t).
Derive NoConfusion for universes_entry.

Definition universes_entry_of_decl (u : universes_decl) : universes_entry :=
  match u with
  | Polymorphic_ctx ctx => Polymorphic_entry (Universes.AUContext.repr ctx)
  | Monomorphic_ctx => Monomorphic_entry ContextSet.empty
  end.

Definition polymorphic_instance uctx :=
  match uctx with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx c => fst (snd (AUContext.repr c))
  end.
(* TODO: duplicate of polymorphic_instance *)
Definition abstract_instance decl :=
  match decl with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx auctx => UContext.instance (AUContext.repr auctx)
  end.

Definition print_universe_instance u :=
  match u with
  | [] => ""
  | _ => "@{" ^ print_list string_of_level " " u ^ "}"
  end.

Definition print_lset t :=
  print_list string_of_level " " (LevelSet.elements t).

Definition print_constraint_type d :=
  match d with
  | ConstraintType.Le n =>
    if (n =? 0)%Z then "<=" else
    if (n =? 1)%Z then "<" else
    if (n <? 0)%Z then "<=" ^ string_of_nat (Z.to_nat (Z.abs n)) ^ " + "
    else " + " ^ string_of_nat (Z.to_nat n) ^ " <= "
  | ConstraintType.Eq => "="
  end.

Definition print_constraint_set t :=
  print_list (fun '(l1, d, l2) => string_of_level l1 ^ " " ^
                         print_constraint_type d ^ " " ^ string_of_level l2)
             " /\ " (ConstraintSet.elements t).
