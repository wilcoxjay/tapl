(* This file formalizes a simplified version of the system from chapters 15 and 16 of TAPL.
   In particular, I've left out records.

   To build this you'll need a copy of https://github.com/wilcoxjay/jrwlib
*)
Require Import List.
Import ListNotations.
Require Import Tactics ListUtil Alists ANYsig.
Require Import Arith.

Set Implicit Arguments.

Module type.
Inductive t : Type :=
| Top : t
| bool : t
| arrow : t -> t -> t
.
End type.

Module Var.
  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
End Var.

Module Exp.
Inductive t : Type :=
| Var : Var.t -> t
| Const : bool -> t
| If : t -> t -> t -> t
| Abs : Var.t -> type.t -> t -> t
| Ap : t -> t -> t
.

Fixpoint freevars (e : t) : list Var.t :=
  match e with
  | Var v => [v]
  | Const _ => []
  | If e1 e2 e3 => freevars e1 ++ freevars e2 ++ freevars e3
  | Abs v _ e' => remove Var.eq_dec v (freevars e')
  | Ap e1 e2 => freevars e1 ++ freevars e2
  end.

(* note that this is not capture avoiding: it assumes that the argument `to` is closed,
   which is sufficient for use in a call-by-value dynamics. *)
Fixpoint subst (from : Var.t) (to : t) (e : t) : t :=
  match e with
  | Var v => if Var.eq_dec from v then to else e
  | Const b => Const b
  | If e1 e2 e3 => If (subst from to e1) (subst from to e2) (subst from to e3)
  | Abs v ty e' => if Var.eq_dec from v then e else Abs v ty (subst from to e')
  | Ap e1 e2 => Ap (subst from to e1) (subst from to e2)
  end.
End Exp.

Require Import NatEq.
Module NatAlist' := Alist(NatEq).
Module NatAlist := Alist_Util(NatAlist').
Module TypeAny : ANY with Definition t := type.t.
  Definition t := type.t.
End TypeAny.

Module Context : MONO_ALIST_UTIL
    with Definition Key.t := Var.t
    with Definition Value.t := type.t
   := SpecializeAlistUtil(NatAlist)(TypeAny).

Module subtype.
  Inductive t : type.t -> type.t -> Prop :=
  | refl : forall ty, t ty ty
  | trans : forall ty1 ty2 ty3, t ty1 ty2 -> t ty2 ty3 -> t ty1 ty3
  | top : forall ty, t ty type.Top
  | arrow : forall s1 s2 t1 t2, t s2 s1 -> t t1 t2 -> t (type.arrow s1 t1) (type.arrow s2 t2).
  Hint Constructors t.
End subtype.


Module has_type.
  Inductive t : Context.t -> Exp.t -> type.t -> Prop :=
  | Var : forall G v ty, Context.get G v = Some ty -> t G (Exp.Var v) ty
  | Const : forall G b, t G (Exp.Const b) type.bool
  | If : forall G e1 e2 e3 ty, t G e1 type.bool ->
                       t G e2 ty ->
                       t G e3 ty ->
                       t G (Exp.If e1 e2 e3) ty
  | Abs : forall G x e' tya tyr,
      t (Context.set G x tya) e' tyr ->
      t G (Exp.Abs x tya e') (type.arrow tya tyr)
  | Ap : forall G e12 e1 ty1 ty2,
      t G e12 (type.arrow ty1 ty2) ->
      t G e1 ty1 ->
      t G (Exp.Ap e12 e1) ty2
  | Sub : forall G e ty ty',
      subtype.t ty ty' ->
      t G e ty ->
      t G e ty'.
  Hint Constructors t.
End has_type.

Module val.
  Inductive t : Exp.t -> Prop :=
  | Const : forall b, t (Exp.Const b)
  | Abs : forall x ty e', t (Exp.Abs x ty e').
  Hint Constructors t.
End val.

Module step.
  Inductive t : Exp.t -> Exp.t -> Prop :=
  | If1 : forall e1 e1' e2 e3, t e1 e1' -> t (Exp.If e1 e2 e3) (Exp.If e1' e2 e3)
  | Iftrue : forall e2 e3, t (Exp.If (Exp.Const true) e2 e3) e2
  | Iffalse : forall e2 e3, t (Exp.If (Exp.Const false) e2 e3) e3
  | Ap1 : forall e1 e1' e2, t e1 e1' -> t (Exp.Ap e1 e2) (Exp.Ap e1' e2)
  | Ap2 : forall v e2 e2', val.t v -> t e2 e2' -> t (Exp.Ap v e2) (Exp.Ap v e2')
  | beta : forall x ty e1 v, val.t v -> t (Exp.Ap (Exp.Abs x ty e1) v) (Exp.subst x v e1).
  Hint Constructors t.
End step.

Hint Resolve in_remove_intro.
Lemma ext :
  forall G G' e ty,
    (forall x, In x (Exp.freevars e) -> Context.get G x = Context.get G' x) ->
    has_type.t G e ty ->
    has_type.t G' e ty.
Proof.
  intros G G' e ty HG He.
  generalize dependent G'.
  induction He; simpl; intros G' HG; econstructor; eauto 7 with *.
  - rewrite <- HG; simpl; intuition.
  - apply IHHe. intros.
    rewrite Context.get_set.
    rewrite Context.get_set.
    break_if; auto.
Qed.

Lemma has_type_freevars :
  forall G e ty x,
    has_type.t G e ty ->
    In x (Exp.freevars e) ->
    exists tyx, Context.get G x = Some tyx.
Proof.
  intros G e ty x He.
  generalize dependent x.
  induction He; simpl; intros y Hy;
    repeat match goal with
           | [ H : In _ (_ ++ _) |- _ ] => apply in_app_or in H; intuition
           end; intuition.
  - subst. eauto.
  - match goal with
    | [ H : In _ (remove _ _ _) |- _ ] => apply in_remove_elim in H; intuition
    end.
    apply IHHe in H0.
    break_exists_exists.
    rewrite Context.get_set in *.
    break_if; try congruence.
Qed.

Lemma weakening_empty :
  forall G e ty,
    has_type.t Context.empty e ty ->
    has_type.t G e ty.
Proof.
  intros.
  apply ext with (G := Context.empty); auto.
  intros x Hx.
  eapply has_type_freevars in H; eauto.
  break_exists.
  rewrite Context.get_empty in *.
  discriminate.
Qed.

Lemma substitution : forall e G x tyx ty ex,
    has_type.t (Context.set G x tyx) e ty ->
    has_type.t Context.empty ex tyx ->
    has_type.t G (Exp.subst x ex e) ty.
Proof.
  intros.
  remember (Context.set G x tyx) as G'.
  assert (Context.equiv (Context.set G x tyx) G') by (subst; apply Context.equiv_refl).
  clear HeqG'.

  generalize dependent x.
  generalize dependent tyx.
  generalize dependent G.
  generalize dependent ex.
  induction H; intros ey G0 tyy Hey y HeqG'; subst; simpl; try break_if; subst; eauto.
  - erewrite <- Context.equiv_get in H by eauto.
    rewrite Context.get_set in *.
    break_if; try congruence.
    find_inversion.
    auto using weakening_empty.
  - erewrite <- Context.equiv_get in H by eauto.
    rewrite Context.get_set in *.
    break_if; try congruence.
    eauto.
  - constructor. eapply ext; try eassumption.
    intros.
    rewrite !Context.get_set.
    break_if; try congruence.
    erewrite <- Context.equiv_get by eauto.
    rewrite !Context.get_set.
    break_if; congruence.
  - constructor. eapply IHt; eauto.
    eapply Context.equiv_trans; [apply Context.set_swap_neq; congruence|].
    auto using  Context.set_preserves_equiv.
Qed.

Lemma arrow_inversion :
  forall tau ty1 ty2,
    subtype.t tau (type.arrow ty1 ty2) ->
    exists tau1 tau2, tau = type.arrow tau1 tau2 /\
                 subtype.t ty1 tau1 /\
                 subtype.t tau2 ty2.
Proof.
  intros tau ty1 ty2 H.
  remember (type.arrow ty1 ty2) as ty.
  revert ty1 ty2 Heqty.
  induction H; intros ty1' ty2' Heqty'; subst; eauto.
  - specialize (IHt2 ty1' ty2'). concludes.
    break_exists_name tau1. break_exists_name tau2. break_and. subst.
    specialize (IHt1 tau1 tau2). concludes.
    break_exists_name tau1'. break_exists_name tau2'. break_and. subst.
    eauto 10.
  - congruence.
  - invc Heqty'. eauto.
Qed.

Lemma abs_inversion :
  forall G x ty e ty1 ty2,
    has_type.t G (Exp.Abs x ty e) (type.arrow ty1 ty2) ->
    subtype.t ty1 ty /\
    has_type.t (Context.set G x ty) e ty2.
Proof.
  intros G x ty e ty1 ty2 H.
  remember (Exp.Abs x ty e) as e'.
  remember (type.arrow ty1 ty2) as tau.
  revert e x ty ty1 ty2 Heqe' Heqtau .
  induction H; intros e'' x' ty'' ty1' ty2' Heqe' Heqtau; subst; try invc Heqe'.
  - invc Heqtau. auto.
  - apply arrow_inversion in H.
    break_exists_name ty1. break_exists_name ty2. break_and. subst.
    specialize (IHt e'' x' ty'' ty1 ty2). repeat concludes. break_and.
    eauto.
Qed.

Theorem preservation :
  forall e ty e', has_type.t Context.empty e ty ->
             step.t e e' ->
             has_type.t Context.empty e' ty.
Proof.
  intros e ty e' Hty Hstep.
  remember Context.empty as G.
  revert e' Hstep HeqG.
  induction Hty; intros e'' Hstep HeqG; subst; invc Hstep; eauto.
  apply abs_inversion in Hty1.
  break_and.
  eapply substitution; eauto.
Qed.

Lemma bool_inversion :
  forall ty, subtype.t ty type.bool ->
        ty = type.bool.
Proof.
  intros ty H.
  prep_induction H.
  induction H; intros; subst; try discriminate; auto.
  concludes. subst. concludes. auto.
Qed.

Lemma canonical_forms_bool :
  forall e,
    has_type.t Context.empty e type.bool ->
    val.t e ->
    exists b, e = Exp.Const b.
Proof.
  intros e Hht Hv.
  prep_induction Hht.
  induction Hht; intros Hv; invc Hv; intros H1 H2; subst.
  - eauto.
  - discriminate.
  - eauto.
  - apply bool_inversion in H. subst.
    repeat concludes.
    auto.
Qed.

Lemma canonical_forms_arrow :
  forall e ty1 ty2,
    has_type.t Context.empty e (type.arrow ty1 ty2) ->
    val.t e ->
    exists x ty e', e = Exp.Abs x ty e' /\ subtype.t ty1 ty.
Proof.
  intros e ty1 ty2 Hty Hv.
  prep_induction Hty.
  induction Hty; intros ty1' ty2' Hv H1 H2; subst.
  - rewrite Context.get_empty in *. discriminate.
  - discriminate.
  - invc Hv.
  - invc H1. eauto.
  - invc Hv.
  - apply arrow_inversion in H.
    break_exists_name tau1. break_exists_name tau2. break_and. subst.
    specialize (IHHty tau1 tau2). repeat concludes.
    break_exists. break_and. subst. eauto 10.
Qed.

Theorem progress :
  forall e ty,
    has_type.t Context.empty e ty ->
    val.t e \/ exists e', step.t e e'.
Proof.
  intros e ty H.
  remember Context.empty as G.
  revert HeqG.
  induction H; intros; subst; repeat concludes.
  - rewrite Context.get_empty in *. discriminate.
  - auto.
  - right. destruct IHt1.
    + eapply canonical_forms_bool in H2; eauto.
      break_exists_name b. subst.
      destruct b; eauto.
    + break_exists_name e'. eauto.
  - auto.
  - right. destruct IHt1; [destruct IHt2|].
    + eapply canonical_forms_arrow in H; eauto.
      break_exists_name x.
      break_exists_name ty.
      break_exists_name e'.
      break_and.
      subst.
      eauto.
    + break_exists. eauto.
    + break_exists. eauto.
  - auto.
Qed.


Module algo_subtype.
  Inductive t : type.t -> type.t -> Prop :=
  | top : forall S, t S type.Top
  | arrow : forall S1 S2 T1 T2, t S2 S1 -> t T1 T2 -> t (type.arrow S1 T1) (type.arrow S2 T2)
  | bool_refl : t type.bool type.bool.
  Hint Constructors t.

  Lemma refl : forall T, t T T.
  Proof.
    induction T; auto.
  Qed.

  Lemma trans' : forall T1 T2 T3,
      (t T1 T2 -> t T2 T3 -> t T1 T3) /\
      (t T2 T1 -> t T3 T2 -> t T3 T1).
  Proof.
    induction T1; intros T2 T3; split; intros H12 H23;
      repeat match goal with
             | [ H : t type.Top _ |- _ ] => invc H
             | [ H : t type.bool _ |- _ ] => invc H
             | [ H : t _ type.bool |- _ ] => invc H
             | [ H : t (type.arrow _ _) _ |- _ ] => invc H
             | [ H : t _ (type.arrow _ _) |- _ ] => invc H
             end; auto.
    constructor; firstorder.
    constructor; firstorder.
  Qed.
  Lemma trans : forall T1 T2 T3,
      t T1 T2 -> t T2 T3 -> t T1 T3.
  Proof.
    firstorder using trans'.
  Qed.

  Theorem soundness : forall S T, t S T -> subtype.t S T.
  Proof.
    induction 1; auto.
  Qed.

  Theorem completeness : forall S T, subtype.t S T -> t S T.
  Proof.
    induction 1; eauto using refl, trans.
  Qed.
End algo_subtype.

Module lattice.
  Definition join (S T ST: type.t) : Prop :=
    subtype.t S ST /\
    subtype.t T ST /\
    (forall U, subtype.t S U -> subtype.t T U -> subtype.t ST U).

  Definition equiv (S T : type.t) : Prop :=
    subtype.t S T /\ subtype.t T S.

  Lemma join_unique_up_to_equiv :
    forall S T ST1 ST2,
      join S T ST1 ->
      join S T ST2 ->
      equiv ST1 ST2.
  Proof.
    unfold join, equiv.
    intuition.
  Qed.

  Definition meet (S T ST: type.t) : Prop :=
    subtype.t ST S /\
    subtype.t ST T /\
    (forall U, subtype.t U S -> subtype.t U T -> subtype.t U ST).

  Lemma meet_unique_up_to_equiv :
    forall S T ST1 ST2,
      meet S T ST1 ->
      meet S T ST2 ->
      equiv ST1 ST2.
  Proof.
    unfold meet, equiv.
    intuition.
  Qed.

  Fixpoint find_meet (S T : type.t) : option type.t :=
    match S, T with
    | type.Top, _ => Some T
    | _, type.Top => Some S
    | type.bool, type.bool => Some type.bool
    | type.arrow S1 S2, type.arrow T1 T2 =>
      match find_meet S2 T2 with
      | None => None
      | Some ST2 => Some (type.arrow (find_join S1 T1) ST2)
      end
    | _, _ => None
    end
  with find_join (S T : type.t) : type.t :=
    match S, T with
    | type.Top, _ => type.Top
    | _, type.Top => type.Top
    | type.bool, type.bool => type.bool
    | type.arrow S1 S2, type.arrow T1 T2 =>
      match find_meet S1 T1 with
      | None => type.Top
      | Some ST1 => type.arrow ST1  (find_join S2 T2)
      end
    | _, _ => type.Top
    end.

  Lemma meet_top_l : forall T, meet type.Top T T.
  Proof. unfold meet. intuition. Qed.

  Lemma join_top_l : forall T, join type.Top T type.Top.
  Proof. unfold join. intuition. Qed.

  Lemma meet_top_r : forall T, meet T type.Top T.
  Proof. unfold meet. intuition. Qed.

  Lemma join_top_r : forall T, join T type.Top type.Top.
  Proof. unfold join. intuition. Qed.

  Lemma meet_refl : forall T, meet T T T.
  Proof. unfold meet. intuition. Qed.

  Lemma join_refl : forall T, join T T T.
  Proof. unfold join. intuition. Qed.

  Lemma meet_sym : forall S T ST, meet S T ST -> meet T S ST.
  Proof. unfold meet. intuition. Qed.

  Lemma join_sym : forall S T ST, join S T ST -> join T S ST.
  Proof. unfold join. intuition. Qed.


  Lemma meet_arrow_intro :
    forall S1 S2 T1 T2 ST1_j ST2_m,
      join S1 T1 ST1_j ->
      meet S2 T2 ST2_m ->
      meet (type.arrow S1 S2) (type.arrow T1 T2) (type.arrow ST1_j ST2_m).
  Proof.
    unfold join, meet. intuition.
    repeat match goal with
           | [ H : subtype.t _ (type.arrow _ _) |- _ ] => apply arrow_inversion in H
           end.
    break_exists. break_and. subst. find_inversion. auto.
  Qed.

  Lemma join_arrow_intro :
    forall S1 S2 T1 T2 ST1_m ST2_j,
      meet S1 T1 ST1_m ->
      join S2 T2 ST2_j ->
      join (type.arrow S1 S2) (type.arrow T1 T2) (type.arrow ST1_m ST2_j).
  Proof.
    unfold join, meet. intuition.
    repeat match goal with
           | [ H : subtype.t (type.arrow _ _) _ |- _ ] =>
             apply algo_subtype.completeness in H; invc H
           | [ H : algo_subtype.t _ _ |- _ ] =>
             apply algo_subtype.soundness in H
           end; auto.
  Qed.

  Lemma bool_arrow_no_meet :
    forall S T U,
      meet type.bool (type.arrow S T) U -> False.
  Proof.
    unfold meet. intuition.
    repeat match goal with
           | [ H : subtype.t _ (type.arrow _ _) |- _ ] => apply arrow_inversion in H
           | [ H : subtype.t _ type.bool |- _ ] => apply bool_inversion in H
           end.
    break_exists. break_and. subst. discriminate.
  Qed.

  Lemma bool_arrow_join_top :
    forall S T,
      join type.bool (type.arrow S T) type.Top.
  Proof.
    unfold join. intuition.
    repeat match goal with
    | [ H : subtype.t _ _ |- _ ] => apply algo_subtype.completeness in H; invc H
    end.
    auto.
  Qed.

  Lemma meet_arrow_elim : forall S1 S2 T1 T2 ST,
      meet (type.arrow S1 S2) (type.arrow T1 T2) ST ->
      exists ST1 ST2,
        ST = type.arrow ST1 ST2 /\
        join S1 T1 ST1 /\
        meet S2 T2 ST2.
  Proof.
    unfold meet, join.
    intuition.
    repeat match goal with
           | [ H : subtype.t _ (type.arrow _ _) |- _ ] => apply arrow_inversion in H
           end.
    break_exists. break_and. subst.
    find_inversion.
    do 2 eexists. intuition eauto.
    - specialize (H2 (type.arrow U x0)).
      repeat concludes.
      apply arrow_inversion in H2. break_exists. break_and. find_inversion.
      auto.
    - specialize (H2 (type.arrow x U)).
      repeat concludes.
      apply arrow_inversion in H2. break_exists. break_and. find_inversion.
      auto.
  Qed.

  Fixpoint find_join_meet_correct S T :
      (forall ST, find_meet S T = Some ST -> meet S T ST) /\
      (find_meet S T = None -> forall ST, subtype.t ST S -> subtype.t ST T -> False) /\
      (join S T (find_join S T)).
  Proof.
    refine match S, T with
    | type.Top, _ => _
    | _, type.Top => _
    | type.bool, type.bool => _
    | type.arrow S1 S2, type.arrow T1 T2 => _
    | _, _ => _
    end; intuition; simpl in *; repeat break_match; repeat find_inversion; try discriminate;
    eauto using meet_top_l, join_top_l, meet_top_r, join_top_r, meet_refl, join_refl,
    meet_sym, join_sym, bool_arrow_no_meet, bool_arrow_join_top.
    - repeat match goal with
             | [ H : subtype.t _ _ |- _ ] => apply algo_subtype.completeness in H; invc H
             end; auto.
    - repeat match goal with
             | [ H : subtype.t _ _ |- _ ] => apply algo_subtype.completeness in H; invc H
             end; auto.
    - apply find_join_meet_correct in Heqo.
      apply meet_arrow_intro; auto. apply find_join_meet_correct.
    - repeat match goal with
             | [ H : subtype.t _ _ |- _ ] => apply algo_subtype.completeness in H; invc H
             end; auto.
      repeat match goal with
      | [ H : algo_subtype.t _ _ |- _ ] => apply algo_subtype.soundness in H
      end.
      eapply find_join_meet_correct; eauto.
    - apply find_join_meet_correct in Heqo.
      apply join_arrow_intro; auto. apply find_join_meet_correct.
    - unfold join. intuition.
      repeat match goal with
             | [ H : subtype.t _ _ |- _ ] => apply algo_subtype.completeness in H; invc H
             end; auto.
      repeat match goal with
      | [ H : algo_subtype.t _ _ |- _ ] => apply algo_subtype.soundness in H
      end.
      exfalso.
      eapply find_join_meet_correct; eauto.
  Qed.

  Lemma find_join_correct S T : join S T (find_join S T).
  Proof. apply find_join_meet_correct. Qed.
End lattice.

Module algo_type.
  Inductive t : Context.t -> Exp.t -> type.t -> Prop :=
  | Var : forall G v ty, Context.get G v = Some ty -> t G (Exp.Var v) ty
  | Const : forall G b, t G (Exp.Const b) type.bool
  | If : forall G e1 e2 e3 ty2 ty3,
      t G e1 type.bool ->
      t G e2 ty2 ->
      t G e3 ty3 ->
      t G (Exp.If e1 e2 e3) (lattice.find_join ty2 ty3)
  | Abs : forall G x e' tya tyr,
      t (Context.set G x tya) e' tyr ->
      t G (Exp.Abs x tya e') (type.arrow tya tyr)
  | Ap : forall G e1 e2 ty11 ty12 ty2,
      t G e1 (type.arrow ty11 ty12) ->
      t G e2 ty2 ->
      algo_subtype.t ty2 ty11 ->
      t G (Exp.Ap e1 e2) ty12.
  Hint Constructors t.

  Theorem soundness : forall G e ty, t G e ty -> has_type.t G e ty.
  Proof.
    induction 1; eauto using algo_subtype.soundness.
    pose proof lattice.find_join_correct ty2 ty3 as Hjoin.
    unfold lattice.join in Hjoin.
    intuition eauto.
  Qed.

  Theorem completeness : forall G e ty, has_type.t G e ty ->
                                   exists ty', t G e ty' /\ subtype.t ty' ty.
  Proof.
    induction 1; eauto.
    - break_exists. intuition. eexists. split.
      + constructor; eauto. find_apply_lem_hyp bool_inversion. subst. auto.
      + pose proof lattice.find_join_correct x0 x.
        unfold lattice.join in *.
        intuition.
    - break_exists_name ty'. break_and. eauto.
    - break_exists. break_and.
      find_apply_lem_hyp arrow_inversion.
      break_exists. break_and. subst.
      eexists. split.
      + econstructor. eauto. eauto. apply algo_subtype.completeness. eauto.
      + auto.
    - break_exists. break_and. eauto.
  Qed.
End algo_type.
