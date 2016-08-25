(******************************************************************************
 *** Formalized proofs to Section 4 of the paper                            ***
 *** "Decentralizing SDN Policies" by Padon et al., POPL 2015               ***
 ***                                                                        ***
 *** Compiles with Coq 8.5pl2                                               ***
 ***                                                                        ***
 *** Aleksandr Karbyshev, Oct 2014                                          ***
 ******************************************************************************)

Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter A : Type. (* Type of actions *)
Parameter E : Type. (* Type of events  *)

(* Equality of events is decidable. *)
Axiom E_eq_dec : forall e1 e2 : E, {e1 = e2} + {e1 <> e2}.

(* Types of histories, policies, and handler generators. *)
Definition History := list E.
Definition Handler := E -> option A.
Definition HandlerGenerator := History -> Handler.

Definition Policy := History -> E -> A.


(******************************************************************************
 ***                               Utilities                                ***
 ******************************************************************************)

Fixpoint subseq A (l1 l2 : list A) :=
  match l1, l2 with
    | [], _ => True 
    | h1 :: t1, [] => False
    | h1 :: t1, h2 :: t2 =>
      subseq (h1 :: t1) t2 \/
      h1 = h2 /\ subseq t1 t2
  end.

Lemma subseq_nil A (l : list A) :
  subseq [] l.
Proof. now case l. Qed.

Hint Resolve subseq_nil.

Lemma subseq_nil_2 A (l : list A) :
  subseq l [] -> l = [].
Proof. now case l. Qed.

Hint Resolve subseq_nil_2.

Lemma subseq_refl A (l : list A) :
  subseq l l.
Proof. induction l; now firstorder. Qed.

Hint Resolve subseq_refl.

Lemma subseq_trans A (l1 l2 l3 : list A) :
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
revert l2 l1.
induction l3; [now destruct l1; destruct l2 |].
induction l2; [destruct l1; try easy |].
now destruct l1; firstorder; subst; firstorder.
Qed.

Lemma subseq_cons_1 A a (l : list A) :
  subseq l (a :: l).
Proof. induction l; now firstorder. Qed.

Hint Resolve subseq_cons_1.

Lemma subseq_cons_2 A a (l : list A) :
  ~ subseq (a :: l) l.
Proof.
revert a.
induction l; [easy |].
intros b H.
inversion H.
- assert (H1 : subseq (a :: l) l).
  eapply subseq_trans.
  + eapply subseq_cons_1.
  + refine H0.
  + eapply IHl; eauto.
- now firstorder.
Qed.

Hint Resolve subseq_cons_2.

Lemma subseq_antisym A (l1 l2 : list A) :
  subseq l1 l2 -> subseq l2 l1 -> l1 = l2.
Proof.
revert l2.
induction l1; [now destruct l2 |].
intros.
destruct l2; [easy |].
assert (T := subseq_trans).
inversion H; inversion H0.
- exfalso.
  assert (Habs: subseq (a0 :: l2) l2).
  { apply (subseq_trans H2).
    eapply subseq_trans; eauto. }
  now eapply subseq_cons_2; eauto.
- destruct H2; subst.
  f_equal.
  now firstorder eauto.
- destruct H1; subst.
  f_equal.
  now firstorder eauto.
- destruct H1; subst.
  destruct H2; subst.
  now f_equal; auto.
Qed.

Hint Resolve subseq_antisym.

Lemma subseq_cons_elim_1 A a (l1 l2 : list A) :
  subseq (a :: l1) (a :: l2) -> subseq l1 l2.
Proof.
intro H.
inversion H; [| easy].
now eapply subseq_trans; eauto.
Qed.

Lemma subseq_cons_elim_2 A a1 a2 (neq : a1 <> a2) (l1 l2 : list A) :
  subseq (a1 :: l1) (a2 :: l2) -> subseq (a1 :: l1) l2.
Proof. intro H. now inversion H. Qed.

Lemma subseq_elim A a (l1 l2 : list A) :
  subseq l1 (a :: l2) ->
  (exists l1', l1 = a :: l1' /\ subseq l1' l2) \/
  subseq l1 l2.
Proof.
revert a l2.
induction l1 as [| a1 l1 IH]; [now auto |].
intros a2 l2 H.
inversion H; auto.
destruct H0; subst a2.
now firstorder.
Qed.


(******************************************************************************
 ***              I-history for the event handler generator I               ***
 ******************************************************************************)

Fixpoint Hgen (I : HandlerGenerator) (l : History) : History :=
  match l with
    | [] => []
    | h :: t =>
      match I (Hgen I t) h with
        | Some _ => Hgen I t
        | None => h :: Hgen I t
      end
  end.

Lemma Hgen_nil I :
  Hgen I [] = [].
Proof. easy. Qed.

Hint Rewrite Hgen_nil : hgen.

Lemma Hgen_cons_1 I l e :
  I (Hgen I l) e = None -> Hgen I (e :: l) = e :: Hgen I l.
Proof. intros eq. simpl. now rewrite eq. Qed.

Lemma Hgen_cons_2 I l e :
  forall a,
    I (Hgen I l) e = Some a ->
    Hgen I (e :: l) = Hgen I l.
Proof. intros a eq. simpl. now rewrite eq. Qed.

Lemma Hgen_cons_2_app I l l1 e :
  forall a,
    I (Hgen I l) e = Some a ->
    Hgen I (l1 ++ e :: l) = Hgen I (l1 ++ l).
Proof.
intros a Ha.
induction l1 as [| f t IH].
- now apply Hgen_cons_2 with (a:=a).
- simpl. now rewrite IH.
Qed.

Lemma Hgen_app I l1 l2 :
  Hgen I (l2 ++ l1) = Hgen I (l2 ++ (Hgen I l1)).
Proof.
revert l2.
induction l1 as [| e t IH]; auto.
intros l.
case_eq (I (Hgen I t) e).
- intros a eq.
  rewrite Hgen_cons_2 with (a:=a); auto.
  now rewrite Hgen_cons_2_app with (a:=a).
- intros eq.
  rewrite Hgen_cons_1; auto.
  change (Hgen I (l ++ [e] ++ t) = Hgen I (l ++ [e] ++ Hgen I t)).
  now do 2 rewrite app_assoc.
Qed.

Theorem Hgen_subseq (I : HandlerGenerator) (l : History) :
  subseq (Hgen I l) l.
Proof.
induction l as [| a l IH]; [easy |].
simpl.
case_eq (I (Hgen I l) a); [| now intuition].
case_eq (Hgen I l); auto.
intros b l0 eq.
rewrite <- eq.
now intuition.
Qed.

Hint Resolve Hgen_subseq.

Lemma Hgen_idemp (I : HandlerGenerator) (l : History) :
  Hgen I (Hgen I l) = Hgen I l.
Proof.
induction l; [easy |].
simpl.
case_eq (I (Hgen I l) a); [easy |].
intros eq.
simpl. now rewrite IHl, eq.
Qed.

Hint Resolve Hgen_idemp.


(******************************************************************************
 ***                        I-reachable histories                           ***
 ******************************************************************************)

Definition reachable I h := exists l, Hgen I l = h.

Lemma reachable_nil I : reachable I [].
Proof. red. now exists []. Qed.

Lemma reachable_Hgen I l : reachable I (Hgen I l).
Proof. red; eauto. Qed.

Hint Resolve reachable_nil.
Hint Resolve reachable_Hgen.

Lemma reachable_Hgen_eq I l (Hreach : reachable I l) :
  Hgen I l = l.
Proof. destruct Hreach. now subst. Qed.

Hint Resolve reachable_Hgen_eq.

Fixpoint Fgen (F : Policy) (I : HandlerGenerator) (h : History) (e : E) :=
  match I (Hgen I h) e with
    | Some a => a
    | None => F (Hgen I h) e
  end.


(******************************************************************************
 ***           Decentralization, compatibility, and transparency            ***
 ******************************************************************************)

Definition decentralize F I := F = Fgen F I.

Definition compatible F I :=
  forall h e a,
    reachable I h ->
    I h e = Some a ->
    F h e = a.

Definition transparent (F : Policy) I :=
  forall h, F h = F (Hgen I h).

Definition transparent_app (F : Policy) I :=
  forall h l, F (h ++ l) = F (h ++ Hgen I l).

Definition transparent_old (F : Policy) I :=
  forall h h' e a,
    I (Hgen I h) e = Some a ->
    F (h' ++ [e] ++ h) = F (h' ++ h).

Definition transparent_reach (F : Policy) I :=
  forall h h' e a,
    reachable I h ->
    I h e = Some a ->
    F (h' ++ [e] ++ h) = F (h' ++ h).

Lemma decentralize_apply F I h e (Hdec : decentralize F I) :
  forall a,
    I (Hgen I h) e = Some a -> F h e = a.
Proof.
intros a eq.
rewrite Hdec.
destruct h; simpl in *; now rewrite eq.
Qed.

Lemma decentralize_apply_2 F I h e (Hdec : decentralize F I) :
  I (Hgen I h) e = None ->
  F h e = F (Hgen I h) e.
Proof.
intros eq.
assert (H := equal_f Hdec h).
rewrite H; clear H.
destruct h; simpl in *; now rewrite eq.
Qed.

Lemma decentralization_compatible F I (Hdec : decentralize F I) :
  compatible F I.
Proof.
intros h e a Hr eq.
destruct Hr as [l Hl].
subst h.
eapply decentralize_apply; eauto.
now rewrite Hgen_idemp.
Qed.

Lemma decentralization_transparent F I (Hdec : decentralize F I) :
  transparent F I.
Proof.
intros h.
assert (Hcomp : compatible F I)
  by now apply decentralization_compatible.
extensionality e.
case_eq (I (Hgen I h) e).
- intros a E.
  rewrite (decentralize_apply Hdec E).
  now rewrite Hcomp.
- intros E.
  now rewrite (decentralize_apply_2 Hdec E).
Qed.

Lemma Fgen_compat F I h (Hcomp : compatible F I) :
  F (Hgen I h) = Fgen F I h.
Proof.
extensionality e.
unfold Fgen.
destruct h as [| f h ].
- simpl; now case_eq (I [] e); auto.
- now case_eq (I (Hgen I (f :: h)) e); auto.
Qed.

Hint Resolve Fgen_compat.

Lemma compat_transp_decentralize F I
      (Hcomp : compatible F I)
      (Htransp : transparent F I) :
  decentralize F I.
Proof.
red in Hcomp.
red in Htransp.
red.
extensionality h.
now rewrite Htransp; auto.
Qed.

(******************************************************************************
 *** Theorem 1. An event handler generator I that decentralizes a policy F  ***
 ***            is optimal iff it is proactive with respect to F.           ***
 ******************************************************************************)

Theorem decentralization_iff_compatible_and_transparent F I :
  decentralize F I <-> compatible F I /\ transparent F I.
Proof.
assert (L1 := @decentralization_compatible F I).
assert (L2 := @decentralization_transparent F I).
assert (L3 := @compat_transp_decentralize F I).
tauto.
Qed.


(******************************************************************************
 ***                             Irrelevance                                ***
 ******************************************************************************)

Definition irrelevant (F : Policy) h e :=
  forall h',
    F (h' ++ [e] ++ h) = F (h' ++ h).

Lemma transparency_irrelevance F I (Htransp : transparent F I) :
  forall h e a,
    reachable I h -> I h e = Some a -> irrelevant F h e.
Proof.
intros h e a Hreach E h1.
simpl.
rewrite Htransp.
rewrite <- (reachable_Hgen_eq Hreach) in E.
now erewrite Hgen_cons_2_app; eauto.
Qed.

Lemma irrelevance_transparency_aux F I :
  (forall h e a,
     reachable I h ->
     I h e = Some a -> irrelevant F h e) ->
  forall h h', F (h' ++ h) = F (h' ++ Hgen I h).
Proof.
intros H.
induction h as [| e h IH]; [easy |].
intros h'.
case_eq (I (Hgen I h) e).
- intros a E.
  rewrite Hgen_cons_2 with (a:=a); auto.
  change (F (h' ++ [e] ++ h) = F (h' ++ Hgen I h)).
  rewrite app_assoc, IH, <- app_assoc.
  now eapply H; eauto.
- intros E.
  rewrite Hgen_cons_1; auto.
  change (F (h' ++ [e] ++ h) = F (h' ++ [e] ++ Hgen I h)).
  now do 2 rewrite app_assoc.
Qed.

Lemma transparency_transparency_app F I (Htransp : transparent F I) :
  forall h h',
    F (h' ++ h) = F (h' ++ Hgen I h).
Proof.
intros h h'.  
apply irrelevance_transparency_aux.
intros.
eapply transparency_irrelevance; eauto.
Qed.

Lemma irrelevance_transparency F I :
  (forall h e a,
     reachable I h ->
     I h e = Some a -> irrelevant F h e) ->
  transparent F I.
Proof.
intros H h.
assert (H0 := irrelevance_transparency_aux).
change (F ([] ++ h) = F ([] ++ Hgen I h)).
now firstorder.
Qed.

(******************************************************************************
 *** Theorem 2. I is transparent with respect to F iff for every            ***
 ***            I-reachable history H, I(H) is only defined for events e    ***
 ***            that are irrelevant with respect to F and H.                ***
 ******************************************************************************)

Theorem transparency_iff_defined_for_irrelevant F I :
  transparent F I <->
  forall h e a,
    reachable I h -> I h e = Some a -> irrelevant F h e.
Proof.
assert (L1 := @transparency_irrelevance F I).
assert (L2 := @irrelevance_transparency F I).
tauto.
Qed.


(******************************************************************************
 ***               Optimality of event-handler generator                    ***
 ******************************************************************************)

Definition optimal F I (Hdec : decentralize F I) :=
  forall I',
    decentralize F I' ->
    forall h, subseq (Hgen I h) (Hgen I' h).

Definition proactive F I :=
  forall h (Hreach : reachable I h) e,
    irrelevant F h e -> exists a, I (Hgen I h) e = Some a.

Require Import Classical.

Lemma proactive_optimal F I (Hdec : decentralize F I) :
  optimal Hdec -> proactive F I.
Proof.
intros Hopt.
apply NNPP.
intros Habs.
unfold proactive in Habs.
apply not_all_ex_not in Habs.
destruct Habs as [h Habs].
apply imply_to_and in Habs.
destruct Habs as [Hreach H].
apply not_all_ex_not in H.
destruct H as [e He].
apply imply_to_and in He.
destruct He as [Hirr Htmp].
assert (E : I (Hgen I h) e = None).
{
  clear - Htmp.
  destruct (I (Hgen I h) e); auto.
  exfalso.
  now eapply Htmp; eauto.
}
clear Htmp.
pose (I' := (fun ht et =>
               match list_eq_dec E_eq_dec ht h, E_eq_dec et e with
                 | left _, left _ => Some (F h e)
                 | _, _ => None
               end)
            : HandlerGenerator).
assert (Hcompat' : compatible F I').
{
  clear - I'.
  intros h1 e1 a1 Hreach1 E1.
  unfold I' in E1.
  destruct (list_eq_dec E_eq_dec h1 h);
    destruct (E_eq_dec e1 e); auto; try inversion E1; subst; auto.
}
assert (Htransp' : transparent F I').
{
  clear - I' Hirr.
  apply irrelevance_transparency.
  intros h1 e1 a1 H1 E1.
  unfold I' in E1.
  destruct (list_eq_dec E_eq_dec h1 h);
    destruct (E_eq_dec e1 e); auto; inversion E1; now subst.
}
assert (Hdec' : decentralize F I')
  by (apply compat_transp_decentralize; auto).
red in Hopt.
assert (H := Hopt _ Hdec' (e :: h)).
assert (H0 : Hgen I' h = h).
{
  cut (forall h1 h2, h2 ++ h1 = h -> Hgen I' h1 = h1).
  - intros H2 .
    eapply H2. now instantiate (1:=[]).
  - induction h1; auto.
    simpl.
    intros h2 H2.
    change (h2 ++ a :: h1) with (h2 ++ [a] ++ h1) in H2.
    rewrite app_assoc in H2.
    erewrite IHh1; eauto.
    assert (neq : h1 <> h).
    {
      intros Habs.
      subst h1; clear - H2.
      rewrite <- app_nil_l in H2.
      apply app_inv_tail in H2.
      symmetry in H2.
      apply (app_cons_not_nil _ _ _ H2).
    }
    unfold I'.
    destruct (list_eq_dec E_eq_dec h1 h);
    destruct (E_eq_dec a e); easy.
}
assert (H1 : Hgen I' (e :: h) = h).
{
  simpl.
  rewrite H0.
  unfold I'.
  destruct (list_eq_dec E_eq_dec h h);
    destruct (E_eq_dec e e); auto; congruence.
}
clear H0.
rewrite H1 in H; clear H1.
rewrite Hgen_cons_1 in H; auto.
rewrite (reachable_Hgen_eq Hreach) in H.
now apply (subseq_cons_2 H).
Qed.

Lemma optimal_proactive F I (Hdec : decentralize F I) :
  proactive F I -> optimal Hdec.
Proof.
intros Hpro.
intros I' Hdec'.
induction h as [| e h IH]; [easy |].
red in Hpro.
case_eq (I (Hgen I h) e).
- intros a E.
  erewrite Hgen_cons_2; eauto.
  eapply subseq_trans; [refine IH |].
  simpl.
  now case_eq (I' (Hgen I' h) e); auto.
- intros E.
  rewrite Hgen_cons_1; auto.
  case_eq (I' (Hgen I' h) e).
  + intros a' E'.
    erewrite Hgen_cons_2; eauto.
    assert (Htrans := transparency_transparency_app (decentralization_transparent Hdec)).
    assert (Htrans' := transparency_transparency_app (decentralization_transparent Hdec')).
    assert (forall h', F (h' ++ [e] ++ Hgen I h) = F (h' ++ Hgen I h)).
    {
      intros h'.
      rewrite app_assoc, <- Htrans, Htrans', app_assoc_reverse.
      symmetry.
      rewrite <- Htrans, Htrans'.
      symmetry.
      assert (H := transparency_irrelevance (decentralization_transparent Hdec')).
      eapply H; eauto.
    }
    assert (H0 : exists a : A, I (Hgen I h) e = Some a).
    {
      rewrite <- Hgen_idemp.
      now apply Hpro.
    }
    rewrite E in H0.
    now inversion H0.
  + intros E'.
    rewrite Hgen_cons_1; auto.
    now firstorder.
Qed.

(******************************************************************************
 *** Theorem 3. An event handler generator I that decentralizes a policy F  ***
 ***            is optimal iff it is proactive with respect to F.           ***
 ******************************************************************************)

Theorem optimal_iff_proactive F I (Hdec : decentralize F I) :
  optimal Hdec <-> proactive F I.
Proof.
assert (L1 := @proactive_optimal F I Hdec).
assert (L2 := @optimal_proactive F I Hdec).
tauto.
Qed.

