(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.InlineWf.
Require Import Crypto.Reflection.InterpProofs.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.


Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op).
  Local Notation wf := (@wf base_type_code op).

  Local Hint Extern 1 => eapply interpf_SmartVarVarf.

  Local Ltac t_fin :=
    repeat match goal with
           | _ => reflexivity
           | _ => progress simpl in *
           | _ => progress unfold postprocess_for_const in *
           | _ => progress intros
           | _ => progress inversion_sigma
           | _ => progress inversion_prod
           | _ => solve [ intuition eauto ]
           | _ => apply (f_equal (interp_op _ _ _))
           | _ => apply (f_equal2 (@pair _ _))
           | _ => progress specialize_by assumption
           | _ => progress subst
           | [ H : context[List.In _ (_ ++ _)] |- _ ] => setoid_rewrite List.in_app_iff in H
           | [ H : or _ _ |- _ ] => destruct H
           | _ => progress break_match
           | _ => rewrite <- !surjective_pairing
           | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
           | [ H : _ |- _ ] => apply H
           | [ H : _ |- _ ] => rewrite H
           end.

  Lemma interpf_inline_constf is_const G {t} e1 e2
        (wf : @wff _ _ G t e1 e2)
        (H : forall t x x',
            List.In
              (existT (fun t : base_type_code => (exprf (Tbase t) * interp_base_type t)%type) t
                      (x, x')) G
            -> interpf interp_op x = x')
    : interpf interp_op (inline_constf is_const e1) = interpf interp_op e2.
  Proof.
    clear -wf H.
    induction wf; t_fin.
  Qed.

  Local Hint Resolve interpf_inline_constf.

  Lemma interp_inline_const is_const {t} e1 e2
        (wf : @wf _ _ t e1 e2)
    : forall x, interp interp_op (inline_const is_const e1) x = interp interp_op e2 x.
  Proof.
    destruct wf.
    simpl in *; intro; eapply (interpf_inline_constf is_const); eauto.
  Qed.

  Lemma Interp_InlineConst is_const {t} (e : Expr t)
        (wf : Wf e)
    : forall x, Interp interp_op (InlineConst is_const e) x = Interp interp_op e x.
  Proof.
    unfold Interp, InlineConst.
    eapply (interp_inline_const is_const); simpl; intuition.
  Qed.
End language.
