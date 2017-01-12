Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Util.Tactics.BreakMatch.

Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.

  Local Ltac t_step :=
    match goal with
    | _ => reflexivity
    | _ => progress simpl in *
    | _ => intro
    | _ => progress break_match
    | _ => progress cbv [LetIn.Let_In]
    | [ H : _ |- _ ] => rewrite H
    | _ => progress autorewrite with core
    end.
  Local Ltac t := repeat t_step.

  Lemma eq_interp_flat_type_eta {var t T f} x
    : @interp_flat_type_eta base_type_code var t T f x = f x.
  Proof. induction t; t. Qed.
  (* Local *) Hint Rewrite @eq_interp_flat_type_eta.
  Lemma interpf_exprf_eta {t e}
    : interpf (@interp_op) (exprf_eta (t:=t) e) = interpf (@interp_op) e.
  Proof. induction e; t. Qed.
  (* Local *) Hint Rewrite @interpf_exprf_eta.
  Lemma interp_expr_eta {t e}
    : forall x, interp (@interp_op) (expr_eta (t:=t) e) x = interp (@interp_op) e x.
  Proof. induction e; t. Qed.
  Lemma InterpExprEta {t e}
    : forall x, Interp (@interp_op) (ExprEta (t:=t) e) x = Interp (@interp_op) e x.
  Proof. apply interp_expr_eta. Qed.
End language.
