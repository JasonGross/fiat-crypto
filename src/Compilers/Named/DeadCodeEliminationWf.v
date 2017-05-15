Require Import Coq.PArith.BinPos.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.DeadCodeElimination.
Require Import Crypto.Compilers.Named.RegisterAssignWf.
Require Import Crypto.Util.Decidable.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {OutContext : Context Name (fun _ : base_type_code => positive)}
          {OutContextOk : ContextOk OutContext}
          {Name_beq : Name -> Name -> bool}
          {base_type_code_beq : base_type_code -> base_type_code -> bool}
          (base_type_code_bl : forall t1 t2, base_type_code_beq t1 t2 = true -> t1 = t2)
          (base_type_code_lb : forall t1 t2, t1 = t2 -> base_type_code_beq t1 t2 = true)
          (Name_bl : forall n1 n2, Name_beq n1 n2 = true -> n1 = n2)
          (Name_lb : forall n1 n2, n1 = n2 -> Name_beq n1 n2 = true).

  Local Notation EliminateDeadCode := (@EliminateDeadCode base_type_code op Name _ base_type_code_bl OutContext).
  Local Notation PContext var := (@PositiveContext base_type_code var base_type_code_beq base_type_code_bl).

  Section with_var.
    Context {var : base_type_code -> Type}
            {VarOutContext : Context Name var}
            {VarOutContextOk : ContextOk VarOutContext}.

    Lemma wf_EliminateDeadCode
          t e new_names
          (ctxi_var : PContext var)
          (ctxr_var : VarOutContext)
          eout
          (Hwf : Named.wf ctxi_var e)
      : @EliminateDeadCode t e new_names = Some eout
        -> Named.wf ctxr_var eout.
    Proof.
      eapply @wf_register_reassign; [ .. | eassumption ];
        solve [ assumption
              | apply @PositiveContextOk; assumption
              | apply Peqb_true_eq
              | apply Pos.eqb_eq
              | eapply dec_rel_of_bool_dec_rel; eauto
              | exact _ ].
    Qed.
  End with_var.

  Lemma Wf_EliminateDeadCode
        (OutContext_var : forall var, Context Name var)
        (OutContext_varOk : forall var, ContextOk (OutContext_var var))
        t e new_names
        eout
        (Hwf : Named.Wf (fun var => PContext var) e)
    : @EliminateDeadCode t e new_names = Some eout
      -> Named.Wf OutContext_var eout.
  Proof.
    intros H ?; revert H.
    eapply wf_EliminateDeadCode, Hwf.
  Qed.
End language.

Hint Resolve wf_EliminateDeadCode Wf_EliminateDeadCode : wf.
