(** * Convert between interpretations of types *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Notations Crypto.Util.Tactics.

Local Open Scope expr_scope.

Section language.
  Context (base_type_code : Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Section map.
    Context (interp_base_type1 interp_base_type2 : base_type_code -> Type).
    Context (f_const : forall t, interp_flat_type_gen interp_base_type1 t -> interp_flat_type_gen interp_base_type2 t).
    Context {var1 var2 : base_type_code -> Type}.
    Context (f_var12 : forall t, var1 t -> var2 t)
            (f_var21 : forall t, var2 t -> var1 t).

    Fixpoint mapf
             {t}
             (e : @exprf base_type_code interp_base_type1 op var1 t)
      : @exprf base_type_code interp_base_type2 op var2 t
      := match e in @exprf _ _ _ _ t return @exprf _ _ _ _ t with
         | Const _ x => Const (f_const _ x)
         | Var _ x => Var (f_var12 _ x)
         | Op _ _ op args => Op op (@mapf _ args)
         | Let _ ex _ eC => Let (@mapf _ ex)
                               (fun x => @mapf _ (eC (mapf_interp_flat_type_gen base_type_code f_var21 x)))
         | Pair _ ex _ ey => Pair (@mapf _ ex)
                                 (@mapf _ ey)
         end.

    Fixpoint map {t} (e : @expr base_type_code interp_base_type1 op var1 t)
      : @expr base_type_code interp_base_type2 op var2 t
      := match e with
         | Return _ x => Return (mapf x)
         | Abs _ _ f => Abs (fun x => @map _ (f (f_var21 _ x)))
         end.
  End map.

  Section mapf_id.
    Context (functional_extensionality : forall {A B} (f g : A -> B), (forall x, f x = g x) -> f = g)
            {interp_base_type : base_type_code -> Type}
            {var : base_type_code -> Type}.

    Lemma mapf_idmap_ext {t} e
      : @mapf interp_base_type interp_base_type
              (fun _ x => x)
              var var
              (fun _ x => x) (fun _ x => x)
              t e
        = e.
    Proof.
      induction e;
        repeat match goal with
               | _ => reflexivity
               | _ => progress simpl in *
               | _ => rewrite_hyp !*
               | _ => apply (f_equal2 (fun x f => Let x f))
               | _ => solve [ eauto ]
               | _ => apply functional_extensionality; intro
               end.
      clear e IHe H.
      revert dependent e0; revert dependent tC; revert dependent x; induction tx; simpl; [ reflexivity | ]; intros.
      destruct x as [x0 x1]; simpl in *.
      lazymatch goal with
      | [ |- ?e0 (?x0', ?x1')%core = _ ]
        => rewrite (IHtx1 x0 _ (fun x0'' => e0 (x0'', x1')%core)); cbv beta in *
      end.
      lazymatch goal with
      | [ |- ?e0 (?x0', ?x1')%core = _ ]
        => rewrite (IHtx2 x1 _ (fun x1'' => e0 (x0', x1'')%core)); cbv beta in *
      end.
      reflexivity.
    Qed.
  End mapf_id.

  Section mapf_id_interp.
    Context {interp_base_type : base_type_code -> Type}
            (interp_op : forall src dst, op src dst -> interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst)
            (f_const : forall t, interp_flat_type_gen interp_base_type t -> interp_flat_type_gen interp_base_type t)
            (f_var12 f_var21 : forall t, interp_base_type t -> interp_base_type t)
            (f_const_id : forall t x, f_const t x = x)
            (f_var12_id : forall t x, f_var12 t x = x)
            (f_var21_id : forall t x, f_var21 t x = x).

    Lemma mapf_idmap {t} e
      : interpf interp_op
                (@mapf interp_base_type interp_base_type
                       f_const
                       _ _
                       f_var12 f_var21
                       t e)
        = interpf interp_op e.
    Proof.
      induction e;
        repeat match goal with
               | _ => reflexivity
               | _ => progress simpl in *
               | _ => rewrite_hyp !*
               | _ => apply (f_equal2 (fun x f => Let x f))
               | _ => solve [ eauto ]
               end.
      clear H IHe.
      generalize (interpf interp_op e); intro x; clear e.
      revert dependent e0; revert dependent tC; revert dependent x; induction tx; simpl;
        [ intros; rewrite_hyp ?*; reflexivity | ]; intros.
      destruct x as [x0 x1]; simpl in *.
      lazymatch goal with
      | [ |- interpf _ (?e0 (?x0', ?x1')%core) = _ ]
        => rewrite (IHtx1 x0 _ (fun x0'' => e0 (x0'', x1')%core)); cbv beta in *
      end.
      lazymatch goal with
      | [ |- interpf _ (?e0 (?x0', ?x1')%core) = _ ]
        => apply (IHtx2 x1 _ (fun x1'' => e0 (x0', x1'')%core)); cbv beta in *
      end.
    Qed.
  End mapf_id_interp.

  Section mapf_interp.
    Context {interp_base_type1 interp_base_type2 : base_type_code -> Type}
            (interp_op1 : forall src dst, op src dst -> interp_flat_type_gen interp_base_type1 src -> interp_flat_type_gen interp_base_type1 dst)
            (interp_op2 : forall src dst, op src dst -> interp_flat_type_gen interp_base_type2 src -> interp_flat_type_gen interp_base_type2 dst)
            (f_var12 : forall t, interp_base_type1 t -> interp_base_type2 t)
            (f_var21 : forall t, interp_base_type2 t -> interp_base_type1 t)
            (f_var12_21 : forall t v, f_var12 t (f_var21 t v) = v).
    Fixpoint f_const {t} : interp_flat_type_gen interp_base_type1 t -> interp_flat_type_gen interp_base_type2 t
      := match t return interp_flat_type_gen interp_base_type1 t -> interp_flat_type_gen interp_base_type2 t with
         | Tbase _ => f_var12 _
         | Prod _ _ => fun x => (@f_const _ (fst x), @f_const _ (snd x))%core
         end.
    Fixpoint f_const_type {t} : interp_type interp_base_type1 t -> interp_type interp_base_type2 t
      := match t return interp_type interp_base_type1 t -> interp_type interp_base_type2 t with
         | Tflat _ => f_const
         | Arrow _ _ => fun f x => @f_const_type _ (f (f_var21 _ x))
         end.
    Context (interp_op_Proper
             : forall t1 tR op argsv,
                interp_op2 t1 tR op (f_const argsv) =
                f_const (interp_op1 t1 tR op argsv)).

    Lemma interpf_mapf {t} e
      : interpf interp_op2
                (@mapf interp_base_type1 interp_base_type2
                       (@f_const)
                       _ _
                       f_var12 f_var21
                       t e)
        = f_const (interpf interp_op1 e).
    Proof.
      induction e;
        repeat match goal with
               | _ => reflexivity
               | _ => progress simpl in *
               | _ => rewrite_hyp !*
               | _ => apply (f_equal2 (fun x f => Let x f))
               | _ => apply (f_equal2 (@Pair _ _))
               | _ => apply (f_equal2 (@pair _ _))
               | _ => solve [ eauto ]
               end.
      clear H IHe interp_op_Proper.
      generalize (interpf interp_op1 e); intro x; clear e.
      revert dependent e0; revert dependent tC; revert dependent x; induction tx; simpl;
        [ intros; rewrite_hyp ?* | ]; intros.
      destruct x as [x0 x1]; simpl in *.
      lazymatch goal with
      | [ |- f_const (interpf _ (?e0 (?x0', ?x1')%core)) = _ ]
        => rewrite (IHtx1 x0 _ (fun x0'' => e0 (x0'', x1')%core)); cbv beta in *
      end.
      lazymatch goal with
      | [ |- f_const (interpf _ (?e0 (?x0', ?x1')%core)) = _ ]
        => apply (IHtx2 x1 _ (fun x1'' => e0 (x0', x1'')%core)); cbv beta in *
      end.
    Qed.

    Lemma interp_map {t} e
      : interp_type_gen_rel_pointwise
          (interp_flat_type_gen interp_base_type2)
          (fun _ => @eq _)
          (interp interp_op2
                  (@map interp_base_type1 interp_base_type2
                        (@f_const)
                        _ _
                        f_var12 f_var21
                        t e))
          (f_const_type (interp interp_op1 e)).
    Proof.
      induction e;
        repeat match goal with
               | _ => progress simpl in *
               | _ => progress intros
               | _ => eauto using interpf_mapf
               end.
    Qed.
  End mapf_interp.
End language.
