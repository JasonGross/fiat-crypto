Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ExprInversion.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Named.RewriteAddToAdc.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.LetIn.

Local Open Scope Z_scope.

Section named.
  Context {interp_base_type : base_type -> Type}
          {interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
          {Name : Type}
          {InterpContext : Context Name interp_base_type}
          {InterpContextOk : ContextOk InterpContext}
          (Name_beq : Name -> Name -> bool)
          (Name_bl : forall n1 n2, Name_beq n1 n2 = true -> n1 = n2)
          (Name_lb : forall n1 n2, n1 = n2 -> Name_beq n1 n2 = true).

  Local Notation exprf := (@exprf base_type op Name).
  Local Notation expr := (@expr base_type op Name).
  Local Notation do_rewrite := (@do_rewrite Name Name_beq).
  Local Notation do_rewriteo := (@do_rewriteo Name Name_beq).
  Local Notation rewrite_exprf := (@rewrite_exprf Name Name_beq).
  Local Notation rewrite_exprf_prestep := (@rewrite_exprf_prestep Name).
  Local Notation rewrite_expr := (@rewrite_expr Name Name_beq).

  Local Ltac t_step :=
    first [ progress simpl in *
          | reflexivity
          | congruence
          | progress unfold option_map, LetIn.Let_In in *
          | progress intros
          | progress subst
          | progress inversion_option
          | progress destruct_head' unit
          | progress destruct_head'_prod
          | progress inversion_prod
          | solve [ f_equal; eauto ]
          | match goal with
            | [ H : interpf (t:=?T) ?e = Some ?v, H' : interpf _ = Some ?v' |- _ ]
              => assert (v = v' :> interp_flat_type _ T) by eauto; (subst v || (progress inversion_prod))
            | [ IH : context[interpf ?e], H' : interpf (ctx:=?ctx') ?e = Some _ |- _ ]
              => specialize (fun v1 v2 => IH ctx' v1 v2); rewrite H' in IH
            | [ H : forall v1 v2, Some _ = Some v1 -> _ |- _ ]
              => specialize (fun v2 => H _ v2 eq_refl)
            | [ H : forall v, Some _ = Some v -> _ |- _ ]
              => specialize (H _ eq_refl)
            | [ H : ?x = interp_op _ _ _ _, H' : context[?x] |- _ ]
              => progress rewrite H in H'
            | [ H : ?x = (_,_)%core, H' : context[?x] |- _ ]
              => progress rewrite H in H'
            end ].
  Local Ltac t_destruct_step :=
    match goal with
    | [ e : exprf ?t |- context[match ?t with _ => _ end] ]
      => is_var t; destruct e
    | [ e : exprf ?t, H : context[match ?t with _ => _ end] |- _ ]
      => is_var t; destruct e
    | [ e : op ?s ?d |- context[match ?s with _ => _ end] ]
      => is_var s; is_var d; destruct e
    | [ e : op ?s ?d |- context[match ?d with _ => _ end] ]
      => is_var s; is_var d; destruct e
    | [ e : op ?s ?d, H : context[match ?s with _ => _ end] |- _ ]
      => is_var s; is_var d; destruct e
    | [ e : op ?s ?d, H : context[match ?d with _ => _ end] |- _ ]
      => is_var s; is_var d; destruct e
    end.
  Local Ltac t'_step :=
    first [ break_innermost_match_step
          | break_innermost_match_hyps_step ].
  Local Ltac t_invert_step :=
    progress invert_expr; break_innermost_match; try exact I; intros.

  Local Notation retT e re :=
    (forall (ctx : InterpContext)
            v,
        Named.interpf (interp_op:=interp_op) (ctx:=ctx) re = Some v
        -> Named.interpf (interp_op:=interp_op) (ctx:=ctx) e = Some v)
      (only parsing).
  Local Notation tZ := (Tbase TZ).
  Local Notation ADC bw c x y := (Op (@AddWithGetCarry bw TZ TZ TZ TZ TZ)
                                     (Pair (Pair (t1:=tZ) c (t2:=tZ) x) (t2:=tZ) y)).
  Local Notation ADD bw x y := (ADC bw (Op (OpConst 0) TT) x y).
  Local Notation ADX x y := (Op (@Add TZ TZ TZ) (Pair (t1:=tZ) x (t2:=tZ) y)).
  Lemma interpf_do_rewrite
        {t} {e e' : exprf t}
        (H : do_rewrite e = Some e')
    : retT e e'.
  Proof.
    (*refine match e return retT (do_rewrite rewrite_exprf) e with
           |           (nlet (a2, c1) : tZ * tZ := (ADD bw1 a b as ex0) in P0)
             => _(*match rewrite_exprf _ P0 in Named.exprf _ _ _ t return exprf t -> exprf t with
            |      (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var _ a2') as ex1) in P1)
              => match P1 in Named.exprf _ _ _ t return exprf t -> exprf t with
                 | (nlet c        : tZ      := (ADX (Var _ c1') (Var _ c2') as ex2) in P)
                   => fun e
                      => if (((bw1 =Z? bw2) && (a2 =n? a2') && (c1 =n? c1') && (c2 =n? c2'))
                               && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                               && negb (name_list_has_duplicate (a2::c1::s::c2::c::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                         then (nlet (a2, c1) : tZ * tZ := ex0 in
                               nlet (s , c2) : tZ * tZ := ex1 in
                               nlet c        : tZ      := ex2 in
                               nlet (s, c)   : tZ * tZ := ADC bw1 c0 a b in
                               P)
                         else e
                 | P1' => fun e => e
                 end
            | P0' => fun e => e
            end (nlet (a2, c1) : tZ * tZ := rewrite_exprf _ ex0 in rewrite_exprf _ P0)*)
       | _ => _
           end%core%nexpr%bool.
    solve [ repeat first [ t_step ] ].
    solve [ repeat first [ t_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    Focus 7.
    { repeat first [ t_step | t'_step ].
      Require Import AdmitAxiom.
      revert H H0.
      Set Printing All.
      admit.
      lazymatch goal with
      | [ H : match ?e with _ => _ end = _ |- _ ] => destruct e eqn:?
      end.
      destruct (lookupb ctx n) eqn:?.

    repeat first [ t_step | t'_step ]. }
      eapply IH.
      2:eassumption.
      rewrite <- H.
      match goal with
      | [ H : interpf (t:=?T) _ = Some ?x, H' : interpf _ = Some ?y |- _ ]
        => assert (x = y :> interp_flat_type _ T) by eauto
      end.
      Arguments interpf : clear implicits.


      etransitivity.
      eapply H0.
      Focus 4.
      {
        t_step.
        Set Printing All.
        clear.
        assert(forall (ctx : @ContextT base_type Name interp_base_type InterpContext)
    (v1 v2 : @interp_flat_type base_type interp_base_type f0)
    (_ : @eq (option (@interp_flat_type base_type interp_base_type f0))
           (@interpf base_type interp_base_type op Name InterpContext interp_op
              (@extendb base_type Name interp_base_type InterpContext
                 (@extendb base_type Name interp_base_type InterpContext ctx i TZ
                    (@fst (interp_base_type TZ) (interp_base_type TZ) tt)) i0 TZ
                 (@snd (interp_base_type TZ) (interp_base_type TZ) tt)) f0 eC)
           (@Some (@interp_flat_type base_type interp_base_type f0) v1))
    (_ : @eq (option (@interp_flat_type base_type interp_base_type f0))
           match
             @interpf base_type interp_base_type op Name InterpContext interp_op ctx
               (@Prod base_type (@Tbase base_type TZ) (@Tbase base_type TZ))
               (rewrite_exprf (@Prod base_type (@Tbase base_type TZ) (@Tbase base_type TZ))
                  (@TT base_type op Name))
             return (option (@interp_flat_type base_type interp_base_type f0))
           with
           | Some xv =>
               @interpf base_type interp_base_type op Name InterpContext interp_op
                 (@extendb base_type Name interp_base_type InterpContext
                    (@extendb base_type Name interp_base_type InterpContext ctx i TZ
                       (@fst (interp_base_type TZ) (interp_base_type TZ) xv)) i0 TZ
                    (@snd (interp_base_type TZ) (interp_base_type TZ) xv)) f0
                 (rewrite_exprf f0 eC)
           | None => @None (@interp_flat_type base_type interp_base_type f0)
           end (@Some (@interp_flat_type base_type interp_base_type f0) v2)),
  @eq (@interp_flat_type base_type interp_base_type f0) v1 v2).
        simpl.
        first [progress simpl in * ].
          | reflexivity  ].
          | congruence ].
          | progress unfold option_map, LetIn.Let_In in *
          | progress intros
          | progress subst
          | progress inversion_option
          | progress destruct_head' unit
          | progress destruct_head'_prod
          | progress inversion_prod ].
          | solve [ f_equal; eauto ]
          | match goal with
            | [ H : interpf ?e = Some ?v, H' : interpf (rewrite_exprf ?e') = Some ?v' |- _ ]
              => assert (v = v') by eauto; subst v
            | [ IH : context[interpf ?e], H' : interpf (ctx:=?ctx') ?e = Some _ |- _ ]
              => specialize (fun v1 v2 => IH ctx' v1 v2); rewrite H' in IH
            | [ H : forall v1 v2, Some _ = Some v1 -> _ |- _ ]
              => specialize (fun v2 => H _ v2 eq_refl)
            | [ H : forall v, Some _ = Some v -> _ |- _ ]
              => specialize (H _ eq_refl)
            | [ H : ?x = interp_op _ _ _ _, H' : context[?x] |- _ ]
              => progress rewrite H in H'
            | [ H : ?x = (_,_)%core, H' : context[?x] |- _ ]
              => progress rewrite H in H'
            end ].

        t_step.
      4:try solve [ repeat first [ t_step ] ].
      2:try solve [ repeat first [ t_step ] ].
                 |
     *)
    (*
    match goal with
    end.
    lazymatch goal with

    end.
    eauto.
        by (rewrite <- H'; eauto); (subst v || (progress inversion_prod))
    end.
    all:simpl; unfold option_map in *.
    all:repeat (break_innermost_match; break_innermost_match_hyps;
        repeat t_step).
    Focus 2.

      repeat t_step.
      intros *;
      let H := fresh in
      lazymatch goal with
      | [ |- context[do_rewrite ?e] ]
        => destruct (do_rewrite e) eqn:H;
             [ pose proof (interpf_do_rewrite H) | ]
      end;
        try solve [ clear H; repeat first [ t_step | t'_step ] ].
    Focus 2.
    clear H.
    { repeat t_step.
      break_match_hyps; repeat t_step.
      specialize (IHe1 _ Heqo0).
      specialize (fun v1 pf => H0 v1 _ pf eq_refl).
      specialize (IHe2 v2).
      repeat first [ t_step | t'_step ].
      specialize (IHe2 _ Heqo0).
      specialize (fun v1 pf => H0 v1 _ pf eq_refl).
      break_match_hyps; repeat t_step.
      repeat first [ t_step | t'_step ].
      [ repeat first [ t_step | t'_step ]
      |
      | repeat first [ t_step | t'_step ] ];
      [].
    intros.
    break_innermost_match_hyps_step.
    2:solve [ repeat first [ t_step | t'_step ] ].
    all:break_innermost_match_hyps_step.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    2:solve [ repeat first [ t_step | t'_step ] ].
    2:solve [ repeat first [ t_step | t'_step ] ].
    match goal with
    | [ H : match ?e with _ => _ end = _ |- _ ] => destruct e eqn:?
    end.
    2:solve [ repeat first [ t_step | t'_step ] ].
    unfold Let_In in *.
    break_innermost_match_hyps_step.
    2:solve [ repeat first [ t_step | t'_step ] ].
    break_innermost_match_hyps_step.
    2:solve [ repeat first [ t_step | t'_step ] ].
    2:solve [ repeat first [ t_step | t'_step ] ].
    break_innermost_match_hyps_step.
    2:solve [ repeat first [ t_step | t'_step ] ].
    break_innermost_match_hyps_step.
    revert dependent e1; intro e1.
    refine match e1 with
           | TT => _
           | _ => _
           end.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    break_innermost_match_step.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    break_innermost_match_step.
    break_innermost_match_step.
    break_innermost_match_step.
    break_innermost_match_step.
    intros.
    all:repeat match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           end.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    { match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => (tryif is_var e
                  then fail
                  else let e' := fresh in
                       set (e' := e) in *;
                       assert (e' = e) by reflexivity;
                       clearbody e';
                       first [ destruct e'
                             | revert dependent e' ])
    end.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    2:solve [ repeat first [ t_step | t'_step ] ].
     match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
     end.
         solve [ repeat first [ t_step | t'_step ] ].
             solve [ repeat first [ t_step | t'_step ] ].
             match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
             end.
             2:
             solve [ repeat first [ t_step | t'_step ] ].
             match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
             end.
             2:
               solve [ repeat first [ t_step | t'_step ] ].
             2:
               solve [ repeat first [ t_step | t'_step ] ].
             break_innermost_match_hyps_step.
             2:solve [ repeat first [ t_step | t'_step ] ].
             2:solve [ repeat first [ t_step | t'_step ] ].
             break_innermost_match_hyps_step.
             2:solve [ repeat first [ t_step | t'_step ] ].
             break_innermost_match_hyps_step.
                          match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
             end.
             do 2 match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
                  end.
             solve [ repeat first [ t_step | t'_step ] ].
             solve [ repeat first [ t_step | t'_step ] ].
             solve [ repeat first [ t_step | t'_step ] ].
             break_innermost_match_step.
             solve [ repeat first [ t_step | t'_step ] ].
             solve [ repeat first [ t_step | t'_step ] ].
             { break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
               break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
               break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               Local Ltac t := match goal with
           | [ H : context[match ?e with _ => _ end] |- _ = _ ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | [ |- context[match ?e with _ => _ end] ]
             => first [ is_var e; destruct e
                      | revert dependent e ]
           | _ => exact I
           | [ |- forall a : op ?s tZ, @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s tZ), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall a : op ?s (tZ * tZ), @?P a ]
             => is_var s; intro a; move a at top; generalize dependent s;
                  lazymatch goal with
                  | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
                    => intros s a;
                         refine match a as a' in op s' d'
                                      return match d' return op s' d' -> _ with
                                             | Prod tZ tZ => fun a'' => P _ a''
                                             | _ => fun _ => True
                                             end a'
                                with
                                | OpConst _ _ => _
                                | _ => _
                                end;
                         clear a;
                         try exact I;
                         intros
                  end
           | [ |- forall e : exprf Unit, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | Unit => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf tZ, @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | tZ => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
           | [ |- forall e : exprf (tZ * tZ * tZ), @?P e ]
             => intro e;
                  refine match e as e' in Named.exprf _ _ _ t
                               return match t return exprf t -> _ with
                                      | (tZ * tZ * tZ)%ctype => fun e' => P e'
                                      | _ => fun _ => True
                                      end e'
                         with
                         | TT => _
                         | _ => _
                         end;
                  clear e;
                  try exact I;
                  intros
                               end.
               t.
               t.
               break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               break_innermost_match_step.
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
               2:solve [ repeat first [ t_step | t'_step ] ].
             solve [ repeat first [ t_step | t'_step ] ].
             brea
             solve [ repeat first [ t_step | t'_step ] ].
             2:solve [ repeat first [ t_step | t'_step ] ].
             2:solve [ repeat first [ t_step | t'_step ] ].
             Focus 9.

             2:
             solve [ repeat first [ t_step | t'_step ] ].
               | revert dependent e ]
    end
    shelve.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    Unshelve.
    Focus 2.
    { repeat first [ t_step | t'_step ].
      Arguments interpf : clear implicits.
    Focus 2.
    revert dependent o.
    match goal with
    end.
    break_innermost_match_step.
    break_innermost_match_step.
    intros.
    break_innermost_match_hyps_step.
    break_innermost_match_hyps_step.
    break_innermost_match_hyps_step.
    revert dependent e0.
    match goal with
    end.
    break_innermost_match_step; try exact I.
    break_innermost_match_step; try exact I.
    solve [ repeat first [ t_step | t'_step ] ].
    solve [ repeat first [ t_step | t'_step ] ].
    { break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      intros.
      revert dependent e3.
      match goal with
      | [ |- forall e : exprf (tZ * tZ), @?P e ]
        => intro e;
             refine match e as e' in Named.exprf _ _ _ t
                          return match t return exprf t -> _ with
                                 | (tZ * tZ)%ctype => fun e' => P e'
                                 | _ => fun _ => True
                                 end e'
                    with
                    | TT => _
                    | _ => _
                    end;
             clear e;
             try exact I;
             intros
      end.
      solve [ repeat first [ t_step | t'_step ] ].
    { break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      solve [ repeat first [ t_step | t'_step ] ]. }
    { break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      intros.
      revert dependent e0.
      match goal with
      end.
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
      solve [ repeat first [ t_step | t'_step ] ].
      intros.
      solve [ repeat first [ t_step | t'_step ] ].

    solve [ repeat first [ t_step | t'_step ] ].


      break_innermost_match_step; try exact I.
      break_innermost_match_step; try exact I.
    {
    | [ |- forall a : op ?s (tZ * tZ), @?P a ]
      => is_var s; intro a; move a at top; generalize dependent s;
         lazymatch goal with
         | [ |- forall s (a : op s (tZ * tZ)), @?P s a ]
           => intros s a;
                refine match a as a' in op s' d'
                             return match d' return op s' d' -> _ with
                                    | Prod tZ tZ => fun a'' => P _ a''
                                    | _ => fun _ => True
                                    end a'
                       with
                       | OpConst _ _ => _
                       | _ => _
                       end;
                clear a;
                try exact I;
                intros
         end
    end.
    break_innermost_match_step.


    match goal with
    | [ |- forall a : op _ _, @?P a ]
      => intro a; refine match a in op s d as a' return P a' with
                         | OpConst _ _ => _
                         | _ => _
                         end; clear a
    end.
    {
      refine match o with
             | OpConst _ _ => _
             | _ => _
             end.
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      solve [ repeat first [ t_step | t'_step ] ].
      break_innermost_match_step.
      break_innermost_match_step.
    solve [ repeat first [ t_step | t'_step ] ].
    Focus 3.
    Focus 2.
    Focus 2.
    match goal with
    | [
    2:repeat first [ t_step | t'_step ].
    { repeat t_step.
      t_destruct_step.
      { repeat first [ t_step | t'_step | t_invert_step ]. }
      { repeat first [ t_step | t'_step | t_invert_step ]. }
      { t_destruct_step.
        { repeat first [ t_step | t'_step | t_invert_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { repeat first [ t_step | t'_step ]. }
        { move Tout1 at bottom.
          destruct Tout1, Tout2.
          repeat t_step.
          { invert_expr.
            Set Printing Depth 100000.
            { t_destruct_step; repeat t_step. }
            Focus 2.
            break_innermost_match; try exact I; intros.
            { repeat t_step. }
            { repeat first [ t_step | t'_step ]. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            { repeat t_step. }
            all:try exact I.
            2:solve [ t_destruct_step; repeat t_step ].
            { t_destruct_step; repeat t_step.
              { t_destruct_step; repeat t_step. }
              { t_destruct_step; repeat t_step.
                { t_destruct_step; repeat t_step. }
                { repeat first [ t_step | t'_step ]. }
                { repeat first [ t_step | t'_step ]. } }
              { repeat first [ t_step | t'_step ]. } }
            { t_destruct_step; repeat t_step.


                { repeat first [ t_step | t'_step ]. }
                { repeat first [ t_step | t'_step ]. }
                { repeat first [ t_step | t'_step ]. }
              { t_destruct_step; repeat t_step.

                { repeat first [ t_step | t'_step ]. }
              { repeat first [ t_step | t'_step ]. }
                { repeat first [ t_step | t'_step ]. }
                  Arguments interpf : clear implicits.
                  move IHe2 at bottom.
                  move H at bottom.
                  specialize (fun v2 => IHe2 _ v2 H).
                { t_destruct_step; repeat t_step.
                  { t_destruct_step; repeat t_step. }
                  { t_destruct_step; repeat t_step.
                    { t_destruct_step; repeat t_step. }
                    { t_destruct_step; repeat t_step.
                      { t_destruct_step; repeat t_step. }
                      { t_destruct_step; repeat t_step.
                        { t_destruct_step; repeat t_step. }
                        Set Printing Depth 1000000.
                        {
                  } } }

                    { t_destruct_step; repeat t_step. } } }
              t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              { t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              t_destruct_step; repeat t_step.
              break_innermost_match_step; try exact I.
            all:break_innermost_match_step; try exact I.
            { repeat first [ t_step | t'_step ].

            }
            { repeat first [ t_step | t'_step ]. }
          t_destruct_step.
        { simpl in *.
          repeat t_step.
          t'_step.
          repeat t_step.
          t'_step.
          repeat t_step.
          repeat t_step.
          repeat t_step.
          match goal with
          end.
          match goal with
          end.
          Set Printing Implicit.
          t'_step.
          repeat t_step.
          rewrite H in IHe2.
          t'_step.
          repeat t_step.
          t'_step.
          repeat t_step.
          { match goal with
            end.
          repeat first [ t_step | t'_step ]. }
      Focus 4.

      simpl.
      .

             try first [ break_innermost_match_hyps_step
                       | progress invert_expr; break_innermost_match; try exact I; intros ]).
    { clear -H0.

      invert_one_expr e1.
      do 20 (repeat first [ progress simpl in *
                   | reflexivity
                   | congruence
                   | progress unfold option_map, LetIn.Let_In in *
                   | progress intros
                   | progress subst
                   | progress inversion_option
                   | progress destruct_head' unit
                   | solve [ f_equal; eauto ]
                   | match goal with
                     | [ H : interpf ?e = Some ?v, H' : interpf (rewrite_exprf ?e') = Some ?v' |- _ ]
                       => assert (v = v') by eauto; subst v
                     end
                   | break_innermost_match_step ];
              first [ break_innermost_match_hyps_step
                    | progress invert_expr; break_innermost_match; try exact I; intros ]).
      progress invert_expr.
             .
    {
      do 10 (repeat first [ progress simpl in *
                   | reflexivity
                   | congruence
                   | progress unfold option_map, LetIn.Let_In in *
                   | progress intros
                   | progress subst
                   | progress inversion_option
                   | solve [ f_equal; eauto ]
                   | match goal with
                     | [ H : interpf ?e = Some ?v, H' : interpf (rewrite_exprf ?e') = Some ?v' |- _ ]
                       => assert (v = v') by eauto; subst v
                     end
                   | break_innermost_match_step ];
             try break_innermost_match_hyps_step).
    Focus 9.
    Focus 2.
    { .
      repeat first [ progress simpl in *
                   | reflexivity
                   | congruence
                   | progress unfold option_map, LetIn.Let_In in *
                   | progress intros
                   | progress subst
                   | progress inversion_option
                   | solve [ f_equal; eauto ]
                   | break_innermost_match_step ].
    Focus 2.
    { break_innermost_match_hyps;
      repeat first [ progress simpl in *
                   | reflexivity
                   | congruence
                   | progress unfold option_map in *
                   | progress intros
                   | progress subst
                   | progress inversion_option
                   | solve [ f_equal; eauto ]
                   | break_innermost_match_step ]. }
    Unfocus.
    break_innermost_match_hyps_step.
      f_equal; eauto.


        do_rewrite
             (rewrite_exprf : forall t (e : exprf t), exprf t)
             {t} (e : exprf t)
    : exprf t
    := match e in Named.exprf _ _ _ t return exprf t with
       |           (nlet (a2, c1) : tZ * tZ := (ADD bw1 a b as ex0) in P0)
         => match rewrite_exprf _ P0 in Named.exprf _ _ _ t return exprf t -> exprf t with
            |      (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var _ a2') as ex1) in P1)
              => match P1 in Named.exprf _ _ _ t return exprf t -> exprf t with
                 | (nlet c        : tZ      := (ADX (Var _ c1') (Var _ c2') as ex2) in P)
                   => fun e
                      => if (((bw1 =Z? bw2) && (a2 =n? a2') && (c1 =n? c1') && (c2 =n? c2'))
                               && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                               && negb (name_list_has_duplicate (a2::c1::s::c2::c::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                         then (nlet (a2, c1) : tZ * tZ := ex0 in
                               nlet (s , c2) : tZ * tZ := ex1 in
                               nlet c        : tZ      := ex2 in
                               nlet (s, c)   : tZ * tZ := ADC bw1 c0 a b in
                               P)
                         else e
                 | P1' => fun e => e
                 end
            | P0' => fun e => e
            end (nlet (a2, c1) : tZ * tZ := rewrite_exprf _ ex0 in rewrite_exprf _ P0)
       | TT => TT
       | Var _ n => Var n
       | Op _ _ opc args
         => Op opc (rewrite_exprf _ args)
       | (nlet nx := ex in eC)
         => (nlet nx := rewrite_exprf _ ex in rewrite_exprf _ eC)
       | Pair tx ex ty ey
         => Pair (rewrite_exprf tx ex) (rewrite_exprf ty ey)
       end%core%nexpr%bool.

  Fixpoint rewrite_exprf {t} (e : exprf t) : exprf t
    := @do_rewrite (@rewrite_exprf) t e.

  Definition rewrite_expr {t} (e : expr t) : expr t
    := match e in Named.expr _ _ _ t return expr t with
       | Abs _ _ n f => Abs n (rewrite_exprf f)
       end.
End named.


interp_base_type : base_type -> Type
  interp_op : forall src dst : flat_type base_type,
              op src dst ->
              interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  t : type base_type
  e : Expr base_type op t
  Hwf : Wf e
  x : interp_flat_type interp_base_type
        match (domain t -> codomain t)%ctype with
        | x -> _ => x
        end
  e0 : Syntax.Named.expr base_type op BinNums.positive t
  Heqo : Compile.compile (e (fun _ : base_type => BinNums.positive)) (Defaults.DefaultNamesFor e) =
         Some e0
  Heqo0 : Wf.Named.wf_unit Context.empty (RewriteAddToAdc.rewrite_expr positive_beq e0) =
          Some PointedProp.trivial
  e1 : Syntax.Named.expr base_type op FMapPositive.PositiveMap.key t
  Heqo1 : DeadCodeElimination.EliminateDeadCode (RewriteAddToAdc.rewrite_expr positive_beq e0)
            (Defaults.Named.default_names_for (RewriteAddToAdc.rewrite_expr positive_beq e0)) =
          Some e1
  Heqo2 : Wf.Named.wf_unit Context.empty e1 = Some PointedProp.trivial
  H, H0 : true = true
  i : interp_flat_type interp_base_type (codomain t)
  Heqo3 : Syntax.Named.interp e1 x = Some i
  i0 : interp_flat_type interp_base_type (codomain t)
  Heqo4 : Syntax.Named.Interp (RewriteAddToAdc.rewrite_expr positive_beq e0) x = Some i0
  ============================
  i0 = Interp interp_op e x*)
  Admitted.

  Lemma interpf_do_rewriteo
        {t} {e : exprf t}
    : retT e (do_rewriteo e).
  Proof.
    unfold do_rewriteo; intros *; break_innermost_match; try congruence.
    apply interpf_do_rewrite; assumption.
  Qed.

  Local Opaque RewriteAddToAdc.do_rewriteo.
  Lemma interpf_rewrite_exprf
        {t} (e : exprf t)
    : retT e (rewrite_exprf e).
  Proof.
    pose t as T.
    pose (rewrite_exprf_prestep (@rewrite_exprf) e) as E.
    induction e; simpl in *;
      intros ctx v H;
      pose proof (interpf_do_rewriteo (t:=T) (e:=E) ctx v H); clear H;
      subst T E;
      repeat first [ assumption
                   | progress unfold option_map, Let_In in *
                   | progress simpl in *
                   | progress subst
                   | progress inversion_option
                   | apply (f_equal (@Some _))
                   | break_innermost_match_step
                   | break_innermost_match_hyps_step
                   | congruence
                   | solve [ eauto ]
                   | match goal with
                     | [ IH : forall ctx v, interpf ?e = Some v -> _ = Some _, H' : interpf ?e = Some _ |- _ ]
                       => specialize (IH _ _ H')
                     | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                       => assert (a = b) by congruence; (subst a || subst b)
                     | [ |- ?rhs = Some _ ]
                       => lazymatch rhs with
                          | Some _ => fail
                          | None => fail
                          | _ => destruct rhs eqn:?
                          end
                     end ].
  Qed.

  Lemma interp_rewrite_expr
        {t} (e : expr t)
    : forall (ctx : InterpContext)
             v x,
      Named.interp (interp_op:=interp_op) (ctx:=ctx) (rewrite_expr e) x = Some v
      -> Named.interp (interp_op:=interp_op) (ctx:=ctx) e x = Some v.
  Proof.
    unfold Named.interp, rewrite_expr; destruct e; simpl.
    intros *; apply interpf_rewrite_exprf.
  Qed.

  Lemma Interp_rewrite_expr
        {t} (e : expr t)
    : forall v x,
      Named.Interp (Context:=InterpContext) (interp_op:=interp_op) (rewrite_expr e) x = Some v
      -> Named.Interp (Context:=InterpContext) (interp_op:=interp_op) e x = Some v.
  Proof.
    intros *; apply interp_rewrite_expr.
  Qed.
End named.
