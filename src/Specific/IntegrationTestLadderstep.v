bRequire Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Local Open Scope Z_scope.



Require Import Crypto.Spec.MxDH.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ForLoop.
Section foo.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq}.
  Delimit Scope F_scope with F.
  Local Open Scope F_scope.
  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "+" := Fadd : F_scope. Local Infix "*" := Fmul : F_scope.
  Local Infix "-" := Fsub : F_scope. Local Infix "/" := Fdiv : F_scope.
  Local Notation "x ^ 2" := (x*x) (at level 30) : F_scope.
  Local Notation "0" := Fzero : F_scope.  Local Notation "1" := Fone : F_scope.
  Local Notation "2" := (1+1) : F_scope. Local Notation "4" := (2+2) : F_scope.

  Context {a b: F}. (* parameters of the Montgomery curve *)
  Context {nonsquare_aa_m4:~exists sqrt, sqrt^2 = a^2-4} {five_neq_zero:1+4<>0}.

  Context {a24:F} {a24_correct:4*a24 = a-2}.

  Context {cswap:bool->F*F->F*F->(F*F)*(F*F)}.

  Local Notation xor := Coq.Init.Datatypes.xorb.

  Local Notation xzladderstep := (@M.xzladderstep _ Fadd Fsub Fmul a24).

  (* Ideally, we would verify that this corresponds to x coordinate
    multiplication *)
  Definition montladder (bound : positive) (testbit:nat->bool) (u:F) :=
    let '(P1, P2, swap) :=
        for (int i = Z.pos bound; i >= 0; i--)
            updating ('(P1, P2, swap) = ((1, 0), (u, 1), false)%F) {{
          dlet s_i := testbit (Z.to_nat i) in
          dlet swap := xor swap s_i in
          let '(P1, P2) := cswap swap P1 P2 in
          dlet swap := s_i in
          let '(P1, P2) := xzladderstep u P1 P2 in
          (P1, P2, swap)
        }} in
    let '((x, z), _) := cswap swap P1 P2 in
    x * Finv z.
End foo.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ETransitivity.
Require Import Crypto.Curves.Montgomery.XZ.
Import ListNotations.

Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.



Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feW_bounded : feW -> Prop
    := fun w => is_bounded_by None bounds (map wordToZ w).
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let phi : feW -> F m :=
    fun x => B.Positional.Fdecode wt (Tuple.map wordToZ x).

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition FMxzladderstep := @M.xzladderstep (F m) F.add F.sub F.mul.

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition Mxzladderstep_sig
    : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
      | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
  Proof.
    exists (@M.xzladderstep _ (proj1_sig add_sig) (proj1_sig sub_sig) (fun x y => proj1_sig carry_sig (proj1_sig mul_sig x y))).
    intros.
    cbv [FMxzladderstep M.xzladderstep].
    destruct Q, Q'; cbv [map map' fst snd Let_In eval].
    repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
    reflexivity.
  Defined.

  Context {cswap:bool->F m*F m->F m*F m->(F m*F m)*(F m*F m)}.
  Context {cswapZ:bool->tuple Z sz*tuple Z sz->tuple Z sz*tuple Z sz->(tuple Z sz*tuple Z sz)*(tuple Z sz*tuple Z sz)}.
  Context {cswapw:bool->feW*feW->feW*feW->(feW*feW)*(feW*feW)}.

  Context {invZ : tuple Z sz -> tuple Z sz}.


  Definition Fmontladder bound testbit a24 := @montladder (F m) 0%F 1%F F.add F.sub F.mul F.inv a24 cswap bound testbit.

  Definition montstep_sig
    : forall bound testbit,
      { montladderZ : tuple Z sz -> tuple Z sz -> tuple Z sz
      | forall a24 u,
          let montladderZ := montladderZ a24 u in
          let eval := B.Positional.Fdecode wt in
          eval montladderZ = Fmontladder bound testbit (eval a24) (eval u) }.
  Proof.
    intros.
    eexists (fun a24 => @montladder _ (proj1_sig zero_sig) (proj1_sig one_sig) (proj1_sig add_sig) (proj1_sig sub_sig) (fun x y => proj1_sig carry_sig (proj1_sig mul_sig x y)) invZ a24 cswapZ bound testbit).
    intros.
    Require Import AdmitAxiom.
    subst montladderZ.
    subst eval.
    unfold Fmontladder.
    unfold montladder.
    match goal with
    | [ |- ?f (let (a, b) := ?d in @?e a b) = ?rhs ]
      => transitivity (let (b, a) := d in f (e a b)); [ destruct d; reflexivity | ] (*** XXXXXX Needing to swap [b] and [a] as arguments to [e] is a BUG, track it down *)
    end.
    admit.
  Defined. (*

revert p;    admit.
    Set Printing All.
    pose (let (a, b) := D in (a, b)).

    end.
    revert p.
    pattern H.
    Set Printing All.
    repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
    reflexivity.
  Defined.*)


  Definition montladderw
    : forall bound testbit,
      { montladderw : feW -> feW -> feW
      | forall a24 u,
          let montladderw := montladderw a24 u in
          feW_bounded a24
          -> feW_bounded u
          -> feW_bounded montladderw
             /\ phi montladderw = Fmontladder bound testbit (phi a24) (phi u) }.
  Proof.
    intros.
    lazymatch goal with
    | [ |- { op | forall (a:?A) (b:?B),
               let v := op a b in
               @?P a b v } ]
      => refine (@lift2_sig A B _ P _)
    end.
    intros.
    lazymatch goal with
    | [ |- { e | ?A -> ?B -> @?E e } ]
      => refine (proj2_sig_map (P:=fun e => A -> B -> (_:Prop)) _ _)
    end.
    { intros ? FINAL.
      repeat let H := fresh in intro H; specialize (FINAL H).
      cbv [phi].
      split; [ refine (proj1 FINAL); shelve | ].
      rewrite <- (proj2_sig (montstep_sig _ _)).
      Unset Printing All.
      apply f_equal.
      cbv [proj1_sig]. cbv [montstep_sig].
      context_to_dlet_in_rhs (montladder _ _).
      cbv [montladder].
      (*do 4 match goal with
           | [ |- context[Tuple.map (n:=?N) (fun x : ?T => ?f (?g x))] ]
             => rewrite <- (Tuple.map_map (n:=N) f g
                            : pointwise_relation _ eq _ (Tuple.map (n:=N) (fun x : T => f (g x))))
           end.*)
      (*rewrite <- (proj2_sig Mxzladderstep_sig).
      apply f_equal.
      cbv [proj1_sig]; cbv [Mxzladderstep_sig].*)
      context_to_dlet_in_rhs (@M.xzladderstep _ _ _ _).
      cbv [M.xzladderstep].
      do 4 lazymatch goal with
           | [ |- context[@proj1_sig ?a ?b ?f_sig] ]
             => context_to_dlet_in_rhs (@proj1_sig a b f_sig)
           end.
      cbv beta iota delta [proj1_sig mul_sig add_sig sub_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz]; cbn [fst snd].
      refine (proj2 FINAL). }
    subst feW feW_bounded; cbv beta.


    apply lift2_sig.

Print montladder.



        downto
          ((1, 0), (u, 1), false)
          bound
          (fun state i =>
             let '(P1, P2, swap) := state in
             let s_i := testbit i in
             let swap := xor swap s_i in
             let '(P1, P2) := cswap swap P1 P2 in
             let swap := s_i in
             let '(P1, P2) := ladderstep u P1 P2 in
             (P1, P2, swap)
          ) in
    let '((x, z), _) := cswap swap P1 P2 in
    x * Finv z.






  (* TODO : change this to field once field isomorphism happens *)
  Definition xzladderstep :
    { xzladderstep : feW -> feW -> feW * feW -> feW * feW -> feW * feW * (feW * feW)
    | forall a24 x1 Q Q',
        let xz := xzladderstep a24 x1 Q Q' in
        feW_bounded a24
        -> feW_bounded x1
        -> feW_bounded (fst Q) /\ feW_bounded (snd Q)
        -> feW_bounded (fst Q') /\ feW_bounded (snd Q')
        -> ((feW_bounded (fst (fst xz)) /\ feW_bounded (snd (fst xz)))
            /\ (feW_bounded (fst (snd xz)) /\ feW_bounded (snd (snd xz))))
           /\ Tuple.map (n:=2) (Tuple.map (n:=2) phi) xz = FMxzladderstep (phi a24) (phi x1) (Tuple.map (n:=2) phi Q) (Tuple.map (n:=2) phi Q') }.
  Proof.
    lazymatch goal with
    | [ |- { op | forall (a:?A) (b:?B) (c:?C) (d:?D),
               let v := op a b c d in
               @?P a b c d v } ]
      => refine (@lift4_sig A B C D _ P _)
    end.
    intros a b c d; cbv beta iota zeta.
    lazymatch goal with
    | [ |- { e | ?A -> ?B -> ?C -> ?D -> @?E e } ]
      => refine (proj2_sig_map (P:=fun e => A -> B -> C -> D -> (_:Prop)) _ _)
    end.
    { intros ? FINAL.
      repeat let H := fresh in intro H; specialize (FINAL H).
      cbv [phi].
      split; [ refine (proj1 FINAL); shelve | ].
      do 4 match goal with
           | [ |- context[Tuple.map (n:=?N) (fun x : ?T => ?f (?g x))] ]
             => rewrite <- (Tuple.map_map (n:=N) f g
                            : pointwise_relation _ eq _ (Tuple.map (n:=N) (fun x : T => f (g x))))
           end.
      rewrite <- (proj2_sig Mxzladderstep_sig).
      apply f_equal.
      cbv [proj1_sig]; cbv [Mxzladderstep_sig].
      context_to_dlet_in_rhs (@M.xzladderstep _ _ _ _).
      cbv [M.xzladderstep].
      do 4 lazymatch goal with
           | [ |- context[@proj1_sig ?a ?b ?f_sig _] ]
             => context_to_dlet_in_rhs (@proj1_sig a b f_sig)
           end.
      cbv beta iota delta [proj1_sig mul_sig add_sig sub_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz]; cbn [fst snd].
      refine (proj2 FINAL). }
    subst feW feW_bounded; cbv beta.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*
    Time Glue.refine_to_reflective_glue (64::128::nil)%nat%list.
    Time ReflectiveTactics.refine_with_pipeline_correct.
    { Time ReflectiveTactics.do_reify. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
    { Time SubstLet.subst_let; clear; abstract vm_cast_no_check (eq_refl true). }
    { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
    { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }
     *)
    Time refine_reflectively.
    Show Ltac Profile.
  Time Defined.

Time End BoundedField25p5.
