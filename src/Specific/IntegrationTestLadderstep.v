Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.MontgomeryX.
Import ListNotations.

Require Import Crypto.Reflection.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 10)).
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

  Let feZ : Type := tuple Z 10.
  Let feW : Type := tuple word32 10.
  Let feBW : Type := BoundedWord 10 32 bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition FMxzladderstep := @M.xzladderstep (F m) F.add F.sub F.mul.

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition Mxzladderstep_sig
    : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
      | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
  Proof.
    exists (@M.xzladderstep _ (proj1_sig add_sig) (proj1_sig sub_sig) (proj1_sig mul_sig)).
    intros.
    cbv [FMxzladderstep M.xzladderstep].
    destruct Q, Q'; cbv [map map' fst snd Let_In eval].
    repeat rewrite <- ?(proj2_sig add_sig), <- ?(proj2_sig mul_sig), <- ?(proj2_sig sub_sig).
    reflexivity.
  Defined.

  Definition adjust_tuple2_tuple2_sig {A P Q}
             (v : { a : { a : tuple (tuple A 2) 2 | (P (fst (fst a)) /\ P (snd (fst a))) /\ (P (fst (snd a)) /\ P (snd (snd a))) }
                  | Q (exist _ _ (proj1 (proj1 (proj2_sig a))),
                       exist _ _ (proj2 (proj1 (proj2_sig a))),
                       (exist _ _ (proj1 (proj2 (proj2_sig a))),
                        exist _ _ (proj2 (proj2 (proj2_sig a))))) })
    : { a : tuple (tuple (@sig A P) 2) 2 | Q a }.
  Proof.
    eexists.
    exact (proj2_sig v).
  Defined.

  (** TODO MOVE ME *)
  (** The [eexists_sig_etransitivity] tactic takes a goal of the form
      [{ a | f a = b }], and splits it into two goals, [?b' = b] and
      [{ a | f a = ?b' }], where [?b'] is a fresh evar. *)
  Definition sig_eq_trans_exist1 {A B} (f : A -> B)
             (b b' : B)
             (pf : b' = b)
             (y : { a : A | f a = b' })
    : { a : A | f a = b }
    := let 'exist a p := y in exist _ a (eq_trans p pf).
  Ltac eexists_sig_etransitivity :=
    lazymatch goal with
    | [ |- { a : ?A | @?f a = ?b } ]
      => let lem := open_constr:(@sig_eq_trans_exist1 A _ f b _) in
         simple refine (lem _ _)
    end.
  Definition sig_eq_trans_rewrite_fun_exist1 {A B} (f f' : A -> B)
             (b : B)
             (pf : forall a, f' a = f a)
             (y : { a : A | f' a = b })
    : { a : A | f a = b }
    := let 'exist a p := y in exist _ a (eq_trans (eq_sym (pf a)) p).
  Ltac eexists_sig_etransitivity_for_rewrite_fun :=
    lazymatch goal with
    | [ |- { a : ?A | @?f a = ?b } ]
      => let lem := open_constr:(@sig_eq_trans_rewrite_fun_exist1 A _ f _ b) in
         simple refine (lem _ _)
    end.


  (** TODO MOVE ME *)
  (** This tactic moves to the context any [dlet x := y in ...] on the
      rhs of a goal of the form [{ a | lhs = rhs }]. *)
  Ltac sig_dlet_in_rhs_to_context :=
    repeat lazymatch goal with
           | [ |- { a | _ = @Let_In ?A ?B ?x ?P } ]
             => let v := fresh "x" in
                pose x as v;
                replace (@Let_In A B x P) with (P v) by (clear; abstract (subst v; cbv [Let_In]; reflexivity));
                cbv beta
           end.
  (** Takes in a uconstr [uc], uses [set] to find it in the goal and
      passes the constr that it finds to [k] *)
  Ltac with_uconstr_in_goal uc k :=
    let f := fresh in
    set (f := uc);
    let f' := (eval cbv delta [f] in f) in
    subst f; k f'.
  (** This tactic creates a [dlet x := f in rhs] in the rhs of a goal
      of the form [lhs = rhs]. *)
  Ltac context_to_dlet_in_rhs f :=
    lazymatch goal with
    | [ |- ?LHS = ?RHS ]
      => with_uconstr_in_goal
           f
           ltac:(fun f
                 => let RHS' := lazymatch (eval pattern f in RHS) with
                                | ?RHS _ => RHS
                                end in
                    let x := fresh "x" in
                    transitivity (dlet x := f in RHS' x);
                    [ | clear; abstract (cbv [Let_In]; reflexivity) ]
                )
    end.
  Tactic Notation "context_to_dlet_in_rhs" uconstr(f) := context_to_dlet_in_rhs f.
  (* TODO : change this to field once field isomorphism happens *)
  Definition xzladderstep :
    { xzladderstep : feBW -> feBW -> feBW * feBW -> feBW * feBW -> feBW * feBW * (feBW * feBW)
    | forall a24 x1 Q Q', Tuple.map (n:=2) (Tuple.map (n:=2) phi) (xzladderstep a24 x1 Q Q') = FMxzladderstep (phi a24) (phi x1) (Tuple.map (n:=2) phi Q) (Tuple.map (n:=2) phi Q') }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b c d, ?phi (f a b c d) = @?rhs a b c d } ]
      => apply lift4_sig with (P:=fun a b c d f => phi f = rhs a b c d)
    end.
    intros.
    eexists_sig_etransitivity. all:cbv [phi].
    rewrite <- !(Tuple.map_map (B.Positional.Fdecode wt) (BoundedWordToZ 10 32 bounds)).
    rewrite <- (proj2_sig Mxzladderstep_sig).
    apply f_equal.
    cbv [proj1_sig]; cbv [Mxzladderstep_sig].
    context_to_dlet_in_rhs M.xzladderstep.
    set (k := M.xzladderstep); context_to_dlet_in_rhs k; subst k.
    cbv [M.xzladderstep].
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b mul_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b mul_sig)
    end.
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b add_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b add_sig)
    end.
    lazymatch goal with
    | [ |- context[@proj1_sig ?a ?b sub_sig] ]
      => context_to_dlet_in_rhs (@proj1_sig a b sub_sig)
    end.
    cbv beta iota delta [proj1_sig mul_sig add_sig sub_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz].
    reflexivity.
    eexists_sig_etransitivity_for_rewrite_fun.
    { intro; cbv beta.
      subst feBW.
      set_evars.
      do 2 lazymatch goal with
           | [ |- context[Tuple.map (n:=?n) (fun x => ?f (?g x))] ]
             => rewrite <- (Tuple.map_map (n:=n) f g : pointwise_relation _ eq _ _)
           end.
      subst_evars.
      reflexivity. }
    cbv beta.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    apply adjust_tuple2_tuple2_sig.
    (* jgross start here! *)
    Set Ltac Profiling.
    change (@map 2) with (fun A B f => @map' A B f 1); cbv [map' BoundedWordToZ].
    cbn [fst snd proj1_sig].
    Set Printing Implicit.
    Set Printing Depth 10000.
    Require Import Coq.Program.Tactics.
    clear.
    lazymatch goal with
    | [ |- { a : ?A | ?P } ]
      => let P'' := fresh a in
         let P' := fresh P'' in
         let term := constr:(fun a : A => match P with
                                          | P' => ltac:(let v := (eval cbv delta [P'] in P') in
                                                        idtac v; exact I)
                                          end) in
         idtac end.
       let Q := lazymatch (eval cbv beta in term) with fun _ => ?term => term end in
       apply (@sig_sig_assoc _ _ Q)
  end.

    Print Ltac Associativity.sig_sig_assoc.
    Locate sig_sig_assoc.
    Glue.reassoc_sig_and_eexists.
    Glu
    Glue.
    Time refine_reflectively. (* Finished transaction in 19.348 secs (19.284u,0.036s) (successful) *)
    (*Show Ltac Profile.*)
    (* total time:     19.632s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
─ReflectiveTactics.do_reflective_pipelin  -0.0%  96.2%       1   18.884s
─ReflectiveTactics.solve_side_conditions   1.2%  96.1%       1   18.860s
─ReflectiveTactics.do_reify ------------  27.7%  44.0%       1    8.640s
─ReflectiveTactics.abstract_vm_compute_r  12.3%  13.9%       2    2.024s
─ReflectiveTactics.abstract_vm_compute_r   8.9%  12.2%       2    1.576s
─Reify_rhs_gen -------------------------   0.8%  11.7%       1    2.300s
─ReflectiveTactics.renamify_rhs --------  10.4%  11.5%       1    2.260s
─ReflectiveTactics.abstract_rhs --------   4.6%   5.8%       1    1.148s
─clear (var_list) ----------------------   5.2%   5.2%      57    0.184s
─eexact --------------------------------   4.1%   4.1%      68    0.028s
─prove_interp_compile_correct ----------   0.0%   3.4%       1    0.664s
─ReflectiveTactics.abstract_cbv_interp_r   2.7%   3.3%       1    0.648s
─unify (constr) (constr) ---------------   3.2%   3.2%       6    0.248s
─rewrite ?EtaInterp.InterpExprEta ------   3.1%   3.1%       1    0.612s
─ReflectiveTactics.abstract_cbv_rhs ----   2.0%   2.7%       1    0.532s
─Glue.refine_to_reflective_glue --------   0.0%   2.2%       1    0.436s
─rewrite H -----------------------------   2.1%   2.1%       1    0.420s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
 ├─ReflectiveTactics.do_reflective_pipel  -0.0%  96.2%       1   18.884s
 │└ReflectiveTactics.solve_side_conditio   1.2%  96.1%       1   18.860s
 │ ├─ReflectiveTactics.do_reify --------  27.7%  44.0%       1    8.640s
 │ │ ├─Reify_rhs_gen -------------------   0.8%  11.7%       1    2.300s
 │ │ │ ├─prove_interp_compile_correct --   0.0%   3.4%       1    0.664s
 │ │ │ │└rewrite ?EtaInterp.InterpExprEt   3.1%   3.1%       1    0.612s
 │ │ │ └─rewrite H ---------------------   2.1%   2.1%       1    0.420s
 │ │ └─eexact --------------------------   4.1%   4.1%      68    0.028s
 │ ├─ReflectiveTactics.abstract_vm_compu  12.3%  13.9%       2    2.024s
 │ ├─ReflectiveTactics.abstract_vm_compu   8.9%  12.2%       2    1.576s
 │ ├─ReflectiveTactics.renamify_rhs ----  10.4%  11.5%       1    2.260s
 │ ├─ReflectiveTactics.abstract_rhs ----   4.6%   5.8%       1    1.148s
 │ ├─ReflectiveTactics.abstract_cbv_inte   2.7%   3.3%       1    0.648s
 │ └─ReflectiveTactics.abstract_cbv_rhs    2.0%   2.7%       1    0.532s
 └─Glue.refine_to_reflective_glue ------   0.0%   2.2%       1    0.436s
*)
  Time Defined. (* Finished transaction in 10.167 secs (10.123u,0.023s) (successful) *)

End BoundedField25p5.
