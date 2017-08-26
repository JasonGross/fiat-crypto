(** * Exact reification of PHOAS Representation of Gallina *)
(** The reification procedure goes through [InputSyntax], which allows
    judgmental equality of the denotation of the reified term. *)
Require Import Coq.Strings.String.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.InputSyntax.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.DebugPrint.
(*Require Import Crypto.Util.Tactics.PrintContext.*)
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstLet.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.TransparentAssert.
Require Import Crypto.Util.Tactics.Ltac2.

Import Ltac2.Init.

(** Change this with [Ltac2 Set reify_debug_level := fun () => 1.] to get
    more debugging. *)
Ltac2 mutable reify_debug_level () := 0.
Module Import ReifyDebugNotations.
  Export Compilers.Syntax.Notations.
  Export Util.LetIn.
End ReifyDebugNotations.

Ltac2 debug_enter_reify_idtac funname e :=
  Message.print None [Message.of_string funname; Message.of_string " Attempting to reify: "; Message.of_constr e].
Ltac2 debug_leave_reify_success_idtac funname e ret :=
  Message.print None [Message.of_string funname; Message.of_string " Success in reifying: "; Message.of_constr e; Message.of_string " as "; Message.of_constr ret].
Ltac2 debug_leave_reify_failure_idtac funname e exn :=
  Message.print
    None
    [Message.of_string funname;
       Message.of_string " Failure in reifying: ";
       Message.of_constr e;
       Message.of_string " (";
       Message.of_exn exn;
       Message.of_string ")"].

Ltac2 debug n tac :=
  let lvl := reify_debug_level () in
  match Int.equal (Int.compare lvl (Int.sub n 1)) 1 with
  | true => tac ()
  | false => () (* (* FIXME Int.compare is broken () *) tac ()*)
  end.
Ltac2 debug_enter_reify_flat_type e :=
  debug 2 (fun () => debug_enter_reify_idtac "reify_flat_type:" e).
Ltac2 debug_leave_reify_flat_type_success e ret :=
  debug 3 (fun () => debug_leave_reify_success_idtac "reify_flat_type:" e ret).
Ltac2 debug_leave_reify_flat_type_failure e exn :=
  debug 3 (fun () => debug_leave_reify_failure_idtac "reify_flat_type:" e exn).
Ltac2 debug_enter_reify_type e :=
  debug 2 (fun () => debug_enter_reify_idtac "reify_type:" e).
Ltac2 debug_enter_reifyf e :=
  debug 2 (fun () => debug_enter_reify_idtac "reifyf:" e).
Ltac2 debug_leave_reifyf_success e ret :=
  debug 3 (fun () => debug_leave_reify_success_idtac "reifyf:" e ret).
Ltac2 debug_leave_reifyf_failure e exn :=
  debug 0 (fun () => debug_leave_reify_failure_idtac "reifyf:" e exn).
Ltac2 debug_leave_reify_abs_success e ret :=
  debug 3 (fun () => debug_leave_reify_success_idtac "reify_abs:" e ret).
Ltac2 debug_leave_reify_abs_failure e exn :=
  debug 0 (fun () => debug_leave_reify_failure_idtac "reify_abs:" e exn).
Ltac2 debug_reifyf_case case :=
  debug 3 (fun () => Message.print None [Message.of_string "reifyf: "; Message.of_string case]).
Ltac2 debug_enter_reifyf_var e :=
  debug 2 (fun () => debug_enter_reify_idtac "reifyf_var:" e).
Ltac2 debug_leave_reifyf_var_success e ret :=
  debug 3 (fun () => debug_leave_reify_success_idtac "reifyf_var:" e ret).
Ltac2 debug_leave_reifyf_var_failure e exn :=
  debug 3 (fun () => debug_leave_reify_failure_idtac "reifyf_var:" e exn).
Ltac2 debug_reifyf_var_case case :=
  debug 3 (fun () => Message.print None [Message.of_string "reifyf_var: "; Message.of_string case]).
Ltac2 debug_reify_abs_case case :=
  debug 3 (fun () => Message.print None [Message.of_string "reify_abs: "; Message.of_string case]).
Ltac2 debug_enter_reify_abs e :=
  debug 2 (fun () => debug_enter_reify_idtac "reify_abs:" e).

Class reify {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify : T.
Definition reify_var_for_in_is base_type_code {T} (x : T) (t : flat_type base_type_code) {eT} (e : eT) := False.
Arguments reify_var_for_in_is _ {T} _ _ {eT} _.

(** [reify] assumes that operations can be reified via the [reify_op]
    typeclass, which gets passed the type family of operations, the
    expression which is headed by an operation, and expects resolution
    to fill in a number of arguments (which [reifyf] will
    automatically curry), as well as the reified operator.

    We also assume that types can be reified via the [reify] typeclass
    with arguments [reify type <type to be reified>]. *)
Class reify_op {opTF} (op_family : opTF) {opExprT} (opExpr : opExprT) (nargs : nat) {opT} (reified_op : opT)
  := Build_reify_op : True.

(** Override this to get a faster [reify_type] *)
Ltac base_reify_type ty :=
  lazymatch constr:(_ : reify type ty) with ?v => v end.
Ltac2 mutable base_reify_type ty :=
  Ltac1.from_ltac1
    ty
    (fun ()
     => ltac1:(let ty := Ltac1.get_ltac2_result () in
               let v := base_reify_type ty in
               Ltac1.save_ltac1_result v)).
(*strip_type_cast '(_ : reify type $ty).*)
Ltac2 reify_base_type ty := base_reify_type ty.


Ltac2 rec reify_flat_type ty :=
  debug_enter_reify_flat_type ty;
    let ret :=
        Control.case
          (fun ()
           => Control.lazymatch0
                ty
                [
                  ((pattern:(prod ?A ?B)),
                   (fun matches
                    => let a := Ident.find @A matches in
                       let b := Ident.find @B matches in
                       let aR := reify_flat_type a in
                       let bR := reify_flat_type b in
                       '(@Prod _ $aR $bR)))
                  ;
                  ((pattern:(Syntax.interp_type _ (Tflat ?T))),
                   (fun matches
                    => Ident.find @T matches))
                  ;
                  ((pattern:(Syntax.interp_flat_type _ ?T)),
                   (fun matches
                    => Ident.find @T matches))
                  ;
                  ((pattern:(_)),
                   (fun _
                    => let v := reify_base_type ty in
                       '(@Tbase _ $v)))
          ]) in
    match ret with
    | Val ret
      => let ((ret, cont)) := ret in
         debug_leave_reify_flat_type_success ty ret;
           ret
    | Err exn
      => debug_leave_reify_flat_type_failure ty exn;
           Control.zero exn
    end.

Ltac2 rec reify_input_type ty :=
  debug_enter_reify_type ty;
    Control.lazymatch0
      ty
      [
        ((pattern:((?A -> ?B)%type)),
         (fun matches
          => let a := Ident.find @A matches in
             let b := Ident.find @B matches in
             let aR := reify_flat_type a in
             let bR := reify_input_type b in
             '(@Arrow _ $aR $bR)))
        ;
        ((pattern:(InputSyntax.interp_type _ ?T)),
         (fun matches
          => Ident.find @T matches))
      ].
Ltac2 reify_type ty :=
  debug_enter_reify_type ty;
    Control.lazymatch0
      ty
      [
        ((pattern:((?A -> ?B)%type)),
         (fun matches
          => let a := Ident.find @A matches in
             let b := Ident.find @B matches in
             let aR := reify_flat_type a in
             let bR := reify_flat_type b in
             '(@Syntax.Arrow _ $aR $bR)))
        ;
        ((pattern:(Syntax.interp_type _ ?T)),
         (fun matches
          => Ident.find @T matches))
      ].
Ltac reify_type ty :=
  let dummy := Ltac1.save_ltac1_result ty in
  let ret := constr:(ltac2:(let ty := Ltac1.get_ltac1_result () in
                            let v := reify_type ty in
                            Control.refine (fun () => v))) in
  let dummy := Ltac1.clear_ltac1_results () in
  eval cbv beta zeta in ret.

Ltac2 rec reifyf_var (ctx : (ident * (constr * ident)) list) (x : constr) (mkVar : constr -> constr -> 'a) :=
  debug_enter_reifyf_var x;
    let ret :=
        Control.case
          (fun ()
           => match Constr.Unsafe.kind (Constr.strip_casts x) with
              | Constr.Unsafe.Var x
                => let ((t, v)) := Ident.find x ctx in
                   debug_reifyf_var_case "var";
                     let v := Constr.Unsafe.make (Constr.Unsafe.Var v) in
                     mkVar t v
              | _
                => Control.lazymatch0
                     x
                     [
                       ((pattern:(fst ?x')),
                        (fun matches
                         => let x' := Ident.find @x' matches in
                            debug_reifyf_var_case "fst";
                            reifyf_var
                              ctx
                              x' (fun t v
                                  => Control.lazymatch0
                                       t
                                       [((pattern:(Prod ?A ?B)),
                                         (fun matches
                                          => let a := Ident.find @A matches in
                                             let b := Ident.find @B matches in
                                             mkVar a '(fst $v)))])))
                       ;
                       ((pattern:(snd ?x')),
                        (fun matches
                         => let x' := Ident.find @x' matches in
                            debug_reifyf_var_case "snd";
                            reifyf_var
                              ctx
                              x' (fun t v
                                  => Control.lazymatch0
                                       t
                                       [((pattern:(Prod ?A ?B)),
                                         (fun matches
                                          => let a := Ident.find @A matches in
                                             let b := Ident.find @B matches in
                                             mkVar b '(snd $v)))])))
                     ]
              end) in
    match ret with
    | Val ret => let ((ret, _)) := ret in
                 debug_leave_reifyf_var_success x ret;
                   ret
    | Err exn => debug_leave_reifyf_var_failure x exn;
                  Control.zero exn
    end.

Inductive reify_result_helper :=
| finished_value {T} (res : T)
| context_value {TF} (resF : TF) {argT} (arg : argT)
| op_info {T} (res : T)
| reification_unsuccessful.

(** Override this to get a faster [reify_op] *)
Ltac base_reify_op op op_head expr :=
  let r := constr:(_ : reify_op op op_head _ _) in
  type of r.
Ltac2 mutable base_reify_op op op_head expr :=
  Ltac1.from_ltac1
    '(($op, $op_head, $expr)%core)
    (fun ()
     => ltac1:(let vals := Ltac1.get_ltac2_result () in
               lazymatch vals with
               | (?op, ?op_head, ?expr)%core
                 => let v := base_reify_op op op_head expr in
                    Ltac1.save_ltac1_result v
               end)).
(*let r := '(_ : reify_op $op $op_head _ _) in
  Constr.type r.*)
Ltac2 reify_op op op_head expr :=
  let t := base_reify_op op op_head expr in
  '(op_info $t).

Ltac2 debug_enter_reify_rec () :=
  debug 1 (fun () => ltac1:(idtac_goal)).
Ltac2 debug_leave_reify_rec e :=
  debug 1 (fun () => Message.print
                       None
                       [Message.of_string "reifyf success: ";
                          Message.of_constr e]).

(** TODO MOVE ME *)
Ltac2 rec head expr :=
  Control.match0
    expr
    [
      ((pattern:(?f _)),
       (fun matches
        => let f := Ident.find @f matches in
           head f))
      ;
      ((pattern:(_)),
       (fun matches
        => expr))
    ].

(* TODO MOVE ME *)
Ltac2 beta_flag :=
  {
    Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
  }.

(* TODO MOVE ME *)
Ltac2 beta_zeta_flag :=
  {
    Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := true; Std.rDelta := false; Std.rConst := [];
  }.

(* TODO MOVE ME *)
Ltac2 rec reference_of_constr (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id => Std.VarRef id
  | Constr.Unsafe.Constant c _ => Std.ConstRef c
  | Constr.Unsafe.Ind c _ => Std.IndRef c
  | Constr.Unsafe.Constructor c _ => Std.ConstructRef c
  | Constr.Unsafe.Cast c _ _ => reference_of_constr c
  | Constr.Unsafe.App c _ => reference_of_constr c
  | Constr.Unsafe.Proj _ _ => Control.throw (Tactic_failure (Some (Message.of_string "projections not yet handled in reference_of_constr")))
  | Constr.Unsafe.Rel _ => Control.zero Match_failure
  | Constr.Unsafe.Meta _ => Control.zero Match_failure
  | Constr.Unsafe.Evar _ _ => Control.zero Match_failure
  | Constr.Unsafe.Sort _ => Control.zero Match_failure
  | Constr.Unsafe.Prod _ _ _ => Control.zero Match_failure
  | Constr.Unsafe.Lambda _ _ _ => Control.zero Match_failure
  | Constr.Unsafe.LetIn _ _ _ _ => Control.zero Match_failure
  | Constr.Unsafe.Case _ _ _ _ => Control.zero Match_failure
  | Constr.Unsafe.Fix _ _ _ _ _ => Control.zero Match_failure
  | Constr.Unsafe.CoFix _ _ _ _ => Control.zero Match_failure
  end.

Ltac2 beta_delta_flag (ls : Std.reference list) :=
  {
    Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := false; Std.rDelta := (match ls with | [] => true | _::_ => false end);
    Std.rConst := ls;
  }.

Ltac2 beta_iota_delta_flag (ls : Std.reference list) :=
  {
    Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
    Std.rZeta := false; Std.rDelta := (match ls with | [] => true | _::_ => false end);
    Std.rConst := ls;
  }.

Ltac2 reify_lambda_pattern
      (base_type_code : constr)
      (var : constr)
      (rec_call : (ident * (constr * ident)) list -> constr -> constr)
      (ctx : (ident * (constr * ident)) list)
      (debug_enter : unit -> unit)
      (fun_name : string)
      (ret : constr (* t *) -> constr (* rt *) -> constr (* c *) -> 'a)
  :=
    ((pattern:(fun x : ?T => @?C x)),
     (fun matches
      => let t := Ident.find @T matches in
         let c := Ident.find @C matches in
         debug_enter ();
           let rt := reify_flat_type t in
           (** We assume the invariant that all bound variables show
               up as Rel nodes rather than Var nodes *)
           match Constr.Unsafe.kind c with
           | Constr.Unsafe.Lambda id t c
             => let c_set := Fresh.Free.of_ids (List.map (fun ((id, _, _)) => id) (Control.hyps ())) in
                let c_set := Fresh.Free.union c_set (Fresh.Free.of_constr c) in
                let x_base := match id with
                              | Some id => id
                              | None => @x
                              end in
                let x := Fresh.fresh c_set x_base in
                let c_set := Fresh.Free.union
                               c_set
                               (Fresh.Free.of_ids [x]) in
                let not_x := Fresh.fresh c_set x_base in
                let ctx := (x, (rt, not_x)) :: ctx in
                let c' :=
                    let c := Constr.Unsafe.substnl [Constr.Unsafe.make (Constr.Unsafe.Var x)] 0 c in
                    let ret :=
                        Control.in_context
                          x t
                          (fun ()
                           => Control.in_context
                                not_x '($var $rt)
                                (fun () => rec_call ctx c)) in
                    ret
                in
                Control.lazymatch0
                  c'
                  [
                    ((pattern:(fun _ => ?C)),
                     (fun matches
                      => let c := Ident.find @C matches in
                         ret t rt c))
                    ;
                    ((pattern:(_)),
                     (fun _
                      => let msg :=
                             Message.join (Message.of_string "")
                                          [Message.of_string "Error: ";
                                             Message.of_string fun_name;
                                             Message.of_string ": Failed to eliminate function dependencies of: ";
                                             Message.of_constr c'] in
                         Message.print None [msg];
                           Control.zero (Tactic_failure (Some msg))))
                  ]
           | _ => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "reify_lambda_pattern: Term matched fun, but was not kinded as lambda: ") (Message.of_constr c))))
           end)).

Ltac2 rec reifyf_aux (base_type_code : constr) (interp_base_type : constr) (op : constr) (var : constr) (ctx : (ident * (constr * ident)) list) (e : constr) :=
  let reify_rec_with ctx e := reifyf_aux base_type_code interp_base_type op var ctx e in
  let reify_rec e := reify_rec_with ctx e in
  let mkLetIn ex eC := '(LetIn (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) $ex $eC) in
  let mkPair ex ey := '(Pair (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) $ex $ey) in
  let mkVar ty ex := '(Var (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) (t:=$ty) $ex) in
  let mkConst ty ex := '(Const (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) (t:=$ty) $ex) in
  let mkOp ty retT op_code args := '(Op (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) (t1:=$ty) (tR:=$retT) $op_code $args) in
  let mkMatchPair tC ex eC := '(MatchPair (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) (tC:=$tC) $ex $eC) in
  let mkFst ex := '(Fst (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) $ex) in
  let mkSnd ex := '(Snd (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) $ex) in
  let reify_pretag := '(@exprf $base_type_code $interp_base_type $op) in
  let reify_tag := '($reify_pretag $var) in
  debug_enter_reifyf e;
    Control.plus
      (fun ()
       => Control.match_hyps_ty
            [((pattern:(reify ?reify_tag' ?v)),
              (fun rv matches
               => let reify_tag' := Ident.find @reify_tag' matches in
                  let v := Ident.find @v matches in
                  match Constr.equal reify_tag reify_tag' with
                  | true
                    => match Constr.equal e v with
                       | true
                         => debug_reifyf_case "hyp";
                              Control.hyp rv
                       | false => Control.zero Match_failure
                       end
                  | false => Control.zero Match_failure
                  end))])
      (fun _
       => Control.plus
            (fun ()
             => let ret :=
                    Control.lazymatch0
                      e
                      [
                        ((pattern:(let x := ?ex in @?eC x)),
                         (fun matches
                          => let ex := Ident.find @ex matches in
                             let eC := Ident.find @eC matches in
                             debug_reifyf_case "let in";
                               let ex := reify_rec ex in
                               let eC := reify_rec eC in
                               mkLetIn ex eC))
                        ;
                        ((pattern:(dlet x := ?ex in @?eC x)),
                         (fun matches
                          => let ex := Ident.find @ex matches in
                             let eC := Ident.find @eC matches in
                             debug_reifyf_case "dlet in";
                               let ex := reify_rec ex in
                               let eC := reify_rec eC in
                               mkLetIn ex eC))
                        ;
                        ((pattern:(pair ?a ?b)),
                         (fun matches
                          => let a := Ident.find @a matches in
                             let b := Ident.find @b matches in
                             debug_reifyf_case "pair";
                               let a := reify_rec a in
                               let b := reify_rec b in
                               mkPair a b))
                        ;
                        (reify_lambda_pattern
                           base_type_code
                           var
                           reify_rec_with
                           ctx
                           (fun () => debug_reifyf_case "fun")
                           "reifyf"
                           (fun t rt c => c))
                        ;
                        ((pattern:(match ?ev with pair a b => @?eC a b end)),
                         (fun matches
                          => let ev := Ident.find @ev matches in
                             let eC := Ident.find @eC matches in
                             debug_reifyf_case "matchpair";
                               let t := Std.eval_cbv beta_flag (Constr.type eC) in
                               let t := Control.lazymatch0
                                          t
                                          [((pattern:(_ -> _ -> ?T)),
                                            (fun matches
                                             => let t := Ident.find @T matches in
                                                reify_flat_type t))] in
                               let v := reify_rec ev in
                               let c := reify_rec eC in
                               mkMatchPair t v c))
                        ;
                        ((pattern:(@fst ?A ?B ?ev)),
                         (fun matches
                          => let a := Ident.find @A matches in
                             let b := Ident.find @B matches in
                             let ev := Ident.find @ev matches in
                             debug_reifyf_case "fst";
                               let v := reify_rec ev in
                               mkFst v))
                        ;
                        ((pattern:(@snd ?A ?B ?ev)),
                         (fun matches
                          => let a := Ident.find @A matches in
                             let b := Ident.find @B matches in
                             let ev := Ident.find @ev matches in
                             debug_reifyf_case "snd";
                               let v := reify_rec ev in
                               mkSnd v))
                        ;
                        ((pattern:(?x)),
                         (fun matches
                          => let x := Ident.find @x matches in
                             debug_reifyf_case "?x";
                               let t := reify_flat_type (Constr.type x) in
                               let retv :=
                                   Control.match_list
                                     (fun f => f ())
                                     [ (fun ()
                                        => let retv := reifyf_var ctx x mkVar in
                                           '(finished_value $retv))
                                       ;(fun ()
                                         => let op_head := head x in
                                            reify_op op op_head x)
                                       ;(fun ()
                                         => Control.lazymatch0
                                              x
                                              [
                                                ((pattern:(?F ?args)),
                                                 (fun matches
                                                  => let f := Ident.find @F matches in
                                                     let args := Ident.find @args matches in
                                                     let rF :=
                                                         Control.match_hyps_ty
                                                           [
                                                             ((pattern:(forall x not_x, reify ?reify_tag' (?F' x))),
                                                              (fun rF matches
                                                               => let f' := Ident.find @F' matches in
                                                                  let reify_tag' := Ident.find @reify_tag' matches in
                                                                  match Constr.equal f f' with
                                                                  | true
                                                                    => match Constr.equal reify_tag reify_tag' with
                                                                       | true => Control.hyp rF
                                                                       | false => Control.zero Match_failure
                                                                       end
                                                                  | false => Control.zero Match_failure
                                                                  end))
                                                             ;
                                                             ((pattern:(forall var' x (not_x : var' _), reify (?reify_pretag' var') (?F' x))),
                                                              (fun rF matches
                                                               => let f' := Ident.find @F' matches in
                                                                  let reify_pretag' := Ident.find @reify_pretag' matches in
                                                                  match Constr.equal f f' with
                                                                  | true
                                                                    => match Constr.equal reify_pretag reify_pretag' with
                                                                       | true => '(ltac2:(Control.refine (fun () => Control.hyp rF)) $var)
                                                                       | false => Control.zero Match_failure
                                                                       end
                                                                  | false => Control.zero Match_failure
                                                                  end))
                                                           ] in
                                                     '(context_value $rF $args)))
                                              ]
                                        )
                                       ;(fun ()
                                         => let c := mkConst t x in
                                            '(finished_value $c))
                                       ;(fun ()
                                         => '(reification_unsuccessful))
                                     ]
                               in
                               Control.lazymatch0
                                 retv
                                 [
                                   ((pattern:(finished_value ?v)),
                                    (fun matches
                                     => Ident.find @v matches))
                                   ;
                                   ((pattern:(context_value ?rFH ?eargs)),
                                    (fun matches
                                     => let rFH := Ident.find @rFH matches in
                                        let eargs := Ident.find @eargs matches in
                                        debug_reifyf_case "context_value";
                                          let args := reify_rec eargs in
                                          let f_head := head rFH in
                                          let rFH := Std.eval_cbv (beta_delta_flag [reference_of_constr f_head]) rFH in
                                          let f := Control.lazymatch0
                                                     rFH
                                                     [
                                                       ((pattern:(fun _ => ?C)),
                                                        (fun matches
                                                         => Ident.find @C matches))
                                                     ] in
                                          mkLetIn args f
))
                                   ;
                                   ((pattern:(op_info (reify_op _ _ ?nargs ?op_code))),
                                    (fun matches
                                     => let nargs := Ident.find @nargs matches in
                                        let op_code := Ident.find @op_code matches in
                                        let tR := reify_flat_type (Constr.type x) in
                                        Control.lazymatch0
                                          nargs
                                          [
                                            ((pattern:(1%nat)),
                                             (fun _
                                              => Control.lazymatch0
                                                   x
                                                   [
                                                     ((pattern:(?f ?x0)),
                                                      (fun matches
                                                       => let f := Ident.find @f matches in
                                                          let x0 := Ident.find @x0 matches in
                                                          let a0T := reify_flat_type (Constr.type x0) in
                                                          let a0 := reify_rec x0 in
                                                          mkOp a0T tR op_code a0))
                                            ]))
                                            ;
                                            ((pattern:(2%nat)),
                                             (fun _
                                              => Control.lazymatch0
                                                   x
                                                   [
                                                     ((pattern:(?f ?x0 ?x1)),
                                                      (fun matches
                                                       => let f := Ident.find @f matches in
                                                          let x0 := Ident.find @x0 matches in
                                                          let x1 := Ident.find @x1 matches in
                                                          let a0T := reify_flat_type (Constr.type x0) in
                                                          let a0 := reify_rec x0 in
                                                          let a1T := reify_flat_type (Constr.type x1) in
                                                          let a1 := reify_rec x1 in
                                                          let args := mkPair a0 a1 in
                                                          mkOp '(@Prod _ $a0T $a1T) tR op_code args))
                                            ]))
                                            ;
                                            ((pattern:(3%nat)),
                                             (fun _
                                              => Control.lazymatch0
                                                   x
                                                   [
                                                     ((pattern:(?f ?x0 ?x1 ?x2)),
                                                      (fun matches
                                                       => let f := Ident.find @f matches in
                                                          let x0 := Ident.find @x0 matches in
                                                          let x1 := Ident.find @x1 matches in
                                                          let x2 := Ident.find @x2 matches in
                                                          let a0T := reify_flat_type (Constr.type x0) in
                                                          let a0 := reify_rec x0 in
                                                          let a1T := reify_flat_type (Constr.type x1) in
                                                          let a1 := reify_rec x1 in
                                                          let a2T := reify_flat_type (Constr.type x2) in
                                                          let a2 := reify_rec x2 in
                                                          let args := let a01 := mkPair a0 a1 in mkPair a01 a2 in
                                                          mkOp '(@Prod _ (@Prod _ $a0T $a1T) $a2T) tR op_code args))
                                            ]))
                                            ;
                                            ((pattern:(4%nat)),
                                             (fun _
                                              => Control.lazymatch0
                                                   x
                                                   [
                                                     ((pattern:(?f ?x0 ?x1 ?x2 ?x3)),
                                                      (fun matches
                                                       => let f := Ident.find @f matches in
                                                          let x0 := Ident.find @x0 matches in
                                                          let x1 := Ident.find @x1 matches in
                                                          let x2 := Ident.find @x2 matches in
                                                          let x3 := Ident.find @x3 matches in
                                                          let a0T := reify_flat_type (Constr.type x0) in
                                                          let a0 := reify_rec x0 in
                                                          let a1T := reify_flat_type (Constr.type x1) in
                                                          let a1 := reify_rec x1 in
                                                          let a2T := reify_flat_type (Constr.type x2) in
                                                          let a2 := reify_rec x2 in
                                                          let a3T := reify_flat_type (Constr.type x3) in
                                                          let a3 := reify_rec x3 in
                                                          let args := let a01 := mkPair a0 a1 in let a012 := mkPair a01 a2 in mkPair a012 a3 in
                                                          mkOp '(@Prod _ (@Prod _ (@Prod _ $a0T $a1T) $a2T) $a3T) tR op_code args))
                                            ]))
                                            ;
                                            ((pattern:(_)),
                                             (fun _
                                              => let msg :=
                                                     Message.join
                                                       (Message.of_string "")
                                                       [Message.of_string "Error: Unsupported number of operation arguments in reifyf: ";
                                                          Message.of_constr nargs] in
                                                 Message.print None [msg];
                                                   Control.zero (Tactic_failure (Some msg))))
                                   ]))
                                   ;
                                   ((pattern:(reification_unsuccessful)),
                                    (fun matches
                                     => let msg :=
                                            Message.join
                                              (Message.of_string " ")
                                              [Message.of_string "Error: Failed to reify:";
                                                 Message.of_constr x] in
                                        Message.print None [msg];
                                          Control.zero (Tactic_failure (Some msg))))
                                 ]
                        ))
                      ] in
                debug_leave_reifyf_success e ret;
                  ret)
            (fun exn
             => debug_leave_reifyf_failure e exn;
                  Control.zero exn)).

Ltac2 reifyf (base_type_code : constr) (interp_base_type : constr) (op : constr) (var : constr) (e : constr) :=
  reifyf_aux base_type_code interp_base_type op var [] e.
Ltac reifyf base_type_code interp_base_type op var e :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op, var, e)%core in
  let ret :=
      constr:(ltac2:(Control.lazymatch0
                       (Ltac1.get_ltac1_result ())
                       [((pattern:((?base_type_code, ?interp_base_type, ?op, ?var, ?e)%core)),
                         (fun matches
                          => let base_type_code := Ident.find @base_type_code matches in
                             let interp_base_type := Ident.find @interp_base_type matches in
                             let op := Ident.find @op matches in
                             let var := Ident.find @var matches in
                             let e := Ident.find @e matches in
                             let v := reifyf base_type_code interp_base_type op var e in
                             Control.refine (fun () => v)))])) in
  let dummy := Ltac1.clear_ltac1_results () in
  eval cbv beta zeta in ret.

Ltac2 reify_goal () :=
  let g := Control.goal () in
  Control.lazymatch0
    g
    [
      ((pattern:(reify (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)),
       (fun matches
        => let base_type_code := Ident.find @base_type_code matches in
           let interp_base_type := Ident.find @interp_base_type matches in
           let op := Ident.find @op matches in
           let var := Ident.find @var matches in
           let e := Ident.find @e matches in
           debug_enter_reify_rec ();
             let e := reifyf base_type_code interp_base_type op var e in
             debug_leave_reify_rec e;
               Notations.exact0 false (fun () => e)))
    ].

Hint Extern 0 (reify (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> (ltac2:(reify_goal ()))
   : typeclass_instances.

(** For reification including [Abs] *)
Class reify_abs {varT} (var : varT) {eT} (e : eT) {T : Type} := Build_reify_abs : T.

Ltac2 rec reify_abs_aux base_type_code interp_base_type op var ctx e :=
  let reify_rec_with ctx e := reify_abs_aux base_type_code interp_base_type op var ctx e in
  let reify_rec e := reify_rec_with ctx e in
  let reifyf_term e := reifyf_aux base_type_code interp_base_type op var ctx e in
  let mkReturn ef := '(Return (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) $ef) in
  let mkAbs src ef := '(Abs (base_type_code:=$base_type_code) (interp_base_type:=$interp_base_type) (op:=$op) (var:=$var) (src:=$src) $ef) in
  let reify_pretag := '(@exprf $base_type_code $interp_base_type $op) in
  let reify_tag := '($reify_pretag $var) in
  debug_enter_reify_abs e;
    let ret :=
        Control.case
          (fun ()
           => Control.plus
                (fun ()
                 => let ((rev, t))
                        := Control.match_hyps1_with_body
                             (pattern:(?rev))
                             (pattern:(forall var' (x : ?T) (not_x : var' _), reify (?reify_pretag' var') (?e' x)))
                             (fun re matches
                              => let rev := Ident.find @rev matches in
                                 let t := Ident.find @T matches in
                                 let reify_pretag' := Ident.find @reify_pretag' matches in
                                 let e' := Ident.find @e' matches in
                                 match Constr.equal reify_pretag' reify_pretag with
                                 | true
                                   => match Constr.equal e' e with
                                      | true => (rev, t)
                                      | false => Control.zero Match_failure
                                      end
                                 | false => Control.zero Match_failure
                                 end) in
                    debug_reify_abs_case "hyp";
                      let t := reify_flat_type t in
                      let f := Control.lazymatch0
                                 (Std.eval_cbv beta_flag '($rev $var))
                                 [((pattern:(fun _ => ?C)),
                                   (fun matches
                                    => let c := Ident.find @C matches in
                                       c))] in
                      mkAbs t f)
                (fun _
                 => Control.lazymatch0
                      e
                      [
                        (reify_lambda_pattern
                           base_type_code
                           var
                           reify_rec_with
                           ctx
                           (fun () => debug_reify_abs_case "fun")
                           "reify_abs"
                           (fun t rt c => mkAbs rt c))
                        ;
                        ((pattern:(?x)),
                         (fun matches
                          => let x := Ident.find @x matches in
                             debug_reify_abs_case "return";
                               let xv := reifyf_term x in
                               mkReturn xv))
          ])) in
    match ret with
    | Val ret => let ((ret, cont)) := ret in
                 debug_leave_reify_abs_success e ret;
                   ret
    | Err exn => debug_leave_reify_abs_failure e exn;
                  Control.zero exn
    end.

Ltac2 reify_abs base_type_code interp_base_type op var e :=
  reify_abs_aux base_type_code interp_base_type op var [] e.

Ltac2 reify_abs_goal () :=
  let g := Control.goal () in
  Control.lazymatch0
    g
    [
      ((pattern:(reify_abs (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)),
       (fun matches
        => let base_type_code := Ident.find @base_type_code matches in
           let interp_base_type := Ident.find @interp_base_type matches in
           let op := Ident.find @op matches in
           let var := Ident.find @var matches in
           let e := Ident.find @e matches in
           debug_enter_reify_rec ();
             let e := reify_abs base_type_code interp_base_type op var e in
             debug_leave_reify_rec e;
               Notations.exact0 false (fun () => e)))
    ].

Hint Extern 0 (reify_abs (@exprf ?base_type_code ?interp_base_type ?op ?var) ?e)
=> (ltac2:(reify_abs_goal ()))
   : typeclass_instances.

Ltac reify_abs base_type_code interp_base_type op var e :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op, var, e)%core in
  let ret := constr:(ltac2:(Control.lazymatch0
                              (Ltac1.get_ltac1_result ())
                              [((pattern:((?base_type_code, ?interp_base_type, ?op, ?var, ?e)%core)),
                                (fun matches
                                 => let base_type_code := Ident.find @base_type_code matches in
                                    let interp_base_type := Ident.find @interp_base_type matches in
                                    let op := Ident.find @op matches in
                                    let var := Ident.find @var matches in
                                    let e := Ident.find @e matches in
                                    let v := reify_abs base_type_code interp_base_type op var e in
                                    Control.refine (fun () => v)))])) in
  let dummy := Ltac1.clear_ltac1_results () in
  eval cbv beta zeta in ret.

Ltac2 _Reify' base_type_code interp_base_type op e :=
  '(fun (var : flat_type $base_type_code -> Type)
    => ltac2:(let ret := reify_abs base_type_code interp_base_type op &var e in
              Control.refine (fun () => ret))).
Ltac Reify' base_type_code interp_base_type op e :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op, e)%core in
  let ret := constr:(ltac2:(Control.lazymatch0
                              (Ltac1.get_ltac1_result ())
                              [((pattern:((?base_type_code, ?interp_base_type, ?op, ?e)%core)),
                                (fun matches
                                 => let base_type_code := Ident.find @base_type_code matches in
                                    let interp_base_type := Ident.find @interp_base_type matches in
                                    let op := Ident.find @op matches in
                                    let e := Ident.find @e matches in
                                    let v := _Reify' base_type_code interp_base_type op e in
                                    Control.refine (fun () => v)))])) in
  let dummy := Ltac1.clear_ltac1_results () in
  eval cbv beta zeta in ret.
Ltac2 _Reify base_type_code interp_base_type op make_const e :=
  let r := _Reify' base_type_code interp_base_type op e in
  let r :=
      Control.lazymatch0
        (Constr.type r)
        [
          ((pattern:(forall var, exprf _ _ _ _)),
           (fun matches
            => '(fun var => Abs (src:=Unit) (fun _ => $r var))))
          ;
          ((pattern:(_)),
           (fun _
            => r))
        ] in
  '(@InputSyntax.Compile $base_type_code $interp_base_type $op $make_const _ $r).
Ltac Reify base_type_code interp_base_type op make_const e :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op, make_const, e)%core in
  let ret :=
      constr:(ltac2:(Control.lazymatch0
                       (Ltac1.get_ltac1_result ())
                       [((pattern:((?base_type_code, ?interp_base_type, ?op, ?make_const, ?e)%core)),
                         (fun matches
                          => let base_type_code := Ident.find @base_type_code matches in
                             let interp_base_type := Ident.find @interp_base_type matches in
                             let op := Ident.find @op matches in
                             let make_const := Ident.find @make_const matches in
                             let e := Ident.find @e matches in
                             let v := _Reify base_type_code interp_base_type op make_const e in
                             Control.refine (fun () => v)))])) in
  let dummy := Ltac1.clear_ltac1_results () in
  eval cbv beta zeta in ret.

Ltac rhs_of_goal :=
  lazymatch goal with
  | [ |- ?R ?LHS ?RHS ] => RHS
  | [ |- forall x, ?R (@?LHS x) (@?RHS x) ] => RHS
  end.

Ltac transitivity_tt term :=
  first [ transitivity term
        | transitivity (term tt)
        | let x := fresh in intro x; transitivity (term x); revert x  ].

Ltac Reify_rhs_gen Reify prove_interp_compile_correct interp_op try_tac :=
  let rhs := rhs_of_goal in
  let RHS := Reify rhs in
  let RHS' := (eval vm_compute in RHS) in
  transitivity_tt (Syntax.Interp interp_op RHS');
  [
  | transitivity_tt (Syntax.Interp interp_op RHS);
    [ lazymatch goal with
      | [ |- ?R ?x ?y ]
        => cut (x = y)
      | [ |- forall k, ?R (?x k) (?y k) ]
        => cut (x = y)
      end;
      [ let H := fresh in
        intro H; rewrite H; reflexivity
      | apply f_equal; vm_compute; reflexivity ]
    | intros; etransitivity; (* first we strip off the [InputSyntax.Compile]
                                bit; Coq is bad at inferring the type, so we
                                help it out by providing it *)
      [ cbv [InputSyntax.compilet];
        prove_interp_compile_correct ()
      | try_tac
          ltac:(fun _
                => (* now we unfold the interpretation function,
                      including the parameterized bits; we assume that
                      [hnf] is enough to unfold the interpretation
                      functions that we're parameterized over. *)
                  clear;
                  abstract (
                      lazymatch goal with
                      | [ |- context[@InputSyntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op ?t ?e] ]
                        => let interp_base_type' := (eval hnf in interp_base_type) in
                           let interp_op' := (eval hnf in interp_op) in
                           change interp_base_type with interp_base_type';
                           change interp_op with interp_op'
                      end;
                      subst_let;
                      cbv iota beta delta [InputSyntax.Interp interp_type interp_type_gen interp_type_gen_hetero interp_flat_type interp interpf InputSyntax.Fst InputSyntax.Snd]; reflexivity)) ] ] ].

Ltac prove_compile_correct_using tac :=
  fun _ => intros;
           lazymatch goal with
           | [ |- @Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op _ (@Compile _ _ _ ?make_const (InputSyntax.Arrow ?src (Tflat ?dst)) ?e) ?x = _ ]
             => apply (fun pf => @InputSyntax.Compile_correct base_type_code interp_base_type op make_const interp_op pf src dst e x);
                solve [ tac () ]
           | [ |- @Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op _ (@Compile _ _ _ ?make_const (Tflat ?T) ?e) ?x = _ ]
             => apply (fun pf => @InputSyntax.Compile_flat_correct_flat base_type_code interp_base_type op make_const interp_op pf T e x);
                solve [ tac () ]
           end.
Ltac prove_compile_correct :=
  prove_compile_correct_using
    ltac:(fun _ => let T := fresh in intro T; destruct T; reflexivity).

Ltac Reify_rhs base_type_code interp_base_type op make_const interp_op :=
  Reify_rhs_gen
    ltac:(Reify base_type_code interp_base_type op make_const)
           prove_compile_correct
           interp_op
           ltac:(fun tac => tac ()).

(** TODO: Figure out a better way to do this *)
Module Import WithNotations.
    Import Ltac2.Notations.
    Ltac2 cbv_beta_in_value_of (h : ident) :=
      cbv beta in (value of $h).
End WithNotations.

(** Reification of context variables of the form [F := _ :
    Syntax.interp_type _ _] *)
Ltac2 unique_reify_context_variable
      (base_type_code : constr)
      (interp_base_type : constr)
      (op : constr)
      (f : ident)
      (fbody : constr)
      (rT : constr)
  :=
    let reify_pretag := '(@exprf $base_type_code $interp_base_type $op) in
    let found :=
        Control.case
          (fun ()
           => Control.match_hyps1
                (pattern:(forall var x not_x, reify _ (?F x)))
                (fun _ matches
                 => let f' := Ident.find @F matches in
                    match Constr.equal (Control.hyp f) f' with
                    | true => ()
                    | false => Control.zero Match_failure
                    end)) in
    match found with
    | Val _ => Control.zero (Tactic_failure None)
    | Err _
      => let free_list := Fresh.Free.of_ids (List.map (fun ((id, _, _)) => id) (Control.hyps ())) in
         let h' := Fresh.fresh free_list @H' in
         let free_list := Fresh.Free.union free_list (Fresh.Free.of_ids [h']) in
         let src := Control.lazymatch0
                      rT
                      [((pattern:(Syntax.Arrow ?src ?dst)),
                        (fun matches
                         => Ident.find @src matches))] in
         let var' := Fresh.fresh (Fresh.Free.of_constr fbody) @var' in
         let srcT := Constr.type src in
         let xT_rF :=
             Control.in_context
               var' '($srcT -> Type)
               (fun ()
                => Control.lazymatch0
                     fbody
                     [reify_lambda_pattern
                        base_type_code
                        (&var')
                        (fun ctx e
                         => reifyf_aux base_type_code interp_base_type op &var' ctx e)
                        []
                        (fun () => ())
                        "unique_reify_context_variable"
                        (fun t rt c => '(($t, $c)%core))]) in
         let ((xT, rF)) :=
             Control.lazymatch0
               xT_rF
               [((pattern:(fun var' => (?t, @?c var')%core)),
                 (fun matches
                  => let xT := Ident.find @t matches in
                     let rF := Ident.find @c matches in
                     (xT, rF)))] in
         let fc := Control.hyp f in
         let free_list := Fresh.Free.union free_list (Fresh.Free.of_ids [@var; @x; @not_x]) in
         let f' := Fresh.fresh free_list f in
         let free_list := Fresh.Free.union free_list (Fresh.Free.of_ids [f']) in
         Std.pose (Some f') rF;
         let f'c := Control.hyp f' in
           Std.pose
             (Some h')
             '((match $f'c with myF' => (fun var (x : $xT) => myF' var) end) : match $fc with myF => forall var (x : $xT) (not_x : var $src), reify ($reify_pretag var) (myF x) end);
           cbv_beta_in_value_of h'
    end.
Ltac2 prereify_context_variables interp_base_type :=
  (** N.B. this assumes that [interp_base_type] is a transparent
      definition; minor reorganization may be needed if this is
      changed (moving the burden of reifying [interp_base_type T] to
      [reify_base_type], rather than keeping it here) *)
  (*cbv beta iota delta [$interp_base_type] in *.*)
  let cl := Some { Std.on_hyps := None; Std.on_concl := Std.AllOccurrences } in
  Std.cbv (beta_iota_delta_flag [reference_of_constr interp_base_type]) (Notations.default_on_concl cl).
Ltac2 reify_context_variable base_type_code interp_base_type op :=
  (** [match reverse] so that we respect the chain of dependencies in
      context variables; otherwise we're going to be trying the last
      context variable many times, and bottlenecking there. *)
  Control.match_reverse_hyps1_with_body
    (pattern:(?Fbody))
    (pattern:(Syntax.interp_type _ ?rT))
    (fun f matches
     => let fbody := Ident.find @Fbody matches in
        let rT := Ident.find @rT matches in
        unique_reify_context_variable base_type_code interp_base_type op f fbody rT).
Ltac2 lazy_reify_context_variable base_type_code interp_base_type op :=
  Control.lazymatch_reverse_hyps1_with_body
    (pattern:(?Fbody))
    (pattern:(Syntax.interp_type _ ?rT))
    (fun f matches
     => let fbody := Ident.find @Fbody matches in
        let rT := Ident.find @rT matches in
        unique_reify_context_variable base_type_code interp_base_type op f fbody rT).
Ltac2 reify_context_variables
      (base_type_code : constr)
      (interp_base_type : constr)
      (op : constr) :=
  prereify_context_variables interp_base_type;
  Notations.repeat0 (fun () => reify_context_variable base_type_code interp_base_type op).
Ltac prereify_context_variables interp_base_type :=
  let dummy := Ltac1.save_ltac1_result interp_base_type in
  ltac2:(Control.lazymatch0
           (Ltac1.get_ltac1_result ())
           [((pattern:(?interp_base_type)),
             (fun matches
              => let interp_base_type := Ident.find @interp_base_type matches in
                 prereify_context_variables interp_base_type))]).
Ltac reify_context_variable base_type_code interp_base_type op :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op)%core in
  ltac2:(Control.lazymatch0
           (Ltac1.get_ltac1_result ())
           [((pattern:((?base_type_code, ?interp_base_type, ?op)%core)),
             (fun matches
              => let base_type_code := Ident.find @base_type_code matches in
                 let interp_base_type := Ident.find @interp_base_type matches in
                 let op := Ident.find @op matches in
                 reify_context_variable base_type_code interp_base_type op))]).
Ltac lazy_reify_context_variable base_type_code interp_base_type op :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op)%core in
  ltac2:(Control.lazymatch0
           (Ltac1.get_ltac1_result ())
           [((pattern:((?base_type_code, ?interp_base_type, ?op)%core)),
             (fun matches
              => let base_type_code := Ident.find @base_type_code matches in
                 let interp_base_type := Ident.find @interp_base_type matches in
                 let op := Ident.find @op matches in
                 lazy_reify_context_variable base_type_code interp_base_type op))]).
Ltac reify_context_variables base_type_code interp_base_type op :=
  let dummy := Ltac1.save_ltac1_result (base_type_code, interp_base_type, op)%core in
  ltac2:(Control.lazymatch0
           (Ltac1.get_ltac1_result ())
           [((pattern:((?base_type_code, ?interp_base_type, ?op)%core)),
             (fun matches
              => let base_type_code := Ident.find @base_type_code matches in
                 let interp_base_type := Ident.find @interp_base_type matches in
                 let op := Ident.find @op matches in
                 reify_context_variables base_type_code interp_base_type op))]).

Global Set Default Proof Mode "Classic".
Global Set Ltac2 Backtrace.
