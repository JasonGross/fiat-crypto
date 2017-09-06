Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Util.Tactics.Ltac2.
Import Ltac2.Init.
Import Ltac2.Notations.

Ltac2 cbv_all_flags :=
  {
    Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
    Std.rZeta := true; Std.rDelta := true; Std.rConst := [];
  }.
Ltac2 cbv_beta_zeta_flags :=
  {
    Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := true; Std.rDelta := false; Std.rConst := [];
  }.

Ltac2 rec renamify_matches_aux (base_name : string) (count : int) (idx : int) (input : constr) :=
  let make_new_name_ret () :=
      let name := String.concat base_name (Int.to_string count) in
      match Ident.of_string name with
      | None => Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "renamify: Invalid identifier: ") (Message.of_string name))))
      | Some id
        => (Some id, Int.add count 1, input)
      end in
  match Constr.Unsafe.kind input with
  | Constr.Unsafe.Case cse return_clause discriminee branches
    => let is_eq := match Constr.Unsafe.kind discriminee with
                    | Constr.Unsafe.Rel idx'
                      => Int.equal idx idx'
                    | _ => false
                    end in
       match Int.equal (Array.length branches) 1 with
       | true
         => let branch := Array.get branches 0 in
            match Constr.Unsafe.kind branch with
            | Constr.Unsafe.Lambda id1 ty1 f
              => match Constr.Unsafe.kind f with
                 | Constr.Unsafe.Lambda id2 ty2 body
                   => let ((id1, id2, body, id, count)) :=
                          match is_eq with
                          | true
                            => let ((id1, count, body)) := renamify_matches_aux base_name count 2 body in
                               let ((id2, count, body)) := renamify_matches_aux base_name count 1 body in
                               (id1, id2, body, None, count)
                          | false
                            => let ((id, count, body)) := renamify_matches_aux base_name count (Int.add idx 2) body in
                               (id1, id2, body, id, count)
                          end in
                      let branch :=
                          Constr.Unsafe.make
                            (Constr.Unsafe.Lambda
                               id1 ty1
                               (Constr.Unsafe.make
                                  (Constr.Unsafe.Lambda id2 ty2 body))) in
                      Array.set branches 0 branch;
                        (id, count, Constr.Unsafe.make (Constr.Unsafe.Case cse return_clause discriminee branches))
                 | _ => make_new_name_ret ()
                 end
            | _ => make_new_name_ret ()
            end
       | false
         => make_new_name_ret ()
       end
  | _ => make_new_name_ret ()
  end.
Ltac2 renamify_matches (base_name : string) (input : constr) :=
  let ((_, _, v)) := renamify_matches_aux base_name 0 1 input in
  v.

Ltac2 renamify (base_name : string) (input : constr) :=
  let t := Std.eval_cbv cbv_all_flags (Constr.type input) in
  match Constr.Unsafe.kind (Constr.strip_casts t) with
  | Constr.Unsafe.Prod id a b
    => let ret :=
           '(fun var : $a
             => ltac2:(let input := '($input &var) in
                       let input := Std.eval_cbv cbv_all_flags input in
                       (lazy_match! input with
                       | @Abs ?base_type_code ?op ?var ?src ?dst ?input
                         =>let abs := '(@Abs $base_type_code $op $var $src $dst) in
                           let arg := match Ident.of_string base_name with
                                      | Some id => id
                                      | None => Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "renamify: Invalid base_name for identifiers: ") (Message.of_string base_name))))
                                      end in
                           let argT := Std.eval_cbv cbv_all_flags '(interp_flat_type $var $src) in
                           let inputT := Std.eval_cbv cbv_all_flags '(interp_flat_type $var $src -> interp_flat_type $var $dst) in
                           let f := Constr.Unsafe.make
                                      (Constr.Unsafe.Lambda
                                         (Some arg)
                                         argT
                                         (Constr.Unsafe.make
                                            (Constr.Unsafe.App
                                               input
                                               (Array.make
                                                  1
                                                  (Constr.Unsafe.make
                                                     (Constr.Unsafe.Rel 1)))))) in
                           let f := Std.eval_cbv cbv_all_flags f in
                           let f := match Constr.Unsafe.kind f with
                                    | Constr.Unsafe.Lambda id ty f
                                      => Constr.Unsafe.make
                                           (Constr.Unsafe.Lambda
                                              id
                                              ty
                                              (renamify_matches base_name f))
                                    | _
                                      => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Internal error in renamify: Not a lambda ") (Message.of_constr f))))
                                    end in
                           let ret := '($abs $f) in
                           Control.refine (fun () => ret)
                        end))) in
       let ret := Std.eval_cbv cbv_beta_zeta_flags '($ret : $t) in
       ret
  | _ => Control.zero (Tactic_failure (Some (Message.concat (Message.of_string "renamify: Not a product type ") (Message.of_constr t))))
  end.

Ltac renamify f :=
  let dummy :=
      match goal with
      | _ => Ltac1.save_ltac1_result f;
             ltac2:(let f := Ltac1.get_ltac1_result () in
                    let v := renamify "arg" f in
                    Ltac1.save_ltac2_result v)
      end in
  let v := Ltac1.get_ltac2_result () in
  v.

Notation renamify f :=
  (let t := _ in
   let renamify_F0 : t := f in
   ((fun renamify_F : t => ltac2:(let v := renamify "arg" &renamify_F in Control.refine (fun () => v)))
      renamify_F0))
    (only parsing).

Global Set Default Proof Mode "Classic".
