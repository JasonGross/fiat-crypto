Require Ltac2.Ltac2.
Import Ltac2.Init.

Module List.
  Ltac2 rec length ls :=
    match ls with
    | [] => 0
    | _ :: xs => Int.add 1 (length xs)
    end.
  Ltac2 rec fold_right f a ls :=
    match ls with
    | [] => a
    | l :: ls => f l (fold_right f a ls)
    end.
  Ltac2 rec fold_left (f : 'a -> 'b -> 'a) (xs : 'b list) (a : 'a) :=
    match xs with
    | [] => a
    | x :: xs => fold_left f xs (f a x)
    end.
  Ltac2 rec map f ls :=
    match ls with
    | [] => []
    | l :: ls => f l :: map f ls
    end.
  Ltac2 rec iter f ls :=
    match ls with
    | [] => ()
    | l :: ls => f l; iter f ls
    end.
  Ltac2 rec seq (start : int) (step : int) (last : int) :=
    match Int.equal (Int.compare (Int.sub last start) step) -1 with
    | true
      => []
    | false
      => start :: seq (Int.add start step) step last
    end.
  Ltac2 rec zip (ls1 : 'a list) (ls2 : 'b list) :=
    match ls1 with
    | [] => []
    | x :: xs
      => match ls2 with
         | y :: ys
           => (x, y) :: zip xs ys
         | [] => []
         end
    end.
  Ltac2 enumerate (ls : 'a list) :=
    zip (seq 0 1 (List.length ls)) ls.
  Ltac2 rec find f xs :=
    match xs with
    | [] => None
    | x :: xs => match f x with
                 | true => Some x
                 | false => find f xs
                 end
    end.
  Ltac2 rec find_rev f xs :=
    match xs with
    | [] => None
    | x :: xs => match find_rev f xs with
                 | Some v => Some v
                 | None => match f x with
                           | true => Some x
                           | false => None
                           end
                 end
    end.
  Ltac2 rec rev_append l l' :=
    match l with
    | [] => l'
    | x :: xs => rev_append xs (x :: l')
    end.
  Ltac2 rev ls := rev_append ls [].
  Ltac2 rec all f ls :=
    match ls with
    | [] => true
    | x :: xs => match f x with
                 | true => all f xs
                 | false => false
                 end
    end.
  Ltac2 rec app ls1 ls2 :=
    match ls1 with
    | [] => ls2
    | x :: xs => x :: app xs ls2
    end.
  Ltac2 rec any f ls :=
    match ls with
    | [] => false
    | x :: xs => match f x with
                 | true => true
                 | false => any f xs
                 end
    end.
End List.
Module String.
  Ltac2 rec copy_gen (from : string) (to : string) (start_from : int) (start_to : int) (len : int) :=
    match Int.equal (Int.compare len 0) 1 with
    | true => String.set to start_to (String.get from start_from);
                copy_gen from to (Int.add start_from 1) (Int.add start_to 1) (Int.sub len 1)
    | false => ()
    end.
  Ltac2 copy (from : string) (to : string) (start : int) :=
    copy_gen from to 0 start (String.length from).
  Ltac2 concat (s1 : string) (s2 : string) :=
    let ret := String.make (Int.add (String.length s1) (String.length s2))
                           (String.get " " 0) in
    copy s1 ret 0;
      copy s2 ret (String.length s1);
      ret.
  Ltac2 of_char_list (ls : char list) :=
    let ret := String.make (List.length ls) (String.get " " 0) in
    List.iter
      (fun ((i, c))
       => String.set ret i c)
      (List.enumerate ls);
      ret.
End String.
Module Option.
  Ltac2 equal (eqb : 'a -> 'b -> bool) (x : 'a option) (y : 'b option)
    := match x with
       | None
         => match y with
            | None => true
            | Some _ => false
            end
       | Some x
         => match y with
            | None => false
            | Some y => eqb x y
            end
       end.
End Option.
Module Int.
  Ltac2 to_char (n : int) :=
    String.get "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" n.
  Ltac2 rec div_mod (n : int) (d : int) :=
    let n_cmp_d := Int.compare n d in
    let n_eq_d := Int.equal n_cmp_d 0 in
    let n_lt_d := Int.equal n_cmp_d -1 in
    match n_eq_d with
    | true => (1, 0)
    | false
      => match n_lt_d with
         | true => (0, n)
         | false
           => let ((q, r)) := div_mod (Int.sub n d) d in
               (Int.add q 1, r)
         end
    end.
  Ltac2 div n d := let ((q, r)) := div_mod n d in q.
  Ltac2 mod n d := let ((q, r)) := div_mod n d in r.
  Ltac2 rec mul_pos (x : int) (y : int) :=
    match Int.equal x 0 with
    | true => 0
    | false
      => Int.add y (mul_pos (Int.sub x 1) y)
    end.
  Ltac2 rec mul (x : int) (y : int) :=
    match Int.equal (Int.compare x 0) -1 with
    | true
      => Int.sub 0 (mul_pos (Int.sub 0 x) y)
    | false => mul_pos x y
    end.
  Ltac2 rec to_char_list_gen_aux (base : int) (n : int) (so_far : char list) :=
    match Int.equal n 0 with
    | true => so_far
    | false
      => let ((q, r)) := div_mod n base in
         to_char_list_gen_aux base q (to_char r :: so_far)
    end.
  Ltac2 to_char_list_gen (base : int) (n : int) :=
    match Int.equal n 0 with
    | true => [to_char 0]
    | false
      => match Int.equal (Int.compare n 0) -1 with
         | true
           => String.get "-" 0 :: to_char_list_gen_aux base (Int.sub 0 n) []
         | false
           => to_char_list_gen_aux base n []
         end
    end.
  Ltac2 to_string_gen (base : int) (n : int) :=
    String.of_char_list (to_char_list_gen base n).
  Ltac2 to_string (n : int) := to_string_gen 10 n.
End Int.
Module Array.
  Ltac2 rec to_list_aux (ls : 'a array) (start : int) :=
    match Int.equal (Int.compare start (Array.length ls)) -1 with
    | true => Array.get ls start :: to_list_aux ls (Int.add start 1)
    | false => []
    end.
  Ltac2 to_list (ls : 'a array) := to_list_aux ls 0.
End Array.
Module Message.
  Ltac2 join sep ms :=
    match ms with
    | [] => Message.of_string ""
    | m :: ms
      => List.fold_left (fun a b => Message.concat a (Message.concat sep b))
                        ms
                        m
    end.
  Ltac2 print sep ms :=
    match sep with
    | Some sep
      => Message.print (Message.join sep ms)
    | None => Message.print (Message.join (Message.of_string "") ms)
    end.
  Ltac2 of_list_gen (oneline : bool) (of_a : 'a -> message) (ls : 'a list) :=
    let nl := match oneline with
              | true => Message.of_string ""
              | false => Message.of_string "\n"
              end in
    Message.join
      nl
      ((Message.of_string "[")
         :: (Message.join (Message.concat (Message.of_string "; ") nl)
                          (List.map of_a ls))
         :: (Message.of_string "]")
         :: []).
  Ltac2 of_pair (of_a : 'a -> message) (of_b : 'b -> message) (x : 'a * 'b) :=
    let ((a, b)) := x in
    Message.join
      (Message.of_string "")
      [Message.of_string "(";
         of_a a;
         Message.of_string ", ";
         of_b b;
         Message.of_string ")"].
  Ltac2 of_list (of_a : 'a -> message) (ls : 'a list) :=
    of_list_gen true of_a ls.
  Ltac2 of_long_list (of_a : 'a -> message) (ls : 'a list) :=
    of_list_gen false of_a ls.
  Ltac2 of_array (of_a : 'a -> message) (ls : 'a array) :=
    of_list of_a (Array.to_list ls).
  Ltac2 of_long_array (of_a : 'a -> message) (ls : 'a array) :=
    of_long_list of_a (Array.to_list ls).
End Message.
Module Ident.
  Ltac2 rec find_error id xs :=
    match xs with
    | [] => None
    | x :: xs
      => let ((id', val)) := x in
         match Ident.equal id id' with
         | true => Some val
         | false => find_error id xs
         end
    end.
  Ltac2 find id xs :=
    match find_error id xs with
    | None => Control.zero Not_found
    | Some val => val
    end.
End Ident.
Module Constr.
  Ltac2 rec strip_casts term :=
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Cast term' _ _ => strip_casts term'
    | _ => term
    end.
  Module Unsafe.
    Ltac2 beta1 (c : constr) :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.App f args
        => match Constr.Unsafe.kind f with
           | Constr.Unsafe.Lambda id ty f
             => Constr.Unsafe.substnl (Array.to_list args) 0 f
           | _ => c
           end
      | _ => c
      end.
    Ltac2 zeta1 (c : constr) :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.LetIn id v ty f
        => Constr.Unsafe.substnl [v] 0 f
      | _ => c
      end.
  End Unsafe.
End Constr.
Module Control.
  Ltac2 Type match_options := { multi : bool ; lazy : bool ; reverse : bool }.
  Ltac2 update_reverse (opts : match_options) (new_val : bool) :=
    { multi := opts.(multi) ; lazy := opts.(lazy) ; reverse := new_val }.
  Ltac2 update_multi (opts : match_options) (new_val : bool) :=
    { multi := new_val ; lazy := opts.(lazy) ; reverse := opts.(reverse) }.
  Ltac2 update_lazy (opts : match_options) (new_val : bool) :=
    { multi := opts.(multi) ; lazy := new_val ; reverse := opts.(reverse) }.
  Ltac2 rec multimatch_list_aux (f : 'a -> 'b) (ls : 'a list) (e : exn) :=
    match ls with
    | [] => Control.zero e
    | x :: xs => Control.plus
                   (fun () => f x)
                   (fun e' =>
                      match e' with
                      | Match_failure => multimatch_list_aux f xs e
                      | _ => multimatch_list_aux f xs e'
                      end)
    end.
  Ltac2 multimatch_list (f : 'a -> 'b) (ls : 'a list) :=
    multimatch_list_aux f ls Match_failure.
  Ltac2 match_list_gen (opts : match_options) (f : 'a -> 'b) (ls : 'a list) :=
    let maybe_once := match opts.(multi) with
                      | false => Control.once
                      | true => fun f => f ()
                      end in
    let ls := match opts.(reverse) with
              | true => List.rev ls
              | false => ls
              end in
    maybe_once (fun () => multimatch_list f ls).
  Ltac2 match_list f ls :=
    Control.once (fun () => multimatch_list f ls).
  Ltac2 match0_gen opts constr_val branches :=
    match opts.(lazy) with
    | true
      => Control.match_list_gen
           opts
           (fun v
            => let ((pat, tac)) := v in
               let matches := Pattern.matches pat constr_val in
               fun () => tac matches)
           branches
           ()
    | false
      => Control.match_list_gen
           opts
           (fun v
            => let ((pat, tac)) := v in
               let matches := Pattern.matches pat constr_val in
               tac matches)
           branches
    end.
  Ltac2 match_goal_gen
        (opts : match_options)
        (branches : ((((ident * constr option * constr) list) * constr -> 'a) list))
    :=
      let ctx := match opts.(reverse) with
                 | true => Control.hyps ()
                 | false => List.rev (Control.hyps ())
                 end in
      let gl := Control.goal () in
      let opts := update_reverse opts false in
      Control.match_list_gen
        opts
        (fun f => f (ctx, gl))
        branches.
  Ltac2 match0 constr_val branches :=
    match0_gen { multi := false ; lazy := false ; reverse := false } constr_val branches.
  Ltac2 lazymatch0 constr_val branches :=
    match0_gen { multi := false ; lazy := true ; reverse := false } constr_val branches.
  Ltac2 multimatch0 constr_val branches :=
    match0_gen { multi := true ; lazy := false ; reverse := false } constr_val branches.

  Ltac2 app_nonlinear_bindings existing_bindings new_bindings :=
    match List.all
            (fun b
             => let ((id, body)) := b in
                match Ident.find_error id existing_bindings with
                | None => true
                | Some body' => Constr.equal body body'
                end)
            new_bindings with
    | true => List.app existing_bindings new_bindings
    | false => Control.zero Match_failure
    end.
  Ltac2 rec enforce_distinct_hyps (ls : (ident option * ident) list) :=
    match ls with
    | [] => ()
    | x :: xs
      => let ((id, idh)) := x in
         match List.any
                 (fun ((id', idh'))
                  => match Ident.equal idh idh' with
                     | true => true
                     | false
                       => match id with
                          | None => false
                          | Some id
                            => match id' with
                               | None => false
                               | Some id' => Ident.equal id id'
                               end
                          end
                     end)
                 xs
         with
         | true => Control.zero Match_failure
         | false => enforce_distinct_hyps xs
         end
    end.

  Ltac2 Type PatternType := [ NormalPattern | ContextPattern (ident option) ].

  Ltac2 pattern_gen_matches (pat : PatternType * pattern) (v : constr) :=
    let ((pat_ty, pat)) := pat in
    match pat_ty with
    | NormalPattern
      => (None, Pattern.matches pat v)
    | ContextPattern id
      => let ((ctx, bindings)) := Pattern.matches_subterm pat v in
         (Some (id, ctx), bindings)
    end.

  Ltac2 match_goal0_gen_aux
        (opts : match_options)
        (branches : (((ident option * (PatternType * pattern) option * (PatternType * pattern)) list) *
                     (PatternType * pattern) *
                     ((((ident option * Pattern.context) option) list (* body ctx *)) *
                      (((ident option * Pattern.context) option) list (* type ctx *)) *
                      ((ident option * Pattern.context) option (* goal ctx *)) *
                      ((ident option * ident) list (* hyp name bindings *)) *
                      ((ident * constr) list (* bindings *))
                      -> 'a))
                      list)
    :=
      let opts_no_rev := update_reverse opts false in
      let opts_no_rev_multi := update_multi opts_no_rev true in
      match_goal_gen
        opts
        (List.map
           (fun ((hyp_pats, gl_pat, tac)) ((hyps, gl))
            => let ((gl_ctx, gl_bindings)) := pattern_gen_matches gl_pat gl in
               let hyp_matches :=
                   List.map
                     (fun ((id, body_pat, ty_pat))
                      => Control.match_list_gen
                           opts_no_rev_multi
                           (fun ((idh, body, ty))
                            => let ((body_ctx, body_bindings)) :=
                                   match body_pat with
                                   | None => (None, [])
                                   | Some body_pat
                                     => match body with
                                        | None => Control.zero Match_failure
                                        | Some body
                                          => pattern_gen_matches body_pat body
                                        end
                                   end in
                               let ((ty_ctx, ty_bindings)) :=
                                   pattern_gen_matches ty_pat ty in
                               ((id, idh), body_ctx, ty_ctx,
                                app_nonlinear_bindings body_bindings ty_bindings))
                           hyps)
                     hyp_pats in
               let ((id_idh, body_ctxs, ty_ctxs, bindings)) :=
                   List.fold_right
                     (fun ((id_idh', body_ctx', ty_ctx', bindings'))
                          ((id_idh, body_ctxs, ty_ctxs, bindings))
                      => ((id_idh' :: id_idh),
                          (body_ctx' :: body_ctxs),
                          (ty_ctx' :: ty_ctxs),
                          app_nonlinear_bindings bindings' bindings))
                     ([], [], [], [])
                     hyp_matches in
               enforce_distinct_hyps id_idh;
                 let bindings := app_nonlinear_bindings bindings gl_bindings in
                 tac (body_ctxs, ty_ctxs, gl_ctx, id_idh, bindings))
           branches).

  Ltac2 match_goal0_gen opts branches :=
    let opts_no_lazy := update_lazy opts false in
    match opts.(lazy) with
    | false
      => match_goal0_gen_aux opts_no_lazy branches
    | true
      => match_goal0_gen_aux
           opts_no_lazy
           (List.map
              (fun ((hyps, gl, tac))
               => (hyps, gl, (fun args () => tac args)))
              branches)
           ()
    end.
  Ltac2 match_goal0 branches :=
    match_goal0_gen { multi := false ; lazy := false ; reverse := false } branches.
  Ltac2 lazymatch_goal0 branches :=
    match_goal0_gen { multi := false ; lazy := true ; reverse := false } branches.
  Ltac2 match_hyps1_gen lazy ty_pattern tac :=
    match_goal0_gen
      { multi := false ; lazy := lazy ; reverse := false }
      [([(None, None, (NormalPattern, ty_pattern))],
        (NormalPattern, pattern:(_)),
        (fun ((body_ctx, ty_ctx, gl_ctx, hyp_names, bindings))
         => match hyp_names with
            | [] => Control.zero Match_failure
            | h :: _
              => let ((_, hyp)) := h in
                 tac hyp bindings
            end))].
  Ltac2 match_hyps1 ty_pattern tac :=
    match_hyps1_gen false ty_pattern tac.
  Ltac2 lazymatch_hyps1 ty_pattern tac :=
    match_hyps1_gen true ty_pattern tac.
  Ltac2 match_hyps1_with_body_gen lazy body_pattern ty_pattern tac :=
    match_goal0_gen
      { multi := false ; lazy := lazy ; reverse := false }
      [([(None, Some (NormalPattern, body_pattern), (NormalPattern, ty_pattern))],
        (NormalPattern, pattern:(_)),
        (fun ((body_ctx, ty_ctx, gl_ctx, hyp_names, bindings))
         => match hyp_names with
            | [] => Control.zero Match_failure
            | h :: _
              => let ((_, hyp)) := h in
                 tac hyp bindings
            end))].
  Ltac2 match_hyps1_with_body body_pattern ty_pattern tac :=
    match_hyps1_with_body_gen false body_pattern ty_pattern tac.
  Ltac2 lazymatch_hyps1_with_body body_pattern ty_pattern tac :=
    match_hyps1_with_body_gen true body_pattern ty_pattern tac.
  Ltac2 match_reverse_hyps1_with_body_gen lazy body_pattern ty_pattern tac :=
    match_goal0_gen
      { multi := false ; lazy := lazy ; reverse := true }
      [([(None, Some (NormalPattern, body_pattern), (NormalPattern, ty_pattern))],
        (NormalPattern, pattern:(_)),
        (fun ((body_ctx, ty_ctx, gl_ctx, hyp_names, bindings))
         => match hyp_names with
            | [] => Control.zero Match_failure
            | h :: _
              => let ((_, hyp)) := h in
                 tac hyp bindings
            end))].
  Ltac2 match_reverse_hyps1_with_body body_pattern ty_pattern tac :=
    match_reverse_hyps1_with_body_gen false body_pattern ty_pattern tac.
  Ltac2 lazymatch_reverse_hyps1_with_body body_pattern ty_pattern tac :=
    match_reverse_hyps1_with_body_gen true body_pattern ty_pattern tac.
  Ltac2 match_hyps_ty_gen lazy ty_tac_ls :=
    match_goal0_gen
      { multi := false ; lazy := lazy ; reverse := false }
      (List.map
         (fun ((ty_pattern, tac))
          => ([(None, None, (NormalPattern, ty_pattern))],
              (NormalPattern, pattern:(_)),
              (fun ((body_ctx, ty_ctx, gl_ctx, hyp_names, bindings))
               => match hyp_names with
                  | [] => Control.zero Match_failure
                  | h :: _
                    => let ((_, hyp)) := h in
                       tac hyp bindings
                  end)))
         ty_tac_ls).
  Ltac2 match_hyps_ty ty_pattern_tac_ls :=
    match_hyps_ty_gen false ty_pattern_tac_ls.
  Ltac2 lazymatch_hyps_ty ty_pattern_tac_ls :=
    match_hyps_ty_gen true ty_pattern_tac_ls.

  Ltac2 rename_if_exists id :=
    let hyps := List.map (fun ((id, _, _)) => id) (Control.hyps ()) in
    let id' := Fresh.fresh (Fresh.Free.of_ids (id :: hyps)) id in
    match List.any (Ident.equal id) hyps with
    | true => Std.rename [id, id']
    | false => ()
    end.
  Ltac2 rename_last id :=
    rename_if_exists id;
    let rec aux l := match l with
                     | [] => Control.throw (Tactic_failure None)
                     | p :: l =>
                       match l with
                       | [] =>
                         let ((n, _, _)) := p in
                         Std.rename [n, id]
                       | _ => aux l
                       end
                     end in
    aux (Control.hyps ()).

  Import Ltac2.Notations.
  Ltac2 in_context_aux id t refine_c :=
    '(ltac2:(Control.refine (fun _ => '(fun __PRIVATE_HOPEFULLY_UNUSED_NAME_FOR_IN_CONTEXT => _)) >
             [exact $t| |rename_last id; refine_c ()])).
  Ltac2 clean_in_context id v :=
    let beta_flag :=
        {
          Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
          Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
        } in
    let v := Std.eval_cbv beta_flag v in
    match Constr.Unsafe.kind v with
    | Constr.Unsafe.Lambda _ ty f
      => let id := Fresh.fresh (Fresh.Free.of_constr f) id in
         Constr.Unsafe.make (Constr.Unsafe.Lambda (Some id) ty f)
    | _ => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "in_context_aux: ") (Message.of_constr v))))
    end.
  Ltac2 in_context id t c :=
    clean_in_context
      id
      (in_context_aux id t (fun ()
                            => let c := c () in
                               Control.refine (fun () => c))).
End Control.

Module Ltac1.
  Class Ltac1Result {T} (v : T) := {}.
  Class Ltac1Results {T} (v : list T) := {}.
  Class Ltac2Result {T} (v : T) := {}.
  Ltac save_ltac1_result v :=
    match goal with
    | _ => assert (Ltac1Result v) by constructor
    end.
  Ltac clear_ltac1_results _ :=
    match goal with
    | _ => repeat match goal with
                  | [ H : Ltac1Result _ |- _ ] => clear H
                  end
    end.
  Ltac2 get_ltac1_result () :=
    Control.lazymatch_hyps1
      (pattern:(Ltac1Result ?v))
      (fun id matches
       => let val := Ident.find @v matches in
          Std.clear [id];
            val).
  Ltac save_ltac1_results v :=
    match goal with
    | _ => assert (Ltac1Result v) by constructor
    end.
  Ltac2 rec list_of_constr_list (ls : constr) :=
    Control.lazymatch0
      ls
      [((pattern:((?x :: ?xs)%list)),
        (fun matches
         => let x := Ident.find @x matches in
            let xs := Ident.find @xs matches in
            x :: list_of_constr_list xs))
       ;
       ((pattern:(_)),
        (fun _ => ls :: []))].
  Ltac2 get_ltac1_results () :=
    Control.lazymatch_hyps1
      (pattern:(Ltac1Results ?v))
      (fun id matches
       => let val := Ident.find @v matches in
          Std.clear [id];
            list_of_constr_list val).
  Ltac2 save_ltac2_result v :=
    Std.cut '(Ltac2Result $v);
      Control.dispatch
        [(fun ()
          => Std.intros false [Std.IntroNaming (Std.IntroFresh @res)])
         ;
         (fun () => Notations.constructor)].
  Ltac get_ltac2_result _ :=
    lazymatch goal with
    | [ res : Ltac2Result ?v |- _ ]
      => let dummy := match goal with
                      | _ => clear res
                      end in
         v
    end.
  Ltac2 from_ltac1 (save_args : constr) (tac : unit -> unit) :=
    let beta_flag :=
        {
          Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
          Std.rZeta := false; Std.rDelta := false; Std.rConst := [];
        } in
    let c := '(ltac2:(save_ltac2_result save_args;
                        tac ();
                        let v := get_ltac1_result () in
                        Control.refine (fun () => v))) in
    Constr.Unsafe.zeta1 (Constr.Unsafe.zeta1 (Std.eval_cbv beta_flag c)).
End Ltac1.
