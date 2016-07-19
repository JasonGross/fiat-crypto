Require Import Crypto.Util.Notations Coq.ZArith.BinInt.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.Util.LetIn.
Local Infix "<<" := Z.shiftr.
Local Infix "&" := Z.land.

Print Ltac change_let_in_with_Let_In.
Definition optfst {A B} := Eval compute in @fst A B.
Definition optsnd {A B} := Eval compute in @snd A B.
Class cidtac {T0 T1 T2} (msg0 : T0) (msg1 : T1) (msg2 : T2) := dummy : True.
Hint Extern 0 (cidtac ?msg0 ?msg1 ?msg2) => idtac "<infomsg>" msg0 msg1 msg2 "</infomsg>"; exact I : typeclass_instances.
Class is_var {T} (x : T) := dummy' : True.
Hint Extern 0 (is_var ?x) => is_var x; exact I : typeclass_instances.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Class is_local_context_var {T} (x : T) := dummy'' : True.
Hint Extern 0 (is_local_context_var ?x)
=> is_var x; match goal with x' : _ |- _ => constr_eq x x' end; exact I : typeclass_instances.
Class from_let_in_to_Let_In_and_remove_pairs {FT T} (fuel : FT) (x : T) := make_from_let_in_to_Let_In_and_remove_pairs : T.
Ltac from_let_in_to_Let_In_and_remove_pairs fuel term :=
  lazymatch fuel with
  | 0 => term
  | _ =>
    let fuel' := match fuel with
                 | S ?f => f
                 | _ => fuel
                 end in
    lazymatch (eval cbv beta in term) with
    | context G[let x := ?y in @?z x]
      => let G' := context G [Let_In y z] in
         from_let_in_to_Let_In_and_remove_pairs fuel' G'
    | context G[match ?y with pair a b => @?f a b end]
      => lazymatch eval hnf in y with
         | pair _ _
           => let G' := context G [Let_In (optfst y) (fun a => Let_In (optsnd y) (fun b => f a b))] in
              from_let_in_to_Let_In_and_remove_pairs fuel' G'
         | _
           => let dummy := match y with
                           | prod_rect _ _ ?y' => constr:(_ : is_local_context_var y')
                           | _ => constr:(_ : is_local_context_var y)
                           | _ => constr:(_ : cidtac "Warning: Term does not reduce to a pair:" y "")
                           end in
              let T := match type of f with _ -> _ -> ?T => T end in
              let G' := context G [prod_rect (fun _ => T) f y] in
              from_let_in_to_Let_In_and_remove_pairs fuel' G'
         end
    | ?f ?x
      => let f' := from_let_in_to_Let_In_and_remove_pairs fuel' f in
         let x' := from_let_in_to_Let_In_and_remove_pairs fuel' x in
         constr:(f' x')
    | fun x : ?T => @?f x
      => let ret := constr:(fun x : T => (_ : from_let_in_to_Let_In_and_remove_pairs fuel' (f x))) in
         let ret := (eval cbv beta delta [from_let_in_to_Let_In_and_remove_pairs] in ret) in
         ret
    | ?term'
      => term'
    end
  end.
Hint Extern 0 (from_let_in_to_Let_In_and_remove_pairs ?fuel ?x)
=> let ret := from_let_in_to_Let_In_and_remove_pairs fuel x in exact ret : typeclass_instances.

Ltac do_from_let_in_to_Let_In_and_remove_pairs'' fuel G tac :=
  let G' := from_let_in_to_Let_In_and_remove_pairs fuel G in
  tac G'.

Ltac do_from_let_in_to_Let_In_and_remove_pairs' fuel tac :=
  let G := match goal with |- ?G => G end in
  do_from_let_in_to_Let_In_and_remove_pairs'' fuel G tac.

Ltac do_from_let_in_to_Let_In_and_remove_pairs :=
  do_from_let_in_to_Let_In_and_remove_pairs' true ltac:(fun G => change G);
  cbv [optfst optsnd].

Ltac is_var_or_tuple term :=
  match term with
  | pair ?x ?y => is_var_or_tuple x; is_var_or_tuple y
  | _ => is_var term
  end.
Class is_var_or_tuple {T} (x : T) := dummyivot : True.
Hint Extern 0 (is_var_or_tuple ?x) => is_var_or_tuple x; exact I : typeclass_instances.

Class prune_lets {FT T} (fuel : FT) (x : T) := make_prune_lets : T.
Ltac prune_lets fuel term :=
  lazymatch fuel with
  | 0 => term
  | _ =>
    let fuel' := match fuel with
                 | S ?f => f
                 | _ => fuel
                 end in
    match (eval cbv beta iota in term) with
    | context G[Let_In ?x ?f]
      => let test := constr:(_ : is_var_or_tuple x) in
         let G' := context G[f x] in
         prune_lets fuel' G'
    | context G[prod_rect ?P ?f (pair ?x ?y)]
      => let prod_rect' := constr:(prod_rect P) in
         let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
         let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
         prune_lets fuel' G'
    | context G[Let_In (pair ?x ?y) ?f]
      => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
         prune_lets fuel' G'
    | context G[Let_In (Let_In ?x ?f) ?g]
      => let G' := context G[Let_In x (fun x' => Let_In (f x') g)] in
         prune_lets fuel' G'
    | context G[prod_rect ?P ?g (Let_In ?x ?f)]
      => let G' := context G[Let_In x (fun x' => prod_rect P g (f x'))] in
         prune_lets fuel' G'
    | ?f ?x
      => let f' := prune_lets fuel' f in
         let x' := prune_lets fuel' x in
         constr:(f' x')
    | fun x : ?T => @?f x
      => let ret := constr:(fun x : T => (_ : prune_lets fuel' (f x))) in
         let ret := (eval cbv beta delta [prune_lets] in ret) in
         ret
    | ?term' => term'
    end
  end.
Hint Extern 0 (prune_lets ?fuel ?x)
=> let ret := prune_lets fuel x in exact ret : typeclass_instances.

Ltac do_prune_lets'' fuel G tac :=
  let G' := prune_lets fuel G in
  tac G'.

Ltac do_prune_lets' fuel tac :=
  let G := match goal with |- ?G => G end in
  do_prune_lets'' fuel G tac.

Ltac do_prune_lets := do_prune_lets' true ltac:(fun G => change G).

Ltac do_change'' fuel1 fuel2 G tac
  := do_from_let_in_to_Let_In_and_remove_pairs''
       fuel1 G
       ltac:(fun G => let G' := (eval cbv [optfst optsnd] in G) in
                      do_prune_lets'' fuel2 G' tac).

Ltac do_change' fuel1 fuel2 tac :=
  let G := match goal with |- ?G => G end in
  do_change'' fuel1 fuel2 G tac.

Ltac do_change :=
  do_change' true true ltac:(fun G => change G).

Section Curve25519.
  Definition ge25519_add' (twice_d : fe25519) :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub ModularBaseSystemOpt.Let_In] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.

  Definition ge25519_add_sig (twice_d : fe25519) : forall P1 P2, { r | r = ge25519_add' twice_d P1 P2 }.
    intros.
    hnf in twice_d.
    repeat match goal with p:prod _ _ |- _ => destruct p end.
    eexists.
    etransitivity.
    Focus 2. {
      cbv beta delta [ge25519_add'].
      Notation "'Let' x := y 'in' f" := (Let_In y (fun x => f)) (format "'[' 'Let'  x  :=  y  'in' ']' '/' '[' f ']'", at level 200, f at level 200).
      Notation "'plet' ( x , y ) := v 'in' f" := (prod_rect _ (fun x y => f) v) (format "'[' 'plet'  ( x ,  y )  :=  v  'in' ']' '/' '[' f ']'", at level 200, f at level 200).
      Set Printing Depth 100000.
      Time do_change' true true ltac:(fun G => pose G as P). (* 356.112 secs *)
      Time change P; subst P. (* 28.678 secs *)
(* 1 focused subgoal
(unfocused: 1-0-1, shelved: 2), subgoal 1 (ID 22553)

  z87, z88, z86, z85, z84, z83, z82, z81, z80, z79, z77, z78, z76, z75, z74, z73, z72, z71, z70, z69,
  z67, z68, z66, z65, z64, z63, z62, z61, z60, z59, z57, z58, z56, z55, z54, z53, z52, z51, z50, z49,
  z47, z48, z46, z45, z44, z43, z42, z41, z40, z39, z37, z38, z36, z35, z34, z33, z32, z31, z30, z29,
  z27, z28, z26, z25, z24, z23, z22, z21, z20, z19, z17, z18, z16, z15, z14, z13, z12, z11, z10, z9,
  z7, z8, z6, z5, z4, z3, z2, z1, z0, z : Z
  ============================
  ?y =
  (Let x' := (67108862 + z67 - z77)%Z in
   Let x'0 := (134217726 + z68 - z78)%Z in
   Let x'1 := (67108862 + z66 - z76)%Z in
   Let x'2 := (134217726 + z65 - z75)%Z in
   Let x'3 := (67108862 + z64 - z74)%Z in
   Let x'4 := (134217726 + z63 - z73)%Z in
   Let x'5 := (67108862 + z62 - z72)%Z in
   Let x'6 := (134217726 + z61 - z71)%Z in
   Let x'7 := (67108862 + z60 - z70)%Z in
   Let x'8 := (134217690 + z59 - z69)%Z in
   Let x'9 := (67108862 + z27 - z37)%Z in
   Let x'10 := (134217726 + z28 - z38)%Z in
   Let x'11 := (67108862 + z26 - z36)%Z in
   Let x'12 := (134217726 + z25 - z35)%Z in
   Let x'13 := (67108862 + z24 - z34)%Z in
   Let x'14 := (134217726 + z23 - z33)%Z in
   Let x'15 := (67108862 + z22 - z32)%Z in
   Let x'16 := (134217726 + z21 - z31)%Z in
   Let x'17 := (67108862 + z20 - z30)%Z in
   Let x'18 := (134217690 + z19 - z29)%Z in
   Let x'19 := (x'8 * x'18 +
                19 *
                (x' * (x'17 * 2) +
                 (x'0 * x'16 +
                  (x'1 * (x'15 * 2) +
                   (x'2 * x'14 +
                    (x'3 * (x'13 * 2) +
                     (x'4 * x'12 + (x'5 * (x'11 * 2) + (x'6 * x'10 + x'7 * (x'9 * 2))))))))))%Z in
   Let x'20 := (x'19 << 26 +
                (x'7 * x'18 + x'8 * x'17 +
                 19 *
                 (x' * x'16 +
                  (x'0 * x'15 +
                   (x'1 * x'14 +
                    (x'2 * x'13 + (x'3 * x'12 + (x'4 * x'11 + (x'5 * x'10 + x'6 * x'9)))))))))%Z in
   Let x'21 := (x'20 << 25 +
                (x'6 * x'18 + (x'7 * (x'17 * 2) + x'8 * x'16) +
                 19 *
                 (x' * (x'15 * 2) +
                  (x'0 * x'14 +
                   (x'1 * (x'13 * 2) +
                    (x'2 * x'12 + (x'3 * (x'11 * 2) + (x'4 * x'10 + x'5 * (x'9 * 2)))))))))%Z in
   Let x'22 := (x'21 << 26 +
                (x'5 * x'18 + (x'6 * x'17 + (x'7 * x'16 + x'8 * x'15)) +
                 19 *
                 (x' * x'14 + (x'0 * x'13 + (x'1 * x'12 + (x'2 * x'11 + (x'3 * x'10 + x'4 * x'9)))))))%Z in
   Let x'23 := (x'22 << 25 +
                (x'4 * x'18 + (x'5 * (x'17 * 2) + (x'6 * x'16 + (x'7 * (x'15 * 2) + x'8 * x'14))) +
                 19 *
                 (x' * (x'13 * 2) +
                  (x'0 * x'12 + (x'1 * (x'11 * 2) + (x'2 * x'10 + x'3 * (x'9 * 2)))))))%Z in
   Let x'24 := (x'23 << 26 +
                (x'3 * x'18 + (x'4 * x'17 + (x'5 * x'16 + (x'6 * x'15 + (x'7 * x'14 + x'8 * x'13)))) +
                 19 * (x' * x'12 + (x'0 * x'11 + (x'1 * x'10 + x'2 * x'9)))))%Z in
   Let x'25 := (x'24 << 25 +
                (x'2 * x'18 +
                 (x'3 * (x'17 * 2) +
                  (x'4 * x'16 + (x'5 * (x'15 * 2) + (x'6 * x'14 + (x'7 * (x'13 * 2) + x'8 * x'12))))) +
                 19 * (x' * (x'11 * 2) + (x'0 * x'10 + x'1 * (x'9 * 2)))))%Z in
   Let x'26 := (x'25 << 26 +
                (x'1 * x'18 +
                 (x'2 * x'17 +
                  (x'3 * x'16 +
                   (x'4 * x'15 + (x'5 * x'14 + (x'6 * x'13 + (x'7 * x'12 + x'8 * x'11)))))) +
                 19 * (x' * x'10 + x'0 * x'9)))%Z in
   Let x'27 := (x'26 << 25 +
                (x'0 * x'18 +
                 (x'1 * (x'17 * 2) +
                  (x'2 * x'16 +
                   (x'3 * (x'15 * 2) +
                    (x'4 * x'14 + (x'5 * (x'13 * 2) + (x'6 * x'12 + (x'7 * (x'11 * 2) + x'8 * x'10))))))) +
                 19 * (x' * (x'9 * 2))))%Z in
   Let x'28 := (x'27 << 26 +
                (x' * x'18 +
                 (x'0 * x'17 +
                  (x'1 * x'16 +
                   (x'2 * x'15 +
                    (x'3 * x'14 +
                     (x'4 * x'13 + (x'5 * x'12 + (x'6 * x'11 + (x'7 * x'10 + x'8 * x'9))))))))))%Z in
   Let x'29 := x'28 & (33554432 + -1) in
   Let y' := x'27 & (67108864 + -1) in
   Let y'0 := x'26 & (33554432 + -1) in
   Let y'1 := x'25 & (67108864 + -1) in
   Let y'2 := x'24 & (33554432 + -1) in
   Let y'3 := x'23 & (67108864 + -1) in
   Let y'4 := x'22 & (33554432 + -1) in
   Let y'5 := x'21 & (67108864 + -1) in
   Let y'6 := x'20 & (33554432 + -1) in
   Let y'7 := (19 * x'28 << 25 + (x'19 & (67108864 + -1)))%Z in
   Let x'30 := (z67 + z77)%Z in
   Let x'31 := (z68 + z78)%Z in
   Let x'32 := (z66 + z76)%Z in
   Let x'33 := (z65 + z75)%Z in
   Let x'34 := (z64 + z74)%Z in
   Let x'35 := (z63 + z73)%Z in
   Let x'36 := (z62 + z72)%Z in
   Let x'37 := (z61 + z71)%Z in
   Let x'38 := (z60 + z70)%Z in
   Let x'39 := (z59 + z69)%Z in
   Let x'40 := (z27 + z37)%Z in
   Let x'41 := (z28 + z38)%Z in
   Let x'42 := (z26 + z36)%Z in
   Let x'43 := (z25 + z35)%Z in
   Let x'44 := (z24 + z34)%Z in
   Let x'45 := (z23 + z33)%Z in
   Let x'46 := (z22 + z32)%Z in
   Let x'47 := (z21 + z31)%Z in
   Let x'48 := (z20 + z30)%Z in
   Let x'49 := (z19 + z29)%Z in
   Let x'50 := (x'39 * x'49 +
                19 *
                (x'30 * (x'48 * 2) +
                 (x'31 * x'47 +
                  (x'32 * (x'46 * 2) +
                   (x'33 * x'45 +
                    (x'34 * (x'44 * 2) +
                     (x'35 * x'43 + (x'36 * (x'42 * 2) + (x'37 * x'41 + x'38 * (x'40 * 2))))))))))%Z in
   Let x'51 := (x'50 << 26 +
                (x'38 * x'49 + x'39 * x'48 +
                 19 *
                 (x'30 * x'47 +
                  (x'31 * x'46 +
                   (x'32 * x'45 +
                    (x'33 * x'44 + (x'34 * x'43 + (x'35 * x'42 + (x'36 * x'41 + x'37 * x'40)))))))))%Z in
   Let x'52 := (x'51 << 25 +
                (x'37 * x'49 + (x'38 * (x'48 * 2) + x'39 * x'47) +
                 19 *
                 (x'30 * (x'46 * 2) +
                  (x'31 * x'45 +
                   (x'32 * (x'44 * 2) +
                    (x'33 * x'43 + (x'34 * (x'42 * 2) + (x'35 * x'41 + x'36 * (x'40 * 2)))))))))%Z in
   Let x'53 := (x'52 << 26 +
                (x'36 * x'49 + (x'37 * x'48 + (x'38 * x'47 + x'39 * x'46)) +
                 19 *
                 (x'30 * x'45 +
                  (x'31 * x'44 + (x'32 * x'43 + (x'33 * x'42 + (x'34 * x'41 + x'35 * x'40)))))))%Z in
   Let x'54 := (x'53 << 25 +
                (x'35 * x'49 +
                 (x'36 * (x'48 * 2) + (x'37 * x'47 + (x'38 * (x'46 * 2) + x'39 * x'45))) +
                 19 *
                 (x'30 * (x'44 * 2) +
                  (x'31 * x'43 + (x'32 * (x'42 * 2) + (x'33 * x'41 + x'34 * (x'40 * 2)))))))%Z in
   Let x'55 := (x'54 << 26 +
                (x'34 * x'49 +
                 (x'35 * x'48 + (x'36 * x'47 + (x'37 * x'46 + (x'38 * x'45 + x'39 * x'44)))) +
                 19 * (x'30 * x'43 + (x'31 * x'42 + (x'32 * x'41 + x'33 * x'40)))))%Z in
   Let x'56 := (x'55 << 25 +
                (x'33 * x'49 +
                 (x'34 * (x'48 * 2) +
                  (x'35 * x'47 +
                   (x'36 * (x'46 * 2) + (x'37 * x'45 + (x'38 * (x'44 * 2) + x'39 * x'43))))) +
                 19 * (x'30 * (x'42 * 2) + (x'31 * x'41 + x'32 * (x'40 * 2)))))%Z in
   Let x'57 := (x'56 << 26 +
                (x'32 * x'49 +
                 (x'33 * x'48 +
                  (x'34 * x'47 +
                   (x'35 * x'46 + (x'36 * x'45 + (x'37 * x'44 + (x'38 * x'43 + x'39 * x'42)))))) +
                 19 * (x'30 * x'41 + x'31 * x'40)))%Z in
   Let x'58 := (x'57 << 25 +
                (x'31 * x'49 +
                 (x'32 * (x'48 * 2) +
                  (x'33 * x'47 +
                   (x'34 * (x'46 * 2) +
                    (x'35 * x'45 +
                     (x'36 * (x'44 * 2) + (x'37 * x'43 + (x'38 * (x'42 * 2) + x'39 * x'41))))))) +
                 19 * (x'30 * (x'40 * 2))))%Z in
   Let x'59 := (x'58 << 26 +
                (x'30 * x'49 +
                 (x'31 * x'48 +
                  (x'32 * x'47 +
                   (x'33 * x'46 +
                    (x'34 * x'45 +
                     (x'35 * x'44 + (x'36 * x'43 + (x'37 * x'42 + (x'38 * x'41 + x'39 * x'40))))))))))%Z in
   Let x'60 := x'59 & (33554432 + -1) in
   Let y'8 := x'58 & (67108864 + -1) in
   Let y'9 := x'57 & (33554432 + -1) in
   Let y'10 := x'56 & (67108864 + -1) in
   Let y'11 := x'55 & (33554432 + -1) in
   Let y'12 := x'54 & (67108864 + -1) in
   Let y'13 := x'53 & (33554432 + -1) in
   Let y'14 := x'52 & (67108864 + -1) in
   Let y'15 := x'51 & (33554432 + -1) in
   Let y'16 := (19 * x'59 << 25 + (x'50 & (67108864 + -1)))%Z in
   Let x'61 := (z39 * z79 +
                19 *
                (z47 * (z80 * 2) +
                 (z48 * z81 +
                  (z46 * (z82 * 2) +
                   (z45 * z83 +
                    (z44 * (z84 * 2) +
                     (z43 * z85 + (z42 * (z86 * 2) + (z41 * z88 + z40 * (z87 * 2))))))))))%Z in
   Let x'62 := (x'61 << 26 +
                (z40 * z79 + z39 * z80 +
                 19 *
                 (z47 * z81 +
                  (z48 * z82 +
                   (z46 * z83 + (z45 * z84 + (z44 * z85 + (z43 * z86 + (z42 * z88 + z41 * z87)))))))))%Z in
   Let x'63 := (x'62 << 25 +
                (z41 * z79 + (z40 * (z80 * 2) + z39 * z81) +
                 19 *
                 (z47 * (z82 * 2) +
                  (z48 * z83 +
                   (z46 * (z84 * 2) + (z45 * z85 + (z44 * (z86 * 2) + (z43 * z88 + z42 * (z87 * 2)))))))))%Z in
   Let x'64 := (x'63 << 26 +
                (z42 * z79 + (z41 * z80 + (z40 * z81 + z39 * z82)) +
                 19 * (z47 * z83 + (z48 * z84 + (z46 * z85 + (z45 * z86 + (z44 * z88 + z43 * z87)))))))%Z in
   Let x'65 := (x'64 << 25 +
                (z43 * z79 + (z42 * (z80 * 2) + (z41 * z81 + (z40 * (z82 * 2) + z39 * z83))) +
                 19 *
                 (z47 * (z84 * 2) + (z48 * z85 + (z46 * (z86 * 2) + (z45 * z88 + z44 * (z87 * 2)))))))%Z in
   Let x'66 := (x'65 << 26 +
                (z44 * z79 + (z43 * z80 + (z42 * z81 + (z41 * z82 + (z40 * z83 + z39 * z84)))) +
                 19 * (z47 * z85 + (z48 * z86 + (z46 * z88 + z45 * z87)))))%Z in
   Let x'67 := (x'66 << 25 +
                (z45 * z79 +
                 (z44 * (z80 * 2) +
                  (z43 * z81 + (z42 * (z82 * 2) + (z41 * z83 + (z40 * (z84 * 2) + z39 * z85))))) +
                 19 * (z47 * (z86 * 2) + (z48 * z88 + z46 * (z87 * 2)))))%Z in
   Let x'68 := (x'67 << 26 +
                (z46 * z79 +
                 (z45 * z80 +
                  (z44 * z81 + (z43 * z82 + (z42 * z83 + (z41 * z84 + (z40 * z85 + z39 * z86)))))) +
                 19 * (z47 * z88 + z48 * z87)))%Z in
   Let x'69 := (x'68 << 25 +
                (z48 * z79 +
                 (z46 * (z80 * 2) +
                  (z45 * z81 +
                   (z44 * (z82 * 2) +
                    (z43 * z83 + (z42 * (z84 * 2) + (z41 * z85 + (z40 * (z86 * 2) + z39 * z88))))))) +
                 19 * (z47 * (z87 * 2))))%Z in
   Let x'70 := (x'69 << 26 +
                (z47 * z79 +
                 (z48 * z80 +
                  (z46 * z81 +
                   (z45 * z82 +
                    (z44 * z83 + (z43 * z84 + (z42 * z85 + (z41 * z86 + (z40 * z88 + z39 * z87))))))))))%Z in
   Let x'71 := x'70 & (33554432 + -1) in
   Let x'72 := x'69 & (67108864 + -1) in
   Let x'73 := x'68 & (33554432 + -1) in
   Let x'74 := x'67 & (67108864 + -1) in
   Let x'75 := x'66 & (33554432 + -1) in
   Let x'76 := x'65 & (67108864 + -1) in
   Let x'77 := x'64 & (33554432 + -1) in
   Let x'78 := x'63 & (67108864 + -1) in
   Let x'79 := x'62 & (33554432 + -1) in
   Let x'80 := (19 * x'70 << 25 + (x'61 & (67108864 + -1)))%Z in
   Let x'81 := (x'80 * z +
                19 *
                (x'71 * (z0 * 2) +
                 (x'72 * z1 +
                  (x'73 * (z2 * 2) +
                   (x'74 * z3 +
                    (x'75 * (z4 * 2) +
                     (x'76 * z5 + (x'77 * (z6 * 2) + (x'78 * z8 + x'79 * (z7 * 2))))))))))%Z in
   Let x'82 := (x'81 << 26 +
                (x'79 * z + x'80 * z0 +
                 19 *
                 (x'71 * z1 +
                  (x'72 * z2 +
                   (x'73 * z3 + (x'74 * z4 + (x'75 * z5 + (x'76 * z6 + (x'77 * z8 + x'78 * z7)))))))))%Z in
   Let x'83 := (x'82 << 25 +
                (x'78 * z + (x'79 * (z0 * 2) + x'80 * z1) +
                 19 *
                 (x'71 * (z2 * 2) +
                  (x'72 * z3 +
                   (x'73 * (z4 * 2) + (x'74 * z5 + (x'75 * (z6 * 2) + (x'76 * z8 + x'77 * (z7 * 2)))))))))%Z in
   Let x'84 := (x'83 << 26 +
                (x'77 * z + (x'78 * z0 + (x'79 * z1 + x'80 * z2)) +
                 19 * (x'71 * z3 + (x'72 * z4 + (x'73 * z5 + (x'74 * z6 + (x'75 * z8 + x'76 * z7)))))))%Z in
   Let x'85 := (x'84 << 25 +
                (x'76 * z + (x'77 * (z0 * 2) + (x'78 * z1 + (x'79 * (z2 * 2) + x'80 * z3))) +
                 19 *
                 (x'71 * (z4 * 2) + (x'72 * z5 + (x'73 * (z6 * 2) + (x'74 * z8 + x'75 * (z7 * 2)))))))%Z in
   Let x'86 := (x'85 << 26 +
                (x'75 * z + (x'76 * z0 + (x'77 * z1 + (x'78 * z2 + (x'79 * z3 + x'80 * z4)))) +
                 19 * (x'71 * z5 + (x'72 * z6 + (x'73 * z8 + x'74 * z7)))))%Z in
   Let x'87 := (x'86 << 25 +
                (x'74 * z +
                 (x'75 * (z0 * 2) +
                  (x'76 * z1 + (x'77 * (z2 * 2) + (x'78 * z3 + (x'79 * (z4 * 2) + x'80 * z5))))) +
                 19 * (x'71 * (z6 * 2) + (x'72 * z8 + x'73 * (z7 * 2)))))%Z in
   Let x'88 := (x'87 << 26 +
                (x'73 * z +
                 (x'74 * z0 +
                  (x'75 * z1 + (x'76 * z2 + (x'77 * z3 + (x'78 * z4 + (x'79 * z5 + x'80 * z6)))))) +
                 19 * (x'71 * z8 + x'72 * z7)))%Z in
   Let x'89 := (x'88 << 25 +
                (x'72 * z +
                 (x'73 * (z0 * 2) +
                  (x'74 * z1 +
                   (x'75 * (z2 * 2) +
                    (x'76 * z3 + (x'77 * (z4 * 2) + (x'78 * z5 + (x'79 * (z6 * 2) + x'80 * z8))))))) +
                 19 * (x'71 * (z7 * 2))))%Z in
   Let x'90 := (x'89 << 26 +
                (x'71 * z +
                 (x'72 * z0 +
                  (x'73 * z1 +
                   (x'74 * z2 +
                    (x'75 * z3 + (x'76 * z4 + (x'77 * z5 + (x'78 * z6 + (x'79 * z8 + x'80 * z7))))))))))%Z in
   Let x'91 := x'90 & (33554432 + -1) in
   Let y'17 := x'89 & (67108864 + -1) in
   Let y'18 := x'88 & (33554432 + -1) in
   Let y'19 := x'87 & (67108864 + -1) in
   Let y'20 := x'86 & (33554432 + -1) in
   Let y'21 := x'85 & (67108864 + -1) in
   Let y'22 := x'84 & (33554432 + -1) in
   Let y'23 := x'83 & (67108864 + -1) in
   Let y'24 := x'82 & (33554432 + -1) in
   Let y'25 := (19 * x'90 << 25 + (x'81 & (67108864 + -1)))%Z in
   Let x'92 := (z17 + z17)%Z in
   Let x'93 := (z18 + z18)%Z in
   Let x'94 := (z16 + z16)%Z in
   Let x'95 := (z15 + z15)%Z in
   Let x'96 := (z14 + z14)%Z in
   Let x'97 := (z13 + z13)%Z in
   Let x'98 := (z12 + z12)%Z in
   Let x'99 := (z11 + z11)%Z in
   Let x'100 := (z10 + z10)%Z in
   Let x'101 := (z9 + z9)%Z in
   Let x'102 := (z49 * x'101 +
                 19 *
                 (z57 * (x'100 * 2) +
                  (z58 * x'99 +
                   (z56 * (x'98 * 2) +
                    (z55 * x'97 +
                     (z54 * (x'96 * 2) +
                      (z53 * x'95 + (z52 * (x'94 * 2) + (z51 * x'93 + z50 * (x'92 * 2))))))))))%Z in
   Let x'103 := (x'102 << 26 +
                 (z50 * x'101 + z49 * x'100 +
                  19 *
                  (z57 * x'99 +
                   (z58 * x'98 +
                    (z56 * x'97 +
                     (z55 * x'96 + (z54 * x'95 + (z53 * x'94 + (z52 * x'93 + z51 * x'92)))))))))%Z in
   Let x'104 := (x'103 << 25 +
                 (z51 * x'101 + (z50 * (x'100 * 2) + z49 * x'99) +
                  19 *
                  (z57 * (x'98 * 2) +
                   (z58 * x'97 +
                    (z56 * (x'96 * 2) +
                     (z55 * x'95 + (z54 * (x'94 * 2) + (z53 * x'93 + z52 * (x'92 * 2)))))))))%Z in
   Let x'105 := (x'104 << 26 +
                 (z52 * x'101 + (z51 * x'100 + (z50 * x'99 + z49 * x'98)) +
                  19 *
                  (z57 * x'97 +
                   (z58 * x'96 + (z56 * x'95 + (z55 * x'94 + (z54 * x'93 + z53 * x'92)))))))%Z in
   Let x'106 := (x'105 << 25 +
                 (z53 * x'101 + (z52 * (x'100 * 2) + (z51 * x'99 + (z50 * (x'98 * 2) + z49 * x'97))) +
                  19 *
                  (z57 * (x'96 * 2) +
                   (z58 * x'95 + (z56 * (x'94 * 2) + (z55 * x'93 + z54 * (x'92 * 2)))))))%Z in
   Let x'107 := (x'106 << 26 +
                 (z54 * x'101 +
                  (z53 * x'100 + (z52 * x'99 + (z51 * x'98 + (z50 * x'97 + z49 * x'96)))) +
                  19 * (z57 * x'95 + (z58 * x'94 + (z56 * x'93 + z55 * x'92)))))%Z in
   Let x'108 := (x'107 << 25 +
                 (z55 * x'101 +
                  (z54 * (x'100 * 2) +
                   (z53 * x'99 + (z52 * (x'98 * 2) + (z51 * x'97 + (z50 * (x'96 * 2) + z49 * x'95))))) +
                  19 * (z57 * (x'94 * 2) + (z58 * x'93 + z56 * (x'92 * 2)))))%Z in
   Let x'109 := (x'108 << 26 +
                 (z56 * x'101 +
                  (z55 * x'100 +
                   (z54 * x'99 +
                    (z53 * x'98 + (z52 * x'97 + (z51 * x'96 + (z50 * x'95 + z49 * x'94)))))) +
                  19 * (z57 * x'93 + z58 * x'92)))%Z in
   Let x'110 := (x'109 << 25 +
                 (z58 * x'101 +
                  (z56 * (x'100 * 2) +
                   (z55 * x'99 +
                    (z54 * (x'98 * 2) +
                     (z53 * x'97 +
                      (z52 * (x'96 * 2) + (z51 * x'95 + (z50 * (x'94 * 2) + z49 * x'93))))))) +
                  19 * (z57 * (x'92 * 2))))%Z in
   Let x'111 := (x'110 << 26 +
                 (z57 * x'101 +
                  (z58 * x'100 +
                   (z56 * x'99 +
                    (z55 * x'98 +
                     (z54 * x'97 +
                      (z53 * x'96 + (z52 * x'95 + (z51 * x'94 + (z50 * x'93 + z49 * x'92))))))))))%Z in
   Let x'112 := x'111 & (33554432 + -1) in
   Let y'26 := x'110 & (67108864 + -1) in
   Let y'27 := x'109 & (33554432 + -1) in
   Let y'28 := x'108 & (67108864 + -1) in
   Let y'29 := x'107 & (33554432 + -1) in
   Let y'30 := x'106 & (67108864 + -1) in
   Let y'31 := x'105 & (33554432 + -1) in
   Let y'32 := x'104 & (67108864 + -1) in
   Let y'33 := x'103 & (33554432 + -1) in
   Let y'34 := (19 * x'111 << 25 + (x'102 & (67108864 + -1)))%Z in
   Let x'113 := (67108862 + x'60 - x'29)%Z in
   Let y'35 := (134217726 + y'8 - y')%Z in
   Let y'36 := (67108862 + y'9 - y'0)%Z in
   Let y'37 := (134217726 + y'10 - y'1)%Z in
   Let y'38 := (67108862 + y'11 - y'2)%Z in
   Let y'39 := (134217726 + y'12 - y'3)%Z in
   Let y'40 := (67108862 + y'13 - y'4)%Z in
   Let y'41 := (134217726 + y'14 - y'5)%Z in
   Let y'42 := (67108862 + y'15 - y'6)%Z in
   Let y'43 := (134217690 + y'16 - y'7)%Z in
   Let x'114 := (67108862 + x'112 - x'91)%Z in
   Let y'44 := (134217726 + y'26 - y'17)%Z in
   Let y'45 := (67108862 + y'27 - y'18)%Z in
   Let y'46 := (134217726 + y'28 - y'19)%Z in
   Let y'47 := (67108862 + y'29 - y'20)%Z in
   Let y'48 := (134217726 + y'30 - y'21)%Z in
   Let y'49 := (67108862 + y'31 - y'22)%Z in
   Let y'50 := (134217726 + y'32 - y'23)%Z in
   Let y'51 := (67108862 + y'33 - y'24)%Z in
   Let y'52 := (134217690 + y'34 - y'25)%Z in
   Let x'115 := (x'112 + x'91)%Z in
   Let y'53 := (y'26 + y'17)%Z in
   Let y'54 := (y'27 + y'18)%Z in
   Let y'55 := (y'28 + y'19)%Z in
   Let y'56 := (y'29 + y'20)%Z in
   Let y'57 := (y'30 + y'21)%Z in
   Let y'58 := (y'31 + y'22)%Z in
   Let y'59 := (y'32 + y'23)%Z in
   Let y'60 := (y'33 + y'24)%Z in
   Let y'61 := (y'34 + y'25)%Z in
   Let x'116 := (x'60 + x'29)%Z in
   Let y'62 := (y'8 + y')%Z in
   Let y'63 := (y'9 + y'0)%Z in
   Let y'64 := (y'10 + y'1)%Z in
   Let y'65 := (y'11 + y'2)%Z in
   Let y'66 := (y'12 + y'3)%Z in
   Let y'67 := (y'13 + y'4)%Z in
   Let y'68 := (y'14 + y'5)%Z in
   Let y'69 := (y'15 + y'6)%Z in
   Let y'70 := (y'16 + y'7)%Z in
   Let x'117 := (y'43 * y'52 +
                 19 *
                 (x'113 * (y'51 * 2) +
                  (y'35 * y'50 +
                   (y'36 * (y'49 * 2) +
                    (y'37 * y'48 +
                     (y'38 * (y'47 * 2) +
                      (y'39 * y'46 + (y'40 * (y'45 * 2) + (y'41 * y'44 + y'42 * (x'114 * 2))))))))))%Z in
   Let x'118 := (x'117 << 26 +
                 (y'42 * y'52 + y'43 * y'51 +
                  19 *
                  (x'113 * y'50 +
                   (y'35 * y'49 +
                    (y'36 * y'48 +
                     (y'37 * y'47 + (y'38 * y'46 + (y'39 * y'45 + (y'40 * y'44 + y'41 * x'114)))))))))%Z in
   Let x'119 := (x'118 << 25 +
                 (y'41 * y'52 + (y'42 * (y'51 * 2) + y'43 * y'50) +
                  19 *
                  (x'113 * (y'49 * 2) +
                   (y'35 * y'48 +
                    (y'36 * (y'47 * 2) +
                     (y'37 * y'46 + (y'38 * (y'45 * 2) + (y'39 * y'44 + y'40 * (x'114 * 2)))))))))%Z in
   Let x'120 := (x'119 << 26 +
                 (y'40 * y'52 + (y'41 * y'51 + (y'42 * y'50 + y'43 * y'49)) +
                  19 *
                  (x'113 * y'48 +
                   (y'35 * y'47 + (y'36 * y'46 + (y'37 * y'45 + (y'38 * y'44 + y'39 * x'114)))))))%Z in
   Let x'121 := (x'120 << 25 +
                 (y'39 * y'52 +
                  (y'40 * (y'51 * 2) + (y'41 * y'50 + (y'42 * (y'49 * 2) + y'43 * y'48))) +
                  19 *
                  (x'113 * (y'47 * 2) +
                   (y'35 * y'46 + (y'36 * (y'45 * 2) + (y'37 * y'44 + y'38 * (x'114 * 2)))))))%Z in
   Let x'122 := (x'121 << 26 +
                 (y'38 * y'52 +
                  (y'39 * y'51 + (y'40 * y'50 + (y'41 * y'49 + (y'42 * y'48 + y'43 * y'47)))) +
                  19 * (x'113 * y'46 + (y'35 * y'45 + (y'36 * y'44 + y'37 * x'114)))))%Z in
   Let x'123 := (x'122 << 25 +
                 (y'37 * y'52 +
                  (y'38 * (y'51 * 2) +
                   (y'39 * y'50 +
                    (y'40 * (y'49 * 2) + (y'41 * y'48 + (y'42 * (y'47 * 2) + y'43 * y'46))))) +
                  19 * (x'113 * (y'45 * 2) + (y'35 * y'44 + y'36 * (x'114 * 2)))))%Z in
   Let x'124 := (x'123 << 26 +
                 (y'36 * y'52 +
                  (y'37 * y'51 +
                   (y'38 * y'50 +
                    (y'39 * y'49 + (y'40 * y'48 + (y'41 * y'47 + (y'42 * y'46 + y'43 * y'45)))))) +
                  19 * (x'113 * y'44 + y'35 * x'114)))%Z in
   Let x'125 := (x'124 << 25 +
                 (y'35 * y'52 +
                  (y'36 * (y'51 * 2) +
                   (y'37 * y'50 +
                    (y'38 * (y'49 * 2) +
                     (y'39 * y'48 +
                      (y'40 * (y'47 * 2) + (y'41 * y'46 + (y'42 * (y'45 * 2) + y'43 * y'44))))))) +
                  19 * (x'113 * (x'114 * 2))))%Z in
   Let x'126 := (x'125 << 26 +
                 (x'113 * y'52 +
                  (y'35 * y'51 +
                   (y'36 * y'50 +
                    (y'37 * y'49 +
                     (y'38 * y'48 +
                      (y'39 * y'47 + (y'40 * y'46 + (y'41 * y'45 + (y'42 * y'44 + y'43 * x'114))))))))))%Z in
   Let x'127 := x'126 & (33554432 + -1) in
   Let y'71 := x'125 & (67108864 + -1) in
   Let y'72 := x'124 & (33554432 + -1) in
   Let y'73 := x'123 & (67108864 + -1) in
   Let y'74 := x'122 & (33554432 + -1) in
   Let y'75 := x'121 & (67108864 + -1) in
   Let y'76 := x'120 & (33554432 + -1) in
   Let y'77 := x'119 & (67108864 + -1) in
   Let y'78 := x'118 & (33554432 + -1) in
   Let y'79 := (19 * x'126 << 25 + (x'117 & (67108864 + -1)))%Z in
   Let x'128 := (y'61 * y'70 +
                 19 *
                 (x'115 * (y'69 * 2) +
                  (y'53 * y'68 +
                   (y'54 * (y'67 * 2) +
                    (y'55 * y'66 +
                     (y'56 * (y'65 * 2) +
                      (y'57 * y'64 + (y'58 * (y'63 * 2) + (y'59 * y'62 + y'60 * (x'116 * 2))))))))))%Z in
   Let x'129 := (x'128 << 26 +
                 (y'60 * y'70 + y'61 * y'69 +
                  19 *
                  (x'115 * y'68 +
                   (y'53 * y'67 +
                    (y'54 * y'66 +
                     (y'55 * y'65 + (y'56 * y'64 + (y'57 * y'63 + (y'58 * y'62 + y'59 * x'116)))))))))%Z in
   Let x'130 := (x'129 << 25 +
                 (y'59 * y'70 + (y'60 * (y'69 * 2) + y'61 * y'68) +
                  19 *
                  (x'115 * (y'67 * 2) +
                   (y'53 * y'66 +
                    (y'54 * (y'65 * 2) +
                     (y'55 * y'64 + (y'56 * (y'63 * 2) + (y'57 * y'62 + y'58 * (x'116 * 2)))))))))%Z in
   Let x'131 := (x'130 << 26 +
                 (y'58 * y'70 + (y'59 * y'69 + (y'60 * y'68 + y'61 * y'67)) +
                  19 *
                  (x'115 * y'66 +
                   (y'53 * y'65 + (y'54 * y'64 + (y'55 * y'63 + (y'56 * y'62 + y'57 * x'116)))))))%Z in
   Let x'132 := (x'131 << 25 +
                 (y'57 * y'70 +
                  (y'58 * (y'69 * 2) + (y'59 * y'68 + (y'60 * (y'67 * 2) + y'61 * y'66))) +
                  19 *
                  (x'115 * (y'65 * 2) +
                   (y'53 * y'64 + (y'54 * (y'63 * 2) + (y'55 * y'62 + y'56 * (x'116 * 2)))))))%Z in
   Let x'133 := (x'132 << 26 +
                 (y'56 * y'70 +
                  (y'57 * y'69 + (y'58 * y'68 + (y'59 * y'67 + (y'60 * y'66 + y'61 * y'65)))) +
                  19 * (x'115 * y'64 + (y'53 * y'63 + (y'54 * y'62 + y'55 * x'116)))))%Z in
   Let x'134 := (x'133 << 25 +
                 (y'55 * y'70 +
                  (y'56 * (y'69 * 2) +
                   (y'57 * y'68 +
                    (y'58 * (y'67 * 2) + (y'59 * y'66 + (y'60 * (y'65 * 2) + y'61 * y'64))))) +
                  19 * (x'115 * (y'63 * 2) + (y'53 * y'62 + y'54 * (x'116 * 2)))))%Z in
   Let x'135 := (x'134 << 26 +
                 (y'54 * y'70 +
                  (y'55 * y'69 +
                   (y'56 * y'68 +
                    (y'57 * y'67 + (y'58 * y'66 + (y'59 * y'65 + (y'60 * y'64 + y'61 * y'63)))))) +
                  19 * (x'115 * y'62 + y'53 * x'116)))%Z in
   Let x'136 := (x'135 << 25 +
                 (y'53 * y'70 +
                  (y'54 * (y'69 * 2) +
                   (y'55 * y'68 +
                    (y'56 * (y'67 * 2) +
                     (y'57 * y'66 +
                      (y'58 * (y'65 * 2) + (y'59 * y'64 + (y'60 * (y'63 * 2) + y'61 * y'62))))))) +
                  19 * (x'115 * (x'116 * 2))))%Z in
   Let x'137 := (x'136 << 26 +
                 (x'115 * y'70 +
                  (y'53 * y'69 +
                   (y'54 * y'68 +
                    (y'55 * y'67 +
                     (y'56 * y'66 +
                      (y'57 * y'65 + (y'58 * y'64 + (y'59 * y'63 + (y'60 * y'62 + y'61 * x'116))))))))))%Z in
   Let x'138 := x'137 & (33554432 + -1) in
   Let y'80 := x'136 & (67108864 + -1) in
   Let y'81 := x'135 & (33554432 + -1) in
   Let y'82 := x'134 & (67108864 + -1) in
   Let y'83 := x'133 & (33554432 + -1) in
   Let y'84 := x'132 & (67108864 + -1) in
   Let y'85 := x'131 & (33554432 + -1) in
   Let y'86 := x'130 & (67108864 + -1) in
   Let y'87 := x'129 & (33554432 + -1) in
   Let y'88 := (19 * x'137 << 25 + (x'128 & (67108864 + -1)))%Z in
   Let x'139 := (y'43 * y'70 +
                 19 *
                 (x'113 * (y'69 * 2) +
                  (y'35 * y'68 +
                   (y'36 * (y'67 * 2) +
                    (y'37 * y'66 +
                     (y'38 * (y'65 * 2) +
                      (y'39 * y'64 + (y'40 * (y'63 * 2) + (y'41 * y'62 + y'42 * (x'116 * 2))))))))))%Z in
   Let x'140 := (x'139 << 26 +
                 (y'42 * y'70 + y'43 * y'69 +
                  19 *
                  (x'113 * y'68 +
                   (y'35 * y'67 +
                    (y'36 * y'66 +
                     (y'37 * y'65 + (y'38 * y'64 + (y'39 * y'63 + (y'40 * y'62 + y'41 * x'116)))))))))%Z in
   Let x'141 := (x'140 << 25 +
                 (y'41 * y'70 + (y'42 * (y'69 * 2) + y'43 * y'68) +
                  19 *
                  (x'113 * (y'67 * 2) +
                   (y'35 * y'66 +
                    (y'36 * (y'65 * 2) +
                     (y'37 * y'64 + (y'38 * (y'63 * 2) + (y'39 * y'62 + y'40 * (x'116 * 2)))))))))%Z in
   Let x'142 := (x'141 << 26 +
                 (y'40 * y'70 + (y'41 * y'69 + (y'42 * y'68 + y'43 * y'67)) +
                  19 *
                  (x'113 * y'66 +
                   (y'35 * y'65 + (y'36 * y'64 + (y'37 * y'63 + (y'38 * y'62 + y'39 * x'116)))))))%Z in
   Let x'143 := (x'142 << 25 +
                 (y'39 * y'70 +
                  (y'40 * (y'69 * 2) + (y'41 * y'68 + (y'42 * (y'67 * 2) + y'43 * y'66))) +
                  19 *
                  (x'113 * (y'65 * 2) +
                   (y'35 * y'64 + (y'36 * (y'63 * 2) + (y'37 * y'62 + y'38 * (x'116 * 2)))))))%Z in
   Let x'144 := (x'143 << 26 +
                 (y'38 * y'70 +
                  (y'39 * y'69 + (y'40 * y'68 + (y'41 * y'67 + (y'42 * y'66 + y'43 * y'65)))) +
                  19 * (x'113 * y'64 + (y'35 * y'63 + (y'36 * y'62 + y'37 * x'116)))))%Z in
   Let x'145 := (x'144 << 25 +
                 (y'37 * y'70 +
                  (y'38 * (y'69 * 2) +
                   (y'39 * y'68 +
                    (y'40 * (y'67 * 2) + (y'41 * y'66 + (y'42 * (y'65 * 2) + y'43 * y'64))))) +
                  19 * (x'113 * (y'63 * 2) + (y'35 * y'62 + y'36 * (x'116 * 2)))))%Z in
   Let x'146 := (x'145 << 26 +
                 (y'36 * y'70 +
                  (y'37 * y'69 +
                   (y'38 * y'68 +
                    (y'39 * y'67 + (y'40 * y'66 + (y'41 * y'65 + (y'42 * y'64 + y'43 * y'63)))))) +
                  19 * (x'113 * y'62 + y'35 * x'116)))%Z in
   Let x'147 := (x'146 << 25 +
                 (y'35 * y'70 +
                  (y'36 * (y'69 * 2) +
                   (y'37 * y'68 +
                    (y'38 * (y'67 * 2) +
                     (y'39 * y'66 +
                      (y'40 * (y'65 * 2) + (y'41 * y'64 + (y'42 * (y'63 * 2) + y'43 * y'62))))))) +
                  19 * (x'113 * (x'116 * 2))))%Z in
   Let x'148 := (x'147 << 26 +
                 (x'113 * y'70 +
                  (y'35 * y'69 +
                   (y'36 * y'68 +
                    (y'37 * y'67 +
                     (y'38 * y'66 +
                      (y'39 * y'65 + (y'40 * y'64 + (y'41 * y'63 + (y'42 * y'62 + y'43 * x'116))))))))))%Z in
   Let x'149 := x'148 & (33554432 + -1) in
   Let y'89 := x'147 & (67108864 + -1) in
   Let y'90 := x'146 & (33554432 + -1) in
   Let y'91 := x'145 & (67108864 + -1) in
   Let y'92 := x'144 & (33554432 + -1) in
   Let y'93 := x'143 & (67108864 + -1) in
   Let y'94 := x'142 & (33554432 + -1) in
   Let y'95 := x'141 & (67108864 + -1) in
   Let y'96 := x'140 & (33554432 + -1) in
   Let y'97 := (19 * x'148 << 25 + (x'139 & (67108864 + -1)))%Z in
   Let x'150 := (y'52 * y'61 +
                 19 *
                 (x'114 * (y'60 * 2) +
                  (y'44 * y'59 +
                   (y'45 * (y'58 * 2) +
                    (y'46 * y'57 +
                     (y'47 * (y'56 * 2) +
                      (y'48 * y'55 + (y'49 * (y'54 * 2) + (y'50 * y'53 + y'51 * (x'115 * 2))))))))))%Z in
   Let x'151 := (x'150 << 26 +
                 (y'51 * y'61 + y'52 * y'60 +
                  19 *
                  (x'114 * y'59 +
                   (y'44 * y'58 +
                    (y'45 * y'57 +
                     (y'46 * y'56 + (y'47 * y'55 + (y'48 * y'54 + (y'49 * y'53 + y'50 * x'115)))))))))%Z in
   Let x'152 := (x'151 << 25 +
                 (y'50 * y'61 + (y'51 * (y'60 * 2) + y'52 * y'59) +
                  19 *
                  (x'114 * (y'58 * 2) +
                   (y'44 * y'57 +
                    (y'45 * (y'56 * 2) +
                     (y'46 * y'55 + (y'47 * (y'54 * 2) + (y'48 * y'53 + y'49 * (x'115 * 2)))))))))%Z in
   Let x'153 := (x'152 << 26 +
                 (y'49 * y'61 + (y'50 * y'60 + (y'51 * y'59 + y'52 * y'58)) +
                  19 *
                  (x'114 * y'57 +
                   (y'44 * y'56 + (y'45 * y'55 + (y'46 * y'54 + (y'47 * y'53 + y'48 * x'115)))))))%Z in
   Let x'154 := (x'153 << 25 +
                 (y'48 * y'61 +
                  (y'49 * (y'60 * 2) + (y'50 * y'59 + (y'51 * (y'58 * 2) + y'52 * y'57))) +
                  19 *
                  (x'114 * (y'56 * 2) +
                   (y'44 * y'55 + (y'45 * (y'54 * 2) + (y'46 * y'53 + y'47 * (x'115 * 2)))))))%Z in
   Let x'155 := (x'154 << 26 +
                 (y'47 * y'61 +
                  (y'48 * y'60 + (y'49 * y'59 + (y'50 * y'58 + (y'51 * y'57 + y'52 * y'56)))) +
                  19 * (x'114 * y'55 + (y'44 * y'54 + (y'45 * y'53 + y'46 * x'115)))))%Z in
   Let x'156 := (x'155 << 25 +
                 (y'46 * y'61 +
                  (y'47 * (y'60 * 2) +
                   (y'48 * y'59 +
                    (y'49 * (y'58 * 2) + (y'50 * y'57 + (y'51 * (y'56 * 2) + y'52 * y'55))))) +
                  19 * (x'114 * (y'54 * 2) + (y'44 * y'53 + y'45 * (x'115 * 2)))))%Z in
   Let x'157 := (x'156 << 26 +
                 (y'45 * y'61 +
                  (y'46 * y'60 +
                   (y'47 * y'59 +
                    (y'48 * y'58 + (y'49 * y'57 + (y'50 * y'56 + (y'51 * y'55 + y'52 * y'54)))))) +
                  19 * (x'114 * y'53 + y'44 * x'115)))%Z in
   Let x'158 := (x'157 << 25 +
                 (y'44 * y'61 +
                  (y'45 * (y'60 * 2) +
                   (y'46 * y'59 +
                    (y'47 * (y'58 * 2) +
                     (y'48 * y'57 +
                      (y'49 * (y'56 * 2) + (y'50 * y'55 + (y'51 * (y'54 * 2) + y'52 * y'53))))))) +
                  19 * (x'114 * (x'115 * 2))))%Z in
   Let x'159 := (x'158 << 26 +
                 (x'114 * y'61 +
                  (y'44 * y'60 +
                   (y'45 * y'59 +
                    (y'46 * y'58 +
                     (y'47 * y'57 +
                      (y'48 * y'56 + (y'49 * y'55 + (y'50 * y'54 + (y'51 * y'53 + y'52 * x'115))))))))))%Z in
   Let x'160 := x'159 & (33554432 + -1) in
   Let y'98 := x'158 & (67108864 + -1) in
   Let y'99 := x'157 & (33554432 + -1) in
   Let y'100 := x'156 & (67108864 + -1) in
   Let y'101 := x'155 & (33554432 + -1) in
   Let y'102 := x'154 & (67108864 + -1) in
   Let y'103 := x'153 & (33554432 + -1) in
   Let y'104 := x'152 & (67108864 + -1) in
   Let y'105 := x'151 & (33554432 + -1) in
   Let y'106 := (19 * x'159 << 25 + (x'150 & (67108864 + -1)))%Z in
   (x'127, y'71, y'72, y'73, y'74, y'75, y'76, y'77, y'78, y'79,
   (x'138, y'80, y'81, y'82, y'83, y'84, y'85, y'86, y'87, y'88),
   (x'160, y'98, y'99, y'100, y'101, y'102, y'103, y'104, y'105, y'106),
   (x'149, y'89, y'90, y'91, y'92, y'93, y'94, y'95, y'96, y'97)))

(dependent evars: (printing disabled) )

*)



      Time change P; subst P.



      (* 1 focused subgoal
(unfocused: 0-1, shelved: 2), subgoal 1 (ID 17112)

  z87, z88, z86, z85, z84, z83, z82, z81, z80, z79, z77, z78, z76, z75, z74, z73, z72, z71, z70, z69,
  z67, z68, z66, z65, z64, z63, z62, z61, z60, z59, z57, z58, z56, z55, z54, z53, z52, z51, z50, z49,
  z47, z48, z46, z45, z44, z43, z42, z41, z40, z39, z37, z38, z36, z35, z34, z33, z32, z31, z30, z29,
  z27, z28, z26, z25, z24, z23, z22, z21, z20, z19, z17, z18, z16, z15, z14, z13, z12, z11, z10, z9,
  z7, z8, z6, z5, z4, z3, z2, z1, z0, z : Z
  ============================
  ?y =
  (Let x' := (67108862 + z67 - z77)%Z in
   Let x'0 := (134217726 + z68 - z78)%Z in
   Let x'1 := (67108862 + z66 - z76)%Z in
   Let x'2 := (134217726 + z65 - z75)%Z in
   Let x'3 := (67108862 + z64 - z74)%Z in
   Let x'4 := (134217726 + z63 - z73)%Z in
   Let x'5 := (67108862 + z62 - z72)%Z in
   Let x'6 := (134217726 + z61 - z71)%Z in
   Let x'7 := (67108862 + z60 - z70)%Z in
   Let x'8 := (134217690 + z59 - z69)%Z in
   Let x'9 := (67108862 + z27 - z37)%Z in
   Let x'10 := (134217726 + z28 - z38)%Z in
   Let x'11 := (67108862 + z26 - z36)%Z in
   Let x'12 := (134217726 + z25 - z35)%Z in
   Let x'13 := (67108862 + z24 - z34)%Z in
   Let x'14 := (134217726 + z23 - z33)%Z in
   Let x'15 := (67108862 + z22 - z32)%Z in
   Let x'16 := (134217726 + z21 - z31)%Z in
   Let x'17 := (67108862 + z20 - z30)%Z in
   Let x'18 := (134217690 + z19 - z29)%Z in
   Let x'19 := (x'8 * x'18 +
                19 *
                (x' * (x'17 * 2) +
                 (x'0 * x'16 +
                  (x'1 * (x'15 * 2) +
                   (x'2 * x'14 +
                    (x'3 * (x'13 * 2) +
                     (x'4 * x'12 + (x'5 * (x'11 * 2) + (x'6 * x'10 + x'7 * (x'9 * 2))))))))))%Z in
   Let x'20 := (x'19 << 26 +
                (x'7 * x'18 + x'8 * x'17 +
                 19 *
                 (x' * x'16 +
                  (x'0 * x'15 +
                   (x'1 * x'14 +
                    (x'2 * x'13 + (x'3 * x'12 + (x'4 * x'11 + (x'5 * x'10 + x'6 * x'9)))))))))%Z in
   Let x'21 := (x'20 << 25 +
                (x'6 * x'18 + (x'7 * (x'17 * 2) + x'8 * x'16) +
                 19 *
                 (x' * (x'15 * 2) +
                  (x'0 * x'14 +
                   (x'1 * (x'13 * 2) +
                    (x'2 * x'12 + (x'3 * (x'11 * 2) + (x'4 * x'10 + x'5 * (x'9 * 2)))))))))%Z in
   Let x'22 := (x'21 << 26 +
                (x'5 * x'18 + (x'6 * x'17 + (x'7 * x'16 + x'8 * x'15)) +
                 19 *
                 (x' * x'14 + (x'0 * x'13 + (x'1 * x'12 + (x'2 * x'11 + (x'3 * x'10 + x'4 * x'9)))))))%Z in
   Let x'23 := (x'22 << 25 +
                (x'4 * x'18 + (x'5 * (x'17 * 2) + (x'6 * x'16 + (x'7 * (x'15 * 2) + x'8 * x'14))) +
                 19 *
                 (x' * (x'13 * 2) +
                  (x'0 * x'12 + (x'1 * (x'11 * 2) + (x'2 * x'10 + x'3 * (x'9 * 2)))))))%Z in
   Let x'24 := (x'23 << 26 +
                (x'3 * x'18 + (x'4 * x'17 + (x'5 * x'16 + (x'6 * x'15 + (x'7 * x'14 + x'8 * x'13)))) +
                 19 * (x' * x'12 + (x'0 * x'11 + (x'1 * x'10 + x'2 * x'9)))))%Z in
   Let x'25 := (x'24 << 25 +
                (x'2 * x'18 +
                 (x'3 * (x'17 * 2) +
                  (x'4 * x'16 + (x'5 * (x'15 * 2) + (x'6 * x'14 + (x'7 * (x'13 * 2) + x'8 * x'12))))) +
                 19 * (x' * (x'11 * 2) + (x'0 * x'10 + x'1 * (x'9 * 2)))))%Z in
   Let x'26 := (x'25 << 26 +
                (x'1 * x'18 +
                 (x'2 * x'17 +
                  (x'3 * x'16 +
                   (x'4 * x'15 + (x'5 * x'14 + (x'6 * x'13 + (x'7 * x'12 + x'8 * x'11)))))) +
                 19 * (x' * x'10 + x'0 * x'9)))%Z in
   Let x'27 := (x'26 << 25 +
                (x'0 * x'18 +
                 (x'1 * (x'17 * 2) +
                  (x'2 * x'16 +
                   (x'3 * (x'15 * 2) +
                    (x'4 * x'14 + (x'5 * (x'13 * 2) + (x'6 * x'12 + (x'7 * (x'11 * 2) + x'8 * x'10))))))) +
                 19 * (x' * (x'9 * 2))))%Z in
   Let x'28 := (x'27 << 26 +
                (x' * x'18 +
                 (x'0 * x'17 +
                  (x'1 * x'16 +
                   (x'2 * x'15 +
                    (x'3 * x'14 +
                     (x'4 * x'13 + (x'5 * x'12 + (x'6 * x'11 + (x'7 * x'10 + x'8 * x'9))))))))))%Z in
   Let x'29 := x'28 & (33554432 + -1) in
   Let y' := x'27 & (67108864 + -1) in
   Let y'0 := x'26 & (33554432 + -1) in
   Let y'1 := x'25 & (67108864 + -1) in
   Let y'2 := x'24 & (33554432 + -1) in
   Let y'3 := x'23 & (67108864 + -1) in
   Let y'4 := x'22 & (33554432 + -1) in
   Let y'5 := x'21 & (67108864 + -1) in
   Let y'6 := x'20 & (33554432 + -1) in
   Let y'7 := (19 * x'28 << 25 + (x'19 & (67108864 + -1)))%Z in
   Let x'30 := (z67 + z77)%Z in
   Let x'31 := (z68 + z78)%Z in
   Let x'32 := (z66 + z76)%Z in
   Let x'33 := (z65 + z75)%Z in
   Let x'34 := (z64 + z74)%Z in
   Let x'35 := (z63 + z73)%Z in
   Let x'36 := (z62 + z72)%Z in
   Let x'37 := (z61 + z71)%Z in
   Let x'38 := (z60 + z70)%Z in
   Let x'39 := (z59 + z69)%Z in
   Let x'40 := (z27 + z37)%Z in
   Let x'41 := (z28 + z38)%Z in
   Let x'42 := (z26 + z36)%Z in
   Let x'43 := (z25 + z35)%Z in
   Let x'44 := (z24 + z34)%Z in
   Let x'45 := (z23 + z33)%Z in
   Let x'46 := (z22 + z32)%Z in
   Let x'47 := (z21 + z31)%Z in
   Let x'48 := (z20 + z30)%Z in
   Let x'49 := (z19 + z29)%Z in
   Let x'50 := (x'39 * x'49 +
                19 *
                (x'30 * (x'48 * 2) +
                 (x'31 * x'47 +
                  (x'32 * (x'46 * 2) +
                   (x'33 * x'45 +
                    (x'34 * (x'44 * 2) +
                     (x'35 * x'43 + (x'36 * (x'42 * 2) + (x'37 * x'41 + x'38 * (x'40 * 2))))))))))%Z in
   Let x'51 := (x'50 << 26 +
                (x'38 * x'49 + x'39 * x'48 +
                 19 *
                 (x'30 * x'47 +
                  (x'31 * x'46 +
                   (x'32 * x'45 +
                    (x'33 * x'44 + (x'34 * x'43 + (x'35 * x'42 + (x'36 * x'41 + x'37 * x'40)))))))))%Z in
   Let x'52 := (x'51 << 25 +
                (x'37 * x'49 + (x'38 * (x'48 * 2) + x'39 * x'47) +
                 19 *
                 (x'30 * (x'46 * 2) +
                  (x'31 * x'45 +
                   (x'32 * (x'44 * 2) +
                    (x'33 * x'43 + (x'34 * (x'42 * 2) + (x'35 * x'41 + x'36 * (x'40 * 2)))))))))%Z in
   Let x'53 := (x'52 << 26 +
                (x'36 * x'49 + (x'37 * x'48 + (x'38 * x'47 + x'39 * x'46)) +
                 19 *
                 (x'30 * x'45 +
                  (x'31 * x'44 + (x'32 * x'43 + (x'33 * x'42 + (x'34 * x'41 + x'35 * x'40)))))))%Z in
   Let x'54 := (x'53 << 25 +
                (x'35 * x'49 +
                 (x'36 * (x'48 * 2) + (x'37 * x'47 + (x'38 * (x'46 * 2) + x'39 * x'45))) +
                 19 *
                 (x'30 * (x'44 * 2) +
                  (x'31 * x'43 + (x'32 * (x'42 * 2) + (x'33 * x'41 + x'34 * (x'40 * 2)))))))%Z in
   Let x'55 := (x'54 << 26 +
                (x'34 * x'49 +
                 (x'35 * x'48 + (x'36 * x'47 + (x'37 * x'46 + (x'38 * x'45 + x'39 * x'44)))) +
                 19 * (x'30 * x'43 + (x'31 * x'42 + (x'32 * x'41 + x'33 * x'40)))))%Z in
   Let x'56 := (x'55 << 25 +
                (x'33 * x'49 +
                 (x'34 * (x'48 * 2) +
                  (x'35 * x'47 +
                   (x'36 * (x'46 * 2) + (x'37 * x'45 + (x'38 * (x'44 * 2) + x'39 * x'43))))) +
                 19 * (x'30 * (x'42 * 2) + (x'31 * x'41 + x'32 * (x'40 * 2)))))%Z in
   Let x'57 := (x'56 << 26 +
                (x'32 * x'49 +
                 (x'33 * x'48 +
                  (x'34 * x'47 +
                   (x'35 * x'46 + (x'36 * x'45 + (x'37 * x'44 + (x'38 * x'43 + x'39 * x'42)))))) +
                 19 * (x'30 * x'41 + x'31 * x'40)))%Z in
   Let x'58 := (x'57 << 25 +
                (x'31 * x'49 +
                 (x'32 * (x'48 * 2) +
                  (x'33 * x'47 +
                   (x'34 * (x'46 * 2) +
                    (x'35 * x'45 +
                     (x'36 * (x'44 * 2) + (x'37 * x'43 + (x'38 * (x'42 * 2) + x'39 * x'41))))))) +
                 19 * (x'30 * (x'40 * 2))))%Z in
   Let x'59 := (x'58 << 26 +
                (x'30 * x'49 +
                 (x'31 * x'48 +
                  (x'32 * x'47 +
                   (x'33 * x'46 +
                    (x'34 * x'45 +
                     (x'35 * x'44 + (x'36 * x'43 + (x'37 * x'42 + (x'38 * x'41 + x'39 * x'40))))))))))%Z in
   Let x'60 := x'59 & (33554432 + -1) in
   Let y'8 := x'58 & (67108864 + -1) in
   Let y'9 := x'57 & (33554432 + -1) in
   Let y'10 := x'56 & (67108864 + -1) in
   Let y'11 := x'55 & (33554432 + -1) in
   Let y'12 := x'54 & (67108864 + -1) in
   Let y'13 := x'53 & (33554432 + -1) in
   Let y'14 := x'52 & (67108864 + -1) in
   Let y'15 := x'51 & (33554432 + -1) in
   Let y'16 := (19 * x'59 << 25 + (x'50 & (67108864 + -1)))%Z in
   Let C := plet (p, f9) := Let y := (z39 * z79 +
                                      19 *
                                      (z47 * (z80 * 2) +
                                       (z48 * z81 +
                                        (z46 * (z82 * 2) +
                                         (z45 * z83 +
                                          (z44 * (z84 * 2) +
                                           (z43 * z85 +
                                            (z42 * (z86 * 2) + (z41 * z88 + z40 * (z87 * 2))))))))))%Z in
            Let y0 := (y << 26 +
                       (z40 * z79 + z39 * z80 +
                        19 *
                        (z47 * z81 +
                         (z48 * z82 +
                          (z46 * z83 +
                           (z45 * z84 + (z44 * z85 + (z43 * z86 + (z42 * z88 + z41 * z87)))))))))%Z in
            Let y1 := (y0 << 25 +
                       (z41 * z79 + (z40 * (z80 * 2) + z39 * z81) +
                        19 *
                        (z47 * (z82 * 2) +
                         (z48 * z83 +
                          (z46 * (z84 * 2) +
                           (z45 * z85 + (z44 * (z86 * 2) + (z43 * z88 + z42 * (z87 * 2)))))))))%Z in
            Let y2 := (y1 << 26 +
                       (z42 * z79 + (z41 * z80 + (z40 * z81 + z39 * z82)) +
                        19 *
                        (z47 * z83 +
                         (z48 * z84 + (z46 * z85 + (z45 * z86 + (z44 * z88 + z43 * z87)))))))%Z in
            Let y3 := (y2 << 25 +
                       (z43 * z79 + (z42 * (z80 * 2) + (z41 * z81 + (z40 * (z82 * 2) + z39 * z83))) +
                        19 *
                        (z47 * (z84 * 2) +
                         (z48 * z85 + (z46 * (z86 * 2) + (z45 * z88 + z44 * (z87 * 2)))))))%Z in
            Let y4 := (y3 << 26 +
                       (z44 * z79 + (z43 * z80 + (z42 * z81 + (z41 * z82 + (z40 * z83 + z39 * z84)))) +
                        19 * (z47 * z85 + (z48 * z86 + (z46 * z88 + z45 * z87)))))%Z in
            Let y5 := (y4 << 25 +
                       (z45 * z79 +
                        (z44 * (z80 * 2) +
                         (z43 * z81 + (z42 * (z82 * 2) + (z41 * z83 + (z40 * (z84 * 2) + z39 * z85))))) +
                        19 * (z47 * (z86 * 2) + (z48 * z88 + z46 * (z87 * 2)))))%Z in
            Let y6 := (y5 << 26 +
                       (z46 * z79 +
                        (z45 * z80 +
                         (z44 * z81 +
                          (z43 * z82 + (z42 * z83 + (z41 * z84 + (z40 * z85 + z39 * z86)))))) +
                        19 * (z47 * z88 + z48 * z87)))%Z in
            Let y7 := (y6 << 25 +
                       (z48 * z79 +
                        (z46 * (z80 * 2) +
                         (z45 * z81 +
                          (z44 * (z82 * 2) +
                           (z43 * z83 +
                            (z42 * (z84 * 2) + (z41 * z85 + (z40 * (z86 * 2) + z39 * z88))))))) +
                        19 * (z47 * (z87 * 2))))%Z in
            Let y8 := (y7 << 26 +
                       (z47 * z79 +
                        (z48 * z80 +
                         (z46 * z81 +
                          (z45 * z82 +
                           (z44 * z83 +
                            (z43 * z84 + (z42 * z85 + (z41 * z86 + (z40 * z88 + z39 * z87))))))))))%Z in
            (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1),
            y5 & (67108864 + -1), y4 & (33554432 + -1), y3 & (67108864 + -1),
            y2 & (33554432 + -1), y1 & (67108864 + -1), y0 & (33554432 + -1),
            (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   plet (p0, f8) := p in
   plet (p1, f7) := p0 in
   plet (p2, f6) := p1 in
   plet (p3, f5) := p2 in
   plet (p4, f4) := p3 in
   plet (p5, f3) := p4 in
   plet (p6, f2) := p5 in
   plet (f0, f1) := p6 in
   Let y := (f9 * z +
             19 *
             (f0 * (z0 * 2) +
              (f1 * z1 +
               (f2 * (z2 * 2) +
                (f3 * z3 + (f4 * (z4 * 2) + (f5 * z5 + (f6 * (z6 * 2) + (f7 * z8 + f8 * (z7 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (f8 * z + f9 * z0 +
               19 *
               (f0 * z1 +
                (f1 * z2 + (f2 * z3 + (f3 * z4 + (f4 * z5 + (f5 * z6 + (f6 * z8 + f7 * z7)))))))))%Z in
   Let y1 := (y0 << 25 +
              (f7 * z + (f8 * (z0 * 2) + f9 * z1) +
               19 *
               (f0 * (z2 * 2) +
                (f1 * z3 + (f2 * (z4 * 2) + (f3 * z5 + (f4 * (z6 * 2) + (f5 * z8 + f6 * (z7 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (f6 * z + (f7 * z0 + (f8 * z1 + f9 * z2)) +
               19 * (f0 * z3 + (f1 * z4 + (f2 * z5 + (f3 * z6 + (f4 * z8 + f5 * z7)))))))%Z in
   Let y3 := (y2 << 25 +
              (f5 * z + (f6 * (z0 * 2) + (f7 * z1 + (f8 * (z2 * 2) + f9 * z3))) +
               19 * (f0 * (z4 * 2) + (f1 * z5 + (f2 * (z6 * 2) + (f3 * z8 + f4 * (z7 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (f4 * z + (f5 * z0 + (f6 * z1 + (f7 * z2 + (f8 * z3 + f9 * z4)))) +
               19 * (f0 * z5 + (f1 * z6 + (f2 * z8 + f3 * z7)))))%Z in
   Let y5 := (y4 << 25 +
              (f3 * z +
               (f4 * (z0 * 2) + (f5 * z1 + (f6 * (z2 * 2) + (f7 * z3 + (f8 * (z4 * 2) + f9 * z5))))) +
               19 * (f0 * (z6 * 2) + (f1 * z8 + f2 * (z7 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (f2 * z +
               (f3 * z0 + (f4 * z1 + (f5 * z2 + (f6 * z3 + (f7 * z4 + (f8 * z5 + f9 * z6)))))) +
               19 * (f0 * z8 + f1 * z7)))%Z in
   Let y7 := (y6 << 25 +
              (f1 * z +
               (f2 * (z0 * 2) +
                (f3 * z1 +
                 (f4 * (z2 * 2) + (f5 * z3 + (f6 * (z4 * 2) + (f7 * z5 + (f8 * (z6 * 2) + f9 * z8))))))) +
               19 * (f0 * (z7 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (f0 * z +
               (f1 * z0 +
                (f2 * z1 +
                 (f3 * z2 + (f4 * z3 + (f5 * z4 + (f6 * z5 + (f7 * z6 + (f8 * z8 + f9 * z7))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   Let x'61 := (z17 + z17)%Z in
   Let x'62 := (z18 + z18)%Z in
   Let x'63 := (z16 + z16)%Z in
   Let x'64 := (z15 + z15)%Z in
   Let x'65 := (z14 + z14)%Z in
   Let x'66 := (z13 + z13)%Z in
   Let x'67 := (z12 + z12)%Z in
   Let x'68 := (z11 + z11)%Z in
   Let x'69 := (z10 + z10)%Z in
   Let x'70 := (z9 + z9)%Z in
   Let x'71 := (z49 * x'70 +
                19 *
                (z57 * (x'69 * 2) +
                 (z58 * x'68 +
                  (z56 * (x'67 * 2) +
                   (z55 * x'66 +
                    (z54 * (x'65 * 2) +
                     (z53 * x'64 + (z52 * (x'63 * 2) + (z51 * x'62 + z50 * (x'61 * 2))))))))))%Z in
   Let x'72 := (x'71 << 26 +
                (z50 * x'70 + z49 * x'69 +
                 19 *
                 (z57 * x'68 +
                  (z58 * x'67 +
                   (z56 * x'66 +
                    (z55 * x'65 + (z54 * x'64 + (z53 * x'63 + (z52 * x'62 + z51 * x'61)))))))))%Z in
   Let x'73 := (x'72 << 25 +
                (z51 * x'70 + (z50 * (x'69 * 2) + z49 * x'68) +
                 19 *
                 (z57 * (x'67 * 2) +
                  (z58 * x'66 +
                   (z56 * (x'65 * 2) +
                    (z55 * x'64 + (z54 * (x'63 * 2) + (z53 * x'62 + z52 * (x'61 * 2)))))))))%Z in
   Let x'74 := (x'73 << 26 +
                (z52 * x'70 + (z51 * x'69 + (z50 * x'68 + z49 * x'67)) +
                 19 *
                 (z57 * x'66 + (z58 * x'65 + (z56 * x'64 + (z55 * x'63 + (z54 * x'62 + z53 * x'61)))))))%Z in
   Let x'75 := (x'74 << 25 +
                (z53 * x'70 + (z52 * (x'69 * 2) + (z51 * x'68 + (z50 * (x'67 * 2) + z49 * x'66))) +
                 19 *
                 (z57 * (x'65 * 2) +
                  (z58 * x'64 + (z56 * (x'63 * 2) + (z55 * x'62 + z54 * (x'61 * 2)))))))%Z in
   Let x'76 := (x'75 << 26 +
                (z54 * x'70 + (z53 * x'69 + (z52 * x'68 + (z51 * x'67 + (z50 * x'66 + z49 * x'65)))) +
                 19 * (z57 * x'64 + (z58 * x'63 + (z56 * x'62 + z55 * x'61)))))%Z in
   Let x'77 := (x'76 << 25 +
                (z55 * x'70 +
                 (z54 * (x'69 * 2) +
                  (z53 * x'68 + (z52 * (x'67 * 2) + (z51 * x'66 + (z50 * (x'65 * 2) + z49 * x'64))))) +
                 19 * (z57 * (x'63 * 2) + (z58 * x'62 + z56 * (x'61 * 2)))))%Z in
   Let x'78 := (x'77 << 26 +
                (z56 * x'70 +
                 (z55 * x'69 +
                  (z54 * x'68 +
                   (z53 * x'67 + (z52 * x'66 + (z51 * x'65 + (z50 * x'64 + z49 * x'63)))))) +
                 19 * (z57 * x'62 + z58 * x'61)))%Z in
   Let x'79 := (x'78 << 25 +
                (z58 * x'70 +
                 (z56 * (x'69 * 2) +
                  (z55 * x'68 +
                   (z54 * (x'67 * 2) +
                    (z53 * x'66 + (z52 * (x'65 * 2) + (z51 * x'64 + (z50 * (x'63 * 2) + z49 * x'62))))))) +
                 19 * (z57 * (x'61 * 2))))%Z in
   Let x'80 := (x'79 << 26 +
                (z57 * x'70 +
                 (z58 * x'69 +
                  (z56 * x'68 +
                   (z55 * x'67 +
                    (z54 * x'66 +
                     (z53 * x'65 + (z52 * x'64 + (z51 * x'63 + (z50 * x'62 + z49 * x'61))))))))))%Z in
   Let x'81 := x'80 & (33554432 + -1) in
   Let y'17 := x'79 & (67108864 + -1) in
   Let y'18 := x'78 & (33554432 + -1) in
   Let y'19 := x'77 & (67108864 + -1) in
   Let y'20 := x'76 & (33554432 + -1) in
   Let y'21 := x'75 & (67108864 + -1) in
   Let y'22 := x'74 & (33554432 + -1) in
   Let y'23 := x'73 & (67108864 + -1) in
   Let y'24 := x'72 & (33554432 + -1) in
   Let y'25 := (19 * x'80 << 25 + (x'71 & (67108864 + -1)))%Z in
   Let x'82 := (67108862 + x'60 - x'29)%Z in
   Let y'26 := (134217726 + y'8 - y')%Z in
   Let y'27 := (67108862 + y'9 - y'0)%Z in
   Let y'28 := (134217726 + y'10 - y'1)%Z in
   Let y'29 := (67108862 + y'11 - y'2)%Z in
   Let y'30 := (134217726 + y'12 - y'3)%Z in
   Let y'31 := (67108862 + y'13 - y'4)%Z in
   Let y'32 := (134217726 + y'14 - y'5)%Z in
   Let y'33 := (67108862 + y'15 - y'6)%Z in
   Let y'34 := (134217690 + y'16 - y'7)%Z in
   Let F := plet (p, g9) := C in
   plet (p0, g8) := p in
   plet (p1, g7) := p0 in
   plet (p2, g6) := p1 in
   plet (p3, g5) := p2 in
   plet (p4, g4) := p3 in
   plet (p5, g3) := p4 in
   plet (p6, g2) := p5 in
   plet (g0, g1) := p6 in
   ((67108862 + x'81 - g0)%Z, (134217726 + y'17 - g1)%Z, (67108862 + y'18 - g2)%Z,
   (134217726 + y'19 - g3)%Z, (67108862 + y'20 - g4)%Z, (134217726 + y'21 - g5)%Z,
   (67108862 + y'22 - g6)%Z, (134217726 + y'23 - g7)%Z, (67108862 + y'24 - g8)%Z,
   (134217690 + y'25 - g9)%Z) in
   Let G := plet (p, g9) := C in
   plet (p0, g8) := p in
   plet (p1, g7) := p0 in
   plet (p2, g6) := p1 in
   plet (p3, g5) := p2 in
   plet (p4, g4) := p3 in
   plet (p5, g3) := p4 in
   plet (p6, g2) := p5 in
   plet (g0, g1) := p6 in
   ((x'81 + g0)%Z, (y'17 + g1)%Z, (y'18 + g2)%Z, (y'19 + g3)%Z, (y'20 + g4)%Z,
   (y'21 + g5)%Z, (y'22 + g6)%Z, (y'23 + g7)%Z, (y'24 + g8)%Z, (y'25 + g9)%Z) in
   Let x'83 := (x'60 + x'29)%Z in
   Let y'35 := (y'8 + y')%Z in
   Let y'36 := (y'9 + y'0)%Z in
   Let y'37 := (y'10 + y'1)%Z in
   Let y'38 := (y'11 + y'2)%Z in
   Let y'39 := (y'12 + y'3)%Z in
   Let y'40 := (y'13 + y'4)%Z in
   Let y'41 := (y'14 + y'5)%Z in
   Let y'42 := (y'15 + y'6)%Z in
   Let y'43 := (y'16 + y'7)%Z in
   Let X3 := plet (p, g9) := F in
   plet (p0, g8) := p in
   plet (p1, g7) := p0 in
   plet (p2, g6) := p1 in
   plet (p3, g5) := p2 in
   plet (p4, g4) := p3 in
   plet (p5, g3) := p4 in
   plet (p6, g2) := p5 in
   plet (g0, g1) := p6 in
   Let y := (y'34 * g9 +
             19 *
             (x'82 * (g8 * 2) +
              (y'26 * g7 +
               (y'27 * (g6 * 2) +
                (y'28 * g5 +
                 (y'29 * (g4 * 2) + (y'30 * g3 + (y'31 * (g2 * 2) + (y'32 * g1 + y'33 * (g0 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (y'33 * g9 + y'34 * g8 +
               19 *
               (x'82 * g7 +
                (y'26 * g6 +
                 (y'27 * g5 + (y'28 * g4 + (y'29 * g3 + (y'30 * g2 + (y'31 * g1 + y'32 * g0)))))))))%Z in
   Let y1 := (y0 << 25 +
              (y'32 * g9 + (y'33 * (g8 * 2) + y'34 * g7) +
               19 *
               (x'82 * (g6 * 2) +
                (y'26 * g5 +
                 (y'27 * (g4 * 2) + (y'28 * g3 + (y'29 * (g2 * 2) + (y'30 * g1 + y'31 * (g0 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (y'31 * g9 + (y'32 * g8 + (y'33 * g7 + y'34 * g6)) +
               19 * (x'82 * g5 + (y'26 * g4 + (y'27 * g3 + (y'28 * g2 + (y'29 * g1 + y'30 * g0)))))))%Z in
   Let y3 := (y2 << 25 +
              (y'30 * g9 + (y'31 * (g8 * 2) + (y'32 * g7 + (y'33 * (g6 * 2) + y'34 * g5))) +
               19 *
               (x'82 * (g4 * 2) + (y'26 * g3 + (y'27 * (g2 * 2) + (y'28 * g1 + y'29 * (g0 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (y'29 * g9 + (y'30 * g8 + (y'31 * g7 + (y'32 * g6 + (y'33 * g5 + y'34 * g4)))) +
               19 * (x'82 * g3 + (y'26 * g2 + (y'27 * g1 + y'28 * g0)))))%Z in
   Let y5 := (y4 << 25 +
              (y'28 * g9 +
               (y'29 * (g8 * 2) +
                (y'30 * g7 + (y'31 * (g6 * 2) + (y'32 * g5 + (y'33 * (g4 * 2) + y'34 * g3))))) +
               19 * (x'82 * (g2 * 2) + (y'26 * g1 + y'27 * (g0 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (y'27 * g9 +
               (y'28 * g8 +
                (y'29 * g7 + (y'30 * g6 + (y'31 * g5 + (y'32 * g4 + (y'33 * g3 + y'34 * g2)))))) +
               19 * (x'82 * g1 + y'26 * g0)))%Z in
   Let y7 := (y6 << 25 +
              (y'26 * g9 +
               (y'27 * (g8 * 2) +
                (y'28 * g7 +
                 (y'29 * (g6 * 2) +
                  (y'30 * g5 + (y'31 * (g4 * 2) + (y'32 * g3 + (y'33 * (g2 * 2) + y'34 * g1))))))) +
               19 * (x'82 * (g0 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (x'82 * g9 +
               (y'26 * g8 +
                (y'27 * g7 +
                 (y'28 * g6 +
                  (y'29 * g5 + (y'30 * g4 + (y'31 * g3 + (y'32 * g2 + (y'33 * g1 + y'34 * g0))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   Let Y3 := plet (p, f9) := G in
   plet (p0, f8) := p in
   plet (p1, f7) := p0 in
   plet (p2, f6) := p1 in
   plet (p3, f5) := p2 in
   plet (p4, f4) := p3 in
   plet (p5, f3) := p4 in
   plet (p6, f2) := p5 in
   plet (f0, f1) := p6 in
   Let y := (f9 * y'43 +
             19 *
             (f0 * (y'42 * 2) +
              (f1 * y'41 +
               (f2 * (y'40 * 2) +
                (f3 * y'39 +
                 (f4 * (y'38 * 2) + (f5 * y'37 + (f6 * (y'36 * 2) + (f7 * y'35 + f8 * (x'83 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (f8 * y'43 + f9 * y'42 +
               19 *
               (f0 * y'41 +
                (f1 * y'40 +
                 (f2 * y'39 + (f3 * y'38 + (f4 * y'37 + (f5 * y'36 + (f6 * y'35 + f7 * x'83)))))))))%Z in
   Let y1 := (y0 << 25 +
              (f7 * y'43 + (f8 * (y'42 * 2) + f9 * y'41) +
               19 *
               (f0 * (y'40 * 2) +
                (f1 * y'39 +
                 (f2 * (y'38 * 2) + (f3 * y'37 + (f4 * (y'36 * 2) + (f5 * y'35 + f6 * (x'83 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (f6 * y'43 + (f7 * y'42 + (f8 * y'41 + f9 * y'40)) +
               19 * (f0 * y'39 + (f1 * y'38 + (f2 * y'37 + (f3 * y'36 + (f4 * y'35 + f5 * x'83)))))))%Z in
   Let y3 := (y2 << 25 +
              (f5 * y'43 + (f6 * (y'42 * 2) + (f7 * y'41 + (f8 * (y'40 * 2) + f9 * y'39))) +
               19 *
               (f0 * (y'38 * 2) + (f1 * y'37 + (f2 * (y'36 * 2) + (f3 * y'35 + f4 * (x'83 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (f4 * y'43 + (f5 * y'42 + (f6 * y'41 + (f7 * y'40 + (f8 * y'39 + f9 * y'38)))) +
               19 * (f0 * y'37 + (f1 * y'36 + (f2 * y'35 + f3 * x'83)))))%Z in
   Let y5 := (y4 << 25 +
              (f3 * y'43 +
               (f4 * (y'42 * 2) +
                (f5 * y'41 + (f6 * (y'40 * 2) + (f7 * y'39 + (f8 * (y'38 * 2) + f9 * y'37))))) +
               19 * (f0 * (y'36 * 2) + (f1 * y'35 + f2 * (x'83 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (f2 * y'43 +
               (f3 * y'42 +
                (f4 * y'41 + (f5 * y'40 + (f6 * y'39 + (f7 * y'38 + (f8 * y'37 + f9 * y'36)))))) +
               19 * (f0 * y'35 + f1 * x'83)))%Z in
   Let y7 := (y6 << 25 +
              (f1 * y'43 +
               (f2 * (y'42 * 2) +
                (f3 * y'41 +
                 (f4 * (y'40 * 2) +
                  (f5 * y'39 + (f6 * (y'38 * 2) + (f7 * y'37 + (f8 * (y'36 * 2) + f9 * y'35))))))) +
               19 * (f0 * (x'83 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (f0 * y'43 +
               (f1 * y'42 +
                (f2 * y'41 +
                 (f3 * y'40 +
                  (f4 * y'39 + (f5 * y'38 + (f6 * y'37 + (f7 * y'36 + (f8 * y'35 + f9 * x'83))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   Let x'84 := (y'34 * y'43 +
                19 *
                (x'82 * (y'42 * 2) +
                 (y'26 * y'41 +
                  (y'27 * (y'40 * 2) +
                   (y'28 * y'39 +
                    (y'29 * (y'38 * 2) +
                     (y'30 * y'37 + (y'31 * (y'36 * 2) + (y'32 * y'35 + y'33 * (x'83 * 2))))))))))%Z in
   Let x'85 := (x'84 << 26 +
                (y'33 * y'43 + y'34 * y'42 +
                 19 *
                 (x'82 * y'41 +
                  (y'26 * y'40 +
                   (y'27 * y'39 +
                    (y'28 * y'38 + (y'29 * y'37 + (y'30 * y'36 + (y'31 * y'35 + y'32 * x'83)))))))))%Z in
   Let x'86 := (x'85 << 25 +
                (y'32 * y'43 + (y'33 * (y'42 * 2) + y'34 * y'41) +
                 19 *
                 (x'82 * (y'40 * 2) +
                  (y'26 * y'39 +
                   (y'27 * (y'38 * 2) +
                    (y'28 * y'37 + (y'29 * (y'36 * 2) + (y'30 * y'35 + y'31 * (x'83 * 2)))))))))%Z in
   Let x'87 := (x'86 << 26 +
                (y'31 * y'43 + (y'32 * y'42 + (y'33 * y'41 + y'34 * y'40)) +
                 19 *
                 (x'82 * y'39 +
                  (y'26 * y'38 + (y'27 * y'37 + (y'28 * y'36 + (y'29 * y'35 + y'30 * x'83)))))))%Z in
   Let x'88 := (x'87 << 25 +
                (y'30 * y'43 +
                 (y'31 * (y'42 * 2) + (y'32 * y'41 + (y'33 * (y'40 * 2) + y'34 * y'39))) +
                 19 *
                 (x'82 * (y'38 * 2) +
                  (y'26 * y'37 + (y'27 * (y'36 * 2) + (y'28 * y'35 + y'29 * (x'83 * 2)))))))%Z in
   Let x'89 := (x'88 << 26 +
                (y'29 * y'43 +
                 (y'30 * y'42 + (y'31 * y'41 + (y'32 * y'40 + (y'33 * y'39 + y'34 * y'38)))) +
                 19 * (x'82 * y'37 + (y'26 * y'36 + (y'27 * y'35 + y'28 * x'83)))))%Z in
   Let x'90 := (x'89 << 25 +
                (y'28 * y'43 +
                 (y'29 * (y'42 * 2) +
                  (y'30 * y'41 +
                   (y'31 * (y'40 * 2) + (y'32 * y'39 + (y'33 * (y'38 * 2) + y'34 * y'37))))) +
                 19 * (x'82 * (y'36 * 2) + (y'26 * y'35 + y'27 * (x'83 * 2)))))%Z in
   Let x'91 := (x'90 << 26 +
                (y'27 * y'43 +
                 (y'28 * y'42 +
                  (y'29 * y'41 +
                   (y'30 * y'40 + (y'31 * y'39 + (y'32 * y'38 + (y'33 * y'37 + y'34 * y'36)))))) +
                 19 * (x'82 * y'35 + y'26 * x'83)))%Z in
   Let x'92 := (x'91 << 25 +
                (y'26 * y'43 +
                 (y'27 * (y'42 * 2) +
                  (y'28 * y'41 +
                   (y'29 * (y'40 * 2) +
                    (y'30 * y'39 +
                     (y'31 * (y'38 * 2) + (y'32 * y'37 + (y'33 * (y'36 * 2) + y'34 * y'35))))))) +
                 19 * (x'82 * (x'83 * 2))))%Z in
   Let x'93 := (x'92 << 26 +
                (x'82 * y'43 +
                 (y'26 * y'42 +
                  (y'27 * y'41 +
                   (y'28 * y'40 +
                    (y'29 * y'39 +
                     (y'30 * y'38 + (y'31 * y'37 + (y'32 * y'36 + (y'33 * y'35 + y'34 * x'83))))))))))%Z in
   Let x'94 := x'93 & (33554432 + -1) in
   Let y'44 := x'92 & (67108864 + -1) in
   Let y'45 := x'91 & (33554432 + -1) in
   Let y'46 := x'90 & (67108864 + -1) in
   Let y'47 := x'89 & (33554432 + -1) in
   Let y'48 := x'88 & (67108864 + -1) in
   Let y'49 := x'87 & (33554432 + -1) in
   Let y'50 := x'86 & (67108864 + -1) in
   Let y'51 := x'85 & (33554432 + -1) in
   Let y'52 := (19 * x'93 << 25 + (x'84 & (67108864 + -1)))%Z in
   Let Z3 := plet (p, f9) := F in
   plet (p0, f8) := p in
   plet (p1, f7) := p0 in
   plet (p2, f6) := p1 in
   plet (p3, f5) := p2 in
   plet (p4, f4) := p3 in
   plet (p5, f3) := p4 in
   plet (p6, f2) := p5 in
   plet (f0, f1) := p6 in
   plet (p7, g9) := G in
   plet (p8, g8) := p7 in
   plet (p9, g7) := p8 in
   plet (p10, g6) := p9 in
   plet (p11, g5) := p10 in
   plet (p12, g4) := p11 in
   plet (p13, g3) := p12 in
   plet (p14, g2) := p13 in
   plet (g0, g1) := p14 in
   Let y := (f9 * g9 +
             19 *
             (f0 * (g8 * 2) +
              (f1 * g7 +
               (f2 * (g6 * 2) +
                (f3 * g5 + (f4 * (g4 * 2) + (f5 * g3 + (f6 * (g2 * 2) + (f7 * g1 + f8 * (g0 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (f8 * g9 + f9 * g8 +
               19 *
               (f0 * g7 +
                (f1 * g6 + (f2 * g5 + (f3 * g4 + (f4 * g3 + (f5 * g2 + (f6 * g1 + f7 * g0)))))))))%Z in
   Let y1 := (y0 << 25 +
              (f7 * g9 + (f8 * (g8 * 2) + f9 * g7) +
               19 *
               (f0 * (g6 * 2) +
                (f1 * g5 + (f2 * (g4 * 2) + (f3 * g3 + (f4 * (g2 * 2) + (f5 * g1 + f6 * (g0 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (f6 * g9 + (f7 * g8 + (f8 * g7 + f9 * g6)) +
               19 * (f0 * g5 + (f1 * g4 + (f2 * g3 + (f3 * g2 + (f4 * g1 + f5 * g0)))))))%Z in
   Let y3 := (y2 << 25 +
              (f5 * g9 + (f6 * (g8 * 2) + (f7 * g7 + (f8 * (g6 * 2) + f9 * g5))) +
               19 * (f0 * (g4 * 2) + (f1 * g3 + (f2 * (g2 * 2) + (f3 * g1 + f4 * (g0 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (f4 * g9 + (f5 * g8 + (f6 * g7 + (f7 * g6 + (f8 * g5 + f9 * g4)))) +
               19 * (f0 * g3 + (f1 * g2 + (f2 * g1 + f3 * g0)))))%Z in
   Let y5 := (y4 << 25 +
              (f3 * g9 +
               (f4 * (g8 * 2) + (f5 * g7 + (f6 * (g6 * 2) + (f7 * g5 + (f8 * (g4 * 2) + f9 * g3))))) +
               19 * (f0 * (g2 * 2) + (f1 * g1 + f2 * (g0 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (f2 * g9 +
               (f3 * g8 + (f4 * g7 + (f5 * g6 + (f6 * g5 + (f7 * g4 + (f8 * g3 + f9 * g2)))))) +
               19 * (f0 * g1 + f1 * g0)))%Z in
   Let y7 := (y6 << 25 +
              (f1 * g9 +
               (f2 * (g8 * 2) +
                (f3 * g7 +
                 (f4 * (g6 * 2) + (f5 * g5 + (f6 * (g4 * 2) + (f7 * g3 + (f8 * (g2 * 2) + f9 * g1))))))) +
               19 * (f0 * (g0 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (f0 * g9 +
               (f1 * g8 +
                (f2 * g7 +
                 (f3 * g6 + (f4 * g5 + (f5 * g4 + (f6 * g3 + (f7 * g2 + (f8 * g1 + f9 * g0))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   (X3, Y3, Z3, (x'94, y'44, y'45, y'46, y'47, y'48, y'49, y'50, y'51, y'52)))

(dependent evars: (printing disabled) )

 *)
      subst P.
      hnf in twice_d.
      assert (H : P); subst P; [ | clear H ].
      { Time do_prune_lets' 100 ltac:(fun G => pose G).
        assert (H : P); subst P; [ | clear H ].
      { Time do_prune_lets' 100 ltac:(fun G => pose G).
        assert (H : P); subst P; [ | clear H ].
      { Time do_prune_lets' 200 ltac:(fun G => pose G).
        assert (H : P); subst P; [ | clear H ].
      { Time do_prune_lets' 200 ltac:(fun G => pose G).
        assert (H : P); subst P; [ | clear H ].
      { Set Printing Depth 100000.
        Time do_prune_lets' 200 ltac:(fun G => pose G).
        assert (H : P); subst P; [ | clear H ].
      { Time do_prune_lets' true ltac:(fun G => pose G).
        assert (H : P); subst P; [ | clear H ].
      { (*
1 focused subgoal
(unfocused: 1-1-1-1-1-1-1-0-1, shelved: 2), subgoal 1 (ID 21139)

  twice_d : fe25519
  z77, z78, z76, z75, z74, z73, z72, z71, z70, z69, z67, z68, z66, z65, z64, z63, z62, z61, z60, z59,
  z57, z58, z56, z55, z54, z53, z52, z51, z50, z49, z47, z48, z46, z45, z44, z43, z42, z41, z40, z39,
  z37, z38, z36, z35, z34, z33, z32, z31, z30, z29, z27, z28, z26, z25, z24, z23, z22, z21, z20, z19,
  z17, z18, z16, z15, z14, z13, z12, z11, z10, z9, z7, z8, z6, z5, z4, z3, z2, z1, z0, z
   : Z
  ============================
  ?y =
  (Let x' := (67108862 + z67 - z77)%Z in
   Let x'0 := (134217726 + z68 - z78)%Z in
   Let x'1 := (67108862 + z66 - z76)%Z in
   Let x'2 := (134217726 + z65 - z75)%Z in
   Let x'3 := (67108862 + z64 - z74)%Z in
   Let x'4 := (134217726 + z63 - z73)%Z in
   Let x'5 := (67108862 + z62 - z72)%Z in
   Let x'6 := (134217726 + z61 - z71)%Z in
   Let x'7 := (67108862 + z60 - z70)%Z in
   Let x'8 := (134217690 + z59 - z69)%Z in
   Let x'9 := (67108862 + z27 - z37)%Z in
   Let x'10 := (134217726 + z28 - z38)%Z in
   Let x'11 := (67108862 + z26 - z36)%Z in
   Let x'12 := (134217726 + z25 - z35)%Z in
   Let x'13 := (67108862 + z24 - z34)%Z in
   Let x'14 := (134217726 + z23 - z33)%Z in
   Let x'15 := (67108862 + z22 - z32)%Z in
   Let x'16 := (134217726 + z21 - z31)%Z in
   Let x'17 := (67108862 + z20 - z30)%Z in
   Let x'18 := (134217690 + z19 - z29)%Z in
   Let x'19 := (x'8 * x'18 +
                19 *
                (x' * (x'17 * 2) +
                 (x'0 * x'16 +
                  (x'1 * (x'15 * 2) +
                   (x'2 * x'14 +
                    (x'3 * (x'13 * 2) +
                     (x'4 * x'12 + (x'5 * (x'11 * 2) + (x'6 * x'10 + x'7 * (x'9 * 2))))))))))%Z in
   Let x'20 := (x'19 << 26 +
                (x'7 * x'18 + x'8 * x'17 +
                 19 *
                 (x' * x'16 +
                  (x'0 * x'15 +
                   (x'1 * x'14 +
                    (x'2 * x'13 + (x'3 * x'12 + (x'4 * x'11 + (x'5 * x'10 + x'6 * x'9)))))))))%Z in
   Let x'21 := (x'20 << 25 +
                (x'6 * x'18 + (x'7 * (x'17 * 2) + x'8 * x'16) +
                 19 *
                 (x' * (x'15 * 2) +
                  (x'0 * x'14 +
                   (x'1 * (x'13 * 2) +
                    (x'2 * x'12 + (x'3 * (x'11 * 2) + (x'4 * x'10 + x'5 * (x'9 * 2)))))))))%Z in
   Let x'22 := (x'21 << 26 +
                (x'5 * x'18 + (x'6 * x'17 + (x'7 * x'16 + x'8 * x'15)) +
                 19 *
                 (x' * x'14 + (x'0 * x'13 + (x'1 * x'12 + (x'2 * x'11 + (x'3 * x'10 + x'4 * x'9)))))))%Z in
   Let x'23 := (x'22 << 25 +
                (x'4 * x'18 + (x'5 * (x'17 * 2) + (x'6 * x'16 + (x'7 * (x'15 * 2) + x'8 * x'14))) +
                 19 *
                 (x' * (x'13 * 2) +
                  (x'0 * x'12 + (x'1 * (x'11 * 2) + (x'2 * x'10 + x'3 * (x'9 * 2)))))))%Z in
   Let x'24 := (x'23 << 26 +
                (x'3 * x'18 + (x'4 * x'17 + (x'5 * x'16 + (x'6 * x'15 + (x'7 * x'14 + x'8 * x'13)))) +
                 19 * (x' * x'12 + (x'0 * x'11 + (x'1 * x'10 + x'2 * x'9)))))%Z in
   Let x'25 := (x'24 << 25 +
                (x'2 * x'18 +
                 (x'3 * (x'17 * 2) +
                  (x'4 * x'16 + (x'5 * (x'15 * 2) + (x'6 * x'14 + (x'7 * (x'13 * 2) + x'8 * x'12))))) +
                 19 * (x' * (x'11 * 2) + (x'0 * x'10 + x'1 * (x'9 * 2)))))%Z in
   Let x'26 := (x'25 << 26 +
                (x'1 * x'18 +
                 (x'2 * x'17 +
                  (x'3 * x'16 +
                   (x'4 * x'15 + (x'5 * x'14 + (x'6 * x'13 + (x'7 * x'12 + x'8 * x'11)))))) +
                 19 * (x' * x'10 + x'0 * x'9)))%Z in
   Let x'27 := (x'26 << 25 +
                (x'0 * x'18 +
                 (x'1 * (x'17 * 2) +
                  (x'2 * x'16 +
                   (x'3 * (x'15 * 2) +
                    (x'4 * x'14 + (x'5 * (x'13 * 2) + (x'6 * x'12 + (x'7 * (x'11 * 2) + x'8 * x'10))))))) +
                 19 * (x' * (x'9 * 2))))%Z in
   Let x'28 := (x'27 << 26 +
                (x' * x'18 +
                 (x'0 * x'17 +
                  (x'1 * x'16 +
                   (x'2 * x'15 +
                    (x'3 * x'14 +
                     (x'4 * x'13 + (x'5 * x'12 + (x'6 * x'11 + (x'7 * x'10 + x'8 * x'9))))))))))%Z in
   Let x'29 := x'28 & (33554432 + -1) in
   Let y' := x'27 & (67108864 + -1) in
   Let y'0 := x'26 & (33554432 + -1) in
   Let y'1 := x'25 & (67108864 + -1) in
   Let y'2 := x'24 & (33554432 + -1) in
   Let y'3 := x'23 & (67108864 + -1) in
   Let y'4 := x'22 & (33554432 + -1) in
   Let y'5 := x'21 & (67108864 + -1) in
   Let y'6 := x'20 & (33554432 + -1) in
   Let y'7 := (19 * x'28 << 25 + (x'19 & (67108864 + -1)))%Z in
   Let x'30 := (z67 + z77)%Z in
   Let x'31 := (z68 + z78)%Z in
   Let x'32 := (z66 + z76)%Z in
   Let x'33 := (z65 + z75)%Z in
   Let x'34 := (z64 + z74)%Z in
   Let x'35 := (z63 + z73)%Z in
   Let x'36 := (z62 + z72)%Z in
   Let x'37 := (z61 + z71)%Z in
   Let x'38 := (z60 + z70)%Z in
   Let x'39 := (z59 + z69)%Z in
   Let x'40 := (z27 + z37)%Z in
   Let x'41 := (z28 + z38)%Z in
   Let x'42 := (z26 + z36)%Z in
   Let x'43 := (z25 + z35)%Z in
   Let x'44 := (z24 + z34)%Z in
   Let x'45 := (z23 + z33)%Z in
   Let x'46 := (z22 + z32)%Z in
   Let x'47 := (z21 + z31)%Z in
   Let x'48 := (z20 + z30)%Z in
   Let x'49 := (z19 + z29)%Z in
   Let x'50 := (x'39 * x'49 +
                19 *
                (x'30 * (x'48 * 2) +
                 (x'31 * x'47 +
                  (x'32 * (x'46 * 2) +
                   (x'33 * x'45 +
                    (x'34 * (x'44 * 2) +
                     (x'35 * x'43 + (x'36 * (x'42 * 2) + (x'37 * x'41 + x'38 * (x'40 * 2))))))))))%Z in
   Let x'51 := (x'50 << 26 +
                (x'38 * x'49 + x'39 * x'48 +
                 19 *
                 (x'30 * x'47 +
                  (x'31 * x'46 +
                   (x'32 * x'45 +
                    (x'33 * x'44 + (x'34 * x'43 + (x'35 * x'42 + (x'36 * x'41 + x'37 * x'40)))))))))%Z in
   Let x'52 := (x'51 << 25 +
                (x'37 * x'49 + (x'38 * (x'48 * 2) + x'39 * x'47) +
                 19 *
                 (x'30 * (x'46 * 2) +
                  (x'31 * x'45 +
                   (x'32 * (x'44 * 2) +
                    (x'33 * x'43 + (x'34 * (x'42 * 2) + (x'35 * x'41 + x'36 * (x'40 * 2)))))))))%Z in
   Let x'53 := (x'52 << 26 +
                (x'36 * x'49 + (x'37 * x'48 + (x'38 * x'47 + x'39 * x'46)) +
                 19 *
                 (x'30 * x'45 +
                  (x'31 * x'44 + (x'32 * x'43 + (x'33 * x'42 + (x'34 * x'41 + x'35 * x'40)))))))%Z in
   Let x'54 := (x'53 << 25 +
                (x'35 * x'49 +
                 (x'36 * (x'48 * 2) + (x'37 * x'47 + (x'38 * (x'46 * 2) + x'39 * x'45))) +
                 19 *
                 (x'30 * (x'44 * 2) +
                  (x'31 * x'43 + (x'32 * (x'42 * 2) + (x'33 * x'41 + x'34 * (x'40 * 2)))))))%Z in
   Let x'55 := (x'54 << 26 +
                (x'34 * x'49 +
                 (x'35 * x'48 + (x'36 * x'47 + (x'37 * x'46 + (x'38 * x'45 + x'39 * x'44)))) +
                 19 * (x'30 * x'43 + (x'31 * x'42 + (x'32 * x'41 + x'33 * x'40)))))%Z in
   Let x'56 := (x'55 << 25 +
                (x'33 * x'49 +
                 (x'34 * (x'48 * 2) +
                  (x'35 * x'47 +
                   (x'36 * (x'46 * 2) + (x'37 * x'45 + (x'38 * (x'44 * 2) + x'39 * x'43))))) +
                 19 * (x'30 * (x'42 * 2) + (x'31 * x'41 + x'32 * (x'40 * 2)))))%Z in
   Let x'57 := (x'56 << 26 +
                (x'32 * x'49 +
                 (x'33 * x'48 +
                  (x'34 * x'47 +
                   (x'35 * x'46 + (x'36 * x'45 + (x'37 * x'44 + (x'38 * x'43 + x'39 * x'42)))))) +
                 19 * (x'30 * x'41 + x'31 * x'40)))%Z in
   Let x'58 := (x'57 << 25 +
                (x'31 * x'49 +
                 (x'32 * (x'48 * 2) +
                  (x'33 * x'47 +
                   (x'34 * (x'46 * 2) +
                    (x'35 * x'45 +
                     (x'36 * (x'44 * 2) + (x'37 * x'43 + (x'38 * (x'42 * 2) + x'39 * x'41))))))) +
                 19 * (x'30 * (x'40 * 2))))%Z in
   Let x'59 := (x'58 << 26 +
                (x'30 * x'49 +
                 (x'31 * x'48 +
                  (x'32 * x'47 +
                   (x'33 * x'46 +
                    (x'34 * x'45 +
                     (x'35 * x'44 + (x'36 * x'43 + (x'37 * x'42 + (x'38 * x'41 + x'39 * x'40))))))))))%Z in
   Let x'60 := x'59 & (33554432 + -1) in
   Let y'8 := x'58 & (67108864 + -1) in
   Let y'9 := x'57 & (33554432 + -1) in
   Let y'10 := x'56 & (67108864 + -1) in
   Let y'11 := x'55 & (33554432 + -1) in
   Let y'12 := x'54 & (67108864 + -1) in
   Let y'13 := x'53 & (33554432 + -1) in
   Let y'14 := x'52 & (67108864 + -1) in
   Let y'15 := x'51 & (33554432 + -1) in
   Let y'16 := (19 * x'59 << 25 + (x'50 & (67108864 + -1)))%Z in
   Let C := plet (p, f9) := plet (p, g9) := twice_d in
            plet (p0, g8) := p in
            plet (p1, g7) := p0 in
            plet (p2, g6) := p1 in
            plet (p3, g5) := p2 in
            plet (p4, g4) := p3 in
            plet (p5, g3) := p4 in
            plet (p6, g2) := p5 in
            plet (g0, g1) := p6 in
            Let y := (z39 * g9 +
                      19 *
                      (z47 * (g8 * 2) +
                       (z48 * g7 +
                        (z46 * (g6 * 2) +
                         (z45 * g5 +
                          (z44 * (g4 * 2) +
                           (z43 * g3 + (z42 * (g2 * 2) + (z41 * g1 + z40 * (g0 * 2))))))))))%Z in
            Let y0 := (y << 26 +
                       (z40 * g9 + z39 * g8 +
                        19 *
                        (z47 * g7 +
                         (z48 * g6 +
                          (z46 * g5 + (z45 * g4 + (z44 * g3 + (z43 * g2 + (z42 * g1 + z41 * g0)))))))))%Z in
            Let y1 := (y0 << 25 +
                       (z41 * g9 + (z40 * (g8 * 2) + z39 * g7) +
                        19 *
                        (z47 * (g6 * 2) +
                         (z48 * g5 +
                          (z46 * (g4 * 2) +
                           (z45 * g3 + (z44 * (g2 * 2) + (z43 * g1 + z42 * (g0 * 2)))))))))%Z in
            Let y2 := (y1 << 26 +
                       (z42 * g9 + (z41 * g8 + (z40 * g7 + z39 * g6)) +
                        19 *
                        (z47 * g5 + (z48 * g4 + (z46 * g3 + (z45 * g2 + (z44 * g1 + z43 * g0)))))))%Z in
            Let y3 := (y2 << 25 +
                       (z43 * g9 + (z42 * (g8 * 2) + (z41 * g7 + (z40 * (g6 * 2) + z39 * g5))) +
                        19 *
                        (z47 * (g4 * 2) + (z48 * g3 + (z46 * (g2 * 2) + (z45 * g1 + z44 * (g0 * 2)))))))%Z in
            Let y4 := (y3 << 26 +
                       (z44 * g9 + (z43 * g8 + (z42 * g7 + (z41 * g6 + (z40 * g5 + z39 * g4)))) +
                        19 * (z47 * g3 + (z48 * g2 + (z46 * g1 + z45 * g0)))))%Z in
            Let y5 := (y4 << 25 +
                       (z45 * g9 +
                        (z44 * (g8 * 2) +
                         (z43 * g7 + (z42 * (g6 * 2) + (z41 * g5 + (z40 * (g4 * 2) + z39 * g3))))) +
                        19 * (z47 * (g2 * 2) + (z48 * g1 + z46 * (g0 * 2)))))%Z in
            Let y6 := (y5 << 26 +
                       (z46 * g9 +
                        (z45 * g8 +
                         (z44 * g7 + (z43 * g6 + (z42 * g5 + (z41 * g4 + (z40 * g3 + z39 * g2)))))) +
                        19 * (z47 * g1 + z48 * g0)))%Z in
            Let y7 := (y6 << 25 +
                       (z48 * g9 +
                        (z46 * (g8 * 2) +
                         (z45 * g7 +
                          (z44 * (g6 * 2) +
                           (z43 * g5 + (z42 * (g4 * 2) + (z41 * g3 + (z40 * (g2 * 2) + z39 * g1))))))) +
                        19 * (z47 * (g0 * 2))))%Z in
            Let y8 := (y7 << 26 +
                       (z47 * g9 +
                        (z48 * g8 +
                         (z46 * g7 +
                          (z45 * g6 +
                           (z44 * g5 + (z43 * g4 + (z42 * g3 + (z41 * g2 + (z40 * g1 + z39 * g0))))))))))%Z in
            (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1),
            y5 & (67108864 + -1), y4 & (33554432 + -1), y3 & (67108864 + -1),
            y2 & (33554432 + -1), y1 & (67108864 + -1), y0 & (33554432 + -1),
            (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   plet (p0, f8) := p in
   plet (p1, f7) := p0 in
   plet (p2, f6) := p1 in
   plet (p3, f5) := p2 in
   plet (p4, f4) := p3 in
   plet (p5, f3) := p4 in
   plet (p6, f2) := p5 in
   plet (f0, f1) := p6 in
   Let y := (f9 * z +
             19 *
             (f0 * (z0 * 2) +
              (f1 * z1 +
               (f2 * (z2 * 2) +
                (f3 * z3 + (f4 * (z4 * 2) + (f5 * z5 + (f6 * (z6 * 2) + (f7 * z8 + f8 * (z7 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (f8 * z + f9 * z0 +
               19 *
               (f0 * z1 +
                (f1 * z2 + (f2 * z3 + (f3 * z4 + (f4 * z5 + (f5 * z6 + (f6 * z8 + f7 * z7)))))))))%Z in
   Let y1 := (y0 << 25 +
              (f7 * z + (f8 * (z0 * 2) + f9 * z1) +
               19 *
               (f0 * (z2 * 2) +
                (f1 * z3 + (f2 * (z4 * 2) + (f3 * z5 + (f4 * (z6 * 2) + (f5 * z8 + f6 * (z7 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (f6 * z + (f7 * z0 + (f8 * z1 + f9 * z2)) +
               19 * (f0 * z3 + (f1 * z4 + (f2 * z5 + (f3 * z6 + (f4 * z8 + f5 * z7)))))))%Z in
   Let y3 := (y2 << 25 +
              (f5 * z + (f6 * (z0 * 2) + (f7 * z1 + (f8 * (z2 * 2) + f9 * z3))) +
               19 * (f0 * (z4 * 2) + (f1 * z5 + (f2 * (z6 * 2) + (f3 * z8 + f4 * (z7 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (f4 * z + (f5 * z0 + (f6 * z1 + (f7 * z2 + (f8 * z3 + f9 * z4)))) +
               19 * (f0 * z5 + (f1 * z6 + (f2 * z8 + f3 * z7)))))%Z in
   Let y5 := (y4 << 25 +
              (f3 * z +
               (f4 * (z0 * 2) + (f5 * z1 + (f6 * (z2 * 2) + (f7 * z3 + (f8 * (z4 * 2) + f9 * z5))))) +
               19 * (f0 * (z6 * 2) + (f1 * z8 + f2 * (z7 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (f2 * z +
               (f3 * z0 + (f4 * z1 + (f5 * z2 + (f6 * z3 + (f7 * z4 + (f8 * z5 + f9 * z6)))))) +
               19 * (f0 * z8 + f1 * z7)))%Z in
   Let y7 := (y6 << 25 +
              (f1 * z +
               (f2 * (z0 * 2) +
                (f3 * z1 +
                 (f4 * (z2 * 2) + (f5 * z3 + (f6 * (z4 * 2) + (f7 * z5 + (f8 * (z6 * 2) + f9 * z8))))))) +
               19 * (f0 * (z7 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (f0 * z +
               (f1 * z0 +
                (f2 * z1 +
                 (f3 * z2 + (f4 * z3 + (f5 * z4 + (f6 * z5 + (f7 * z6 + (f8 * z8 + f9 * z7))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   Let x'61 := (z17 + z17)%Z in
   Let x'62 := (z18 + z18)%Z in
   Let x'63 := (z16 + z16)%Z in
   Let x'64 := (z15 + z15)%Z in
   Let x'65 := (z14 + z14)%Z in
   Let x'66 := (z13 + z13)%Z in
   Let x'67 := (z12 + z12)%Z in
   Let x'68 := (z11 + z11)%Z in
   Let x'69 := (z10 + z10)%Z in
   Let x'70 := (z9 + z9)%Z in
   Let x'71 := (z49 * x'70 +
                19 *
                (z57 * (x'69 * 2) +
                 (z58 * x'68 +
                  (z56 * (x'67 * 2) +
                   (z55 * x'66 +
                    (z54 * (x'65 * 2) +
                     (z53 * x'64 + (z52 * (x'63 * 2) + (z51 * x'62 + z50 * (x'61 * 2))))))))))%Z in
   Let x'72 := (x'71 << 26 +
                (z50 * x'70 + z49 * x'69 +
                 19 *
                 (z57 * x'68 +
                  (z58 * x'67 +
                   (z56 * x'66 +
                    (z55 * x'65 + (z54 * x'64 + (z53 * x'63 + (z52 * x'62 + z51 * x'61)))))))))%Z in
   Let x'73 := (x'72 << 25 +
                (z51 * x'70 + (z50 * (x'69 * 2) + z49 * x'68) +
                 19 *
                 (z57 * (x'67 * 2) +
                  (z58 * x'66 +
                   (z56 * (x'65 * 2) +
                    (z55 * x'64 + (z54 * (x'63 * 2) + (z53 * x'62 + z52 * (x'61 * 2)))))))))%Z in
   Let x'74 := (x'73 << 26 +
                (z52 * x'70 + (z51 * x'69 + (z50 * x'68 + z49 * x'67)) +
                 19 *
                 (z57 * x'66 + (z58 * x'65 + (z56 * x'64 + (z55 * x'63 + (z54 * x'62 + z53 * x'61)))))))%Z in
   Let x'75 := (x'74 << 25 +
                (z53 * x'70 + (z52 * (x'69 * 2) + (z51 * x'68 + (z50 * (x'67 * 2) + z49 * x'66))) +
                 19 *
                 (z57 * (x'65 * 2) +
                  (z58 * x'64 + (z56 * (x'63 * 2) + (z55 * x'62 + z54 * (x'61 * 2)))))))%Z in
   Let x'76 := (x'75 << 26 +
                (z54 * x'70 + (z53 * x'69 + (z52 * x'68 + (z51 * x'67 + (z50 * x'66 + z49 * x'65)))) +
                 19 * (z57 * x'64 + (z58 * x'63 + (z56 * x'62 + z55 * x'61)))))%Z in
   Let x'77 := (x'76 << 25 +
                (z55 * x'70 +
                 (z54 * (x'69 * 2) +
                  (z53 * x'68 + (z52 * (x'67 * 2) + (z51 * x'66 + (z50 * (x'65 * 2) + z49 * x'64))))) +
                 19 * (z57 * (x'63 * 2) + (z58 * x'62 + z56 * (x'61 * 2)))))%Z in
   Let x'78 := (x'77 << 26 +
                (z56 * x'70 +
                 (z55 * x'69 +
                  (z54 * x'68 +
                   (z53 * x'67 + (z52 * x'66 + (z51 * x'65 + (z50 * x'64 + z49 * x'63)))))) +
                 19 * (z57 * x'62 + z58 * x'61)))%Z in
   Let x'79 := (x'78 << 25 +
                (z58 * x'70 +
                 (z56 * (x'69 * 2) +
                  (z55 * x'68 +
                   (z54 * (x'67 * 2) +
                    (z53 * x'66 + (z52 * (x'65 * 2) + (z51 * x'64 + (z50 * (x'63 * 2) + z49 * x'62))))))) +
                 19 * (z57 * (x'61 * 2))))%Z in
   Let x'80 := (x'79 << 26 +
                (z57 * x'70 +
                 (z58 * x'69 +
                  (z56 * x'68 +
                   (z55 * x'67 +
                    (z54 * x'66 +
                     (z53 * x'65 + (z52 * x'64 + (z51 * x'63 + (z50 * x'62 + z49 * x'61))))))))))%Z in
   Let x'81 := x'80 & (33554432 + -1) in
   Let y'17 := x'79 & (67108864 + -1) in
   Let y'18 := x'78 & (33554432 + -1) in
   Let y'19 := x'77 & (67108864 + -1) in
   Let y'20 := x'76 & (33554432 + -1) in
   Let y'21 := x'75 & (67108864 + -1) in
   Let y'22 := x'74 & (33554432 + -1) in
   Let y'23 := x'73 & (67108864 + -1) in
   Let y'24 := x'72 & (33554432 + -1) in
   Let y'25 := (19 * x'80 << 25 + (x'71 & (67108864 + -1)))%Z in
   Let x'82 := (67108862 + x'60 - x'29)%Z in
   Let y'26 := (134217726 + y'8 - y')%Z in
   Let y'27 := (67108862 + y'9 - y'0)%Z in
   Let y'28 := (134217726 + y'10 - y'1)%Z in
   Let y'29 := (67108862 + y'11 - y'2)%Z in
   Let y'30 := (134217726 + y'12 - y'3)%Z in
   Let y'31 := (67108862 + y'13 - y'4)%Z in
   Let y'32 := (134217726 + y'14 - y'5)%Z in
   Let y'33 := (67108862 + y'15 - y'6)%Z in
   Let y'34 := (134217690 + y'16 - y'7)%Z in
   Let F := plet (p, g9) := C in
   plet (p0, g8) := p in
   plet (p1, g7) := p0 in
   plet (p2, g6) := p1 in
   plet (p3, g5) := p2 in
   plet (p4, g4) := p3 in
   plet (p5, g3) := p4 in
   plet (p6, g2) := p5 in
   plet (g0, g1) := p6 in
   ((67108862 + x'81 - g0)%Z, (134217726 + y'17 - g1)%Z, (67108862 + y'18 - g2)%Z,
   (134217726 + y'19 - g3)%Z, (67108862 + y'20 - g4)%Z, (134217726 + y'21 - g5)%Z,
   (67108862 + y'22 - g6)%Z, (134217726 + y'23 - g7)%Z, (67108862 + y'24 - g8)%Z,
   (134217690 + y'25 - g9)%Z) in
   Let G := plet (p, g9) := C in
   plet (p0, g8) := p in
   plet (p1, g7) := p0 in
   plet (p2, g6) := p1 in
   plet (p3, g5) := p2 in
   plet (p4, g4) := p3 in
   plet (p5, g3) := p4 in
   plet (p6, g2) := p5 in
   plet (g0, g1) := p6 in
   ((x'81 + g0)%Z, (y'17 + g1)%Z, (y'18 + g2)%Z, (y'19 + g3)%Z, (y'20 + g4)%Z,
   (y'21 + g5)%Z, (y'22 + g6)%Z, (y'23 + g7)%Z, (y'24 + g8)%Z, (y'25 + g9)%Z) in
   Let x'83 := (x'60 + x'29)%Z in
   Let y'35 := (y'8 + y')%Z in
   Let y'36 := (y'9 + y'0)%Z in
   Let y'37 := (y'10 + y'1)%Z in
   Let y'38 := (y'11 + y'2)%Z in
   Let y'39 := (y'12 + y'3)%Z in
   Let y'40 := (y'13 + y'4)%Z in
   Let y'41 := (y'14 + y'5)%Z in
   Let y'42 := (y'15 + y'6)%Z in
   Let y'43 := (y'16 + y'7)%Z in
   Let X3 := plet (p, g9) := F in
   plet (p0, g8) := p in
   plet (p1, g7) := p0 in
   plet (p2, g6) := p1 in
   plet (p3, g5) := p2 in
   plet (p4, g4) := p3 in
   plet (p5, g3) := p4 in
   plet (p6, g2) := p5 in
   plet (g0, g1) := p6 in
   Let y := (y'34 * g9 +
             19 *
             (x'82 * (g8 * 2) +
              (y'26 * g7 +
               (y'27 * (g6 * 2) +
                (y'28 * g5 +
                 (y'29 * (g4 * 2) + (y'30 * g3 + (y'31 * (g2 * 2) + (y'32 * g1 + y'33 * (g0 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (y'33 * g9 + y'34 * g8 +
               19 *
               (x'82 * g7 +
                (y'26 * g6 +
                 (y'27 * g5 + (y'28 * g4 + (y'29 * g3 + (y'30 * g2 + (y'31 * g1 + y'32 * g0)))))))))%Z in
   Let y1 := (y0 << 25 +
              (y'32 * g9 + (y'33 * (g8 * 2) + y'34 * g7) +
               19 *
               (x'82 * (g6 * 2) +
                (y'26 * g5 +
                 (y'27 * (g4 * 2) + (y'28 * g3 + (y'29 * (g2 * 2) + (y'30 * g1 + y'31 * (g0 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (y'31 * g9 + (y'32 * g8 + (y'33 * g7 + y'34 * g6)) +
               19 * (x'82 * g5 + (y'26 * g4 + (y'27 * g3 + (y'28 * g2 + (y'29 * g1 + y'30 * g0)))))))%Z in
   Let y3 := (y2 << 25 +
              (y'30 * g9 + (y'31 * (g8 * 2) + (y'32 * g7 + (y'33 * (g6 * 2) + y'34 * g5))) +
               19 *
               (x'82 * (g4 * 2) + (y'26 * g3 + (y'27 * (g2 * 2) + (y'28 * g1 + y'29 * (g0 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (y'29 * g9 + (y'30 * g8 + (y'31 * g7 + (y'32 * g6 + (y'33 * g5 + y'34 * g4)))) +
               19 * (x'82 * g3 + (y'26 * g2 + (y'27 * g1 + y'28 * g0)))))%Z in
   Let y5 := (y4 << 25 +
              (y'28 * g9 +
               (y'29 * (g8 * 2) +
                (y'30 * g7 + (y'31 * (g6 * 2) + (y'32 * g5 + (y'33 * (g4 * 2) + y'34 * g3))))) +
               19 * (x'82 * (g2 * 2) + (y'26 * g1 + y'27 * (g0 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (y'27 * g9 +
               (y'28 * g8 +
                (y'29 * g7 + (y'30 * g6 + (y'31 * g5 + (y'32 * g4 + (y'33 * g3 + y'34 * g2)))))) +
               19 * (x'82 * g1 + y'26 * g0)))%Z in
   Let y7 := (y6 << 25 +
              (y'26 * g9 +
               (y'27 * (g8 * 2) +
                (y'28 * g7 +
                 (y'29 * (g6 * 2) +
                  (y'30 * g5 + (y'31 * (g4 * 2) + (y'32 * g3 + (y'33 * (g2 * 2) + y'34 * g1))))))) +
               19 * (x'82 * (g0 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (x'82 * g9 +
               (y'26 * g8 +
                (y'27 * g7 +
                 (y'28 * g6 +
                  (y'29 * g5 + (y'30 * g4 + (y'31 * g3 + (y'32 * g2 + (y'33 * g1 + y'34 * g0))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   Let Y3 := plet (p, f9) := G in
   plet (p0, f8) := p in
   plet (p1, f7) := p0 in
   plet (p2, f6) := p1 in
   plet (p3, f5) := p2 in
   plet (p4, f4) := p3 in
   plet (p5, f3) := p4 in
   plet (p6, f2) := p5 in
   plet (f0, f1) := p6 in
   Let y := (f9 * y'43 +
             19 *
             (f0 * (y'42 * 2) +
              (f1 * y'41 +
               (f2 * (y'40 * 2) +
                (f3 * y'39 +
                 (f4 * (y'38 * 2) + (f5 * y'37 + (f6 * (y'36 * 2) + (f7 * y'35 + f8 * (x'83 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (f8 * y'43 + f9 * y'42 +
               19 *
               (f0 * y'41 +
                (f1 * y'40 +
                 (f2 * y'39 + (f3 * y'38 + (f4 * y'37 + (f5 * y'36 + (f6 * y'35 + f7 * x'83)))))))))%Z in
   Let y1 := (y0 << 25 +
              (f7 * y'43 + (f8 * (y'42 * 2) + f9 * y'41) +
               19 *
               (f0 * (y'40 * 2) +
                (f1 * y'39 +
                 (f2 * (y'38 * 2) + (f3 * y'37 + (f4 * (y'36 * 2) + (f5 * y'35 + f6 * (x'83 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (f6 * y'43 + (f7 * y'42 + (f8 * y'41 + f9 * y'40)) +
               19 * (f0 * y'39 + (f1 * y'38 + (f2 * y'37 + (f3 * y'36 + (f4 * y'35 + f5 * x'83)))))))%Z in
   Let y3 := (y2 << 25 +
              (f5 * y'43 + (f6 * (y'42 * 2) + (f7 * y'41 + (f8 * (y'40 * 2) + f9 * y'39))) +
               19 *
               (f0 * (y'38 * 2) + (f1 * y'37 + (f2 * (y'36 * 2) + (f3 * y'35 + f4 * (x'83 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (f4 * y'43 + (f5 * y'42 + (f6 * y'41 + (f7 * y'40 + (f8 * y'39 + f9 * y'38)))) +
               19 * (f0 * y'37 + (f1 * y'36 + (f2 * y'35 + f3 * x'83)))))%Z in
   Let y5 := (y4 << 25 +
              (f3 * y'43 +
               (f4 * (y'42 * 2) +
                (f5 * y'41 + (f6 * (y'40 * 2) + (f7 * y'39 + (f8 * (y'38 * 2) + f9 * y'37))))) +
               19 * (f0 * (y'36 * 2) + (f1 * y'35 + f2 * (x'83 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (f2 * y'43 +
               (f3 * y'42 +
                (f4 * y'41 + (f5 * y'40 + (f6 * y'39 + (f7 * y'38 + (f8 * y'37 + f9 * y'36)))))) +
               19 * (f0 * y'35 + f1 * x'83)))%Z in
   Let y7 := (y6 << 25 +
              (f1 * y'43 +
               (f2 * (y'42 * 2) +
                (f3 * y'41 +
                 (f4 * (y'40 * 2) +
                  (f5 * y'39 + (f6 * (y'38 * 2) + (f7 * y'37 + (f8 * (y'36 * 2) + f9 * y'35))))))) +
               19 * (f0 * (x'83 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (f0 * y'43 +
               (f1 * y'42 +
                (f2 * y'41 +
                 (f3 * y'40 +
                  (f4 * y'39 + (f5 * y'38 + (f6 * y'37 + (f7 * y'36 + (f8 * y'35 + f9 * x'83))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   Let x'84 := (y'34 * y'43 +
                19 *
                (x'82 * (y'42 * 2) +
                 (y'26 * y'41 +
                  (y'27 * (y'40 * 2) +
                   (y'28 * y'39 +
                    (y'29 * (y'38 * 2) +
                     (y'30 * y'37 + (y'31 * (y'36 * 2) + (y'32 * y'35 + y'33 * (x'83 * 2))))))))))%Z in
   Let x'85 := (x'84 << 26 +
                (y'33 * y'43 + y'34 * y'42 +
                 19 *
                 (x'82 * y'41 +
                  (y'26 * y'40 +
                   (y'27 * y'39 +
                    (y'28 * y'38 + (y'29 * y'37 + (y'30 * y'36 + (y'31 * y'35 + y'32 * x'83)))))))))%Z in
   Let x'86 := (x'85 << 25 +
                (y'32 * y'43 + (y'33 * (y'42 * 2) + y'34 * y'41) +
                 19 *
                 (x'82 * (y'40 * 2) +
                  (y'26 * y'39 +
                   (y'27 * (y'38 * 2) +
                    (y'28 * y'37 + (y'29 * (y'36 * 2) + (y'30 * y'35 + y'31 * (x'83 * 2)))))))))%Z in
   Let x'87 := (x'86 << 26 +
                (y'31 * y'43 + (y'32 * y'42 + (y'33 * y'41 + y'34 * y'40)) +
                 19 *
                 (x'82 * y'39 +
                  (y'26 * y'38 + (y'27 * y'37 + (y'28 * y'36 + (y'29 * y'35 + y'30 * x'83)))))))%Z in
   Let x'88 := (x'87 << 25 +
                (y'30 * y'43 +
                 (y'31 * (y'42 * 2) + (y'32 * y'41 + (y'33 * (y'40 * 2) + y'34 * y'39))) +
                 19 *
                 (x'82 * (y'38 * 2) +
                  (y'26 * y'37 + (y'27 * (y'36 * 2) + (y'28 * y'35 + y'29 * (x'83 * 2)))))))%Z in
   Let x'89 := (x'88 << 26 +
                (y'29 * y'43 +
                 (y'30 * y'42 + (y'31 * y'41 + (y'32 * y'40 + (y'33 * y'39 + y'34 * y'38)))) +
                 19 * (x'82 * y'37 + (y'26 * y'36 + (y'27 * y'35 + y'28 * x'83)))))%Z in
   Let x'90 := (x'89 << 25 +
                (y'28 * y'43 +
                 (y'29 * (y'42 * 2) +
                  (y'30 * y'41 +
                   (y'31 * (y'40 * 2) + (y'32 * y'39 + (y'33 * (y'38 * 2) + y'34 * y'37))))) +
                 19 * (x'82 * (y'36 * 2) + (y'26 * y'35 + y'27 * (x'83 * 2)))))%Z in
   Let x'91 := (x'90 << 26 +
                (y'27 * y'43 +
                 (y'28 * y'42 +
                  (y'29 * y'41 +
                   (y'30 * y'40 + (y'31 * y'39 + (y'32 * y'38 + (y'33 * y'37 + y'34 * y'36)))))) +
                 19 * (x'82 * y'35 + y'26 * x'83)))%Z in
   Let x'92 := (x'91 << 25 +
                (y'26 * y'43 +
                 (y'27 * (y'42 * 2) +
                  (y'28 * y'41 +
                   (y'29 * (y'40 * 2) +
                    (y'30 * y'39 +
                     (y'31 * (y'38 * 2) + (y'32 * y'37 + (y'33 * (y'36 * 2) + y'34 * y'35))))))) +
                 19 * (x'82 * (x'83 * 2))))%Z in
   Let x'93 := (x'92 << 26 +
                (x'82 * y'43 +
                 (y'26 * y'42 +
                  (y'27 * y'41 +
                   (y'28 * y'40 +
                    (y'29 * y'39 +
                     (y'30 * y'38 + (y'31 * y'37 + (y'32 * y'36 + (y'33 * y'35 + y'34 * x'83))))))))))%Z in
   Let x'94 := x'93 & (33554432 + -1) in
   Let y'44 := x'92 & (67108864 + -1) in
   Let y'45 := x'91 & (33554432 + -1) in
   Let y'46 := x'90 & (67108864 + -1) in
   Let y'47 := x'89 & (33554432 + -1) in
   Let y'48 := x'88 & (67108864 + -1) in
   Let y'49 := x'87 & (33554432 + -1) in
   Let y'50 := x'86 & (67108864 + -1) in
   Let y'51 := x'85 & (33554432 + -1) in
   Let y'52 := (19 * x'93 << 25 + (x'84 & (67108864 + -1)))%Z in
   Let Z3 := plet (p, f9) := F in
   plet (p0, f8) := p in
   plet (p1, f7) := p0 in
   plet (p2, f6) := p1 in
   plet (p3, f5) := p2 in
   plet (p4, f4) := p3 in
   plet (p5, f3) := p4 in
   plet (p6, f2) := p5 in
   plet (f0, f1) := p6 in
   plet (p7, g9) := G in
   plet (p8, g8) := p7 in
   plet (p9, g7) := p8 in
   plet (p10, g6) := p9 in
   plet (p11, g5) := p10 in
   plet (p12, g4) := p11 in
   plet (p13, g3) := p12 in
   plet (p14, g2) := p13 in
   plet (g0, g1) := p14 in
   Let y := (f9 * g9 +
             19 *
             (f0 * (g8 * 2) +
              (f1 * g7 +
               (f2 * (g6 * 2) +
                (f3 * g5 + (f4 * (g4 * 2) + (f5 * g3 + (f6 * (g2 * 2) + (f7 * g1 + f8 * (g0 * 2))))))))))%Z in
   Let y0 := (y << 26 +
              (f8 * g9 + f9 * g8 +
               19 *
               (f0 * g7 +
                (f1 * g6 + (f2 * g5 + (f3 * g4 + (f4 * g3 + (f5 * g2 + (f6 * g1 + f7 * g0)))))))))%Z in
   Let y1 := (y0 << 25 +
              (f7 * g9 + (f8 * (g8 * 2) + f9 * g7) +
               19 *
               (f0 * (g6 * 2) +
                (f1 * g5 + (f2 * (g4 * 2) + (f3 * g3 + (f4 * (g2 * 2) + (f5 * g1 + f6 * (g0 * 2)))))))))%Z in
   Let y2 := (y1 << 26 +
              (f6 * g9 + (f7 * g8 + (f8 * g7 + f9 * g6)) +
               19 * (f0 * g5 + (f1 * g4 + (f2 * g3 + (f3 * g2 + (f4 * g1 + f5 * g0)))))))%Z in
   Let y3 := (y2 << 25 +
              (f5 * g9 + (f6 * (g8 * 2) + (f7 * g7 + (f8 * (g6 * 2) + f9 * g5))) +
               19 * (f0 * (g4 * 2) + (f1 * g3 + (f2 * (g2 * 2) + (f3 * g1 + f4 * (g0 * 2)))))))%Z in
   Let y4 := (y3 << 26 +
              (f4 * g9 + (f5 * g8 + (f6 * g7 + (f7 * g6 + (f8 * g5 + f9 * g4)))) +
               19 * (f0 * g3 + (f1 * g2 + (f2 * g1 + f3 * g0)))))%Z in
   Let y5 := (y4 << 25 +
              (f3 * g9 +
               (f4 * (g8 * 2) + (f5 * g7 + (f6 * (g6 * 2) + (f7 * g5 + (f8 * (g4 * 2) + f9 * g3))))) +
               19 * (f0 * (g2 * 2) + (f1 * g1 + f2 * (g0 * 2)))))%Z in
   Let y6 := (y5 << 26 +
              (f2 * g9 +
               (f3 * g8 + (f4 * g7 + (f5 * g6 + (f6 * g5 + (f7 * g4 + (f8 * g3 + f9 * g2)))))) +
               19 * (f0 * g1 + f1 * g0)))%Z in
   Let y7 := (y6 << 25 +
              (f1 * g9 +
               (f2 * (g8 * 2) +
                (f3 * g7 +
                 (f4 * (g6 * 2) + (f5 * g5 + (f6 * (g4 * 2) + (f7 * g3 + (f8 * (g2 * 2) + f9 * g1))))))) +
               19 * (f0 * (g0 * 2))))%Z in
   Let y8 := (y7 << 26 +
              (f0 * g9 +
               (f1 * g8 +
                (f2 * g7 +
                 (f3 * g6 + (f4 * g5 + (f5 * g4 + (f6 * g3 + (f7 * g2 + (f8 * g1 + f9 * g0))))))))))%Z in
   (y8 & (33554432 + -1), y7 & (67108864 + -1), y6 & (33554432 + -1), y5 & (67108864 + -1),
   y4 & (33554432 + -1), y3 & (67108864 + -1), y2 & (33554432 + -1), y1 & (67108864 + -1),
   y0 & (33554432 + -1), (19 * y8 << 25 + (y & (67108864 + -1)))%Z) in
   (X3, Y3, Z3, (x'94, y'44, y'45, y'46, y'47, y'48, y'49, y'50, y'51, y'52)))

(dependent evars: (printing disabled) )

*)
Ltac prune_lets fuel term ::=
  lazymatch fuel with
  | 0 => term
  | _ =>
    let fuel' := match fuel with
                 | S ?f => f
                 | _ => fuel
                 end in
    match (eval cbv beta iota in term) with
    | context G[Let_In ?x ?f]
      => let test := constr:(_ : is_var_or_tuple x) in
         let G' := context G[f x] in
         prune_lets fuel' G'
    | context G[prod_rect ?P ?f (pair ?x ?y)]
      => let prod_rect' := constr:(prod_rect P) in
         let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
         let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
         prune_lets fuel' G'
    | context G[Let_In (pair ?x ?y) ?f]
      => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
         prune_lets fuel' G'
    | context G[Let_In (Let_In ?x ?f) ?g]
      => let G' := context G[Let_In x (fun x' => Let_In (f x') g)] in
         prune_lets fuel' G'
    | ?f ?x
      => let f' := prune_lets fuel' f in
         let x' := prune_lets fuel' x in
         constr:(f' x')
  | fun x : ?T => @?f x
    => match constr:(Set) with
       | _ => let ret := constr:(fun x : T => (_ : prune_lets fuel' (f x))) in
              let ret := (eval cbv beta delta [prune_lets] in ret) in
              ret
       | _ => let dummy := constr:(_ : cidtac "Error: Failed to handle" term "") in f
       end
  | ?term' => let bot := constr:(_ : cidtac "bot" term' "") in term'
    end
  end.
Time do_prune_lets' true ltac:(fun G => pose G).



      idtac.



      do_prune_lets' ltac:(fun G' => pose G' as P).
      assert (H : P); subst P; [ | clear H ].
      Notation "'plet' ( x , y ) := v 'in' f" := (prod_rect _ (fun x y => f) v) (at level 9).
      Notation "'Let' x := y 'in' f" := (Let_In y (fun x => f)) (at level 9).
      Set Printing Depth 1000000.
      {
do_prune_lets' ltac:(fun G' => pose G' as P).
      assert (H : P); subst P; [ | clear H ].
{
Ltac prune_lets term ::=
do_prune_lets' ltac:(fun G' => pose G' as P).
      assert (H : P); subst P; [ | clear H ].
{ Notation "'Let' x := y 'in' f" := (Let_In y (fun x => f)) (format "'[' 'Let'  x  :=  y  'in' ']' '//' '[' f ']'", at level 9).

Ltac prune_lets term ::=
  match (eval cbv beta iota in term) with
  | context G[prod_rect ?P ?f (pair ?x ?y)]
    => let dummy := constr:(_ : cidtac f x y) in
let prod_rect' := constr:(prod_rect P) in
       let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
       let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
       prune_lets G'
  | ?f ?x
    => let f' := prune_lets f in
       let x' := prune_lets x in
       constr:(f' x')
  | fun x : ?T => @?f x
    => match constr:(Set) with
       | _ => let ret := constr:(fun x : T => (_ : prune_lets (f x))) in
              let ret := (eval cbv beta delta [prune_lets] in ret) in
              ret
       | _ => let dummy := constr:(_ : cidtac "Error: Failed to handle" term "") in f
       end
  | ?term' => let bot := constr:(_ : cidtac "bot" term' "") in term'
  end.



      Focus 2.
      do 20 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do 20 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do 4 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do 10 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f (pair ?x ?y)] ]
        => let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
           change G'
      | [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'
            end; cbv beta iota).
      do 10 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f (pair ?x ?y)] ]
        => let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
           change G'(*
      | [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'*)
            end; cbv beta iota).
      do 100 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f (pair ?x ?y)] ]
        => let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
           change G'(*
      | [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'*)
            end; cbv beta iota).
      do 3 (match goal with
| [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'
            end; cbv beta iota).
      do 3 (match goal with
| [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'
            end; cbv beta iota).
      do 10 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f (pair ?x ?y)] ]
        => let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
           change G'(*
      | [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'*)
            end; cbv beta iota).
      do 5 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f (pair ?x ?y)] ]
        => let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
           change G'(*
      | [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'*)
            end; cbv beta iota).
      match goal with
| [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'
            end; cbv beta iota.
      do 100 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f (pair ?x ?y)] ]
        => let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[Let_In x (fun x' => Let_In y (fun y' => prod_rect' f (pair x' y')))] in
           change G'(*
      | [ |- appcontext G[Let_In (pair ?x ?y) ?f] ]
        => let G' := context G[Let_In x (fun x' => Let_In y (fun y' => f (pair x' y')))] in
           change G'*)
            end; cbv beta iota).

      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do 1 (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).


      Notation "'plet' ( x , y ) := v 'in' f" := (prod_rect _ (fun x y => f) v) (at level 9).

      cbv [optfst optsnd].
      do 100 try (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do 100 try (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do 1000 try (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).

progress
      do 1000 try (match goal with
      | [ |- appcontext G[Let_In ?x ?f] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let G' := context G[f x] in
           change G'
      | [ |- appcontext G[prod_rect ?P ?f ?x] ]
        => let test := constr:(_ : is_var_or_tuple x) in
           let prod_rect' := constr:(prod_rect P) in
           let prod_rect' := (eval cbv [prod_rect] in prod_rect') in
           let G' := context G[prod_rect' f x] in
           change G'
      end; cbv beta iota).
      do_from_let_in_to_Let_In_and_remove_pairs.

Set Printing All.
      cbv beta iota.
      change_let_in_with_Let_In.
      Print Ltac change_let_in_with_Let_In.
      progress change_let_in_with_Let_In.
      progress change_let_in_with_Let_In.
      progress change_let_in_with_Let_In.
      progress change_let_in_with_Let_In.

      do 10 lazymatch goal with
        |- context G[match (?a, ?b) with pair x y => @?C x y end]
        => let C' := eval cbv beta in (C a b) in
           let g' := context G[C'] in
           change g'
      end.
      cbv iota; cbv beta.
      cbv iota; cbv beta.
      cbv iota; cbv beta.
      eapply Proper_Let_In_changevalue.
      Unshelve.
      Focus 2.


      Set Printing All.


      repeat (let_nonvariables_of_type_before_match_pair Z; repeat let_in_changebody; cbv iota; cbv beta).
      replace_match_let_in_pair_with_let_in_match_pair_step.

    replace_match_let_in_pair_with_let_in_match_pair.
    Print Ltac replace_match_let_in_pair_with_let_in_match_pair.

End Curve25519.
