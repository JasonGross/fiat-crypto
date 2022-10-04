(** * Reification Cache *)
(** This file defines the cache that holds reified versions of
    operations, as well as the tactics that reify and apply things
    from the cache. *)
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.Wf.

Import
  Language.API.Compilers
  Language.Wf.Compilers.

Import Compilers.API.

Fixpoint pointwise_equal {t} : relation (type.interp base.interp t)
  := match t with
     | type.base t => Logic.eq
     | type.arrow s d
       => fun (f g : type.interp base.interp s -> type.interp base.interp d)
          => forall x, pointwise_equal (f x) (g x)
     end.

Definition is_reification_of' {t} (e : Expr t) (v : type.interp base.interp t) : Prop
  := pointwise_equal (Interp e) v /\ Wf e.

Notation is_reification_of rop op
  := (match @is_reification_of' (reify_type_of op) rop op with
      | T
        => ltac:(
             let T := (eval cbv [pointwise_equal is_reification_of' T] in T) in
             let T := (eval cbn [type.interp base.interp base.base_interp] in T) in
             exact T)
      end)
       (only parsing).

Require Ltac2.Ltac2.
Module WithLtac2.
  Import Ltac2.Ltac2.
  Module Exports.
    #[global,export] Ltac2 Set Reify.should_debug_profile := fun () => true.
  End Exports.
  Ltac2 cache_reify () :=
    let timed_abstract_exact_no_check ce1 a1 e1 c :=
      Control.time (Some ce1) (fun () => ltac1:(subst_evars));
      Control.time (Some a1) (fun () => abstract (Control.time (Some e1) (fun () => Std.exact_no_check c))) in
    let timed_abstract_reflexivity ce1 r1 a1 e1 :=
      let c := Control.time (Some r1)
                            (fun () =>
                               let g := Control.goal () in
                               constr:(match True return $g with _ => eq_refl end)) in
      timed_abstract_exact_no_check ce1 a1 e1 c in
    split
    > [ intros;
        etransitivity
        > [
          | Control.time (Some "repeat apply f_equal")
                         (fun () => ltac1:(repeat match goal with [ |- _ = ?f' ?x ] => is_var x; apply (f_equal (fun f => f _)) end));
            Control.time (Some "Reify_rhs") (fun () => ltac1:(Reify_rhs ()));
            timed_abstract_reflexivity "subst_evars1" "reflexivity1" "abstract1" "exact_no_check1" ];
        Control.time (Some "subst_evars1.5") (fun () => ltac1:(subst_evars));
        timed_abstract_reflexivity "subst_evars2" "reflexivity2" "abstract2" "exact_no_check2"
      | let c := Control.time (Some "prove_Wf") (fun () => let g := Control.goal () in constr:(match True return $g with _ => ltac:(prove_Wf ()) end)) in
        timed_abstract_exact_no_check "subst_evars3" "abstract3" "exact_no_check3" c ].
End WithLtac2.

Ltac cache_reify _ := ltac2:(WithLtac2.cache_reify ()).

Ltac apply_cached_reification op lem :=
  lazymatch goal with
  | [ |- _ = ?RHS ]
    => let f := head RHS in
       constr_eq f op;
       simple apply lem
  end.

Create HintDb reify_gen_cache discriminated.
Create HintDb wf_gen_cache discriminated.

Module Export Hints.
  Export WithLtac2.Exports.
#[global]
  Hint Resolve conj : reify_gen_cache wf_gen_cache.
#[global]
  Hint Unfold Wf.Compilers.Wf : wf_gen_cache.
End Hints.
