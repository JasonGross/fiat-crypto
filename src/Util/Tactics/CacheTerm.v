Require Import Crypto.Util.Tactics.TransparentAssert.

Ltac cache_term_with_type_by ty tac id :=
  let id' := fresh id in
  let dummy := match goal with
               | _ => transparent assert ( id' : ty );
                      [ transparent_abstract tac using id'
                      | ]
               end in
  let ret := (eval cbv delta [id'] in id') in
  let dummy := match goal with
               | _ => clear id'
               end in
  ret.
Ltac cache_term term id :=
  let ty := type of term in
  cache_term_with_type_by ty ltac:(exact_no_check term) id.
