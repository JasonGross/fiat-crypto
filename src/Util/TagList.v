Require Import Coq.Lists.List.
Import ListNotations.

Module Tag.
  Record tagged :=
    { keyT : Type;
      key : keyT;
      valueT : Type;
      value : valueT;
      local : bool }.

  Definition Context := list tagged.

  Definition add_gen {K V} (key' : K) (value' : V) (local' : bool) (ctx : Context) : Context
    := cons {| key := key' ; value := value' ; local := local' |} ctx.

  Definition add {K V} (key' : K) (value' : V) (ctx : Context) : Context
    := add_gen key' value' false ctx.

  Definition add_local {K V} (key' : K) (value' : V) (ctx : Context) : Context
    := add_gen key' value' true ctx.

  Definition strip_local (ctx : Context) : Context
    := List.filter (fun '{| key := k ; value := v ; local := loc |}
                    => negb loc)
                   ctx.

  Ltac strip_local ctx :=
    let upd := (eval cbv [strip_local negb List.filter] in strip_local) in
    eval cbv [add add_local add_gen] in (upd ctx).

  Ltac update ctx key value :=
    constr:(add key value ctx).

  Ltac local_update ctx key value :=
    constr:(add_local key value ctx).

  Ltac get_gen ctx key' default :=
    lazymatch (eval hnf in ctx) with
    | context[{| key := key' ; value := ?value' |}]
      => value'
    | context[add_gen ?key' ?value' _ _] => value'
    | context[add_local ?key' ?value' _] => value'
    | context[add ?key' ?value' _] => value'
    | _ => default ()
    end.

  Ltac get_error ctx key' :=
    lazymatch (eval hnf in ctx) with
    | context[{| key := key' ; value := ?value' |}]
      => value'
    | context[add_gen ?key' ?value' _ _] => value'
    | context[add_local ?key' ?value' _] => value'
    | context[add ?key' ?value' _] => value'
    end.

  Ltac get ctx key' := get_gen ctx key' ltac:(fun _ => constr:(I)).

  Notation get ctx key' := ltac:(let v := get ctx key' in exact v) (only parsing).

  Notation empty := (@nil tagged).
End Tag.
