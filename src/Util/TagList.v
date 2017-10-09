Require Import Coq.Lists.List.
Import ListNotations.

Module Tag.
  Record tagged :=
    { keyT : Type;
      key : keyT;
      valueT : Type;
      value : valueT }.

  Definition Context := list tagged.

  Definition add {K V} (key' : K) (value' : V) (ctx : Context) : Context
    := cons {| key := key' ; value := value' |} ctx.

  Ltac update ctx key value :=
    constr:(add key value ctx).

  Ltac get_gen ctx key' default :=
    lazymatch (eval hnf in ctx) with
    | context[{| key := key' ; value := ?value' |}]
      => value'
    | _ => default ()
    end.

  Ltac get_error ctx key' :=
    lazymatch (eval hnf in ctx) with
    | context[{| key := key' ; value := ?value' |}]
      => value'
    end.

  Ltac get ctx key' := get_gen ctx key' ltac:(fun _ => constr:(I)).

  Notation get ctx key' := ltac:(let v := get ctx key' in exact v) (only parsing).

  Notation empty := (@nil tagged).
End Tag.
