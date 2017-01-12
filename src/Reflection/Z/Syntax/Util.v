Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Syntax.

Definition make_const t : interp_base_type t -> op Unit (Tbase t)
  := OpConst.
Definition is_const s d (v : op s d) : bool
  := match v with OpConst _ _ => true | _ => false end.
Arguments is_const [s d] v.
Definition is_cast s d (v : op s d) : bool
  := match v with Cast _ _ => true | _ => false end.
Arguments is_cast [s d] v.

Definition base_type_max (v1 v2 : base_type) : base_type
  := match v1, v2 with
     | TZ, _ => TZ
     | _, TZ => TZ
     | TWord logsz1, TWord logsz2 => TWord (max logsz1 logsz2)
     end.
Definition base_type_min (v1 v2 : base_type) : base_type
  := match v1, v2 with
     | TZ, v => v
     | v, TZ => v
     | TWord logsz1, TWord logsz2 => TWord (min logsz1 logsz2)
     end.
