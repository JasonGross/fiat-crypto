Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation Expr := (@Expr base_type_code op).
  Section with_var.
    Context {var : base_type_code -> Type}.
    Local Notation exprf := (@exprf base_type_code op var).
    Local Notation expr := (@expr base_type_code op var).
    Fixpoint interp_flat_type_eta {t T} : (interp_flat_type var t -> T) -> interp_flat_type var t -> T
      := match t return (interp_flat_type var t -> T) -> interp_flat_type var t -> T with
         | Tbase T => fun f => f
         | Unit => fun f => f
         | Prod A B
           => fun f x
              => let '(a, b) := x in
                 @interp_flat_type_eta
                   A _
                   (fun a' => @interp_flat_type_eta B _ (fun b' => f (a', b')) b)
                   a
         end.
    Fixpoint exprf_eta {t} (e : exprf t) : exprf t
      := match e in Syntax.exprf _ _ t return exprf t with
         | TT => TT
         | Var t v => Var v
         | Op t1 tR opc args => Op opc (@exprf_eta _ args)
         | LetIn tx ex tC eC
           => LetIn (@exprf_eta _ ex)
                    (interp_flat_type_eta eC)
         | Pair tx ex ty ey => Pair (@exprf_eta _ ex) (@exprf_eta _ ey)
         end.
    Definition expr_eta {t} (e : expr t) : expr (Arrow (domain t) (codomain t))
      := Abs (interp_flat_type_eta (fun x => exprf_eta (invert_Abs e x))).
  End with_var.
  Definition ExprEta {t} (e : Expr t) : Expr (Arrow (domain t) (codomain t))
    := fun var => expr_eta (e var).
End language.
