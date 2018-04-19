{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

id :: a1 -> a1
id x =
  x

data SigT a p =
   ExistT a p

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

type Key = Positive

data Tree a =
   Leaf
 | Node (Tree a) (Prelude.Maybe a) (Tree a)

type T a = Tree a

empty :: T a1
empty =
  Leaf

find :: Key -> (T a1) -> Prelude.Maybe a1
find i m =
  case m of {
   Leaf -> Prelude.Nothing;
   Node l o r -> case i of {
                  XI ii -> find ii r;
                  XO ii -> find ii l;
                  XH -> o}}

add :: Key -> a1 -> (T a1) -> T a1
add i v m =
  case m of {
   Leaf ->
    case i of {
     XI ii -> Node Leaf Prelude.Nothing (add ii v Leaf);
     XO ii -> Node (add ii v Leaf) Prelude.Nothing Leaf;
     XH -> Node Leaf (Prelude.Just v) Leaf};
   Node l o r ->
    case i of {
     XI ii -> Node l o (add ii v r);
     XO ii -> Node (add ii v l) o r;
     XH -> Node l (Prelude.Just v) r}}

bind :: (Prelude.Maybe a1) -> (a1 -> Prelude.Maybe a2) -> Prelude.Maybe a2
bind v f =
  case v of {
   Prelude.Just v0 -> f v0;
   Prelude.Nothing -> Prelude.Nothing}

data Zrange =
   Build_zrange Z Z

data Primitive =
   Unit
 | Z1
 | Nat0
 | Bool

data Type =
   Type_primitive Primitive
 | Prod Type Type
 | Arrow Type Type
 | List Type

type Interp = Any

try_transport :: Type -> Type -> a1 -> Prelude.Maybe a1
try_transport t1 t2 =
  case t1 of {
   Type_primitive p -> (\x ->
    case p of {
     Unit ->
      case t2 of {
       Type_primitive p0 ->
        case p0 of {
         Unit -> Prelude.Just x;
         _ -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     Z1 ->
      case t2 of {
       Type_primitive p0 ->
        case p0 of {
         Z1 -> Prelude.Just x;
         _ -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     Nat0 ->
      case t2 of {
       Type_primitive p0 ->
        case p0 of {
         Nat0 -> Prelude.Just x;
         _ -> Prelude.Nothing};
       _ -> Prelude.Nothing};
     Bool ->
      case t2 of {
       Type_primitive p0 ->
        case p0 of {
         Bool -> Prelude.Just x;
         _ -> Prelude.Nothing};
       _ -> Prelude.Nothing}});
   Prod a b -> (\x ->
    case t2 of {
     Prod a' b' -> bind (try_transport a a' x) (\v -> try_transport b b' v);
     _ -> Prelude.Nothing});
   Arrow s d -> (\x ->
    case t2 of {
     Arrow s' d' -> bind (try_transport s s' x) (\v -> try_transport d d' v);
     _ -> Prelude.Nothing});
   List a ->
    case t2 of {
     List a' -> try_transport a a';
     _ -> (\_ -> Prelude.Nothing)}}

data Expr ident var =
   Var Type var
 | TT
 | AppIdent Type Type ident (Expr ident var)
 | App Type Type (Expr ident var) (Expr ident var)
 | Pair Type Type (Expr ident var) (Expr ident var)
 | Abs Type Type (var -> Expr ident var)

type Expr0 ident = () -> Expr ident Any

data Ident =
   Primitive0 Primitive Interp
 | Let_In Type Type
 | Nat_succ
 | Nat_add
 | Nat_sub
 | Nat_mul
 | Nat_max
 | Nil Type
 | Cons Type
 | Fst Type Type
 | Snd Type Type
 | Bool_rect Type
 | Nat_rect Type
 | Pred
 | List_rect Type Type
 | List_nth_default Type
 | List_nth_default_concrete Primitive Interp Nat
 | Z_shiftr Z
 | Z_shiftl Z
 | Z_land Z
 | Z_add
 | Z_mul
 | Z_pow
 | Z_sub
 | Z_opp
 | Z_div
 | Z_modulo
 | Z_eqb
 | Z_leb
 | Z_of_nat
 | Z_cast Zrange
 | Z_cast2 ((,) Zrange Zrange)

invert_Pair :: Type -> Type -> (Expr Ident a1) -> Prelude.Maybe
               ((,) (Expr Ident a1) (Expr Ident a1))
invert_Pair _ _ e =
  case e of {
   Pair _ _ a b -> Prelude.Just ((,) a b);
   _ -> Prelude.Nothing}

default0 :: Primitive -> Interp
default0 t =
  case t of {
   Unit -> unsafeCoerce ();
   Z1 -> unsafeCoerce (Zneg XH);
   Nat0 -> unsafeCoerce O;
   Bool -> unsafeCoerce Prelude.True}

default1 :: Type -> Expr Ident a1
default1 t =
  case t of {
   Type_primitive x -> AppIdent (Type_primitive Unit) (Type_primitive x)
    (Primitive0 x (default0 x)) TT;
   Prod a b -> Pair a b (default1 a) (default1 b);
   Arrow s d -> Abs s d (\_ -> default1 d);
   List a -> AppIdent (Type_primitive Unit) (List a) (Nil a) TT}

data Expr1 =
   Var0 Type Positive
 | TT0
 | AppIdent0 Type Type Ident Expr1
 | App0 Type Type Expr1 Expr1
 | Pair0 Type Type Expr1 Expr1
 | Abs0 Type Positive Type Expr1

eRROR :: a1 -> a1
eRROR v =
  v

to_flat' :: Type -> (Expr Ident Key) -> Key -> Expr1
to_flat' _ e cur_idx =
  case e of {
   Var t v -> Var0 t v;
   TT -> TT0;
   AppIdent s d idc args -> AppIdent0 s d idc (to_flat' s args cur_idx);
   App s d f x -> App0 s d (to_flat' (Arrow s d) f cur_idx)
    (to_flat' s x cur_idx);
   Pair a b a0 b0 -> Pair0 a b (to_flat' a a0 cur_idx)
    (to_flat' b b0 cur_idx);
   Abs s d f -> Abs0 s cur_idx d (to_flat' d (f cur_idx) (succ cur_idx))}

from_flat :: Type -> Expr1 -> (T (SigT Type a1)) -> Expr Ident a1
from_flat _ e x =
  case e of {
   Var0 t v ->
    case bind (find v x) (\tv -> try_transport (projT1 tv) t (projT2 tv)) of {
     Prelude.Just v0 -> Var t v0;
     Prelude.Nothing -> eRROR (default1 t)};
   TT0 -> TT;
   AppIdent0 s d idc args ->
    let {args' = \_ -> from_flat s args} in AppIdent s d idc (args' __ x);
   App0 s d f x0 ->
    let {f' = \_ -> from_flat (Arrow s d) f} in
    let {x' = \_ -> from_flat s x0} in App s d (f' __ x) (x' __ x);
   Pair0 a b a0 b0 ->
    let {a' = \_ -> from_flat a a0} in
    let {b' = \_ -> from_flat b b0} in Pair a b (a' __ x) (b' __ x);
   Abs0 s cur_idx d f ->
    let {f' = \_ -> from_flat d f} in
    Abs s d (\v -> f' __ (add cur_idx (ExistT s v) x))}

to_flat :: Type -> (Expr Ident Key) -> Expr1
to_flat t e =
  to_flat' t e XH

toFlat :: Type -> (Expr0 Ident) -> Expr1
toFlat t e =
  to_flat t (unsafeCoerce e __)

fromFlat :: Type -> Expr1 -> Expr Ident a1
fromFlat t e =
  from_flat t e empty

type Value var = Any

reify :: Type -> (Value a1) -> Expr Ident a1
reify t =
  case t of {
   Type_primitive p -> (\v ->
    case unsafeCoerce v of {
     Prelude.Left e -> e;
     Prelude.Right v0 -> AppIdent (Type_primitive Unit) (Type_primitive p)
      (Primitive0 p v0) TT});
   Prod a b -> (\v ->
    case unsafeCoerce v of {
     Prelude.Left e -> e;
     Prelude.Right p ->
      case p of {
       (,) a0 b0 -> Pair a b (reify a a0) (reify b b0)}});
   Arrow s d -> (\f -> Abs s d (\v ->
    reify d (unsafeCoerce f (reflect s (Var s v)))));
   List _ -> unsafeCoerce id}

reflect :: Type -> (Expr Ident a1) -> Value a1
reflect t =
  case t of {
   Type_primitive _ -> (\v -> unsafeCoerce (Prelude.Left v));
   Prod a b -> (\v ->
    case invert_Pair a b v of {
     Prelude.Just p ->
      case p of {
       (,) a0 b0 ->
        unsafeCoerce (Prelude.Right ((,) (reflect a a0) (reflect b b0)))};
     Prelude.Nothing -> unsafeCoerce (Prelude.Left v)});
   Arrow s d -> (\f ->
    unsafeCoerce (\v -> reflect d (App s d f (reify s v))));
   List _ -> unsafeCoerce id}

red'_ident2 :: Type -> Type -> Ident -> (Value a1) -> Value a1
red'_ident2 _ _ idc =
  case idc of {
   Primitive0 _ v -> (\_ -> unsafeCoerce (Prelude.Right v));
   Let_In tx tC -> (\v ->
    reflect tC (AppIdent (Prod tx (Arrow tx tC)) tC (Let_In tx tC)
      (reify (Prod tx (Arrow tx tC)) v)));
   Nat_succ -> (\v ->
    case unsafeCoerce v of {
     Prelude.Left _ ->
      reflect (Type_primitive Nat0) (AppIdent (Type_primitive Nat0)
        (Type_primitive Nat0) Nat_succ (reify (Type_primitive Nat0) v));
     Prelude.Right v0 -> unsafeCoerce (Prelude.Right (S v0))});
   Nat_add -> (\v ->
    reflect (Type_primitive Nat0) (AppIdent (Prod (Type_primitive Nat0)
      (Type_primitive Nat0)) (Type_primitive Nat0) Nat_add
      (reify (Prod (Type_primitive Nat0) (Type_primitive Nat0)) v)));
   Nat_sub -> (\v ->
    reflect (Type_primitive Nat0) (AppIdent (Prod (Type_primitive Nat0)
      (Type_primitive Nat0)) (Type_primitive Nat0) Nat_sub
      (reify (Prod (Type_primitive Nat0) (Type_primitive Nat0)) v)));
   Nat_mul -> (\v ->
    reflect (Type_primitive Nat0) (AppIdent (Prod (Type_primitive Nat0)
      (Type_primitive Nat0)) (Type_primitive Nat0) Nat_mul
      (reify (Prod (Type_primitive Nat0) (Type_primitive Nat0)) v)));
   Nat_max -> (\v ->
    reflect (Type_primitive Nat0) (AppIdent (Prod (Type_primitive Nat0)
      (Type_primitive Nat0)) (Type_primitive Nat0) Nat_max
      (reify (Prod (Type_primitive Nat0) (Type_primitive Nat0)) v)));
   Nil t -> (\v ->
    reflect (List t) (AppIdent (Type_primitive Unit) (List t) (Nil t)
      (reify (Type_primitive Unit) v)));
   Cons t -> (\v ->
    reflect (List t) (AppIdent (Prod t (List t)) (List t) (Cons t)
      (reify (Prod t (List t)) v)));
   Fst a b -> (\v ->
    case unsafeCoerce v of {
     Prelude.Left _ ->
      reflect a (AppIdent (Prod a b) a (Fst a b) (reify (Prod a b) v));
     Prelude.Right p -> case p of {
                         (,) a0 _ -> a0}});
   Snd a b -> (\v ->
    case unsafeCoerce v of {
     Prelude.Left _ ->
      reflect b (AppIdent (Prod a b) b (Snd a b) (reify (Prod a b) v));
     Prelude.Right p -> case p of {
                         (,) _ b0 -> b0}});
   Bool_rect t -> (\v ->
    reflect t (AppIdent (Prod (Prod (Arrow (Type_primitive Unit) t) (Arrow
      (Type_primitive Unit) t)) (Type_primitive Bool)) t (Bool_rect t)
      (reify (Prod (Prod (Arrow (Type_primitive Unit) t) (Arrow
        (Type_primitive Unit) t)) (Type_primitive Bool)) v)));
   Nat_rect p ->
    let {idc0 = Nat_rect p} in
    (\v ->
    case unsafeCoerce v of {
     Prelude.Left _ ->
      reflect p (AppIdent (Prod (Prod (Arrow (Type_primitive Unit) p) (Arrow
        (Prod (Type_primitive Nat0) p) p)) (Type_primitive Nat0)) p idc0
        (reify (Prod (Prod (Arrow (Type_primitive Unit) p) (Arrow (Prod
          (Type_primitive Nat0) p) p)) (Type_primitive Nat0)) v));
     Prelude.Right p0 ->
      case p0 of {
       (,) s s0 ->
        case s of {
         Prelude.Left _ ->
          reflect p (AppIdent (Prod (Prod (Arrow (Type_primitive Unit) p)
            (Arrow (Prod (Type_primitive Nat0) p) p)) (Type_primitive Nat0))
            p idc0
            (reify (Prod (Prod (Arrow (Type_primitive Unit) p) (Arrow (Prod
              (Type_primitive Nat0) p) p)) (Type_primitive Nat0)) v));
         Prelude.Right p1 ->
          case p1 of {
           (,) n c ->
            case s0 of {
             Prelude.Left _ ->
              reflect p (AppIdent (Prod (Prod (Arrow (Type_primitive Unit) p)
                (Arrow (Prod (Type_primitive Nat0) p) p)) (Type_primitive
                Nat0)) p idc0
                (reify (Prod (Prod (Arrow (Type_primitive Unit) p) (Arrow
                  (Prod (Type_primitive Nat0) p) p)) (Type_primitive Nat0))
                  v));
             Prelude.Right n0 ->
              nat_rect (n (Prelude.Right ())) (\n' v0 ->
                c (Prelude.Right ((,) (Prelude.Right n') v0))) n0}}}}});
   Pred -> (\v ->
    reflect (Type_primitive Nat0) (AppIdent (Type_primitive Nat0)
      (Type_primitive Nat0) Pred (reify (Type_primitive Nat0) v)));
   List_rect a p -> (\v ->
    reflect p (AppIdent (Prod (Prod (Arrow (Type_primitive Unit) p) (Arrow
      (Prod (Prod a (List a)) (Arrow (Type_primitive Unit) p)) p)) (List a))
      p (List_rect a p)
      (reify (Prod (Prod (Arrow (Type_primitive Unit) p) (Arrow (Prod (Prod a
        (List a)) (Arrow (Type_primitive Unit) p)) p)) (List a)) v)));
   List_nth_default t -> (\v ->
    reflect t (AppIdent (Prod (Prod t (List t)) (Type_primitive Nat0)) t
      (List_nth_default t)
      (reify (Prod (Prod t (List t)) (Type_primitive Nat0)) v)));
   List_nth_default_concrete t d n -> (\v ->
    reflect (Type_primitive t) (AppIdent (List (Type_primitive t))
      (Type_primitive t) (List_nth_default_concrete t d n)
      (reify (List (Type_primitive t)) v)));
   Z_shiftr offset -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Type_primitive Z1) (Type_primitive
      Z1) (Z_shiftr offset) (reify (Type_primitive Z1) v)));
   Z_shiftl offset -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Type_primitive Z1) (Type_primitive
      Z1) (Z_shiftl offset) (reify (Type_primitive Z1) v)));
   Z_land mask -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Type_primitive Z1) (Type_primitive
      Z1) (Z_land mask) (reify (Type_primitive Z1) v)));
   Z_add -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Z1) Z_add
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_mul -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Z1) Z_mul
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_pow -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Z1) Z_pow
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_sub -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Z1) Z_sub
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_opp -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Type_primitive Z1) (Type_primitive
      Z1) Z_opp (reify (Type_primitive Z1) v)));
   Z_div -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Z1) Z_div
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_modulo -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Z1) Z_modulo
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_eqb -> (\v ->
    reflect (Type_primitive Bool) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Bool) Z_eqb
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_leb -> (\v ->
    reflect (Type_primitive Bool) (AppIdent (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Type_primitive Bool) Z_leb
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)));
   Z_of_nat -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Type_primitive Nat0)
      (Type_primitive Z1) Z_of_nat (reify (Type_primitive Nat0) v)));
   Z_cast range -> (\v ->
    reflect (Type_primitive Z1) (AppIdent (Type_primitive Z1) (Type_primitive
      Z1) (Z_cast range) (reify (Type_primitive Z1) v)));
   Z_cast2 range -> (\v ->
    reflect (Prod (Type_primitive Z1) (Type_primitive Z1)) (AppIdent (Prod
      (Type_primitive Z1) (Type_primitive Z1)) (Prod (Type_primitive Z1)
      (Type_primitive Z1)) (Z_cast2 range)
      (reify (Prod (Type_primitive Z1) (Type_primitive Z1)) v)))}

red' :: (Type -> Type -> Ident -> (Value a1) -> Value a1) -> Type -> (Expr
        Ident (Value a1)) -> Value a1
red' red'_ident _ e =
  case e of {
   Var _ v -> v;
   TT -> unsafeCoerce (Prelude.Right ());
   AppIdent s d idc args -> red'_ident s d idc (red' red'_ident s args);
   App s d f x ->
    unsafeCoerce red' red'_ident (Arrow s d) f (red' red'_ident s x);
   Pair a b a0 b0 ->
    unsafeCoerce (Prelude.Right ((,) (red' red'_ident a a0)
      (red' red'_ident b b0)));
   Abs _ d f -> unsafeCoerce (\v -> red' red'_ident d (f v))}

red2 :: Type -> (Expr0 Ident) -> Expr Ident a1
red2 t e =
  reify t (red' red'_ident2 t (e __))

k'' :: Expr1
k'' =
  Abs0 (Type_primitive Unit) XH (Type_primitive Z1) (App0 (Arrow (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1) (AppIdent0
    (Prod (Prod (Arrow (Type_primitive Unit) (Arrow (Arrow (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1))) (Arrow
    (Prod (Type_primitive Nat0) (Arrow (Arrow (Arrow (Prod (Type_primitive
    Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive
    Z1)) (Type_primitive Z1)) (Type_primitive Z1))) (Arrow (Arrow (Arrow
    (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive
    Z1))) (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1))))
    (Type_primitive Nat0)) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0)
    (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1)) (Nat_rect (Arrow (Arrow (Arrow
    (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive
    Z1))) (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1)))
    (Pair0 (Prod (Arrow (Type_primitive Unit) (Arrow (Arrow (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1))) (Arrow
    (Prod (Type_primitive Nat0) (Arrow (Arrow (Arrow (Prod (Type_primitive
    Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive
    Z1)) (Type_primitive Z1)) (Type_primitive Z1))) (Arrow (Arrow (Arrow
    (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive
    Z1))) (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1))))
    (Type_primitive Nat0) (Pair0 (Arrow (Type_primitive Unit) (Arrow (Arrow
    (Arrow (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Type_primitive Z1)) (Type_primitive Z1))
    (Type_primitive Z1))) (Arrow (Prod (Type_primitive Nat0) (Arrow (Arrow
    (Arrow (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Type_primitive Z1)) (Type_primitive Z1))
    (Type_primitive Z1))) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0)
    (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1))) (Abs0 (Type_primitive Unit)
    (XO XH) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1)) (Abs0 (Arrow (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1)) (XI XH) (Type_primitive Z1)
    (App0 (Arrow (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Type_primitive Z1)) (Type_primitive Z1) (Var0
    (Arrow (Arrow (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Type_primitive Z1)) (Type_primitive Z1)) (XI XH))
    (Abs0 (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (XO (XO XH)) (Type_primitive Z1) (App0
    (Type_primitive Z1) (Type_primitive Z1) (AppIdent0 (Prod (Type_primitive
    Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (Snd (Type_primitive Nat0)
    (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Var0 (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (XO (XO XH)))) (AppIdent0 (Type_primitive Unit) (Type_primitive Z1)
    (Primitive0 Z1 (unsafeCoerce Z0)) TT0)))))) (Abs0 (Prod (Type_primitive
    Nat0) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1))) (XO XH) (Arrow (Arrow (Arrow
    (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive
    Z1))) (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1))
    (Abs0 (Arrow (Arrow (Prod (Type_primitive Nat0) (Arrow (Type_primitive
    Z1) (Type_primitive Z1))) (Type_primitive Z1)) (Type_primitive Z1)) (XI
    XH) (Type_primitive Z1) (App0 (Arrow (Arrow (Prod (Type_primitive Nat0)
    (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1) (AppIdent0 (Prod (Type_primitive
    Nat0) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1))) (Arrow (Arrow (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1)) (Type_primitive Z1)) (Snd
    (Type_primitive Nat0) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0)
    (Arrow (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1))) (Var0 (Prod (Type_primitive
    Nat0) (Arrow (Arrow (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1))
    (Type_primitive Z1)) (Type_primitive Z1))) (XO XH))) (Abs0 (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (XO (XO XH)) (Type_primitive Z1) (App0 (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1) (Var0 (Arrow (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (Type_primitive Z1)) (XI XH)) (Abs0 (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (XI (XO XH)) (Type_primitive Z1) (App0 (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (Type_primitive Z1) (AppIdent0 (Prod (Prod (Arrow
    (Type_primitive Unit) (Arrow (Arrow (Type_primitive Z1) (Type_primitive
    Z1)) (Type_primitive Z1))) (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Arrow (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1)))
    (Arrow (Arrow (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive
    Z1)))) (Type_primitive Nat0)) (Arrow (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (Type_primitive Z1)) (Nat_rect (Arrow (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1))) (Pair0
    (Prod (Arrow (Type_primitive Unit) (Arrow (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (Type_primitive Z1))) (Arrow (Prod (Type_primitive
    Nat0) (Arrow (Arrow (Type_primitive Z1) (Type_primitive Z1))
    (Type_primitive Z1))) (Arrow (Arrow (Type_primitive Z1) (Type_primitive
    Z1)) (Type_primitive Z1)))) (Type_primitive Nat0) (Pair0 (Arrow
    (Type_primitive Unit) (Arrow (Arrow (Type_primitive Z1) (Type_primitive
    Z1)) (Type_primitive Z1))) (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Arrow (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1)))
    (Arrow (Arrow (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive
    Z1))) (Abs0 (Type_primitive Unit) (XO (XI XH)) (Arrow (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1)) (Abs0
    (Arrow (Type_primitive Z1) (Type_primitive Z1)) (XI (XI XH))
    (Type_primitive Z1) (App0 (Type_primitive Z1) (Type_primitive Z1) (Var0
    (Arrow (Type_primitive Z1) (Type_primitive Z1)) (XI (XI XH))) (AppIdent0
    (Type_primitive Unit) (Type_primitive Z1) (Primitive0 Z1
    (unsafeCoerce Z0)) TT0)))) (Abs0 (Prod (Type_primitive Nat0) (Arrow
    (Arrow (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1))) (XO
    (XI XH)) (Arrow (Arrow (Type_primitive Z1) (Type_primitive Z1))
    (Type_primitive Z1)) (Abs0 (Arrow (Type_primitive Z1) (Type_primitive
    Z1)) (XI (XI XH)) (Type_primitive Z1) (App0 (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (Type_primitive Z1) (AppIdent0 (Prod (Type_primitive
    Nat0) (Arrow (Arrow (Type_primitive Z1) (Type_primitive Z1))
    (Type_primitive Z1))) (Arrow (Arrow (Type_primitive Z1) (Type_primitive
    Z1)) (Type_primitive Z1)) (Snd (Type_primitive Nat0) (Arrow (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1))) (Var0
    (Prod (Type_primitive Nat0) (Arrow (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (Type_primitive Z1))) (XO (XI XH)))) (Abs0
    (Type_primitive Z1) (XO (XO (XO XH))) (Type_primitive Z1) (App0 (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1) (Var0 (Arrow (Prod (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Z1)) (XO (XO
    XH))) (Pair0 (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (AppIdent0 (Prod (Type_primitive Nat0) (Arrow (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1)))
    (Type_primitive Nat0) (Fst (Type_primitive Nat0) (Arrow (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (Type_primitive Z1))) (Var0
    (Prod (Type_primitive Nat0) (Arrow (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (Type_primitive Z1))) (XO (XI XH)))) (Abs0
    (Type_primitive Z1) (XI (XO (XO XH))) (Type_primitive Z1) (App0
    (Type_primitive Z1) (Type_primitive Z1) (Var0 (Arrow (Type_primitive Z1)
    (Type_primitive Z1)) (XI (XI XH))) (Var0 (Type_primitive Z1) (XI (XO (XO
    XH))))))))))))) (AppIdent0 (Prod (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1))) (Type_primitive Nat0) (Fst
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Var0 (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (XI (XO XH)))))) (Abs0 (Type_primitive Z1) (XO (XI
    XH)) (Type_primitive Z1) (App0 (Type_primitive Z1) (Type_primitive Z1)
    (AppIdent0 (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Arrow (Type_primitive Z1) (Type_primitive Z1))
    (Snd (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive
    Z1))) (Var0 (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (XI (XO XH)))) (Var0 (Type_primitive Z1) (XO (XI
    XH))))))))))))) (AppIdent0 (Type_primitive Unit) (Type_primitive Nat0)
    (Primitive0 Nat0
    (unsafeCoerce (S (S (S (S (S (S (S (S (S (S O)))))))))))) TT0))) (Abs0
    (Arrow (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Type_primitive Z1)) (XO XH) (Type_primitive Z1)
    (App0 (Prod (Type_primitive Nat0) (Arrow (Type_primitive Z1)
    (Type_primitive Z1))) (Type_primitive Z1) (Var0 (Arrow (Prod
    (Type_primitive Nat0) (Arrow (Type_primitive Z1) (Type_primitive Z1)))
    (Type_primitive Z1)) (XO XH)) (Pair0 (Type_primitive Nat0) (Arrow
    (Type_primitive Z1) (Type_primitive Z1)) (AppIdent0 (Type_primitive Unit)
    (Type_primitive Nat0) (Primitive0 Nat0
    (unsafeCoerce (S (S (S (S (S (S (S (S (S (S O)))))))))))) TT0) (Abs0
    (Type_primitive Z1) (XI XH) (Type_primitive Z1) (Var0 (Type_primitive Z1)
    (XI XH)))))))

toFlatFFromFlat_Slow2 :: () -> Expr1
toFlatFFromFlat_Slow2 _ =
  toFlat (Arrow (Type_primitive Unit) (Type_primitive Z1)) (\_ ->
    red2 (Arrow (Type_primitive Unit) (Type_primitive Z1)) (\_ ->
      fromFlat (Arrow (Type_primitive Unit) (Type_primitive Z1)) k''))

return :: a1 -> GHC.Base.IO ()
return = \ v -> return v GHC.Base.>> return ()

main :: GHC.Base.IO ()
main =
  return (toFlatFFromFlat_Slow2 ())


