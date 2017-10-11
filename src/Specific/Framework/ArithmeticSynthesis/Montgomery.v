Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Util.Sigma.Lift.
Require Import Coq.ZArith.BinInt.
Require Import Coq.PArith.BinPos.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Arithmetic.Saturated.UniformWeightInstances.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.Tactics.CacheTerm.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Local Definition sig_by_eq {A P} (x : { a : A | P a }) (a : A) (H : a = proj1_sig x)
  : { a : A | P a }.
Proof.
  exists a; subst; exact (proj2_sig x).
Defined.

Section with_args.
  Context (wt : nat -> Z)
          (r : positive)
          (sz : nat)
          (m : positive)
          (m_enc : Z^sz)
          (r' : Z)
          (r'_correct : ((Z.pos r * r') mod (Z.pos m) = 1)%Z)
          (m' : Z)
          (m'_correct : ((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r)%Z)
          (m_enc_correct_montgomery : Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc)
          (r'_pow_correct : ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1)%Z)
          (* computable *)
          (r_big : Z.pos r > 1)
          (m_big : 1 < Z.pos m)
          (m_enc_small : small (Z.pos r) m_enc)
          (map_m_enc : Tuple.map (Z.land (Z.pos r - 1)) m_enc = m_enc).

  Local Ltac t_fin :=
    repeat match goal with
           | _ => assumption
           | [ |- ?x = ?x ] => reflexivity
           | [ |- and _ _ ] => split
           | [ |- (0 <= MontgomeryAPI.eval (Z.pos r) _)%Z ] => apply MontgomeryAPI.eval_small
           | _ => rewrite <- !m_enc_correct_montgomery
           | _ => rewrite !r'_correct
           | _ => rewrite !Z.mod_1_l by assumption; reflexivity
           | _ => rewrite !(Z.mul_comm m' (Z.pos m))
           | _ => lia
           end.


  Local Definition mul'_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | forall (A B : Z^sz),
          small (Z.pos r) A -> small (Z.pos r) B ->
          let eval := MontgomeryAPI.eval (Z.pos r) in
          (small (Z.pos r) (f A B)
           /\ (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)
           /\ (eval (f A B) mod Z.pos m
               = (eval A * eval B * r'^(Z.of_nat sz)) mod Z.pos m))%Z
      }.
  Proof.
    exists (fun A B => redc (r:=r)(R_numlimbs:=sz) m_enc A B m').
    abstract (
        intros;
        split; [ | split ];
        [ apply small_redc with (ri:=r') | apply redc_bound_N with (ri:=r') | rewrite !m_enc_correct_montgomery; apply redc_mod_N ];
        t_fin
      ).
  Defined.

  Import ModularArithmetic.

  Definition montgomery_to_F_gen (v : Z) : F m
    := (F.of_Z m v * F.of_Z m (r'^Z.of_nat sz)%Z)%F.

  Local Definition mul_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        (forall (A : Z^sz) (_ : small (Z.pos r) A)
                (B : Z^sz) (_ : small (Z.pos r) B),
            montgomery_to_F_gen (eval (f A B))
            = (montgomery_to_F_gen (eval A) * montgomery_to_F_gen (eval B))%F)
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)%Z) }.
  Proof.
    exists (proj1_sig mul'_gen).
    abstract (
        split; intros A Asm B Bsm;
        pose proof (proj2_sig mul'_gen A B Asm Bsm) as H;
        cbv zeta in *;
        try solve [ destruct_head'_and; assumption ];
        rewrite ModularArithmeticTheorems.F.eq_of_Z_iff in H;
        unfold montgomery_to_F_gen;
        destruct H as [H1 [H2 H3]];
        rewrite H3;
        rewrite <- !ModularArithmeticTheorems.F.of_Z_mul;
        f_equal; nia
      ).
  Defined.

  Local Definition add_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) + montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc)))%Z }.
  Proof.
    exists (fun A B => add (r:=r)(R_numlimbs:=sz) m_enc A B).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_add;
        rewrite <- ?Z.mul_add_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_add_mod_N; pull_Zmod
        | apply add_bound ];
        t_fin
      ).
  Defined.

  Local Definition sub_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) - montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc)))%Z }.
  Proof.
    exists (fun A B => sub (r:=r) (R_numlimbs:=sz) m_enc A B).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_sub;
        rewrite <- ?Z.mul_sub_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_sub_mod_N; pull_Zmod
        | apply sub_bound ];
        t_fin
      ).
  Defined.

  Local Definition opp_ext_gen
    : { f:Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A),
             (eval A < eval m_enc
              -> montgomery_to_F_gen (eval (f A))
                 = (F.opp (montgomery_to_F_gen (eval A)))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc)))%Z }.
  Proof.
    exists (fun A => opp (r:=r) (R_numlimbs:=sz) m_enc A).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?F_of_Z_opp;
        rewrite <- ?Z.mul_opp_l;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_opp_mod_N; pull_Zmod
        | apply opp_bound ];
        t_fin
      ).
  Defined.

  Local Definition nonzero_ext_gen
    : { f:Z^sz -> Z
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        forall (A : Z^sz) (_ : small (Z.pos r) A),
          (eval A < eval m_enc
           -> f A = 0 <-> (montgomery_to_F_gen (eval A) = F.of_Z m 0))%Z }.
  Proof.
    exists (fun A => nonzero (R_numlimbs:=sz) A).
    abstract (
        intros eval A H **; rewrite (@eval_nonzero r) by (eassumption || reflexivity);
        subst eval;
        unfold montgomery_to_F_gen, uweight in *; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul;
        rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery;
        let H := fresh in
        split; intro H;
        [ rewrite H; autorewrite with zsimplify_const; reflexivity
        | cut ((MontgomeryAPI.eval (Z.pos r) A * (r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz)) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 0)%Z;
          [ rewrite Z.mul_mod, r'_pow_correct; autorewrite with zsimplify_const; pull_Zmod; [ | t_fin ];
            rewrite Z.mod_small; [ trivial | split; try assumption; apply MontgomeryAPI.eval_small; try assumption; lia ]
          | rewrite Z.mul_assoc, Z.mul_mod, H by t_fin; autorewrite with zsimplify_const; reflexivity ] ]
      ).
  Defined.
End with_args.

Local Definition for_assumptions
  := (mul_ext_gen, add_ext_gen, sub_ext_gen, opp_ext_gen, nonzero_ext_gen).

Print Assumptions for_assumptions.

Local Ltac if_montgomery montgomery tac :=
  lazymatch (eval compute in montgomery) with
  | true => tac
  | false => exact I
  end.
Local Ltac if_montgomery_for_notation montgomery t :=
  lazymatch (eval compute in montgomery) with
  | true => exact t
  | false => exact True
  end.
Local Notation if_montgomery montgomery t :=
  (match montgomery with
   | true => t
   | false => True
   end)
    (only parsing).

Ltac solve_m' montgomery modinv_fuel m r := (* (-m)⁻¹ mod r *)
  if_montgomery montgomery ltac:(idtac; solve_modinv modinv_fuel (-Z.pos m) (Z.pos r)).
Ltac solve_r' montgomery modinv_fuel m r := (* r⁻¹ mod m *)
  if_montgomery montgomery ltac:(idtac; solve_modinv modinv_fuel (Z.pos r) (Z.pos m)).

Notation m'_correct_prop montgomery m m' r :=
  (if_montgomery montgomery ((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r))
    (only parsing).
Ltac solve_m'_correct :=
  lazymatch goal with
  | [ |- m'_correct_prop ?montgomery ?m ?m' ?r ]
    => vm_compute; constructor
  end.
Notation r'_correct_prop montgomery m r r' :=
  (if_montgomery montgomery ((Z.pos r * r') mod (Z.pos m) = 1))
    (only parsing).
Ltac solve_r'_correct :=
  lazymatch goal with
  | [ |- r'_correct_prop ?montgomery ?m ?r ?r' ]
    => vm_compute; constructor
  end.

Notation m_enc_correct_montgomery_prop montgomery m sz r m_enc :=
  (if_montgomery montgomery (Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc))
    (only parsing).

Ltac solve_m_enc_correct_montgomery :=
  lazymatch goal with
  | [ |- m_enc_correct_montgomery_prop ?montgomery ?m ?sz ?r ?m_enc ]
    => vm_compute; constructor
  end.

Notation r'_pow_correct_prop montgomery r' sz r m_enc :=
  (if_montgomery montgomery ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1))
    (only parsing).

Ltac solve_r'_pow_correct :=
  lazymatch goal with
  | [ |- r'_pow_correct_prop ?montgomery ?r' ?sz ?r ?m_enc ]
    => vm_compute; constructor
  end.

Ltac solve_montgomery_to_F sz m r' :=
  lazymatch type of r' with
  | Z
    => let v := (eval cbv [montgomery_to_F_gen] in (montgomery_to_F_gen sz m r')) in
       exact v
  | True
    => exact I
  end.

Notation r_big_prop r :=
  (Z.pos r > 1)
    (only parsing).

Ltac solve_r_big :=
  lazymatch goal with
  | [ |- r_big_prop ?r ]
    => vm_compute; reflexivity
  end.

Notation m_big_prop m :=
  (1 < Z.pos m)
    (only parsing).

Ltac solve_m_big :=
  lazymatch goal with
  | [ |- m_big_prop ?m ]
    => vm_compute; reflexivity
  end.

Notation m_enc_small_prop montgomery sz r m_enc :=
  (if_montgomery montgomery (small (n:=sz) (Z.pos r) m_enc))
    (only parsing).

Ltac solve_m_enc_small :=
  lazymatch goal with
  | [ |- m_enc_small_prop ?montgomery ?sz ?r ?m_enc ]
    => if_montgomery
         montgomery
         ltac:(pose (small_Decidable (n:=sz) (bound:=Z.pos r)); vm_decide_no_check)
  end.

Notation map_m_enc_prop montgomery sz r m_enc :=
  (if_montgomery montgomery (Tuple.map (n:=sz) (Z.land (Z.pos r - 1)) m_enc = m_enc))
    (only parsing).

Ltac solve_map_m_enc :=
  lazymatch goal with
  | [ |- map_m_enc_prop ?montgomery ?sz ?r ?m_enc ]
    => if_montgomery montgomery
                     ltac:(pose (@dec_eq_prod); pose dec_eq_Z; vm_decide_no_check)
  end.

Ltac internal_solve_sig_by_eq ty sigl tac_eq id :=
  refine (_ : ty);
  eapply (@sig_by_eq _ _ sigl _); tac_eq ().

Import ModularArithmetic.

Local Ltac reduce_eq _ :=
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp runtime_lor Let_In].

Notation mul_ext_type montgomery sz r montgomery_to_F m_enc :=
  (if_montgomery
     montgomery
     { f:Z^sz -> Z^sz -> Z^sz
     | let eval := MontgomeryAPI.eval (Z.pos r) in
       (forall (A : Z^sz) (_ : small (Z.pos r) A)
               (B : Z^sz) (_ : small (Z.pos r) B),
           montgomery_to_F%F (eval (f A B))
           = F.mul (montgomery_to_F (eval A)) (montgomery_to_F (eval B)))
       /\ (forall (A' : Z^sz) (_ : small (Z.pos r) A')
                  (B' : Z^sz) (_ : small (Z.pos r) B'),
              (eval B' < eval m_enc -> 0 <= eval (f A' B') < eval m_enc)%Z) })
    (only parsing).
Ltac solve_mul_ext m r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small :=
  lazymatch goal with
  | [ |- mul_ext_type ?montgomery ?sz ?r ?montgomery_to_F ?m_enc ]
    => if_montgomery
         montgomery
         ltac:(idtac;
               internal_solve_sig_by_eq
                 (@mul_ext_gen r sz m m_enc r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small))
  end.

Notation add_ext_type montgomery sz r montgomery_to_F m_enc :=
  (if_montgomery
     montgomery
     { f:Z^sz -> Z^sz -> Z^sz
     | let eval := MontgomeryAPI.eval (Z.pos r) in
       ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                (B : Z^sz) (_ : small (Z.pos r) B),
            (eval A < eval m_enc%Z
             -> eval B < eval m_enc%Z
             -> montgomery_to_F%F (eval (f A B))
                = F.add (montgomery_to_F (eval A)) (montgomery_to_F (eval B))))
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               (eval A < eval m_enc
                -> eval B < eval m_enc
                -> 0 <= eval (f A B) < eval m_enc)%Z)) })
    (only parsing).
Ltac solve_add_ext m r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small :=
  lazymatch goal with
  | [ |- add_ext_type ?montgomery ?sz ?r ?montgomery_to_F ?m_enc ]
    => if_montgomery
         montgomery
         ltac:(idtac;
               internal_solve_sig_by_eq
                 (@add_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_big m_enc_small))
  end.


Notation sub_ext_type montgomery sz r montgomery_to_F m_enc :=
  (if_montgomery
     montgomery
     { f:Z^sz -> Z^sz -> Z^sz
     | let eval := MontgomeryAPI.eval (Z.pos r) in
       ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                (B : Z^sz) (_ : small (Z.pos r) B),
            (eval A < eval m_enc%Z
             -> eval B < eval m_enc%Z
             -> montgomery_to_F%F (eval (f A B))
                = F.sub (montgomery_to_F (eval A)) (montgomery_to_F (eval B))))
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               (eval A < eval m_enc
                -> eval B < eval m_enc
                -> 0 <= eval (f A B) < eval m_enc)%Z)) })
    (only parsing).

Ltac solve_sub_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F :=
  lazymatch goal with
  | [ |- sub_ext_type ?montgomery ?sz ?r ?montgomery_to_F ?m_enc ]
    => if_montgomery
         montgomery
         ltac:(idtac;
               internal_solve_sig_by_eq
                 (@sub_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc))
  end.

Notation opp_ext_type montgomery sz r montgomery_to_F m_enc :=
  (if_montgomery
     montgomery
     { f:Z^sz -> Z^sz
     | let eval := MontgomeryAPI.eval (Z.pos r) in
       ((forall (A : Z^sz) (_ : small (Z.pos r) A),
            (eval A < eval m_enc%Z
             -> montgomery_to_F%F (eval (f A))
                = (F.opp (montgomery_to_F (eval A)))%F))
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
               ((eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc))%Z)) })
    (only parsing).
Ltac solve_opp_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F opp_ext :=
 lazymatch goal with
  | [ |- opp_ext_type ?montgomery ?sz ?r ?montgomery_to_F ?m_enc ]
    => if_montgomery
         montgomery
         ltac:(idtac;
               internal_solve_sig_by_eq
                 (@opp_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc))
 end.

Ltac solve_nonzero_ext r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big montgomery_to_F nonzero_ext :=
  internal_solve_sig_by_eq
    { f:Z^sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }
    (@nonzero_ext_gen r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big)
    ltac:(fun _ => reduce_eq (); reflexivity)
           nonzero_ext.

Notation mul_sig_type r sz montgomery_to_F :=
  { f:Z^sz -> Z^sz -> Z^sz
  | let eval := MontgomeryAPI.eval (Z.pos r) in
    forall (A : Z^sz) (_ : small (Z.pos r) A)
           (B : Z^sz) (_ : small (Z.pos r) B),
      montgomery_to_F%F (eval (f A B))
      = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F }
    (only parsing).

Ltac solve_mul_sig mul_ext :=
  lazymatch goal with
  | [ |- mul_sig_type ?r ?sz ?montgomery_to_F ]
    => idtac;
       let v := (eval cbv [proj1_sig mul_ext_gen mul_ext sig_by_eq] in (proj1_sig mul_ext)) in
       (exists v);
       abstract apply (proj2_sig mul_ext)
  end.

Notation mul_bounded_prop r sz m_enc mul_sig :=
  (let eval := MontgomeryAPI.eval (Z.pos r) in
   forall (A : Z^sz) (_ : small (Z.pos r) A)
          (B : Z^sz) (_ : small (Z.pos r) B),
     (eval B < eval m_enc
      -> 0 <= eval (proj1_sig mul_sig A B) < eval m_enc)%Z)
    (only parsing).

Ltac solve_mul_bounded montgomery_to_F mul_ext :=
  lazymatch goal with
  | [ |- mul_bounded_prop ?montgomery ?r ?sz ?m_enc ?mul_sig ]
    => apply (proj2_sig mul_ext)
  end.


Notation add_sig_type r sz m_enc montgomery_to_F :=
  { f:Z^sz -> Z^sz -> Z^sz
  | let eval := MontgomeryAPI.eval (Z.pos r) in
    forall (A : Z^sz) (_ : small (Z.pos r) A)
           (B : Z^sz) (_ : small (Z.pos r) B),
      (eval A < eval m_enc
       -> eval B < eval m_enc
       -> montgomery_to_F%F (eval (f A B))
          = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F)%Z }
    (only parsing).


Ltac solve_add_sig add_ext :=
  lazymatch goal with
  | [ |- add_sig_type ?r ?sz ?m_enc ?montgomery_to_F ]
    => idtac;
       let v := (eval cbv [proj1_sig add_ext_gen add_ext sig_by_eq] in (proj1_sig add_ext)) in
       (exists v);
       abstract apply (proj2_sig add_ext)
  end.

Notation add_bounded_prop r sz m_enc add_sig :=
  (let eval := MontgomeryAPI.eval (Z.pos r)%Z in
   (forall (A : Z^sz) (_ : small (Z.pos r) A)
           (B : Z^sz) (_ : small (Z.pos r) B),
       (eval A < eval m_enc
        -> eval B < eval m_enc
        -> 0 <= eval (proj1_sig add_sig A B) < eval m_enc))%Z)
    (only parsing).

Ltac solve_add_bounded montgomery_to_F add_ext :=
  lazymatch goal with
  | [ |- add_bounded_prop ?montgomery ?r ?sz ?m_enc ?add_sig ]
    => apply (proj2_sig add_ext)
  end.


Notation sub_sig_type r sz m_enc montgomery_to_F :=
  { f:Z^sz -> Z^sz -> Z^sz
  | let eval := MontgomeryAPI.eval (Z.pos r) in
    forall (A : Z^sz) (_ : small (Z.pos r) A)
           (B : Z^sz) (_ : small (Z.pos r) B),
      (eval A < eval m_enc
       -> eval B < eval m_enc
       -> montgomery_to_F%F (eval (f A B))
          = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F)%Z }
    (only parsing).


Ltac solve_sub_sig sub_ext :=
  lazymatch goal with
  | [ |- sub_sig_type ?r ?sz ?m_enc ?montgomery_to_F ]
    => idtac;
       let v := (eval cbv [proj1_sig sub_ext_gen sub_ext sig_by_eq] in (proj1_sig sub_ext)) in
       (exists v);
       abstract apply (proj2_sig sub_ext)
  end.

Notation sub_bounded_prop r sz m_enc sub_sig :=
  (let eval := MontgomeryAPI.eval (Z.pos r)%Z in
   (forall (A : Z^sz) (_ : small (Z.pos r) A)
           (B : Z^sz) (_ : small (Z.pos r) B),
       (eval A < eval m_enc
        -> eval B < eval m_enc
        -> 0 <= eval (proj1_sig sub_sig A B) < eval m_enc))%Z)
    (only parsing).

Ltac solve_sub_bounded montgomery_to_F sub_ext :=
  lazymatch goal with
  | [ |- sub_bounded_prop ?montgomery ?r ?sz ?m_enc ?sub_sig ]
    => apply (proj2_sig sub_ext)
  end.


Notation opp_sig_type r sz m_enc montgomery_to_F :=
  { f:Z^sz -> Z^sz
  | let eval := MontgomeryAPI.eval (Z.pos r) in
    forall (A : Z^sz) (_ : small (Z.pos r) A),
      (eval A < eval m_enc
       -> montgomery_to_F%F (eval (f A))
          = (F.opp (montgomery_to_F (eval A)))%F)%Z }
    (only parsing).


Ltac solve_opp_sig opp_ext :=
  lazymatch goal with
  | [ |- opp_sig_type ?r ?sz ?m_enc ?montgomery_to_F ]
    => idtac;
       let v := (eval cbv [proj1_sig opp_ext_gen opp_ext sig_by_eq] in (proj1_sig opp_ext)) in
       (exists v);
       abstract apply (proj2_sig opp_ext)
  end.

Notation opp_bounded_prop r sz m_enc opp_sig :=
  (let eval := MontgomeryAPI.eval (Z.pos r)%Z in
   (forall (A : Z^sz) (_ : small (Z.pos r) A),
       (eval A < eval m_enc
        -> 0 <= eval (proj1_sig opp_sig A) < eval m_enc))%Z)
    (only parsing).

Ltac solve_opp_bounded montgomery_to_F opp_ext :=
  lazymatch goal with
  | [ |- opp_bounded_prop ?montgomery ?r ?sz ?m_enc ?opp_sig ]
    => apply (proj2_sig opp_ext)
  end.


Notation nonzero_sig_type r sz m m_enc montgomery_to_F :=
  { f:Z^sz -> Z
  | let eval := MontgomeryAPI.eval (Z.pos r) in
    forall (A : Z^sz) (_ : small (Z.pos r) A),
      (eval A < eval m_enc
       -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }
    (only parsing).


Ltac solve_nonzero_sig nonzero_ext :=
  lazymatch goal with
  | [ |- nonzero_sig_type ?r ?sz ?m ?m_enc ?montgomery_to_F ]
    => idtac;
       let v := (eval cbv [proj1_sig nonzero_ext_gen nonzero_ext sig_by_eq] in (proj1_sig nonzero_ext)) in
       (exists v);
       abstract apply (proj2_sig nonzero_ext)
  end.

Ltac solve_ring:=
  (* FIXME: TODO *)
  exact
    I
.

(* disable default unused things *)
Ltac solve_carry_sig:=
  exact tt.
Ltac solve_freeze_sig:=
  exact tt.
Ltac solve_Mxzladderstep_sig:=
  exact tt.
