Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Spec.EdDSA Bedrock.Word.
Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Crypto.Algebra. Import Group ScalarMult.
Require Import Crypto.Util.Decidable Crypto.Util.Option Crypto.Util.Tactics.
Require Import Coq.omega.Omega.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Option Crypto.Util.Logic Crypto.Util.Relations Crypto.Util.WordUtil Util.LetIn.
Require Import Crypto.Spec.ModularArithmetic Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Util.Tuple.

Import Notations.

  Section HomomorphismComposition.
    Context {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}.
    Context {H eq op id inv} {groupH:@group H eq op id inv}.
    Context {K eqK opK idK invK} {groupK:@group K eqK opK idK invK}.
    Context {phi:G->H} {phi':H->K}
            {Hphi:@is_homomorphism G EQ OP H eq op phi}
            {Hphi':@is_homomorphism H eq op K eqK opK phi'}.
    Lemma is_homomorphism_compose
          {phi'':G->K}
          (Hphi'' : forall x, eqK (phi' (phi x)) (phi'' x))
      : @is_homomorphism G EQ OP K eqK opK phi''.
    Proof.
      split; repeat intro; rewrite <- !Hphi''.
      { rewrite !homomorphism; reflexivity. }
      { apply Hphi', Hphi; assumption. }
    Qed.

    Global Instance is_homomorphism_compose_refl
      : @is_homomorphism G EQ OP K eqK opK (fun x => phi' (phi x))
      := is_homomorphism_compose (fun x => reflexivity _).
  End HomomorphismComposition.


Section EdDSA.
  Import Group Ring Field.
  Local Notation F := (ModularArithmetic.F (2^255 - 19)).
  Local Instance prime_25519 : Znumtheory.prime (2 ^ 255 - 19). Admitted.
  Let field : field := PrimeFieldTheorems.F.field_modulo (2^255 - 19).
  Local Existing Instance field.
  Context {a d}
          {prm:@E.twisted_edwards_params F Logic.eq ModularArithmetic.F.zero ModularArithmetic.F.one ModularArithmetic.F.add ModularArithmetic.F.mul a d}.
  Local Open Scope F_scope.
  Context {a_eq_minus1 : a = F.opp 1}.
  Context {twice_d:F} {Htwice_d:twice_d = d + d}.
  Notation "T ^ n" := (tuple T n) : type_scope.
  Local Notation ten_words := ((word 32)^10)%type.
  Local Notation ten_Z := (Z^10)%type.
  Axiom ten_words_are_bounded : ten_words -> Prop.
  Local Notation bounded_words := { words : ten_words | ten_words_are_bounded words }.

  Definition Z10toF (k : ten_Z) : F
    := ModularBaseSystem.decode k.
  Definition KtoZ10 (k : bounded_words) : ten_Z
    := Tuple.map (fun v => NtoZ (wordToN v)) (proj1_sig k).
  Definition KtoF (k : bounded_words) : F
    := Z10toF (KtoZ10 k).

  Axiom proof_admitted : False.
  Ltac admit := abstract case proof_admitted.

  Definition FtoZ10 (v : F) : ten_Z
    := ModularBaseSystem.encode v.
  Definition FtoK (v : F) : bounded_words.
  Proof.
    exists (Tuple.map (fun v => NToWord _ (ZtoN v)) (ModularBaseSystem.encode v)).
    admit.
  Defined.

  (** TODO: Move *)
  Definition lift_iso1 {A B} (to : A -> B) (from : B -> A) (f : A -> A) : B -> B
    := fun x => to (f (from x)).
  Definition lift_iso2 {A B} (to : A -> B) (from : B -> A) (f : A -> A -> A) : B -> B -> B
    := fun x y => to (f (from x) (from y)).


  Local Existing Instance Extended.extended_group.
  Local Existing Instance Extended.Equivalence_eq.

  Goal sigT (fun Erep : _ => sigT (fun ErepEq : _ => sigT (fun ErepAdd : _ => sigT (fun EToRep : _ => @Group.is_homomorphism _ Extended.eq (Extended.add (a_eq_minus1:=a_eq_minus1) (Htwice_d:=Htwice_d)) Erep ErepEq ErepAdd EToRep)))).
  Proof.
    exists (Extended.point (F:=bounded_words) (d:=FtoK d) (a:=FtoK a)
                           (Feq:=fun x y => KtoF x = KtoF y)
                           (Fzero:=FtoK F.zero)
                           (Fone:=FtoK F.one)
                           (Fmul:=lift_iso2 FtoK KtoF F.mul)
                           (Fdiv:=lift_iso2 FtoK KtoF F.div)
                           (Fadd:=lift_iso2 FtoK KtoF F.add)).
    eexists (Extended.eq).
    eexists.
    eexists (fun x => Extended.ref_phi
                        (F:=ten_Z)
                        (Feq:=fun x y => Z10toF x = Z10toF y)
                        (Extended.ref_phi x)).
    Arguments Group.is_homomorphism : clear implicits.
    eapply @homomorphism_from_redundant_representation
    with (phi':=fun x => Extended.ref_phi
                           (Feq:=fun x y => Z10toF x = Z10toF y)
                           (Fzero:=FtoZ10 F.zero)
                           (Fone:=FtoZ10 F.one)
                           (Fmul:=lift_iso2 FtoZ10 Z10toF F.mul)
                           (Fdiv:=lift_iso2 FtoZ10 Z10toF F.div)
                           (Fadd:=lift_iso2 FtoZ10 Z10toF F.add)
                           (phi:=Z10toF)
                           (Extended.ref_phi
                              (phi:=KtoZ10)
                              (Fzero:=FtoK F.zero)
                              (Fone:=FtoK F.one)
                              (Fmul:=lift_iso2 FtoK KtoF F.mul)
                              (Fdiv:=lift_iso2 FtoK KtoF F.div)
                              (Fadd:=lift_iso2 FtoK KtoF F.add)
                              (Feq:=fun x y => KtoF x = KtoF y)
                              x));
      try exact _.
    About Extended.ref_phi.
    Arguments Extended.ref_phi {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ {_ _ _ _ _} _.
    Print Extended.ref_phi.
    Set Printing Implicit.
    pose ?phi'.
    Arguments group : clear implicits.
    Arguments Extended.point : clear implicits.
    Set Printing Implicit.
    eapply @is_homomorphism_compose_refl with (phi:=Extended.ref_phi (F:=F)) (phi':=Extended.ref_phi).
    Focus 4.
    intro.
    simple refine (reflexivity _).
    eapply Extended.Equivalence_eq.
    all:shelve_unifiable.
    Set Printing Implicit.
    exact _.
    Print Extended.
    exact _.
    apply reflexivity.
    4:reflexivity.

    2:eapply @homomorphism_from_redundant_representation; try exact _.
    Print Extended.
    Print Extended.point.
    split; intros.
    { Notation "( a ; ! )" := (exist _ a _).
      cbv beta delta [Extended.add].
      cbv beta delta [Extended.add_coordinates].
      Arguments Extended.point : clear implicits.
      cbv beta delta [Extended.ref_phi].
    2:intros ???.
    Focus 2.
    {
      Set Printing Implicit.
    Print Extended.lift_homomorphism.
    eapply @Extended.lift_homomorphism
    with (K := bounded_words) (Keq := fun x y => KtoF x = KtoF y).
    Set Printing Implicit.
    Focus 2.
    {
    Notation leq := Logic.eq.
    Set Printing All.
    Set P
    {
    P
    split; intros.
    { Show Existentials.


  Goal

  Context `{prm:EdDSA}.
  Local Infix "==" := Eeq. Local Infix "+" := Eadd. Local Infix "*" := EscalarMult.
  Context {Proper_Eenc : Proper (Eeq==>Logic.eq) Eenc}.
  Global Instance Proper_eq_Eenc ref : Proper (Eeq ==> iff) (fun P => Eenc P = ref).
  Proof. intros ? ? Hx; rewrite Hx; reflexivity. Qed.

  Context {Edec:word b-> option E}   {eq_enc_E_iff: forall P_ P, Eenc P = P_ <-> Edec P_ = Some P}.
  Context {Sdec:word b-> option (F l)} {eq_enc_S_iff: forall n_ n, Senc n = n_ <-> Sdec n_ = Some n}.

  Local Infix "++" := combine.

      Context {Erep ErepEq ErepAdd ErepId ErepOpp} {Agroup:@group Erep ErepEq ErepAdd ErepId ErepOpp}.
    Context {EToRep} {Ahomom:@is_homomorphism E Eeq Eadd Erep ErepEq ErepAdd EToRep}.


  Definition

  1 focused subgoal
(unfocused: 0-1, shelved: 2), subgoal 1 (ID 14473)

  E : Type
  Eeq : E -> E -> Prop
  Eadd : E -> E -> E
  Ezero : E
  Eopp : E -> E
  EscalarMult : nat -> E -> E
  b : nat
  H : forall n : nat, word n -> word (b + b)
  c, n : nat
  l : Z
  B : E
  Eenc : E -> word b
  Senc : F l -> word b
  prm : EdDSA
  Proper_Eenc : Proper (Eeq ==> eq) Eenc
  Edec : word b -> option E
  eq_enc_E_iff : forall (P_ : word b) (P : E), Eenc P = P_ <-> Edec P_ = Some P
  Sdec : word b -> option (F l)
  eq_enc_S_iff : forall (n_ : word b) (n : F l), Senc n = n_ <-> Sdec n_ = Some n
  Erep : Type
  ErepEq : Erep -> Erep -> Prop
  ErepAdd : Erep -> Erep -> Erep
  ErepId : Erep
  ErepOpp : Erep -> Erep
  Agroup : group
  EToRep : E -> Erep
  Ahomom : is_homomorphism
  ERepEnc : Erep -> word b
  ERepEnc_correct : forall P : E, Eenc P = ERepEnc (EToRep P)
  Proper_ERepEnc : Proper (ErepEq ==> eq) ERepEnc
  ERepDec : word b -> option Erep
  ERepDec_correct : forall w : word b, ERepDec w = option_map EToRep (Edec w)
  SRep : Type
  SRepEq : relation SRep
  H0 : Equivalence SRepEq
  S2Rep : F l -> SRep
  SRepDecModL : word (b + b) -> SRep
  SRepDecModL_correct : forall w : word (b + b),
                        SRepEq (S2Rep (F.of_nat l (wordToNat w))) (SRepDecModL w)
  SRepERepMul : SRep -> Erep -> Erep
  SRepERepMul_correct : forall (n : nat) (P : E),
                        ErepEq (EToRep (n * P)) (SRepERepMul (S2Rep (F.of_nat l n)) (EToRep P))
  Proper_SRepERepMul : Proper (SRepEq ==> ErepEq ==> ErepEq) SRepERepMul
  SRepDec : word b -> option SRep
  SRepDec_correct : forall w : word b, option_eq SRepEq (option_map S2Rep (Sdec w)) (SRepDec w)
  mlen : nat
  message : word mlen
  pk : word b
  sig : word (b + b)
  H1 : (2 < l)%Z
  l_pos : (0 < l)%Z
  a : E
  a0 : F l
  ============================
  ?x a0 =
  weqb
    (ERepEnc
       (ErepAdd (SRepERepMul (S2Rep a0) (EToRep B))
          (SRepERepMul (SRepDecModL (H (b + (b + mlen)) (split1 b b sig ++ pk ++ message)))
             (ErepOpp (EToRep a))))) (split1 b b sig)

(dependent evars: (printing disabled) )
