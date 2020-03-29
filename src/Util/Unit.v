Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

(* an equivalence for a relation on trivial things, like [unit] *)
Global Instance Equivalence_trivial {A} : Equivalence (fun _ _ : A => True).
Proof.
  repeat constructor.
Qed.
