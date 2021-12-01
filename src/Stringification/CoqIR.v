From Coq Require Import ZArith.ZArith MSets.MSetPositive FSets.FMapPositive
     Strings.String Strings.Ascii Bool.Bool Lists.List Strings.HexString.
From Crypto.Util Require Import
     ListUtil
     Strings.String Strings.Decimal Strings.Show
     ZRange.Operations ZRange.Show
     Option OptionList Bool.Equality.
(* Work around COQBUG(https://github.com/coq/coq/issues/12251) *)
Require Import Crypto.Util.ZRange.

From Crypto Require Import Stringification.Language AbstractInterpretation.ZRange.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Import Stringification.Language.Compilers.
Import Stringification.Language.Compilers.Options.
Import Stringification.Language.Compilers.ToString.
Import Stringification.Language.Compilers.ToString.OfPHOAS.
Import Stringification.Language.Compilers.ToString.int.Notations.

Module CoqIR.
  Definition indent (indent : string) : list string -> list string
    := List.map (fun s => indent ++ s)%string.

  Definition comment_block (lines : list string) : list string
    := match lines with
       | [] => []
       | [line] => ["(** " ++ line ++ " *)"]%string
       | line::lines => ("(** " ++ line)%string::indent "    " lines ++ [" *)"]
       end%list%string.

  Definition ToFunctionLines
             {absint_opts : AbstractInterpretation.Options}
             {relax_zrange : relax_zrange_opt}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z)
             (do_bounds_check : bool) (internal_private : bool) (private : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
             {t}
             (e : API.Expr t)
             (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
             (name_list : option (list string))
             (inbounds : type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t)
             (outbounds : Compilers.ZRange.type.base.option.interp (type.final_codomain t))
             (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
             (outtypedefs : base_var_typedef_data (type.final_codomain t))
    : (list string * ToString.ident_infos) + string :=
    inl ((["Definition " ++ name ++ " : API.Expr :="]%string)
           ++ indent "  " (show_lines e)
           ++ ["."],
          ToString.ident_info_empty)%list.

  Definition OutputCoqIRAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := comment_block;
       ToString.comment_file_header_block := comment_block;
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := fun _ _ _ _ _ _ _ _ _ _ _ => [];
       ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];
       (** No special handling for any functions *)
       ToString.strip_special_infos machine_wordsize infos := infos |}.
End CoqIR.
