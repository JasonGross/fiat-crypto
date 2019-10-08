open Constr
(*open Ppconstr*)
open Genredexpr
open Names
open Constrexpr_ops


let qualid_of_ref n =
  n |> Coqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_scraped_data_ty () = qualid_of_ref "rewriter.scraped_data.type"

let vernac_rewriter_emit_inductives (scraped_data : Constrexpr.constr_expr) (base : Names.Id.t) (ident : Names.Id.t) (raw_ident : Names.Id.t) (pattern_ident : Names.Id.t) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, scraped_data) = Constrintern.interp_constr_evars env sigma scraped_data in
  let _app x y = mkAppC (x,[y]) in
  let cref q = mkRefC q in
  let _cscraped_data_ty = cref (q_scraped_data_ty ()) in
  let (hnffun, _) = Redexpr.reduction_of_red_expr env Hnf in
  let (sigma, scraped_data) = hnffun env sigma scraped_data in
  match EConstr.kind sigma scraped_data with
  | App (_build, [|_base_type_list_named; _all_ident_list_named|]) ->
    let _sigma = sigma in
    let _scraped_data = scraped_data in
    ()
  | _ ->
    CErrors.user_err Pp.(str "Invalid scraped data:" ++ Printer.pr_econstr_env env sigma scraped_data)
