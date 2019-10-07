let [@warning "-3"] tclSHOW_PROOF =
  Proofview.Goal.enter begin
    fun _ ->
      let pstate = Vernacstate.Proof_global.get_pstate () in
      let pstate = Option.get pstate in
      let p = Proof_global.get_proof pstate in
      let sigma, env = Pfedit.get_current_context pstate in
      let pprf = Proof.partial_proof p in
      Feedback.msg_notice (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf);
      Proofview.tclUNIT ()
  end
