Require Import Crypto.Specific.Framework.Pipeline.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Set Primitive Projections.
Record prim_prod {A B} := pair { fst : A ; snd : B }.
Arguments prim_prod A B : clear implicits.

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (curve_sc' : vm_decide_package (Base.CurveParameterBaseSideConditions_bool curve = true)).

  Ltac evar_destruct ev H v :=
    revert ev H;
    instantiate (2:=ltac:(destruct v));
    instantiate (1:=ltac:(destruct v));
    destruct v;
    intros ev H; cbv iota zeta in *.

  Definition Pipeline' : { evarT : _ & { HT : evarT -> Prop & forall evars, HT evars -> SynthesisOutput curve } }.
  Proof.
    do 2 eexists; intros ev H.
    unshelve eapply @Pipeline; [ exact curve_sc' | ].
    hnf.
    case_eq curve.(montgomery); intro Hmontgomery.
    Focus 2.
    Local Ltac do_unfold0 :=
      repeat match goal with
             | _ => progress cbn [Syntax.tuple Syntax.tuple']
             | [ |- context G[Syntax.tuple ?T 1] ]
               => let G' := context G[T] in change G'
             | [ |- context G[Syntax.tuple ?T 2] ]
               => let G' := context G[Syntax.Prod T T] in change G'
             | _ => progress cbv_CurveParameters
             | _ => progress cbv [Base.half_sz' Base.sz2' val Option.invert_Some proj1_sig]
             | [ |- context[?f curve] ]
               => first [ constr_eq f (@BoundsPipeline.BoundsSideConditions); fail 1
                        | progress cbv [f] ]
             end.
    { unshelve econstructor. unshelve econstructor.
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0. eexists (Some _); shelve. }
      { do_unfold0.
        let c := match goal with |- context[if ?c then _ else _] => c end in
        eexists (if c then Some (Some _) else None); case_eq c;
          [ intro H'; apply f_equal; revert H'; shelve | reflexivity ]. }
      { do_unfold0.
        let c := match goal with |- context[if ?c then _ else _] => c end in
        eexists (if c then Some (Some _) else None); case_eq c;
          [ intro H'; apply f_equal; revert H'; shelve | reflexivity ]. }
      { do_unfold0.
        let c := match goal with |- context[if ?c then _ else _] => c end in
        eexists (if c then Some (Some _) else None); case_eq c;
          [ intro H'; apply f_equal; revert H'; shelve | reflexivity ]. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0.
        let c := match goal with |- context[if ?c then _ else _] => c end in
        eexists (if c then Some _ else None); case_eq c;
          [ shelve | constructor ]. }
      { do_unfold0.
        let c := match goal with |- context[if ?c then _ else _] => c end in
        eexists (if c then Some _ else None); case_eq c;
          [ shelve | constructor ]. }
      { do_unfold0.
        let c := match goal with |- context[if ?c then _ else _] => c end in
        eexists (if c then Some _ else None); case_eq c;
          [ shelve | constructor ]. }
      { do_unfold0. exact Hmontgomery. }
      { do_unfold0.
        let c := match goal with |- context[option_map _ ?c] => c end in
        eexists (if c then Some _ else None); case_eq c;
          cbv [option_map]; [ shelve | constructor ]. }
      { do_unfold0.
        let c := match goal with |- context[option_map _ ?c] => c end in
        eexists (if c then Some _ else None); case_eq c;
          cbv [option_map]; [ shelve | constructor ]. }
      { do_unfold0.
        cbv [ModularArithmetic.F.to_Z ModularArithmetic.F.one ModularArithmetic.F.zero ModularArithmetic.F.of_Z proj1_sig Z.modulo Z.div_eucl Z.pos_div_eucl].
        eexists; shelve. }
      { do_unfold0.
        cbv [ModularArithmetic.F.to_Z ModularArithmetic.F.one ModularArithmetic.F.of_Z proj1_sig Z.modulo Z.div_eucl Z.pos_div_eucl].
        eexists; shelve. }
      { do_unfold0.
        let c := match goal with |- context[option_map _ ?c] => c end in
        case_eq c; cbv [option_map]; [ shelve | constructor ]. }
      { do_unfold0.
        let c := match goal with |- context[option_map _ ?c] => c end in
        case_eq c; cbv [option_map]; [ shelve | constructor ]. }
      { cbv [SolinasBoundsPipelineInputSideConditions.ropsZ
               val
               Solinas.zeroZ
               Solinas.oneZ
               Solinas.addZ
               Solinas.subZ
               Solinas.carry_mulZ
               Solinas.carryZ
               Solinas.mul_codeZ
               Solinas.reduceZ
               Solinas.reduceZ_sz_sz
               Solinas.reduceZ_sz_1p5
               Solinas.premulZ
               Solinas.carry_squareZ
               Solinas.square_codeZ
               Solinas.val_pregoldilocks_squareZ
               Solinas.val_presquareZ
               Solinas.val_prekaratsuba_squareZ
               Solinas.prekaratsuba_mulZ
               Solinas.pregoldilocks_mulZ
               Solinas.oppZ
               Solinas.freezeZ
               FencodeTuple
               FdecodeTuple
               Base.wt].
        do_unfold0.
        unshelve econstructor.
        { do_unfold0.
          cbn [Syntax.interp_flat_type].
          eexists (fun var => Syntax.Abs (src:=Syntax.Unit) (fun u : unit => ltac:(clear u))).
          shelve. }
        { do_unfold0.
          cbn [Syntax.interp_flat_type].
          eexists (fun var => Syntax.Abs (src:=Syntax.Unit) (fun u : unit => ltac:(clear u))).
          shelve. }
        Local Ltac RBPSC :=
          let e' := fresh "e" in
          let H' := fresh "H" in
          lazymatch goal with
          | [ |- BoundsPipeline.RBPipelineSideConditions ?curve ?t ?e ?b1 ?b2 ?opts ]
            => let et := type of e in
               evar (e' : et);
               evar (H' : e' = e);
               clearbody H';
               cut (BoundsPipeline.RBPipelineSideConditions curve t e' b1 b2 opts)
          end;
          [ let v := fresh "v" in
            intro v;
            simple refine {| BoundsPipeline.RBEvars := BoundsPipeline.RBEvars v;
                             BoundsPipeline.RBSideConditions
                             := fun v' H''
                                => let 'existT a p := BoundsPipeline.RBSideConditions v v' H'' in
                                   existT _ a (_ p);
                             BoundsPipeline.RBVal := BoundsPipeline.RBVal v |};
            subst e'; exact id
          | let evars := open_constr:({| ReflectiveTactics.e_pkg := _ |}) in
            simple refine {| BoundsPipeline.RBEvars := evars |};
            do_unfold0;
            [ intro v'; eexists; shelve | eexists; shelve ] ].
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0.
          let c := match goal with |- context[if ?c then _ else _] => c end in
          case_eq c; cbv [option_map]; [ intro Hfreeze | reflexivity ].
          RBPSC. }
        { do_unfold0. exact Hmontgomery. } } }
    Unfocus.
    { unshelve econstructor.
      unshelve econstructor.
      { do_unfold0. eexists; shelve. }
      { do_unfold0. cbv [Decidable.dec]. shelve. }
      { do_unfold0. eexists; shelve. }
      { do_unfold0. shelve. }
      { do_unfold0. shelve. }
      { do_unfold0. shelve. }
      { do_unfold0. shelve. }
      { do_unfold0. shelve. }
      { do_unfold0.
        unshelve econstructor.
        { do_unfold0. eexists (Some _); shelve. }
        { do_unfold0. eexists (Some _); shelve. }
        { do_unfold0. eexists (Some _); shelve. }
        { do_unfold0. eexists (Some _); shelve. }
        { do_unfold0. eexists (Some _); shelve. }
        { do_unfold0. eexists; shelve. }
        { do_unfold0. eexists; shelve. }
        { do_unfold0. eexists; shelve. }
        { do_unfold0. eexists; shelve. }
        { do_unfold0. eexists; shelve. }
        { do_unfold0. shelve. }
        { do_unfold0. shelve. }
        { do_unfold0. shelve. }
        { do_unfold0. shelve. }
        { do_unfold0.
          cbn [Syntax.interp_flat_type].
          eexists (fun var => Syntax.Abs (src:=Syntax.Unit) (fun u : unit => ltac:(clear u))).
          shelve. }
        { do_unfold0.
          cbn [Syntax.interp_flat_type].
          eexists (fun var => Syntax.Abs (src:=Syntax.Unit) (fun u : unit => ltac:(clear u))).
          shelve. } }
      { cbv [val
               MontgomeryBoundsPipelineInputSideConditions.ropsZ
               Montgomery.not_freeze
               Montgomery.tight_is_limb_width'
               Montgomery.loose_is_limb_width'
               Montgomery.limb_width_is_bitwidth'
               Montgomery.vm_compiled_preadd
               Montgomery.vm_compiled_presub
               Montgomery.vm_compiled_preopp
               Montgomery.vm_compiled_prenonzero
               Montgomery.vm_compiled_premul
               Montgomery.zeroZ
               Montgomery.oneZ
               Montgomery.addZ
               Montgomery.subZ
               Montgomery.oppZ
               Montgomery.nonzeroZ
               Montgomery.mulZ
               Montgomery.montgomery_of_F Montgomery.montgomery_to_F
               Montgomery.r' Montgomery.m'
               Montgomery.val_squareZ].
        do_unfold0.
        unshelve econstructor.
        { do_unfold0.
          cbn [Syntax.interp_flat_type].
          eexists (fun var => Syntax.Abs (src:=Syntax.Unit) (fun u : unit => ltac:(clear u))).
          shelve. }
        { do_unfold0.
          cbn [Syntax.interp_flat_type].
          eexists (fun var => Syntax.Abs (src:=Syntax.Unit) (fun u : unit => ltac:(clear u))).
          shelve. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. RBPSC. }
        { do_unfold0. shelve. }
        { do_unfold0. RBPSC. } } }
    Unshelve.
    1-2:shelve.
    Record Evars
           {T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T94 T95 T96 T97 T98 T99 T100 T101 T102 T103 T104 T105 T106 T107 T108 T109 T110 T111 T112 T113 T114 T115 T116 T117 T118 T119 T120 T121 T122 T123 T124 T125 T126 T127 T128 T129 T130 T131 T132 T133 T134 T135 T136 T137 T138 T139 T140 T141 dT0 dT1 dT2 dT3 dT4 dT5 dT6 dT7 dT8 dT9 dT10 dT11 dT12 dT13}
      := {
          v0:T0 ; v1:T1 ; v2:T2 ; v3:T3 ; v4:T4 ; v5:T5 ; v6:T6 ; v7:T7 ; v8:T8 ; v9:T9 ; v10:T10 ; v11:T11 ; v12:T12 ; v13:T13 ; v14:T14 ; v15:T15 ; v16:T16 ; v17:T17 ; v18:T18 ; v19:T19 ; v20:T20 ; v21:T21 ; v22:T22 ; v23:T23 ; v24:T24 ; v25:T25 ; v26:T26 ; v27:T27 ; v28:T28 ; v29:T29 ; v30:T30 ; v31:T31 ; v32:T32 ; v33:T33 ; v34:T34 ; v35:T35 ; v36:T36 ; v37:T37 ; v38:T38 ; v39:T39 ; v40:T40 ; v41:T41 ; v42:T42 ; v43:T43 ; v44:T44 ; v45:T45 ; v46:T46 ; v47:T47 ; v48:T48 ; v49:T49 ; v50:T50 ; v51:T51 ; v52:T52 ; v53:T53 ; v54:T54 ; v55:T55 ; v56:T56 ; v57:T57 ; v58:T58 ; v59:T59 ; v60:T60 ; v61:T61 ; v62:T62 ; v63:T63 ; v64:T64 ; v65:T65 ; v66:T66 ; v67:T67 ; v68:T68 ; v69:T69 ; v70:T70 ; v71:T71 ; v72:T72 ; v73:T73 ; v74:T74 ; v75:T75 ; v76:T76 ; v77:T77 ; v78:T78 ; v79:T79 ; v80:T80 ; v81:T81 ; v82:T82 ; v83:T83 ; v84:T84 ; v85:T85 ; v86:T86 ; v87:T87 ; v88:T88 ; v89:T89 ; v90:T90 ; v91:T91 ; v92:T92 ; v93:T93 ; v94:T94 ; v95:T95 ; v96:T96 ; v97:T97 ; v98:T98 ; v99:T99 ; v100:T100 ; v101:T101 ; v102:T102 ; v103:T103 ; v104:T104 ; v105:T105 ; v106:T106 ; v107:T107 ; v108:T108 ; v109:T109 ; v110:T110 ; v111:T111 ; v112:T112 ; v113:T113 ; v114:T114 ; v115:T115 ; v116:T116 ; v117:T117 ; v118:T118 ; v119:T119 ; v120:T120 ; v121:T121 ; v122:T122 ; v123:T123 ; v124:T124 ; v125:T125 ; v126:T126 ; v127:T127 ; v128:T128 ; v129:T129 ; v130:T130 ; v131:T131 ; v132:T132 ; v133:T133 ; v134:T134 ; v135:T135 ; v136:T136 ; v137:T137 ; v138:T138 ; v139:T139 ; v140:T140 ; v141:T141 ; dv0:dT0 v26 ; dv1:dT1 v33 ; dv2:dT2 v40 ; dv3:dT3 v47 ; dv4:dT4 v54 ; dv5:dT5 v61 ; dv6:dT6 v68 ; dv7:dT7 v87 ; dv8:dT8 v94 ; dv9:dT9 v101 ; dv10:dT10 v108 ; dv11:dT11 v115 ; dv12:dT12 v122 ; dv13:dT13 v129 }.
    all:let G := match goal with |- ?G => G end in
        lazymatch type of G with
        | Prop => shelve
        | _ => cbv [raw_evar_package];
                 cbn [SmartMap.lift_flat_type]; try clear H;
                   first [ has_evar G; shelve | idtac ]
        end.
    { refine (v0 (fst ev)); shelve. }
    { refine (v1 (fst ev)); shelve. }
    { refine (v2 (fst ev)); shelve. }
    { refine (v3 (fst ev)); shelve. }
    { refine (v4 (fst ev)); shelve. }
    { refine (v5 (fst ev)); shelve. }
    { refine (v6 (fst ev)); shelve. }
    { refine (v7 (fst ev)); shelve. }
    { refine (v8 (fst ev)); shelve. }
    { refine (v9 (fst ev)); shelve. }
    { refine (v10 (fst ev)); shelve. }
    { refine (v11 (fst ev)); shelve. }
    { refine (v12 (fst ev)); shelve. }
    { refine (v13 (fst ev)); shelve. }
    { refine (v14 (fst ev)); shelve. }
    { refine (v15 (fst ev)); shelve. }
    { refine (v16 (fst ev)); shelve. }
    { refine (v17 (fst ev)); shelve. }
    { refine (v18 (fst ev)); shelve. }
    { refine (v19 (fst ev)); shelve. }
    { refine (v20 (fst ev)); shelve. }
    { refine (v21 (fst ev)); shelve. }
    { refine (v22 (fst ev)); shelve. }
    { refine (v23 (fst ev)); shelve. }
    { refine (v24 (fst ev)); shelve. }
    { refine (v25 (fst ev)); shelve. }
    { refine (v26 (fst ev)); shelve. }
    { refine (v27 (fst ev)); shelve. }
    { refine (v28 (fst ev)); shelve. }
    { refine (v29 (fst ev)); shelve. }
    { refine (v30 (fst ev)); shelve. }
    { refine (v31 (fst ev)); shelve. }
    { refine (v32 (fst ev)); shelve. }
    { refine (v33 (fst ev)); shelve. }
    { refine (v34 (fst ev)); shelve. }
    { refine (v35 (fst ev)); shelve. }
    { refine (v36 (fst ev)); shelve. }
    { refine (v37 (fst ev)); shelve. }
    { refine (v38 (fst ev)); shelve. }
    { refine (v39 (fst ev)); shelve. }
    { refine (v40 (fst ev)); shelve. }
    { refine (v41 (fst ev)); shelve. }
    { refine (v42 (fst ev)); shelve. }
    { refine (v43 (fst ev)); shelve. }
    { refine (v44 (fst ev)); shelve. }
    { refine (v45 (fst ev)); shelve. }
    { refine (v46 (fst ev)); shelve. }
    { refine (v47 (fst ev)); shelve. }
    { refine (v48 (fst ev)); shelve. }
    { refine (v49 (fst ev)); shelve. }
    { refine (v50 (fst ev)); shelve. }
    { refine (v51 (fst ev)); shelve. }
    { refine (v52 (fst ev)); shelve. }
    { refine (v53 (fst ev)); shelve. }
    { refine (v54 (fst ev)); shelve. }
    { refine (v55 (fst ev)); shelve. }
    { refine (v56 (fst ev)); shelve. }
    { refine (v57 (fst ev)); shelve. }
    { refine (v58 (fst ev)); shelve. }
    { refine (v59 (fst ev)); shelve. }
    { refine (v60 (fst ev)); shelve. }
    { refine (v61 (fst ev)); shelve. }
    { refine (v62 (fst ev)); shelve. }
    { refine (v63 (fst ev)); shelve. }
    { refine (v64 (fst ev)); shelve. }
    { refine (v65 (fst ev)); shelve. }
    { refine (v66 (fst ev)); shelve. }
    { refine (v67 (fst ev)); shelve. }
    { refine (v68 (fst ev)); shelve. }
    { refine (v69 (fst ev)); shelve. }
    { refine (v70 (fst ev)); shelve. }
    { refine (v71 (fst ev)); shelve. }
    { refine (v72 (fst ev)); shelve. }
    { refine (v73 (fst ev)); shelve. }
    { refine (v74 (fst ev)); shelve. }
    { refine (v75 (fst ev)); shelve. }
    { refine (v76 (fst ev)); shelve. }
    { refine (v77 (fst ev)); shelve. }
    { refine (v78 (fst ev)); shelve. }
    { refine (v79 (fst ev)); shelve. }
    { refine (v80 (fst ev)); shelve. }
    { refine (v81 (fst ev)); shelve. }
    { refine (v82 (fst ev)); shelve. }
    { refine (v83 (fst ev)); shelve. }
    { refine (v84 (fst ev)); shelve. }
    { refine (v85 (fst ev)); shelve. }
    { refine (v86 (fst ev)); shelve. }
    { refine (v87 (fst ev)); shelve. }
    { refine (v88 (fst ev)); shelve. }
    { refine (v89 (fst ev)); shelve. }
    { refine (v90 (fst ev)); shelve. }
    { refine (v91 (fst ev)); shelve. }
    { refine (v92 (fst ev)); shelve. }
    { refine (v93 (fst ev)); shelve. }
    { refine (v94 (fst ev)); shelve. }
    { refine (v95 (fst ev)); shelve. }
    { refine (v96 (fst ev)); shelve. }
    { refine (v97 (fst ev)); shelve. }
    { refine (v98 (fst ev)); shelve. }
    { refine (v99 (fst ev)); shelve. }
    { refine (v100 (fst ev)); shelve. }
    { refine (v101 (fst ev)); shelve. }
    { refine (v102 (fst ev)); shelve. }
    { refine (v103 (fst ev)); shelve. }
    { refine (v104 (fst ev)); shelve. }
    { refine (v105 (fst ev)); shelve. }
    { refine (v106 (fst ev)); shelve. }
    { refine (v107 (fst ev)); shelve. }
    { refine (v108 (fst ev)); shelve. }
    { refine (v109 (fst ev)); shelve. }
    { refine (v110 (fst ev)); shelve. }
    { refine (v111 (fst ev)); shelve. }
    { refine (v112 (fst ev)); shelve. }
    { refine (v113 (fst ev)); shelve. }
    { refine (v114 (fst ev)); shelve. }
    { refine (v115 (fst ev)); shelve. }
    { refine (v116 (fst ev)); shelve. }
    { refine (v117 (fst ev)); shelve. }
    { refine (v118 (fst ev)); shelve. }
    { refine (v119 (fst ev)); shelve. }
    { refine (v120 (fst ev)); shelve. }
    { refine (v121 (fst ev)); shelve. }
    { refine (v122 (fst ev)); shelve. }
    { refine (v123 (fst ev)); shelve. }
    { refine (v124 (fst ev)); shelve. }
    { refine (v125 (fst ev)); shelve. }
    { refine (v126 (fst ev)); shelve. }
    { refine (v127 (fst ev)); shelve. }
    { refine (v128 (fst ev)); shelve. }
    { refine (v129 (fst ev)); shelve. }
    { refine (v130 (fst ev)); shelve. }
    { refine (v131 (fst ev)); shelve. }
    { refine (v132 (fst ev)); shelve. }
    { refine (v133 (fst ev)); shelve. }
    { refine (v134 (fst ev)); shelve. }
    { refine (v135 (fst ev)); shelve. }
    Unshelve.
    1:shelve.
    all:let G := match goal with |- ?G => G end in
        lazymatch type of G with
        | Prop => shelve
        | _ => first [ has_evar G; shelve | idtac ]
        end;
          lazymatch G with Type => shelve | _ -> Type => shelve | _ => idtac end.
    Ltac do_pattern ev :=
      lazymatch goal with |- context[?v (?p ev)] => pattern (v (p ev)) end.
    { do_pattern ev; refine (dv0 (fst ev)); shelve. }
    { do_pattern ev; refine (dv1 (fst ev)); shelve. }
    { do_pattern ev; refine (dv2 (fst ev)); shelve. }
    { do_pattern ev; refine (dv3 (fst ev)); shelve. }
    { do_pattern ev; refine (dv4 (fst ev)); shelve. }
    { do_pattern ev; refine (dv5 (fst ev)); shelve. }
    { do_pattern ev; refine (dv6 (fst ev)); shelve. }
    { do_pattern ev; refine (dv7 (fst ev)); shelve. }
    { do_pattern ev; refine (dv8 (fst ev)); shelve. }
    { do_pattern ev; refine (dv9 (fst ev)); shelve. }
    { do_pattern ev; refine (dv10 (fst ev)); shelve. }
    { do_pattern ev; refine (dv11 (fst ev)); shelve. }
    { do_pattern ev; refine (dv12 (fst ev)); shelve. }
    { do_pattern ev; refine (dv13 (fst ev)); shelve. }
    Grab Existential Variables.
    all:let G := match goal with |- ?G => G end in
        lazymatch type of G with
        | Prop => shelve
        | _ => first [ has_evar G; shelve | idtac ]
        end;
          lazymatch G with Type => shelve | _ -> Type => shelve | _ => idtac end.
    { revert var; refine (v136 (fst ev)); shelve. }
    { revert var; refine (v137 (fst ev)); shelve. }
    { revert var; refine (v138 (fst ev)); shelve. }
    { revert var; refine (v139 (fst ev)); shelve. }
    { revert var; refine (v140 (fst ev)); shelve. }
    { revert var; refine (v141 (fst ev)); shelve. }
    Unshelve.
    Time Optimize Proof.
    Time Optimize Heap.
    all:cycle -2.
    1-2:shelve.
    all:let G := match goal with |- ?G => G end in
        lazymatch type of G with
        | Prop => idtac
        | _ => fail
        end.
    lazymatch type of ev with prim_prod _ ?e => unify e unit end.
    all:cbv [fst v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 dv0 dv1 dv2 dv3 dv4 dv5 dv6 dv7 dv8 dv9 dv10 dv11 dv12 dv13].
    Record BigAnd {T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T94 T95 T96 T97 T98 : Prop} :=
      { pf0:T0 ; pf1:T1 ; pf2:T2 ; pf3:T3 ; pf4:T4 ; pf5:T5 ; pf6:T6 ; pf7:T7 ; pf8:T8 ; pf9:T9 ; pf10:T10 ; pf11:T11 ; pf12:T12 ; pf13:T13 ; pf14:T14 ; pf15:T15 ; pf16:T16 ; pf17:T17 ; pf18:T18 ; pf19:T19 ; pf20:T20 ; pf21:T21 ; pf22:T22 ; pf23:T23 ; pf24:T24 ; pf25:T25 ; pf26:T26 ; pf27:T27 ; pf28:T28 ; pf29:T29 ; pf30:T30 ; pf31:T31 ; pf32:T32 ; pf33:T33 ; pf34:T34 ; pf35:T35 ; pf36:T36 ; pf37:T37 ; pf38:T38 ; pf39:T39 ; pf40:T40 ; pf41:T41 ; pf42:T42 ; pf43:T43 ; pf44:T44 ; pf45:T45 ; pf46:T46 ; pf47:T47 ; pf48:T48 ; pf49:T49 ; pf50:T50 ; pf51:T51 ; pf52:T52 ; pf53:T53 ; pf54:T54 ; pf55:T55 ; pf56:T56 ; pf57:T57 ; pf58:T58 ; pf59:T59 ; pf60:T60 ; pf61:T61 ; pf62:T62 ; pf63:T63 ; pf64:T64 ; pf65:T65 ; pf66:T66 ; pf67:T67 ; pf68:T68 ; pf69:T69 ; pf70:T70 ; pf71:T71 ; pf72:T72 ; pf73:T73 ; pf74:T74 ; pf75:T75 ; pf76:T76 ; pf77:T77 ; pf78:T78 ; pf79:T79 ; pf80:T80 ; pf81:T81 ; pf82:T82 ; pf83:T83 ; pf84:T84 ; pf85:T85 ; pf86:T86 ; pf87:T87 ; pf88:T88 ; pf89:T89 ; pf90:T90 ; pf91:T91 ; pf92:T92 ; pf93:T93 ; pf94:T94 ; pf95:T95 ; pf96:T96 ; pf97:T97 ; pf98:T98 }.
    all: repeat lazymatch goal with
                | [ H' : _ |- _ ]
                  => first [ constr_eq H' H; fail 1
                           | revert H' ]
                end.
    revert dependent ev.
    { Time refine (let T0 : Evars -> Prop := _ in
              let T1 : Evars -> Prop := ltac:(clear T0) in
              let T2 : Evars -> Prop := ltac:(clear T0 T1) in
              let T3 : Evars -> Prop := ltac:(clear T0 T1 T2) in
              let T4 : Evars -> Prop := ltac:(clear T0 T1 T2 T3) in
              let T5 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4) in
              let T6 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5) in
              let T7 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6) in
              let T8 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7) in
              let T9 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8) in
              let T10 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) in
              let T11 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) in
              let T12 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) in
              let T13 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) in
              let T14 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) in
              let T15 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) in
              let T16 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) in
              let T17 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) in
              let T18 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) in
              let T19 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18) in
              let T20 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19) in
              let T21 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20) in
              let T22 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21) in
              let T23 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22) in
              let T24 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23) in
              let T25 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24) in
              let T26 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25) in
              let T27 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26) in
              let T28 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27) in
              let T29 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28) in
              let T30 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29) in
              let T31 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30) in
              let T32 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31) in
              let T33 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32) in
              let T34 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33) in
              let T35 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34) in
              let T36 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35) in
              let T37 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36) in
              let T38 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37) in
              let T39 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38) in
              let T40 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39) in
              let T41 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40) in
              let T42 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41) in
              let T43 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42) in
              let T44 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43) in
              let T45 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44) in
              let T46 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45) in
              let T47 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46) in
              let T48 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47) in
              let T49 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48) in
              let T50 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49) in
              let T51 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50) in
              let T52 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51) in
              let T53 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52) in
              let T54 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53) in
              let T55 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54) in
              let T56 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55) in
              let T57 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56) in
              let T58 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57) in
              let T59 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58) in
              let T60 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59) in
              let T61 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60) in
              let T62 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61) in
              let T63 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62) in
              let T64 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63) in
              let T65 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64) in
              let T66 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65) in
              let T67 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66) in
              let T68 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67) in
              let T69 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68) in
              let T70 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69) in
              let T71 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70) in
              let T72 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71) in
              let T73 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72) in
              let T74 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73) in
              let T75 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74) in
              let T76 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75) in
              let T77 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76) in
              let T78 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77) in
              let T79 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78) in
              let T80 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79) in
              let T81 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80) in
              let T82 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81) in
              let T83 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82) in
              let T84 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83) in
              let T85 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84) in
              let T86 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85) in
              let T87 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86) in
              let T88 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87) in
              let T89 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88) in
              let T90 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89) in
              let T91 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90) in
              let T92 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91) in
              let T93 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92) in
              let T94 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93) in
              let T95 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T94) in
              let T96 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T94 T95) in
              let T97 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T94 T95 T96) in
              let T98 : Evars -> Prop := ltac:(clear T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 T43 T44 T45 T46 T47 T48 T49 T50 T51 T52 T53 T54 T55 T56 T57 T58 T59 T60 T61 T62 T63 T64 T65 T66 T67 T68 T69 T70 T71 T72 T73 T74 T75 T76 T77 T78 T79 T80 T81 T82 T83 T84 T85 T86 T87 T88 T89 T90 T91 T92 T93 T94 T95 T96 T97) in
              _).
      intros ev.
      Time refine (fun H : (fun ev => @BigAnd (T0 (fst ev)) (T1 (fst ev)) (T2 (fst ev)) (T3 (fst ev)) (T4 (fst ev)) (T5 (fst ev)) (T6 (fst ev)) (T7 (fst ev)) (T8 (fst ev)) (T9 (fst ev)) (T10 (fst ev)) (T11 (fst ev)) (T12 (fst ev)) (T13 (fst ev)) (T14 (fst ev)) (T15 (fst ev)) (T16 (fst ev)) (T17 (fst ev)) (T18 (fst ev)) (T19 (fst ev)) (T20 (fst ev)) (T21 (fst ev)) (T22 (fst ev)) (T23 (fst ev)) (T24 (fst ev)) (T25 (fst ev)) (T26 (fst ev)) (T27 (fst ev)) (T28 (fst ev)) (T29 (fst ev)) (T30 (fst ev)) (T31 (fst ev)) (T32 (fst ev)) (T33 (fst ev)) (T34 (fst ev)) (T35 (fst ev)) (T36 (fst ev)) (T37 (fst ev)) (T38 (fst ev)) (T39 (fst ev)) (T40 (fst ev)) (T41 (fst ev)) (T42 (fst ev)) (T43 (fst ev)) (T44 (fst ev)) (T45 (fst ev)) (T46 (fst ev)) (T47 (fst ev)) (T48 (fst ev)) (T49 (fst ev)) (T50 (fst ev)) (T51 (fst ev)) (T52 (fst ev)) (T53 (fst ev)) (T54 (fst ev)) (T55 (fst ev)) (T56 (fst ev)) (T57 (fst ev)) (T58 (fst ev)) (T59 (fst ev)) (T60 (fst ev)) (T61 (fst ev)) (T62 (fst ev)) (T63 (fst ev)) (T64 (fst ev)) (T65 (fst ev)) (T66 (fst ev)) (T67 (fst ev)) (T68 (fst ev)) (T69 (fst ev)) (T70 (fst ev)) (T71 (fst ev)) (T72 (fst ev)) (T73 (fst ev)) (T74 (fst ev)) (T75 (fst ev)) (T76 (fst ev)) (T77 (fst ev)) (T78 (fst ev)) (T79 (fst ev)) (T80 (fst ev)) (T81 (fst ev)) (T82 (fst ev)) (T83 (fst ev)) (T84 (fst ev)) (T85 (fst ev)) (T86 (fst ev)) (T87 (fst ev)) (T88 (fst ev)) (T89 (fst ev)) (T90 (fst ev)) (T91 (fst ev)) (T92 (fst ev)) (T93 (fst ev)) (T94 (fst ev)) (T95 (fst ev)) (T96 (fst ev)) (T97 (fst ev)) (T98 (fst ev))) ev => _).
      subst T0.
    Ltac do_pattern_fst ev :=
      lazymatch goal with |- context[?p ev] => pattern (p ev) end.
    do_pattern_fst ev. refine (pf0 H). }
    all:cbv beta in H.
    Time Optimize Proof.
    Time Optimize Heap.
    Time all:let G := match goal with |- ?G => G end in
             first [ has_evar G; shelve | idtac ].
    Time all: first [ do_pattern_fst ev | pattern (fst ev) ].
    { Time refine (pf1 H). }
    { Time refine (pf2 H). }
    { Time refine (pf3 H). }
    { Time refine (pf4 H). }
    { Time refine (pf5 H). }
    { Time refine (pf6 H). }
    { Time refine (pf7 H). }
    { Time refine (pf8 H). }
    { Time refine (pf9 H). }
    { Time refine (pf10 H). }
    { Time refine (pf11 H). }
    { Time refine (pf12 H). }
    { Time refine (pf13 H). }
    { Time refine (pf14 H). }
    { Time refine (pf15 H). }
    { Time refine (pf16 H). }
    { Time refine (pf17 H). }
    { Time refine (pf18 H). }
    { Time refine (pf19 H). }
    { Time refine (pf20 H). }
    { Time refine (pf21 H). }
    { Time refine (pf22 H). }
    { Time refine (pf23 H). }
    { Time refine (pf24 H). }
    { Time refine (pf25 H). }
    { Time refine (pf26 H). }
    { Time refine (pf27 H). }
    { Time refine (pf28 H). }
    { Time refine (pf29 H). }
    { Time refine (pf30 H). }
    { Time refine (pf31 H). }
    { Time refine (pf32 H). }
    { Time refine (pf33 H). }
    { Time refine (pf34 H). }
    { Time refine (pf35 H). }
    { Time refine (pf36 H). }
    { Time refine (pf37 H). }
    { Time refine (pf38 H). }
    { Time refine (pf39 H). }
    { Time refine (pf40 H). }
    { Time refine (pf41 H). }
    { Time refine (pf42 H). }
    { Time refine (pf43 H). }
    { Time refine (pf44 H). }
    { Time refine (pf45 H). }
    { Time refine (pf46 H). }
    { Time refine (pf47 H). }
    { Time refine (pf48 H). }
    { Time refine (pf49 H). }
    { Time refine (pf50 H). }
    { Time refine (pf51 H). }
    { Time refine (pf52 H). }
    { Time refine (pf53 H). }
    { Time refine (pf54 H). }
    { Time refine (pf55 H). }
    { Time refine (pf56 H). }
    { Time refine (pf57 H). }
    { Time refine (pf58 H). }
    { Time refine (pf59 H). }
    { Time refine (pf60 H). }
    { Time refine (pf61 H). }
    { Time refine (pf62 H). }
    { Time refine (pf63 H). }
    { Time refine (pf64 H). }
    { Time refine (pf65 H). }
    { Time refine (pf66 H). }
    { Time refine (pf67 H). }
    { Time refine (pf68 H). }
    { Time refine (pf69 H). }
    { Time refine (pf70 H). }
    { Time refine (pf71 H). }
    { Time refine (pf72 H). }
    { Time refine (pf73 H). }
    { Time refine (pf74 H). }
    { Time refine (pf75 H). }
    { Time refine (pf76 H). }
    { Time refine (pf77 H). }
    { Time refine (pf78 H). }
    { Time refine (pf79 H). }
    { Time refine (pf80 H). }
    { Time refine (pf81 H). }
    { Time refine (pf82 H). }
    { Time refine (pf83 H). }
    { Time refine (pf84 H). }
    { Time refine (pf85 H). }
    { Time refine (pf86 H). }
    { Time refine (pf87 H). }
    { Time refine (pf88 H). }
    { Time refine (pf89 H). }
    { Time refine (pf90 H). }
    { Time refine (pf91 H). }
    { Time refine (pf92 H). }
    { Time refine (pf93 H). }
    { Time refine (pf94 H). }
    { Time refine (pf95 H). }
    { Time refine (pf96 H). }
    { Time refine (pf97 H). }
    { Time refine (pf98 H). }
    Time Optimize Proof.
    Time Optimize Heap.
    Time Defined.
