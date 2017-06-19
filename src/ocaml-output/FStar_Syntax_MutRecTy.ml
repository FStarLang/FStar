open Prims
let disentangle_abbrevs_from_bundle:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____35;
                             FStar_Syntax_Syntax.lbunivs = uu____36;
                             FStar_Syntax_Syntax.lbtyp = uu____37;
                             FStar_Syntax_Syntax.lbeff = uu____38;
                             FStar_Syntax_Syntax.lbdef = uu____39;_}::[]),uu____40,uu____41)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let
                        (uu____55,uu____56,uu____57) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____63 -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, members));
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigquals = quals;
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta
               }, [])
          | uu____70 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____77,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79;
                                         FStar_Syntax_Syntax.lbtyp = uu____80;
                                         FStar_Syntax_Syntax.lbeff = uu____81;
                                         FStar_Syntax_Syntax.lbdef = uu____82;_}::[]),uu____83,uu____84)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____102 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____124 =
                    let uu____126 = FStar_ST.read not_unfolded_yet in
                    FStar_All.pipe_right uu____126
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____134,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____136;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____137;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____138;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____139;_}::[]),uu____140,uu____141)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____159 -> true)) in
                  FStar_ST.write not_unfolded_yet uu____124 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____179,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____181;
                                      FStar_Syntax_Syntax.lbtyp = uu____182;
                                      FStar_Syntax_Syntax.lbeff = uu____183;
                                      FStar_Syntax_Syntax.lbdef = uu____184;_}::[]),uu____185,uu____186)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> Some x
                    | uu____208 -> None in
                  let replacee_term x =
                    match replacee x with
                    | Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____219,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____220;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____221;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____222;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____223;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____225,uu____226);
                          FStar_Syntax_Syntax.sigrng = uu____227;
                          FStar_Syntax_Syntax.sigquals = uu____228;
                          FStar_Syntax_Syntax.sigmeta = uu____229;_}
                        -> Some tm
                    | uu____248 -> None in
                  let uu____252 =
                    let uu____256 = FStar_ST.read rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____256 replacee_term in
                  match uu____252 with
                  | Some x -> x
                  | None  ->
                      let uu____270 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____270 with
                       | Some se ->
                           let uu____273 =
                             let uu____274 = FStar_ST.read in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____274 in
                           if uu____273
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                             raise
                               (FStar_Errors.Error
                                  (msg,
                                    (FStar_Ident.range_of_lid
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                           else unfold_abbrev se
                       | uu____294 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let
                      ((false ,lb::[]),uu____298,attr) ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___190_312  ->
                                match uu___190_312 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____313 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____320 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____324 =
                          let uu____326 = FStar_ST.read in_progress in lid ::
                            uu____326 in
                        FStar_ST.write in_progress uu____324);
                       (match () with
                        | () ->
                            (remove_not_unfolded lid;
                             (match () with
                              | () ->
                                  let ty' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbtyp in
                                  let tm' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbdef in
                                  let lb' =
                                    let uu___191_338 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___191_338.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___191_338.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___191_338.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid], attr) in
                                  ((let uu____347 =
                                      let uu____349 =
                                        FStar_ST.read
                                          rev_unfolded_type_abbrevs in
                                      (let uu___192_354 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___192_354.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___192_354.FStar_Syntax_Syntax.sigmeta)
                                       }) :: uu____349 in
                                    FStar_ST.write rev_unfolded_type_abbrevs
                                      uu____347);
                                   (match () with
                                    | () ->
                                        ((let uu____359 =
                                            let uu____361 =
                                              FStar_ST.read in_progress in
                                            FStar_List.tl uu____361 in
                                          FStar_ST.write in_progress
                                            uu____359);
                                         (match () with | () -> tm'))))))))
                  | uu____369 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____374 =
                  let uu____375 = FStar_ST.read not_unfolded_yet in
                  match uu____375 with
                  | x::uu____382 -> let _unused = unfold_abbrev x in aux ()
                  | uu____385 ->
                      let uu____387 = FStar_ST.read rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____387 in
                aux () in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          Prims.op_Negation (FStar_Ident.lid_equals lid lid'))
                       type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____416,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____418;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____419;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____420;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____422,uu____423)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> Some tm
                       | uu____447 -> None) in
                let unfold_fv t fv =
                  let uu____457 = find_in_unfolded fv in
                  match uu____457 with | Some t' -> t' | uu____466 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___193_490 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs1, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___193_490.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___193_490.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___193_490.FStar_Syntax_Syntax.sigmeta)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs1,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___194_504 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs1, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___194_504.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___194_504.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___194_504.FStar_Syntax_Syntax.sigmeta)
                        })]
                  | FStar_Syntax_Syntax.Sig_let
                      (uu____506,uu____507,uu____508) -> []
                  | uu____513 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible" in
                FStar_List.collect unfold_in_sig sigelts in
              let new_members = filter_out_type_abbrevs members in
              let new_bundle =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_bundle
                       (inductives_with_abbrevs_unfolded, new_members));
                  FStar_Syntax_Syntax.sigrng = rng;
                  FStar_Syntax_Syntax.sigquals = quals;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
                } in
              (new_bundle, unfolded_type_abbrevs)