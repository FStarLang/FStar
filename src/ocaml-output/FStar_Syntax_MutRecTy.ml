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
                               uu____31;
                             FStar_Syntax_Syntax.lbunivs = uu____32;
                             FStar_Syntax_Syntax.lbtyp = uu____33;
                             FStar_Syntax_Syntax.lbeff = uu____34;
                             FStar_Syntax_Syntax.lbdef = uu____35;_}::[]),uu____36,uu____37)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let
                        (uu____51,uu____52,uu____53) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____59 -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, members));
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigqual = quals
               }, [])
          | uu____66 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____73,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____75;
                                         FStar_Syntax_Syntax.lbtyp = uu____76;
                                         FStar_Syntax_Syntax.lbeff = uu____77;
                                         FStar_Syntax_Syntax.lbdef = uu____78;_}::[]),uu____79,uu____80)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____98 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____120 =
                    let uu____122 = FStar_ST.read not_unfolded_yet in
                    FStar_All.pipe_right uu____122
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____130,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____132;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____133;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____134;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____135;_}::[]),uu____136,uu____137)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____155 -> true)) in
                  FStar_ST.write not_unfolded_yet uu____120 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____175,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____177;
                                      FStar_Syntax_Syntax.lbtyp = uu____178;
                                      FStar_Syntax_Syntax.lbeff = uu____179;
                                      FStar_Syntax_Syntax.lbdef = uu____180;_}::[]),uu____181,uu____182)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> Some x
                    | uu____204 -> None in
                  let replacee_term x =
                    match replacee x with
                    | Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____215,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____216;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____217;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____218;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____219;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____221,uu____222);
                          FStar_Syntax_Syntax.sigrng = uu____223;
                          FStar_Syntax_Syntax.sigqual = uu____224;_}
                        -> Some tm
                    | uu____243 -> None in
                  let uu____247 =
                    let uu____251 = FStar_ST.read rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____251 replacee_term in
                  match uu____247 with
                  | Some x -> x
                  | None  ->
                      let uu____265 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____265 with
                       | Some se ->
                           let uu____268 =
                             let uu____269 = FStar_ST.read in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____269 in
                           if uu____268
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                             Prims.raise
                               (FStar_Errors.Error
                                  (msg,
                                    (FStar_Ident.range_of_lid
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                           else unfold_abbrev se
                       | uu____289 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let
                      ((false ,lb::[]),uu____293,attr) ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigqual
                          (FStar_List.filter
                             (fun uu___203_307  ->
                                match uu___203_307 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____308 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____315 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____319 =
                          let uu____321 = FStar_ST.read in_progress in lid ::
                            uu____321 in
                        FStar_ST.write in_progress uu____319);
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
                                    let uu___204_333 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___204_333.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___204_333.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___204_333.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid], attr) in
                                  ((let uu____342 =
                                      let uu____344 =
                                        FStar_ST.read
                                          rev_unfolded_type_abbrevs in
                                      (let uu___205_349 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___205_349.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigqual = quals1
                                       }) :: uu____344 in
                                    FStar_ST.write rev_unfolded_type_abbrevs
                                      uu____342);
                                   (match () with
                                    | () ->
                                        ((let uu____354 =
                                            let uu____356 =
                                              FStar_ST.read in_progress in
                                            FStar_List.tl uu____356 in
                                          FStar_ST.write in_progress
                                            uu____354);
                                         (match () with | () -> tm'))))))))
                  | uu____364 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____369 =
                  let uu____370 = FStar_ST.read not_unfolded_yet in
                  match uu____370 with
                  | x::uu____377 -> let _unused = unfold_abbrev x in aux ()
                  | uu____380 ->
                      let uu____382 = FStar_ST.read rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____382 in
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
                           ((uu____411,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____413;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____414;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____415;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____417,uu____418)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> Some tm
                       | uu____442 -> None) in
                let unfold_fv t fv =
                  let uu____452 = find_in_unfolded fv in
                  match uu____452 with | Some t' -> t' | uu____461 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___206_485 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs1, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___206_485.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigqual =
                            (uu___206_485.FStar_Syntax_Syntax.sigqual)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs1,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___207_499 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs1, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___207_499.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigqual =
                            (uu___207_499.FStar_Syntax_Syntax.sigqual)
                        })]
                  | FStar_Syntax_Syntax.Sig_let
                      (uu____501,uu____502,uu____503) -> []
                  | uu____508 ->
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
                  FStar_Syntax_Syntax.sigqual = quals
                } in
              (new_bundle, unfolded_type_abbrevs)