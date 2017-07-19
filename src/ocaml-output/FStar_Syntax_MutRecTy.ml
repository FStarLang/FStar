open Prims
let disentangle_abbrevs_from_bundle:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let sigattrs =
            FStar_List.collect (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
              sigelts in
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____63;
                             FStar_Syntax_Syntax.lbunivs = uu____64;
                             FStar_Syntax_Syntax.lbtyp = uu____65;
                             FStar_Syntax_Syntax.lbeff = uu____66;
                             FStar_Syntax_Syntax.lbdef = uu____67;_}::[]),uu____68)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____91,uu____92) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____99 -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, members));
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigquals = quals;
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = sigattrs
               }, [])
          | uu____112 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____131,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____133;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____134;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____135;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____136;_}::[]),uu____137)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____160 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____189 =
                    let uu____192 = FStar_ST.read not_unfolded_yet in
                    FStar_All.pipe_right uu____192
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____212,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____214;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____215;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____216;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____217;_}::[]),uu____218)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____241 -> true)) in
                  FStar_ST.write not_unfolded_yet uu____189 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____264,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____266;
                                      FStar_Syntax_Syntax.lbtyp = uu____267;
                                      FStar_Syntax_Syntax.lbeff = uu____268;
                                      FStar_Syntax_Syntax.lbdef = uu____269;_}::[]),uu____270)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____293 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____310,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____311;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____312;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____313;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____314;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____316);
                          FStar_Syntax_Syntax.sigrng = uu____317;
                          FStar_Syntax_Syntax.sigquals = uu____318;
                          FStar_Syntax_Syntax.sigmeta = uu____319;
                          FStar_Syntax_Syntax.sigattrs = uu____320;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____355 -> FStar_Pervasives_Native.None in
                  let uu____362 =
                    let uu____369 = FStar_ST.read rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____369 replacee_term in
                  match uu____362 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____393 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____393 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____397 =
                             let uu____398 = FStar_ST.read in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____398 in
                           if uu____397
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
                       | uu____409 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____414)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___182_435  ->
                                match uu___182_435 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____436 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____439 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____445 =
                          let uu____448 = FStar_ST.read in_progress in lid ::
                            uu____448 in
                        FStar_ST.write in_progress uu____445);
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
                                    let uu___183_463 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___183_463.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___183_463.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___183_463.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid]) in
                                  ((let uu____476 =
                                      let uu____479 =
                                        FStar_ST.read
                                          rev_unfolded_type_abbrevs in
                                      (let uu___184_487 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___184_487.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___184_487.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___184_487.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____479 in
                                    FStar_ST.write rev_unfolded_type_abbrevs
                                      uu____476);
                                   (match () with
                                    | () ->
                                        ((let uu____493 =
                                            let uu____496 =
                                              FStar_ST.read in_progress in
                                            FStar_List.tl uu____496 in
                                          FStar_ST.write in_progress
                                            uu____493);
                                         (match () with | () -> tm'))))))))
                  | uu____507 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____513 =
                  let uu____514 = FStar_ST.read not_unfolded_yet in
                  match uu____514 with
                  | x::uu____524 -> let _unused = unfold_abbrev x in aux ()
                  | uu____528 ->
                      let uu____531 = FStar_ST.read rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____531 in
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
                           ((uu____584,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____586;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____587;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____588;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____590)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____617 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu____629 = find_in_unfolded fv in
                  match uu____629 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____645 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___185_680 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs1, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___185_680.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___185_680.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___185_680.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___185_680.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs1,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___186_700 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs1, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___186_700.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___186_700.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___186_700.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___186_700.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____703,uu____704) -> []
                  | uu____709 ->
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
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = sigattrs
                } in
              (new_bundle, unfolded_type_abbrevs)