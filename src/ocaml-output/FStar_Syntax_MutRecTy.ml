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
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____43;
                             FStar_Syntax_Syntax.lbunivs = uu____44;
                             FStar_Syntax_Syntax.lbtyp = uu____45;
                             FStar_Syntax_Syntax.lbeff = uu____46;
                             FStar_Syntax_Syntax.lbdef = uu____47;_}::[]),uu____48,uu____49)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let
                        (uu____63,uu____64,uu____65) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____71 -> [])) in
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
          | uu____78 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____94,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____96;
                                         FStar_Syntax_Syntax.lbtyp = uu____97;
                                         FStar_Syntax_Syntax.lbeff = uu____98;
                                         FStar_Syntax_Syntax.lbdef = uu____99;_}::[]),uu____100,uu____101)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____115 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____137 =
                    let uu____139 = FStar_ST.read not_unfolded_yet in
                    FStar_All.pipe_right uu____139
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____156,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____158;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____159;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____160;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____161;_}::[]),uu____162,uu____163)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____177 -> true)) in
                  FStar_ST.write not_unfolded_yet uu____137 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____197,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____199;
                                      FStar_Syntax_Syntax.lbtyp = uu____200;
                                      FStar_Syntax_Syntax.lbeff = uu____201;
                                      FStar_Syntax_Syntax.lbdef = uu____202;_}::[]),uu____203,uu____204)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____218 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____229,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____230;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____231;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____232;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____233;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____235,uu____236);
                          FStar_Syntax_Syntax.sigrng = uu____237;
                          FStar_Syntax_Syntax.sigquals = uu____238;
                          FStar_Syntax_Syntax.sigmeta = uu____239;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____258 -> FStar_Pervasives_Native.None in
                  let uu____262 =
                    let uu____266 = FStar_ST.read rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____266 replacee_term in
                  match uu____262 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____280 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____280 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____283 =
                             let uu____284 = FStar_ST.read in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____284 in
                           if uu____283
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
                       | uu____293 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let
                      ((false ,lb::[]),uu____297,attr) ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___182_312  ->
                                match uu___182_312 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____313 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____316 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____320 =
                          let uu____322 = FStar_ST.read in_progress in lid ::
                            uu____322 in
                        FStar_ST.write in_progress uu____320);
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
                                    let uu___183_334 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___183_334.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___183_334.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___183_334.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid], attr) in
                                  ((let uu____343 =
                                      let uu____345 =
                                        FStar_ST.read
                                          rev_unfolded_type_abbrevs in
                                      (let uu___184_351 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___184_351.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___184_351.FStar_Syntax_Syntax.sigmeta)
                                       }) :: uu____345 in
                                    FStar_ST.write rev_unfolded_type_abbrevs
                                      uu____343);
                                   (match () with
                                    | () ->
                                        ((let uu____356 =
                                            let uu____358 =
                                              FStar_ST.read in_progress in
                                            FStar_List.tl uu____358 in
                                          FStar_ST.write in_progress
                                            uu____356);
                                         (match () with | () -> tm'))))))))
                  | uu____366 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____371 =
                  let uu____372 = FStar_ST.read not_unfolded_yet in
                  match uu____372 with
                  | x::uu____379 -> let _unused = unfold_abbrev x in aux ()
                  | uu____382 ->
                      let uu____384 = FStar_ST.read rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____384 in
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
                           ((uu____424,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____426;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____427;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____428;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____430,uu____431)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____447 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu____457 = find_in_unfolded fv in
                  match uu____457 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____466 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___185_491 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs1, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___185_491.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___185_491.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___185_491.FStar_Syntax_Syntax.sigmeta)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs1,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___186_506 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs1, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___186_506.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___186_506.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___186_506.FStar_Syntax_Syntax.sigmeta)
                        })]
                  | FStar_Syntax_Syntax.Sig_let
                      (uu____508,uu____509,uu____510) -> []
                  | uu____515 ->
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