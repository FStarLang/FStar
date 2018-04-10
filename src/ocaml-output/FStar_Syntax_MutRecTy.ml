open Prims
let (disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let sigattrs =
            FStar_List.collect (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
              sigelts
             in
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____69;
                             FStar_Syntax_Syntax.lbunivs = uu____70;
                             FStar_Syntax_Syntax.lbtyp = uu____71;
                             FStar_Syntax_Syntax.lbeff = uu____72;
                             FStar_Syntax_Syntax.lbdef = uu____73;
                             FStar_Syntax_Syntax.lbattrs = uu____74;
                             FStar_Syntax_Syntax.lbpos = uu____75;_}::[]),uu____76)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____99,uu____100) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____107 -> []))
             in
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
          | uu____120 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____141,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____143;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____144;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____145;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____146;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____147;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____148;_}::[]),uu____149)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____172 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____202 =
                    let uu____205 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____205
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____273,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____275;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____276;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____277;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____278;
                                              FStar_Syntax_Syntax.lbattrs =
                                                uu____279;
                                              FStar_Syntax_Syntax.lbpos =
                                                uu____280;_}::[]),uu____281)
                                ->
                                let uu____304 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____304
                            | uu____305 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____202  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____377,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____379;
                                      FStar_Syntax_Syntax.lbtyp = uu____380;
                                      FStar_Syntax_Syntax.lbeff = uu____381;
                                      FStar_Syntax_Syntax.lbdef = uu____382;
                                      FStar_Syntax_Syntax.lbattrs = uu____383;
                                      FStar_Syntax_Syntax.lbpos = uu____384;_}::[]),uu____385)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____408 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____422,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____423;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____424;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____425;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____426;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____428;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____429;_}::[]),uu____430);
                          FStar_Syntax_Syntax.sigrng = uu____431;
                          FStar_Syntax_Syntax.sigquals = uu____432;
                          FStar_Syntax_Syntax.sigmeta = uu____433;
                          FStar_Syntax_Syntax.sigattrs = uu____434;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____467 -> FStar_Pervasives_Native.None  in
                  let uu____472 =
                    let uu____477 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____477 replacee_term  in
                  match uu____472 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____538 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____538 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____542 =
                             let uu____543 = FStar_ST.op_Bang in_progress  in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____543
                              in
                           if uu____542
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____598 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____598
                           else unfold_abbrev se
                       | uu____600 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____605)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___29_626  ->
                                match uu___29_626 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____627 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____630 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      let uu____635 =
                        let uu____636 =
                          let uu____639 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____639  in
                        FStar_ST.op_Colon_Equals in_progress uu____636  in
                      (match uu____635 with
                       | () ->
                           let uu____740 = remove_not_unfolded lid  in
                           (match uu____740 with
                            | () ->
                                let ty' =
                                  FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                    lb.FStar_Syntax_Syntax.lbtyp
                                   in
                                let tm' =
                                  FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let lb' =
                                  let uu___30_744 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname =
                                      (uu___30_744.FStar_Syntax_Syntax.lbname);
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___30_744.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp = ty';
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___30_744.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = tm';
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___30_744.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___30_744.FStar_Syntax_Syntax.lbpos)
                                  }  in
                                let sigelt' =
                                  FStar_Syntax_Syntax.Sig_let
                                    ((false, [lb']), [lid])
                                   in
                                let uu____756 =
                                  let uu____757 =
                                    let uu____760 =
                                      FStar_ST.op_Bang
                                        rev_unfolded_type_abbrevs
                                       in
                                    (let uu___31_813 = x  in
                                     {
                                       FStar_Syntax_Syntax.sigel = sigelt';
                                       FStar_Syntax_Syntax.sigrng =
                                         (uu___31_813.FStar_Syntax_Syntax.sigrng);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         (uu___31_813.FStar_Syntax_Syntax.sigmeta);
                                       FStar_Syntax_Syntax.sigattrs =
                                         (uu___31_813.FStar_Syntax_Syntax.sigattrs)
                                     }) :: uu____760
                                     in
                                  FStar_ST.op_Colon_Equals
                                    rev_unfolded_type_abbrevs uu____757
                                   in
                                (match uu____756 with
                                 | () ->
                                     let uu____863 =
                                       let uu____864 =
                                         let uu____867 =
                                           FStar_ST.op_Bang in_progress  in
                                         FStar_List.tl uu____867  in
                                       FStar_ST.op_Colon_Equals in_progress
                                         uu____864
                                        in
                                     (match uu____863 with | () -> tm'))))
                  | uu____968 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____975 =
                  let uu____976 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____976 with
                  | x::uu____1031 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____1035 ->
                      let uu____1038 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____1038
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____1106 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____1106) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____1136,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv';
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____1138;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____1139;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____1140;
                                          FStar_Syntax_Syntax.lbdef = tm;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____1142;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____1143;_}::[]),uu____1144)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____1169 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____1181 = find_in_unfolded fv  in
                  match uu____1181 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____1191 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___32_1225 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___32_1225.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___32_1225.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___32_1225.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___32_1225.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___33_1245 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___33_1245.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___33_1245.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___33_1245.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___33_1245.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____1248,uu____1249) -> []
                  | uu____1254 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible"
                   in
                FStar_List.collect unfold_in_sig sigelts  in
              let new_members = filter_out_type_abbrevs members  in
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
                }  in
              (new_bundle, unfolded_type_abbrevs)
  