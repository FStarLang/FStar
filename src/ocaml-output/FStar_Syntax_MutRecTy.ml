open Prims
let (disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
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
                               uu____44695;
                             FStar_Syntax_Syntax.lbunivs = uu____44696;
                             FStar_Syntax_Syntax.lbtyp = uu____44697;
                             FStar_Syntax_Syntax.lbeff = uu____44698;
                             FStar_Syntax_Syntax.lbdef = uu____44699;
                             FStar_Syntax_Syntax.lbattrs = uu____44700;
                             FStar_Syntax_Syntax.lbpos = uu____44701;_}::[]),uu____44702)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____44721,uu____44722)
                        ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____44730 -> []))
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
          | uu____44743 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____44764,{
                                            FStar_Syntax_Syntax.lbname =
                                              FStar_Util.Inr fv;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____44766;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____44767;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____44768;
                                            FStar_Syntax_Syntax.lbdef =
                                              uu____44769;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____44770;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____44771;_}::[]),uu____44772)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____44791 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____44823 =
                    let uu____44826 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____44826
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____44891,{
                                                FStar_Syntax_Syntax.lbname =
                                                  FStar_Util.Inr fv;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uu____44893;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____44894;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____44895;
                                                FStar_Syntax_Syntax.lbdef =
                                                  uu____44896;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____44897;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____44898;_}::[]),uu____44899)
                                ->
                                let uu____44918 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____44918
                            | uu____44920 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____44823  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____44993,{
                                        FStar_Syntax_Syntax.lbname =
                                          FStar_Util.Inr fv';
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____44995;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____44996;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____44997;
                                        FStar_Syntax_Syntax.lbdef =
                                          uu____44998;
                                        FStar_Syntax_Syntax.lbattrs =
                                          uu____44999;
                                        FStar_Syntax_Syntax.lbpos =
                                          uu____45000;_}::[]),uu____45001)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____45020 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____45035,{
                                            FStar_Syntax_Syntax.lbname =
                                              uu____45036;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____45037;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____45038;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____45039;
                                            FStar_Syntax_Syntax.lbdef = tm;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____45041;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____45042;_}::[]),uu____45043);
                          FStar_Syntax_Syntax.sigrng = uu____45044;
                          FStar_Syntax_Syntax.sigquals = uu____45045;
                          FStar_Syntax_Syntax.sigmeta = uu____45046;
                          FStar_Syntax_Syntax.sigattrs = uu____45047;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____45076 -> FStar_Pervasives_Native.None  in
                  let uu____45081 =
                    let uu____45086 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____45086 replacee_term  in
                  match uu____45081 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____45143 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____45143 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____45147 =
                             let uu____45149 = FStar_ST.op_Bang in_progress
                                in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____45149
                              in
                           if uu____45147
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____45203 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____45203
                           else unfold_abbrev se
                       | uu____45207 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____45212)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___402_45229  ->
                                match uu___402_45229 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____45232 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____45236 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____45243 =
                          let uu____45246 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____45246  in
                        FStar_ST.op_Colon_Equals in_progress uu____45243);
                       (match () with
                        | () ->
                            (remove_not_unfolded lid;
                             (match () with
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
                                    let uu___547_45343 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___547_45343.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___547_45343.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___547_45343.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___547_45343.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___547_45343.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____45352 =
                                      let uu____45355 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___551_45404 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___551_45404.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___551_45404.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___551_45404.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____45355
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____45352);
                                   (match () with
                                    | () ->
                                        ((let uu____45451 =
                                            let uu____45454 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____45454  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____45451);
                                         (match () with | () -> tm'))))))))
                  | uu____45547 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____45556 =
                  let uu____45557 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____45557 with
                  | x::uu____45608 ->
                      let _unused = unfold_abbrev x  in aux ()
                  | uu____45612 ->
                      let uu____45615 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____45615
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____45680 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____45680) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____45712,{
                                           FStar_Syntax_Syntax.lbname =
                                             FStar_Util.Inr fv';
                                           FStar_Syntax_Syntax.lbunivs =
                                             uu____45714;
                                           FStar_Syntax_Syntax.lbtyp =
                                             uu____45715;
                                           FStar_Syntax_Syntax.lbeff =
                                             uu____45716;
                                           FStar_Syntax_Syntax.lbdef = tm;
                                           FStar_Syntax_Syntax.lbattrs =
                                             uu____45718;
                                           FStar_Syntax_Syntax.lbpos =
                                             uu____45719;_}::[]),uu____45720)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____45741 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____45755 = find_in_unfolded fv  in
                  match uu____45755 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____45765 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___606_45800 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___606_45800.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___606_45800.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___606_45800.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___606_45800.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___618_45822 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___618_45822.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___618_45822.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___618_45822.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___618_45822.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____45826,uu____45827) ->
                      []
                  | uu____45832 ->
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
  