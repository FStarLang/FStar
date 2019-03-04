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
                               uu____44706;
                             FStar_Syntax_Syntax.lbunivs = uu____44707;
                             FStar_Syntax_Syntax.lbtyp = uu____44708;
                             FStar_Syntax_Syntax.lbeff = uu____44709;
                             FStar_Syntax_Syntax.lbdef = uu____44710;
                             FStar_Syntax_Syntax.lbattrs = uu____44711;
                             FStar_Syntax_Syntax.lbpos = uu____44712;_}::[]),uu____44713)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____44732,uu____44733)
                        ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____44741 -> []))
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
          | uu____44754 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____44775,{
                                            FStar_Syntax_Syntax.lbname =
                                              FStar_Util.Inr fv;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____44777;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____44778;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____44779;
                                            FStar_Syntax_Syntax.lbdef =
                                              uu____44780;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____44781;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____44782;_}::[]),uu____44783)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____44802 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let uu____44834 =
                    let uu____44837 = FStar_ST.op_Bang not_unfolded_yet  in
                    FStar_All.pipe_right uu____44837
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____44902,{
                                                FStar_Syntax_Syntax.lbname =
                                                  FStar_Util.Inr fv;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uu____44904;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____44905;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____44906;
                                                FStar_Syntax_Syntax.lbdef =
                                                  uu____44907;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____44908;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____44909;_}::[]),uu____44910)
                                ->
                                let uu____44929 =
                                  FStar_Ident.lid_equals lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                Prims.op_Negation uu____44929
                            | uu____44931 -> true))
                     in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____44834  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____45004,{
                                        FStar_Syntax_Syntax.lbname =
                                          FStar_Util.Inr fv';
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____45006;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____45007;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____45008;
                                        FStar_Syntax_Syntax.lbdef =
                                          uu____45009;
                                        FStar_Syntax_Syntax.lbattrs =
                                          uu____45010;
                                        FStar_Syntax_Syntax.lbpos =
                                          uu____45011;_}::[]),uu____45012)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____45031 -> FStar_Pervasives_Native.None  in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____45046,{
                                            FStar_Syntax_Syntax.lbname =
                                              uu____45047;
                                            FStar_Syntax_Syntax.lbunivs =
                                              uu____45048;
                                            FStar_Syntax_Syntax.lbtyp =
                                              uu____45049;
                                            FStar_Syntax_Syntax.lbeff =
                                              uu____45050;
                                            FStar_Syntax_Syntax.lbdef = tm;
                                            FStar_Syntax_Syntax.lbattrs =
                                              uu____45052;
                                            FStar_Syntax_Syntax.lbpos =
                                              uu____45053;_}::[]),uu____45054);
                          FStar_Syntax_Syntax.sigrng = uu____45055;
                          FStar_Syntax_Syntax.sigquals = uu____45056;
                          FStar_Syntax_Syntax.sigmeta = uu____45057;
                          FStar_Syntax_Syntax.sigattrs = uu____45058;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____45087 -> FStar_Pervasives_Native.None  in
                  let uu____45092 =
                    let uu____45097 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map uu____45097 replacee_term  in
                  match uu____45092 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____45154 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____45154 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____45158 =
                             let uu____45160 = FStar_ST.op_Bang in_progress
                                in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____45160
                              in
                           if uu____45158
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             let uu____45214 =
                               FStar_Ident.range_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_CycleInRecTypeAbbreviation,
                                 msg) uu____45214
                           else unfold_abbrev se
                       | uu____45218 -> t)
                
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____45223)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___402_45240  ->
                                match uu___402_45240 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____45243 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____45247 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let uu____45254 =
                          let uu____45257 = FStar_ST.op_Bang in_progress  in
                          lid :: uu____45257  in
                        FStar_ST.op_Colon_Equals in_progress uu____45254);
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
                                    let uu___547_45354 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___547_45354.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___547_45354.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___547_45354.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm';
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___547_45354.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___547_45354.FStar_Syntax_Syntax.lbpos)
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid])
                                     in
                                  ((let uu____45363 =
                                      let uu____45366 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs
                                         in
                                      (let uu___551_45415 = x  in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___551_45415.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___551_45415.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___551_45415.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____45366
                                       in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____45363);
                                   (match () with
                                    | () ->
                                        ((let uu____45462 =
                                            let uu____45465 =
                                              FStar_ST.op_Bang in_progress
                                               in
                                            FStar_List.tl uu____45465  in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____45462);
                                         (match () with | () -> tm'))))))))
                  | uu____45558 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____45567 =
                  let uu____45568 = FStar_ST.op_Bang not_unfolded_yet  in
                  match uu____45568 with
                  | x::uu____45619 ->
                      let _unused = unfold_abbrev x  in aux ()
                  | uu____45623 ->
                      let uu____45626 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs  in
                      FStar_List.rev uu____45626
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          let uu____45691 = FStar_Ident.lid_equals lid lid'
                             in
                          Prims.op_Negation uu____45691) type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____45723,{
                                           FStar_Syntax_Syntax.lbname =
                                             FStar_Util.Inr fv';
                                           FStar_Syntax_Syntax.lbunivs =
                                             uu____45725;
                                           FStar_Syntax_Syntax.lbtyp =
                                             uu____45726;
                                           FStar_Syntax_Syntax.lbeff =
                                             uu____45727;
                                           FStar_Syntax_Syntax.lbdef = tm;
                                           FStar_Syntax_Syntax.lbattrs =
                                             uu____45729;
                                           FStar_Syntax_Syntax.lbpos =
                                             uu____45730;_}::[]),uu____45731)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____45752 -> FStar_Pervasives_Native.None)
                   in
                let unfold_fv t fv =
                  let uu____45766 = find_in_unfolded fv  in
                  match uu____45766 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____45776 -> t  in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___606_45811 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___606_45811.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___606_45811.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___606_45811.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___606_45811.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [(let uu___618_45833 = x  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___618_45833.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___618_45833.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___618_45833.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___618_45833.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____45837,uu____45838) ->
                      []
                  | uu____45843 ->
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
  