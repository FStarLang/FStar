open Prims
let disentangle_abbrevs_from_bundle :
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list)
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
                             FStar_Syntax_Syntax.lbdef = uu____35;_}::[]),uu____36,uu____37,uu____38)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let
                        (uu____54,uu____55,uu____56,uu____57) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____67 -> []))
             in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, quals, members));
                 FStar_Syntax_Syntax.sigrng = rng
               }, [])
          | uu____73 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____80,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____82;
                                         FStar_Syntax_Syntax.lbtyp = uu____83;
                                         FStar_Syntax_Syntax.lbeff = uu____84;
                                         FStar_Syntax_Syntax.lbdef = uu____85;_}::[]),uu____86,uu____87,uu____88)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____108 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"))
                 in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref []  in
                let in_progress = FStar_Util.mk_ref []  in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts
                   in
                let remove_not_unfolded lid =
                  let _0_732 =
                    let _0_731 = FStar_ST.read not_unfolded_yet  in
                    FStar_All.pipe_right _0_731
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____140,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____142;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____143;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____144;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____145;_}::[]),uu____146,uu____147,uu____148)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____171 -> true))
                     in
                  FStar_ST.write not_unfolded_yet _0_732  in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____188,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____190;
                                      FStar_Syntax_Syntax.lbtyp = uu____191;
                                      FStar_Syntax_Syntax.lbeff = uu____192;
                                      FStar_Syntax_Syntax.lbdef = uu____193;_}::[]),uu____194,uu____195,uu____196)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> Some x
                    | uu____221 -> None  in
                  let replacee_term x =
                    match replacee x with
                    | Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____231,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____232;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____233;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____234;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____235;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____237,uu____238,uu____239);
                          FStar_Syntax_Syntax.sigrng = uu____240;_}
                        -> Some tm
                    | uu____261 -> None  in
                  let uu____265 =
                    let _0_733 = FStar_ST.read rev_unfolded_type_abbrevs  in
                    FStar_Util.find_map _0_733 replacee_term  in
                  match uu____265 with
                  | Some x -> x
                  | None  ->
                      let uu____281 =
                        FStar_Util.find_map type_abbrev_sigelts replacee  in
                      (match uu____281 with
                       | Some se ->
                           let uu____284 =
                             let _0_734 = FStar_ST.read in_progress  in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               _0_734
                              in
                           (match uu____284 with
                            | true  ->
                                let msg =
                                  FStar_Util.format1
                                    "Cycle on %s in mutually recursive type abbreviations"
                                    ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                   in
                                Prims.raise
                                  (FStar_Errors.Error
                                     (msg,
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                            | uu____302 -> unfold_abbrev se)
                       | uu____303 -> t)
                
                and unfold_abbrev uu___203_305 =
                  match uu___203_305 with
                  | FStar_Syntax_Syntax.Sig_let
                      ((false ,lb::[]),uu____310,quals1,attr) ->
                      let quals2 =
                        FStar_All.pipe_right quals1
                          (FStar_List.filter
                             (fun uu___198_327  ->
                                match uu___198_327 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____326 -> true))
                         in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____335 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                         in
                      ((let _0_736 =
                          let _0_735 = FStar_ST.read in_progress  in lid ::
                            _0_735
                           in
                        FStar_ST.write in_progress _0_736);
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
                                    let uu___205_347 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___199_353.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___199_353.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___199_353.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    }  in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), rng, [lid], quals,
                                        attr)
                                     in
                                  ((let _0_738 =
                                      let _0_737 =
                                        FStar_ST.read
                                          rev_unfolded_type_abbrevs
                                         in
                                      sigelt' :: _0_737  in
                                    FStar_ST.write rev_unfolded_type_abbrevs
                                      uu____363);
                                   (match () with
                                    | () ->
                                        ((let _0_739 =
                                            FStar_List.tl
                                              (FStar_ST.read in_progress)
                                             in
                                          FStar_ST.write in_progress _0_739);
                                         (match () with | () -> tm'))))))))
                  | uu____385 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
                 in
                let rec aux uu____375 =
                  let uu____376 = FStar_ST.read not_unfolded_yet  in
                  match uu____376 with
                  | x::uu____383 -> let _unused = unfold_abbrev x  in aux ()
                  | uu____386 ->
                      FStar_List.rev
                        (FStar_ST.read rev_unfolded_type_abbrevs)
                   in
                aux ()  in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          Prims.op_Negation (FStar_Ident.lid_equals lid lid'))
                       type_abbrevs) l
                 in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____432,{
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv';
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____434;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____435;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____436;
                                         FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____438,uu____439,uu____440)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> Some tm
                       | uu____450 -> None)
                   in
                let unfold_fv t fv =
                  let uu____460 = find_in_unfolded fv  in
                  match uu____460 with | Some t' -> t' | uu____469 -> t  in
                let unfold_in_sig uu___204_477 =
                  match uu___204_477 with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc,quals1) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd  in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid, univs, bnd', ty', mut', dc, quals, rng)]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs,ty,res,npars,quals,mut,rng) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty  in
                      let mut' = filter_out_type_abbrevs mut  in
                      [FStar_Syntax_Syntax.Sig_datacon
                         (lid, univs, ty', res, npars, quals, mut', rng)]
                  | FStar_Syntax_Syntax.Sig_let
                      (uu____533,uu____534,uu____535,uu____536) -> []
                  | uu____543 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible"
                   in
                FStar_List.collect unfold_in_sig sigelts  in
              let new_members = filter_out_type_abbrevs members  in
              let new_bundle =
                FStar_Syntax_Syntax.Sig_bundle
                  (inductives_with_abbrevs_unfolded, quals, new_members, rng)
                 in
              (new_bundle, unfolded_type_abbrevs)
  