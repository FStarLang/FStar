open Prims
let interleave :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list
  =
  fun iface  ->
    fun impl  ->
      let id_eq_lid i l =
        i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText  in
      let is_val x d =
        match d.FStar_Parser_AST.d with
        | FStar_Parser_AST.Val (y,uu____28) ->
            x.FStar_Ident.idText = y.FStar_Ident.idText
        | uu____29 -> false  in
      let is_type x d =
        match d.FStar_Parser_AST.d with
        | FStar_Parser_AST.Tycon (uu____37,tys) ->
            FStar_All.pipe_right tys
              (FStar_Util.for_some
                 (fun uu____54  ->
                    match uu____54 with
                    | (t,uu____59) ->
                        (FStar_Parser_AST.id_of_tycon t) =
                          x.FStar_Ident.idText))
        | uu____62 -> false  in
      let is_let x d =
        match d.FStar_Parser_AST.d with
        | FStar_Parser_AST.TopLevelLet (uu____70,defs) ->
            let _0_879 = FStar_Parser_AST.lids_of_let defs  in
            FStar_All.pipe_right _0_879 (FStar_Util.for_some (id_eq_lid x))
        | FStar_Parser_AST.Tycon (uu____79,tys) ->
            let _0_880 =
              FStar_All.pipe_right tys
                (FStar_List.map
                   (fun uu____98  -> match uu____98 with | (x,uu____103) -> x))
               in
            FStar_All.pipe_right _0_880
              (FStar_Util.for_some
                 (fun uu___124_110  ->
                    match uu___124_110 with
                    | FStar_Parser_AST.TyconAbbrev
                        (id',uu____112,uu____113,uu____114) ->
                        x.FStar_Ident.idText = id'.FStar_Ident.idText
                    | uu____115 -> false))
        | uu____116 -> false  in
      let prefix_until_let x ds =
        FStar_All.pipe_right ds (FStar_Util.prefix_until (is_let x))  in
      let aux_ml iface impl =
        let rec interleave_vals vals impl =
          match vals with
          | [] -> impl
          | { FStar_Parser_AST.d = FStar_Parser_AST.Val (x,uu____166);
              FStar_Parser_AST.drange = uu____167;
              FStar_Parser_AST.doc = uu____168;
              FStar_Parser_AST.quals = uu____169;
              FStar_Parser_AST.attrs = uu____170;_}::remaining_vals ->
              let d = FStar_List.hd vals  in
              let lopt = prefix_until_let x impl  in
              (match lopt with
               | None  ->
                   Prims.raise
                     (FStar_Errors.Error
                        ((Prims.strcat "No definition found for "
                            x.FStar_Ident.idText),
                          (d.FStar_Parser_AST.drange)))
               | Some (prefix,let_x,rest_impl) ->
                   let impl =
                     FStar_List.append prefix
                       (FStar_List.append [d; let_x] rest_impl)
                      in
                   interleave_vals remaining_vals impl)
          | uu____203::remaining_vals -> interleave_vals remaining_vals impl
           in
        interleave_vals iface impl  in
      let rec aux out iface impl =
        match iface with
        | [] ->
            let _0_881 =
              FStar_All.pipe_right (FStar_List.rev out) FStar_List.flatten
               in
            FStar_List.append _0_881 impl
        | d::ds ->
            (match d.FStar_Parser_AST.d with
             | FStar_Parser_AST.Tycon (uu____240,tys) when
                 FStar_All.pipe_right tys
                   (FStar_Util.for_some
                      (fun uu___125_257  ->
                         match uu___125_257 with
                         | (FStar_Parser_AST.TyconAbstract
                            uu____261,uu____262) -> true
                         | uu____270 -> false))
                 ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Interface contains an abstract 'type' declaration; use 'val' instead",
                        (d.FStar_Parser_AST.drange)))
             | FStar_Parser_AST.Val (x,t) ->
                 ((let uu____278 =
                     FStar_All.pipe_right impl1
                       (FStar_List.tryFind
                          (fun d  -> (is_val x d) || (is_type x d)))
                      in
                   match uu____272 with
                   | None  -> ()
                   | Some
                       { FStar_Parser_AST.d = FStar_Parser_AST.Val uu____283;
                         FStar_Parser_AST.drange = r;
                         FStar_Parser_AST.doc = uu____285;
                         FStar_Parser_AST.quals = uu____286;
                         FStar_Parser_AST.attrs = uu____287;_}
                       ->
                       Prims.raise
                         (FStar_Errors.Error
                            (let _0_883 =
                               let _0_882 = FStar_Parser_AST.decl_to_string d
                                  in
                               FStar_Util.format1
                                 "%s is repeated in the implementation"
                                 _0_882
                                in
                             (_0_883, r)))
                   | Some i ->
                       Prims.raise
                         (FStar_Errors.Error
                            (let _0_885 =
                               let _0_884 = FStar_Parser_AST.decl_to_string d
                                  in
                               FStar_Util.format1
                                 "%s in the interface is implemented with a 'type'"
                                 _0_884
                                in
                             (_0_885, (i.FStar_Parser_AST.drange)))));
                  (let uu____286 = prefix_until_let x iface  in
                   match uu____286 with
                   | Some uu____294 ->
                       Prims.raise
                         (FStar_Errors.Error
                            (let _0_886 =
                               FStar_Util.format2
                                 "'val %s' and 'let %s' cannot both be provided in an interface"
                                 x.FStar_Ident.idText x.FStar_Ident.idText
                                in
                             (_0_886, (d.FStar_Parser_AST.drange))))
                   | None  ->
                       let lopt = prefix_until_let x impl  in
                       (match lopt with
                        | None  ->
                            let uu____347 =
                              FStar_All.pipe_right d.FStar_Parser_AST.quals
                                (FStar_List.contains
                                   FStar_Parser_AST.Assumption)
                               in
                            (match uu____324 with
                             | true  -> aux ([d] :: out) ds impl
                             | uu____327 ->
                                 Prims.raise
                                   (FStar_Errors.Error
                                      ((Prims.strcat
                                          "No definition found for "
                                          x.FStar_Ident.idText),
                                        (d.FStar_Parser_AST.drange))))
                        | Some (prefix,let_x,rest_impl) ->
                            let uu____341 =
                              FStar_All.pipe_right d.FStar_Parser_AST.quals
                                (FStar_List.contains
                                   FStar_Parser_AST.Assumption)
                               in
                            (match uu____341 with
                             | true  ->
                                 Prims.raise
                                   (FStar_Errors.Error
                                      (let _0_888 =
                                         let _0_887 =
                                           FStar_Range.string_of_range
                                             let_x.FStar_Parser_AST.drange
                                            in
                                         FStar_Util.format2
                                           "Assumed declaration %s is defined at %s"
                                           x.FStar_Ident.idText _0_887
                                          in
                                       (_0_888, (d.FStar_Parser_AST.drange))))
                             | uu____344 ->
                                 let remaining_iface_vals =
                                   FStar_All.pipe_right ds
                                     (FStar_List.collect
                                        (fun d  ->
                                           match d.FStar_Parser_AST.d with
                                           | FStar_Parser_AST.Val
                                               (x,uu____352) -> [x]
                                           | uu____353 -> []))
                                    in
                                 let uu____354 =
                                   FStar_All.pipe_right prefix
                                     (FStar_List.tryFind
                                        (fun d  ->
                                           FStar_All.pipe_right
                                             remaining_iface_vals
                                             (FStar_Util.for_some
                                                (fun x  -> is_let x d))))
                                    in
                                 (match uu____354 with
                                  | Some d ->
                                      Prims.raise
                                        (FStar_Errors.Error
                                           (let _0_891 =
                                              let _0_890 =
                                                FStar_Parser_AST.decl_to_string
                                                  d
                                                 in
                                              let _0_889 =
                                                FStar_Parser_AST.decl_to_string
                                                  let_x
                                                 in
                                              FStar_Util.format2
                                                "%s is out of order with %s"
                                                _0_890 _0_889
                                               in
                                            (_0_891,
                                              (d.FStar_Parser_AST.drange))))
                                  | uu____364 ->
                                      (match let_x.FStar_Parser_AST.d with
                                       | FStar_Parser_AST.TopLevelLet
                                           (uu____367,defs) ->
                                           let def_lids =
                                             FStar_Parser_AST.lids_of_let
                                               defs
                                              in
                                           let iface_prefix_opt =
                                             FStar_All.pipe_right iface
                                               (FStar_Util.prefix_until
                                                  (fun d  ->
                                                     match d.FStar_Parser_AST.d
                                                     with
                                                     | FStar_Parser_AST.Val
                                                         (y,uu____393) ->
                                                         Prims.op_Negation
                                                           (FStar_All.pipe_right
                                                              def_lids
                                                              (FStar_Util.for_some
                                                                 (id_eq_lid y)))
                                                     | uu____395 -> true))
                                              in
                                           let uu____396 =
                                             match iface_prefix_opt with
                                             | None  -> (iface, [])
                                             | Some
                                                 (all_vals_for_defs,first_non_val,rest_iface)
                                                 ->
                                                 (all_vals_for_defs,
                                                   (first_non_val ::
                                                   rest_iface))
                                              in
                                           (match uu____396 with
                                            | (all_vals_for_defs,rest_iface)
                                                ->
                                                let hoist =
                                                  FStar_List.append prefix
                                                    (FStar_List.append
                                                       all_vals_for_defs
                                                       [let_x])
                                                   in
                                                aux (hoist :: out) rest_iface
                                                  rest_impl)
                                       | uu____436 -> failwith "Impossible"))))))
             | uu____438 -> aux ([d] :: out) ds impl)
         in
      let uu____440 = FStar_Options.ml_ish ()  in
      match uu____440 with
      | true  -> aux_ml iface impl
      | uu____442 -> aux [] iface impl
  