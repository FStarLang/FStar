open Prims
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____5 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____5
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___195_37  ->
          match uu___195_37 with
          | (uu____41,Some (FStar_Syntax_Syntax.Implicit uu____42)) -> false
          | uu____44 -> true))
let resugar_arg_qual:
  FStar_Syntax_Syntax.arg_qualifier option ->
    FStar_Parser_AST.arg_qualifier option option
  =
  fun q  ->
    match q with
    | None  -> Some None
    | Some (FStar_Syntax_Syntax.Implicit b) ->
        if b then None else Some (Some FStar_Parser_AST.Implicit)
    | Some (FStar_Syntax_Syntax.Equality ) ->
        Some (Some FStar_Parser_AST.Equality)
let rec universe_to_int:
  Prims.int ->
    FStar_Syntax_Syntax.universe -> (Prims.int* FStar_Syntax_Syntax.universe)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____78 -> (n1, u)
let rec resugar_universe:
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
      | FStar_Syntax_Syntax.U_succ uu____97 ->
          let uu____98 = universe_to_int (Prims.parse_int "0") u in
          (match uu____98 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____103 =
                      let uu____104 =
                        let uu____105 =
                          let uu____111 = FStar_Util.string_of_int n1 in
                          (uu____111, None) in
                        FStar_Const.Const_int uu____105 in
                      FStar_Parser_AST.Const uu____104 in
                    mk1 uu____103 r
                | uu____117 ->
                    let e1 =
                      let uu____119 =
                        let uu____120 =
                          let uu____121 =
                            let uu____127 = FStar_Util.string_of_int n1 in
                            (uu____127, None) in
                          FStar_Const.Const_int uu____121 in
                        FStar_Parser_AST.Const uu____120 in
                      mk1 uu____119 r in
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____137 ->
               let t =
                 let uu____140 =
                   let uu____141 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____141 in
                 mk1 uu____140 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____144 =
                        let uu____145 =
                          let uu____149 = resugar_universe x r in
                          (acc, uu____149, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____145 in
                      mk1 uu____144 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____151 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____156 =
              let uu____159 =
                let uu____160 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____160 in
              (uu____159, r) in
            FStar_Ident.mk_ident uu____156 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op: Prims.string -> (Prims.string* Prims.int) option =
  fun s  ->
    let name_of_op uu___196_173 =
      match uu___196_173 with
      | "Amp" -> Some ("&", (Prims.parse_int "0"))
      | "At" -> Some ("@", (Prims.parse_int "0"))
      | "Plus" -> Some ("+", (Prims.parse_int "0"))
      | "Minus" -> Some ("-", (Prims.parse_int "0"))
      | "Subtraction" -> Some ("-", (Prims.parse_int "2"))
      | "Slash" -> Some ("/", (Prims.parse_int "0"))
      | "Less" -> Some ("<", (Prims.parse_int "0"))
      | "Equals" -> Some ("=", (Prims.parse_int "0"))
      | "Greater" -> Some (">", (Prims.parse_int "0"))
      | "Underscore" -> Some ("_", (Prims.parse_int "0"))
      | "Bar" -> Some ("|", (Prims.parse_int "0"))
      | "Bang" -> Some ("!", (Prims.parse_int "0"))
      | "Hat" -> Some ("^", (Prims.parse_int "0"))
      | "Percent" -> Some ("%", (Prims.parse_int "0"))
      | "Star" -> Some ("*", (Prims.parse_int "0"))
      | "Question" -> Some ("?", (Prims.parse_int "0"))
      | "Colon" -> Some (":", (Prims.parse_int "0"))
      | uu____211 -> None in
    match s with
    | "op_String_Assignment" -> Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" -> Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" -> Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" -> Some (".()", (Prims.parse_int "0"))
    | uu____225 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____231 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____231 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____238 ->
               let op =
                 let uu____241 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some (op,uu____258) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____241 in
               Some (op, (Prims.parse_int "0")))
        else None
let rec resugar_term_as_op:
  FStar_Syntax_Syntax.term -> (Prims.string* Prims.int) option =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Syntax_Const.op_Addition, "+");
      (FStar_Syntax_Const.op_Subtraction, "-");
      (FStar_Syntax_Const.op_Minus, "-");
      (FStar_Syntax_Const.op_Multiply, "*");
      (FStar_Syntax_Const.op_Division, "/");
      (FStar_Syntax_Const.op_Modulus, "%");
      (FStar_Syntax_Const.read_lid, "!");
      (FStar_Syntax_Const.list_append_lid, "@");
      (FStar_Syntax_Const.list_tot_append_lid, "@");
      (FStar_Syntax_Const.strcat_lid, "^");
      (FStar_Syntax_Const.pipe_right_lid, "|>");
      (FStar_Syntax_Const.pipe_left_lid, "<|");
      (FStar_Syntax_Const.op_Eq, "=");
      (FStar_Syntax_Const.op_ColonEq, ":=");
      (FStar_Syntax_Const.op_notEq, "<>");
      (FStar_Syntax_Const.not_lid, "~");
      (FStar_Syntax_Const.op_And, "&&");
      (FStar_Syntax_Const.op_Or, "||");
      (FStar_Syntax_Const.op_LTE, "<=");
      (FStar_Syntax_Const.op_GTE, ">=");
      (FStar_Syntax_Const.op_LT, "<");
      (FStar_Syntax_Const.op_GT, ">");
      (FStar_Syntax_Const.op_Modulus, "mod");
      (FStar_Syntax_Const.and_lid, "/\\");
      (FStar_Syntax_Const.or_lid, "\\/");
      (FStar_Syntax_Const.imp_lid, "==>");
      (FStar_Syntax_Const.iff_lid, "<==>");
      (FStar_Syntax_Const.precedes_lid, "<<");
      (FStar_Syntax_Const.eq2_lid, "==");
      (FStar_Syntax_Const.eq3_lid, "===");
      (FStar_Syntax_Const.forall_lid, "forall");
      (FStar_Syntax_Const.exists_lid, "exists");
      (FStar_Syntax_Const.salloc_lid, "alloc")] in
    let fallback fv =
      let uu____356 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____356 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
      | uu____381 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1")) in
          if FStar_Util.starts_with str "dtuple"
          then Some ("dtuple", (Prims.parse_int "0"))
          else
            if FStar_Util.starts_with str "tuple"
            then Some ("tuple", (Prims.parse_int "0"))
            else
              if FStar_Util.starts_with str "try_with"
              then Some ("try_with", (Prims.parse_int "0"))
              else
                (let uu____424 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____424
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____437 =
      let uu____438 = FStar_Syntax_Subst.compress t in
      uu____438.FStar_Syntax_Syntax.n in
    match uu____437 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1")) in
        let uu____466 = string_to_op s in
        (match uu____466 with | Some t1 -> Some t1 | uu____480 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____490 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____496 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____500 -> true
    | uu____501 -> false
let is_disj_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____505 -> true
    | uu____509 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____537 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____537 in
    let var a r =
      let uu____545 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____545 in
    let uu____546 =
      let uu____547 = FStar_Syntax_Subst.compress t in
      uu____547.FStar_Syntax_Syntax.n in
    match uu____546 with
    | FStar_Syntax_Syntax.Tm_delayed uu____550 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____573 = let uu____575 = bv_as_unique_ident x in [uu____575] in
          FStar_Ident.lid_of_ids uu____573 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____578 = let uu____580 = bv_as_unique_ident x in [uu____580] in
          FStar_Ident.lid_of_ids uu____578 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr in
        let s =
          if length1 = (Prims.parse_int "0")
          then a.FStar_Ident.str
          else
            FStar_Util.substring_from a.FStar_Ident.str
              (length1 + (Prims.parse_int "1")) in
        let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_" in
        if FStar_Util.starts_with s is_prefix
        then
          let rest =
            FStar_Util.substring_from s (FStar_String.length is_prefix) in
          let uu____604 =
            let uu____605 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____605 in
          mk1 uu____604
        else
          if
            FStar_Util.starts_with s FStar_Syntax_Util.field_projector_prefix
          then
            (let rest =
               FStar_Util.substring_from s
                 (FStar_String.length
                    FStar_Syntax_Util.field_projector_prefix) in
             let r =
               FStar_Util.split rest FStar_Syntax_Util.field_projector_sep in
             match r with
             | fst1::snd1::[] ->
                 let l =
                   FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos in
                 let r1 =
                   FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos)) in
                 mk1 (FStar_Parser_AST.Projector (l, r1))
             | uu____616 -> failwith "wrong projector format")
          else
            (let uu____619 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____620 =
                    let uu____621 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____621 in
                  let uu____622 = FStar_String.get s (Prims.parse_int "0") in
                  uu____620 <> uu____622) in
             if uu____619
             then
               let uu____623 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____623
             else
               (let uu____625 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____625))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____632 = FStar_Options.print_universes () in
        if uu____632
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____636 =
                   let uu____637 =
                     let uu____641 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____641, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____637 in
                 mk1 uu____636) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____644 = FStar_Syntax_Syntax.is_teff t in
        if uu____644
        then
          let uu____645 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____645
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____648 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____648
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____649 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____649
         | uu____650 ->
             let uu____651 = FStar_Options.print_universes () in
             if uu____651
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____662 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____662))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____665) ->
        let uu____688 = FStar_Syntax_Subst.open_term xs body in
        (match uu____688 with
         | (xs1,body1) ->
             let xs2 =
               let uu____694 = FStar_Options.print_implicits () in
               if uu____694 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____701  ->
                       match uu____701 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____721 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____721 with
         | (xs1,body1) ->
             let xs2 =
               let uu____727 = FStar_Options.print_implicits () in
               if uu____727 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____732 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____732 FStar_List.rev in
             let rec aux body3 uu___197_745 =
               match uu___197_745 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____758 =
          let uu____761 =
            let uu____762 = FStar_Syntax_Syntax.mk_binder x in [uu____762] in
          FStar_Syntax_Subst.open_term uu____761 phi in
        (match uu____758 with
         | (x1,phi1) ->
             let b =
               let uu____766 = FStar_List.hd x1 in
               resugar_binder uu____766 t.FStar_Syntax_Syntax.pos in
             let uu____769 =
               let uu____770 =
                 let uu____773 = resugar_term phi1 in (b, uu____773) in
               FStar_Parser_AST.Refine uu____770 in
             mk1 uu____769)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___198_803 =
          match uu___198_803 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____850 -> failwith "last of an empty list" in
        let rec last_two uu___199_874 =
          match uu___199_874 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____894::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____946::t1 -> last_two t1 in
        let rec last_three uu___200_974 =
          match uu___200_974 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____994::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1012::uu____1013::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1086::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1122  ->
                    match uu____1122 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1136 = FStar_Options.print_implicits () in
          if uu____1136 then args else filter_imp args in
        let uu____1145 = resugar_term_as_op e in
        (match uu____1145 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1151) ->
             (match args1 with
              | (fst1,uu____1155)::(snd1,uu____1157)::rest ->
                  let e1 =
                    let uu____1181 =
                      let uu____1182 =
                        let uu____1186 =
                          let uu____1188 = resugar_term fst1 in
                          let uu____1189 =
                            let uu____1191 = resugar_term snd1 in
                            [uu____1191] in
                          uu____1188 :: uu____1189 in
                        ((FStar_Ident.id_of_text "*"), uu____1186) in
                      FStar_Parser_AST.Op uu____1182 in
                    mk1 uu____1181 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1196  ->
                         match uu____1196 with
                         | (x,uu____1200) ->
                             let uu____1201 =
                               let uu____1202 =
                                 let uu____1206 =
                                   let uu____1208 =
                                     let uu____1210 = resugar_term x in
                                     [uu____1210] in
                                   e1 :: uu____1208 in
                                 ((FStar_Ident.id_of_text "*"), uu____1206) in
                               FStar_Parser_AST.Op uu____1202 in
                             mk1 uu____1201) e1 rest
              | uu____1212 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1218) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1240)::[] -> b
               | uu____1253 -> failwith "wrong arguments to dtuple" in
             let uu____1261 =
               let uu____1262 = FStar_Syntax_Subst.compress body in
               uu____1262.FStar_Syntax_Syntax.n in
             (match uu____1261 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1267) ->
                  let uu____1290 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1290 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1296 = FStar_Options.print_implicits () in
                         if uu____1296 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1304 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1315  ->
                            match uu____1315 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1323) -> resugar_as_app e args1
         | Some (ref_read,uu____1327) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1330 = FStar_List.hd args1 in
             (match uu____1330 with
              | (t1,uu____1340) ->
                  let uu____1345 =
                    let uu____1346 = FStar_Syntax_Subst.compress t1 in
                    uu____1346.FStar_Syntax_Syntax.n in
                  (match uu____1345 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1359 =
                         let uu____1360 =
                           let uu____1363 = resugar_term t1 in
                           (uu____1363, f) in
                         FStar_Parser_AST.Project uu____1360 in
                       mk1 uu____1359
                   | uu____1364 -> resugar_term t1))
         | Some ("try_with",uu____1365) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1381 =
               match new_args with
               | (a1,uu____1395)::(a2,uu____1397)::[] -> (a1, a2)
               | uu____1422 -> failwith "wrong arguments to try_with" in
             (match uu____1381 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1448 =
                      let uu____1449 = FStar_Syntax_Subst.compress term in
                      uu____1449.FStar_Syntax_Syntax.n in
                    match uu____1448 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1454) ->
                        let uu____1477 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1477 with | (x1,e2) -> e2)
                    | uu____1482 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1484 = decomp body in resugar_term uu____1484 in
                  let handler1 =
                    let uu____1486 = decomp handler in
                    resugar_term uu____1486 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1492,uu____1493,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1510,uu____1511,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1524 =
                          let uu____1525 =
                            let uu____1530 = resugar_body t11 in
                            (uu____1530, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1525 in
                        mk1 uu____1524
                    | uu____1532 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1565 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1581) -> resugar_as_app e args1
         | Some (op,uu____1585) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1636 -> (xs, pat, t1) in
             let resugar body =
               let uu____1644 =
                 let uu____1645 = FStar_Syntax_Subst.compress body in
                 uu____1645.FStar_Syntax_Syntax.n in
               match uu____1644 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1650) ->
                   let uu____1673 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1673 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1679 = FStar_Options.print_implicits () in
                          if uu____1679 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1685 =
                          let uu____1690 =
                            let uu____1691 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1691.FStar_Syntax_Syntax.n in
                          match uu____1690 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1731  ->
                                                 match uu____1731 with
                                                 | (e2,uu____1735) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1738) ->
                                    let uu____1739 =
                                      let uu____1741 =
                                        let uu____1742 = name s r in
                                        mk1 uu____1742 in
                                      [uu____1741] in
                                    [uu____1739]
                                | uu____1745 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1750 ->
                              let uu____1751 = resugar_term body2 in
                              ([], uu____1751) in
                        (match uu____1685 with
                         | (pats,body3) ->
                             let uu____1761 = uncurry xs3 pats body3 in
                             (match uu____1761 with
                              | (xs4,pats1,body4) ->
                                  let xs5 =
                                    FStar_All.pipe_right xs4 FStar_List.rev in
                                  if op = "forall"
                                  then
                                    mk1
                                      (FStar_Parser_AST.QForall
                                         (xs5, pats1, body4))
                                  else
                                    mk1
                                      (FStar_Parser_AST.QExists
                                         (xs5, pats1, body4)))))
               | uu____1788 ->
                   if op = "forall"
                   then
                     let uu____1789 =
                       let uu____1790 =
                         let uu____1797 = resugar_term body in
                         ([], [[]], uu____1797) in
                       FStar_Parser_AST.QForall uu____1790 in
                     mk1 uu____1789
                   else
                     (let uu____1804 =
                        let uu____1805 =
                          let uu____1812 = resugar_term body in
                          ([], [[]], uu____1812) in
                        FStar_Parser_AST.QExists uu____1805 in
                      mk1 uu____1804) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1832)::[] -> resugar b
                | uu____1845 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1852) ->
             let uu____1855 = FStar_List.hd args1 in
             (match uu____1855 with | (e1,uu____1865) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1892  ->
                       match uu____1892 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1897 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1897 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1905 =
                         let uu____1906 =
                           let uu____1910 =
                             let uu____1912 = last1 args1 in
                             resugar uu____1912 in
                           (op1, uu____1910) in
                         FStar_Parser_AST.Op uu____1906 in
                       mk1 uu____1905
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1924 =
                         let uu____1925 =
                           let uu____1929 =
                             let uu____1931 = last_two args1 in
                             resugar uu____1931 in
                           (op1, uu____1929) in
                         FStar_Parser_AST.Op uu____1925 in
                       mk1 uu____1924
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1943 =
                         let uu____1944 =
                           let uu____1948 =
                             let uu____1950 = last_three args1 in
                             resugar uu____1950 in
                           (op1, uu____1948) in
                         FStar_Parser_AST.Op uu____1944 in
                       mk1 uu____1943
                   | uu____1955 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1963 =
                    let uu____1964 =
                      let uu____1968 =
                        let uu____1970 = last_two args1 in resugar uu____1970 in
                      (op1, uu____1968) in
                    FStar_Parser_AST.Op uu____1964 in
                  mk1 uu____1963
              | uu____1975 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1978,t1)::[]) when
        let uu____2029 = is_disj_pat pat in Prims.op_Negation uu____2029 ->
        let bnds =
          let uu____2034 =
            let uu____2037 = resugar_pat pat in
            let uu____2038 = resugar_term e in (uu____2037, uu____2038) in
          [uu____2034] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2049,t1)::(pat2,uu____2052,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2127 =
          let uu____2128 =
            let uu____2132 = resugar_term e in
            let uu____2133 = resugar_term t1 in
            let uu____2134 = resugar_term t2 in
            (uu____2132, uu____2133, uu____2134) in
          FStar_Parser_AST.If uu____2128 in
        mk1 uu____2127
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2174 =
          match uu____2174 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2193 = resugar_term e1 in Some uu____2193 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2196 =
          let uu____2197 =
            let uu____2205 = resugar_term e in
            let uu____2206 = FStar_List.map resugar_branch branches in
            (uu____2205, uu____2206) in
          FStar_Parser_AST.Match uu____2197 in
        mk1 uu____2196
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2228) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2281 =
          let uu____2282 =
            let uu____2287 = resugar_term e in (uu____2287, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2282 in
        mk1 uu____2281
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2305 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2305 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2321 =
                 let uu____2324 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2324 in
               match uu____2321 with
               | (univs1,td) ->
                   let uu____2331 =
                     let uu____2338 =
                       let uu____2339 = FStar_Syntax_Subst.compress td in
                       uu____2339.FStar_Syntax_Syntax.n in
                     match uu____2338 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2348,(t1,uu____2350)::(d,uu____2352)::[]) ->
                         (t1, d)
                     | uu____2386 -> failwith "wrong let binding format" in
                   (match uu____2331 with
                    | (typ,def) ->
                        let uu____2407 =
                          let uu____2411 =
                            let uu____2412 = FStar_Syntax_Subst.compress def in
                            uu____2412.FStar_Syntax_Syntax.n in
                          match uu____2411 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2420) ->
                              let uu____2443 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2443 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2452 =
                                       FStar_Options.print_implicits () in
                                     if uu____2452 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2454 -> ([], def, false) in
                        (match uu____2407 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2475 =
                                 FStar_Options.print_universes () in
                               if uu____2475
                               then
                                 let uu____2476 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2476
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2481 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2492 =
                                     let uu____2493 =
                                       let uu____2494 =
                                         let uu____2498 =
                                           bv_as_unique_ident bv in
                                         (uu____2498, None) in
                                       FStar_Parser_AST.PatVar uu____2494 in
                                     mk_pat uu____2493 in
                                   (uu____2492, term) in
                             (match uu____2481 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2515  ->
                                              match uu____2515 with
                                              | (bv,uu____2519) ->
                                                  let uu____2520 =
                                                    let uu____2521 =
                                                      let uu____2525 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2525, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2521 in
                                                  mk_pat uu____2520)) in
                                    let uu____2527 =
                                      let uu____2530 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2530) in
                                    let uu____2532 =
                                      universe_to_string univs1 in
                                    (uu____2527, uu____2532)
                                  else
                                    (let uu____2536 =
                                       let uu____2539 = resugar_term term1 in
                                       (pat, uu____2539) in
                                     let uu____2540 =
                                       universe_to_string univs1 in
                                     (uu____2536, uu____2540))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2579) ->
        let s =
          let uu____2593 =
            let uu____2594 = FStar_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2594 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2593 in
        let uu____2598 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2598
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___201_2608 =
          match uu___201_2608 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2609 =
                let uu____2610 = FStar_Syntax_Subst.compress e in
                uu____2610.FStar_Syntax_Syntax.n in
              (match uu____2609 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2636 =
                       let uu____2637 = FStar_Syntax_Subst.compress h in
                       uu____2637.FStar_Syntax_Syntax.n in
                     match uu____2636 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2644 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2644, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2652 = aux h1 in
                         (match uu____2652 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2664 -> failwith "wrong Data_app head format" in
                   let uu____2668 = aux head1 in
                   (match uu____2668 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2683 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2683, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2692  ->
                               match uu____2692 with
                               | (t1,uu____2698) ->
                                   let uu____2699 = resugar_term t1 in
                                   (uu____2699, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2700 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2700
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2705 = FStar_Options.print_universes () in
                           if uu____2705
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2715,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2721,uu____2722) -> resugar_term e
                    | uu____2727 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2728 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2734,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2750 =
                      let uu____2751 =
                        let uu____2756 = resugar_seq t11 in
                        (uu____2756, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2751 in
                    mk1 uu____2750
                | uu____2758 -> t1 in
              resugar_seq term
          | FStar_Syntax_Syntax.Primop  -> resugar_term e
          | FStar_Syntax_Syntax.Masked_effect  -> resugar_term e
          | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term e
          | FStar_Syntax_Syntax.Mutable_alloc  ->
              let term = resugar_term e in
              (match term.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier ,l,t1)
                   ->
                   mk1
                     (FStar_Parser_AST.Let (FStar_Parser_AST.Mutable, l, t1))
               | uu____2771 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2773 =
                let uu____2774 = FStar_Syntax_Subst.compress e in
                uu____2774.FStar_Syntax_Syntax.n in
              (match uu____2773 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2778;
                      FStar_Syntax_Syntax.pos = uu____2779;
                      FStar_Syntax_Syntax.vars = uu____2780;_},(term,uu____2782)::[])
                   -> resugar_term term
               | uu____2804 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2826  ->
                       match uu____2826 with
                       | (x,uu____2830) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2832,p) ->
             let uu____2834 =
               let uu____2835 =
                 let uu____2839 = resugar_term e in (uu____2839, l, p) in
               FStar_Parser_AST.Labeled uu____2835 in
             mk1 uu____2834
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2848 =
               let uu____2849 =
                 let uu____2854 = resugar_term e in
                 let uu____2855 =
                   let uu____2856 =
                     let uu____2857 =
                       let uu____2863 =
                         let uu____2867 =
                           let uu____2870 = resugar_term t1 in
                           (uu____2870, FStar_Parser_AST.Nothing) in
                         [uu____2867] in
                       (name1, uu____2863) in
                     FStar_Parser_AST.Construct uu____2857 in
                   mk1 uu____2856 in
                 (uu____2854, uu____2855, None) in
               FStar_Parser_AST.Ascribed uu____2849 in
             mk1 uu____2848
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2880,t1) ->
             let uu____2886 =
               let uu____2887 =
                 let uu____2892 = resugar_term e in
                 let uu____2893 =
                   let uu____2894 =
                     let uu____2895 =
                       let uu____2901 =
                         let uu____2905 =
                           let uu____2908 = resugar_term t1 in
                           (uu____2908, FStar_Parser_AST.Nothing) in
                         [uu____2905] in
                       (name1, uu____2901) in
                     FStar_Parser_AST.Construct uu____2895 in
                   mk1 uu____2894 in
                 (uu____2892, uu____2893, None) in
               FStar_Parser_AST.Ascribed uu____2887 in
             mk1 uu____2886)
    | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild
and resugar_comp: FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term =
  fun c  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_Tot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2939 = FStar_Options.print_universes () in
             if uu____2939
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_Tot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.GTotal (typ,u) ->
        let t = resugar_term typ in
        (match u with
         | None  ->
             mk1
               (FStar_Parser_AST.Construct
                  (FStar_Syntax_Const.effect_GTot_lid,
                    [(t, FStar_Parser_AST.Nothing)]))
         | Some u1 ->
             let uu____2975 = FStar_Options.print_universes () in
             if uu____2975
             then
               let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_GTot_lid,
                      [(u2, FStar_Parser_AST.UnivApp);
                      (t, FStar_Parser_AST.Nothing)]))
             else
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Syntax_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)])))
    | FStar_Syntax_Syntax.Comp c1 ->
        let result =
          let uu____2998 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2998, FStar_Parser_AST.Nothing) in
        let uu____2999 = FStar_Options.print_effect_args () in
        if uu____2999
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___202_3039 =
                match uu___202_3039 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3081 -> aux l tl1
                     | uu____3086 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3106  ->
                 match uu____3106 with
                 | (e,uu____3112) ->
                     let uu____3113 = resugar_term e in
                     (uu____3113, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___203_3127 =
            match uu___203_3127 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3147 = resugar_term e in
                       (uu____3147, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3150 -> aux l tl1) in
          let decrease = aux [] c1.FStar_Syntax_Syntax.flags in
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name),
                 (FStar_List.append (result :: decrease) args1)))
        else
          mk1
            (FStar_Parser_AST.Construct
               ((c1.FStar_Syntax_Syntax.effect_name), [result]))
and resugar_binder:
  FStar_Syntax_Syntax.binder -> FStar_Range.range -> FStar_Parser_AST.binder
  =
  fun b  ->
    fun r  ->
      let uu____3174 = b in
      match uu____3174 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3178 =
                 let uu____3179 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3179 in
               FStar_Parser_AST.mk_binder uu____3178 r
                 FStar_Parser_AST.Type_level None
           | uu____3180 ->
               let uu____3181 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3181
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3183 =
                    let uu____3184 =
                      let uu____3187 = bv_as_unique_ident x in
                      (uu____3187, e) in
                    FStar_Parser_AST.Annotated uu____3184 in
                  FStar_Parser_AST.mk_binder uu____3183 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3195 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3195 in
      let uu____3196 =
        let uu____3197 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3197.FStar_Syntax_Syntax.n in
      match uu____3196 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3203 = mk1 FStar_Parser_AST.PatWild in Some uu____3203
          else
            (let uu____3205 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3205
               (fun aq  ->
                  let uu____3211 =
                    let uu____3212 =
                      let uu____3213 =
                        let uu____3217 = bv_as_unique_ident x in
                        (uu____3217, aq) in
                      FStar_Parser_AST.PatVar uu____3213 in
                    mk1 uu____3212 in
                  Some uu____3211))
      | uu____3219 ->
          let uu____3220 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3220
            (fun aq  ->
               let pat =
                 let uu____3227 =
                   let uu____3228 =
                     let uu____3232 = bv_as_unique_ident x in
                     (uu____3232, aq) in
                   FStar_Parser_AST.PatVar uu____3228 in
                 mk1 uu____3227 in
               let uu____3234 = FStar_Options.print_bound_var_types () in
               if uu____3234
               then
                 let uu____3236 =
                   let uu____3237 =
                     let uu____3238 =
                       let uu____3241 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3241) in
                     FStar_Parser_AST.PatAscribed uu____3238 in
                   mk1 uu____3237 in
                 Some uu____3236
               else Some pat)
and resugar_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let rec aux p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
      | FStar_Syntax_Syntax.Pat_disj args ->
          let args1 = FStar_List.map (fun p2  -> aux p2) args in
          mk1 (FStar_Parser_AST.PatOr args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
          mk1
            (FStar_Parser_AST.PatName
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          FStar_Ident.lid_equals
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Syntax_Const.cons_lid
          ->
          let args1 =
            FStar_List.map
              (fun uu____3294  -> match uu____3294 with | (p2,b) -> aux p2)
              args in
          mk1 (FStar_Parser_AST.PatList args1)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) when
          (FStar_Syntax_Util.is_tuple_data_lid'
             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
            ||
            (FStar_Syntax_Util.is_dtuple_data_lid'
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
          ->
          let args1 =
            FStar_List.map
              (fun uu____3323  -> match uu____3323 with | (p2,b) -> aux p2)
              args in
          let uu____3328 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3328
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3336;
             FStar_Syntax_Syntax.fv_delta = uu____3337;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3358 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3358 FStar_List.rev in
          let args1 =
            let uu____3367 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3377  ->
                      match uu____3377 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3367 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3419 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3419
            | (hd1::tl1,hd2::tl2) ->
                let uu____3433 = map21 tl1 tl2 in (hd1, hd2) :: uu____3433 in
          let args2 =
            let uu____3443 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3443 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3471  -> match uu____3471 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3482 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3482 with
           | Some (op,uu____3487) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3492 =
                 let uu____3493 =
                   let uu____3497 = bv_as_unique_ident v1 in
                   (uu____3497, None) in
                 FStar_Parser_AST.PatVar uu____3493 in
               mk1 uu____3492)
      | FStar_Syntax_Syntax.Pat_wild uu____3499 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3507 =
              let uu____3508 =
                let uu____3512 = bv_as_unique_ident bv in (uu____3512, None) in
              FStar_Parser_AST.PatVar uu____3508 in
            mk1 uu____3507 in
          let uu____3514 = FStar_Options.print_bound_var_types () in
          if uu____3514
          then
            let uu____3515 =
              let uu____3516 =
                let uu____3519 = resugar_term term in (pat, uu____3519) in
              FStar_Parser_AST.PatAscribed uu____3516 in
            mk1 uu____3515
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___204_3524  ->
    match uu___204_3524 with
    | FStar_Syntax_Syntax.Assumption  -> Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  -> Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  -> Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        Some FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true then None else Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible  -> Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  -> Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  -> Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  -> Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  -> Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  -> Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  ->
        if true then None else Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  -> Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____3530 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3531 -> None
    | FStar_Syntax_Syntax.Projector uu____3532 -> None
    | FStar_Syntax_Syntax.RecordType uu____3535 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3540 -> None
    | FStar_Syntax_Syntax.Action uu____3545 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___205_3548  ->
    match uu___205_3548 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
let resugar_typ:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelts* FStar_Parser_AST.tycon)
  =
  fun datacon_ses  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (tylid,uvs,bs,t,uu____3570,datacons) ->
          let uu____3576 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3587,uu____3588,uu____3589,inductive_lid,uu____3591,uu____3592)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3595 -> failwith "unexpected")) in
          (match uu____3576 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3606 = FStar_Options.print_implicits () in
                 if uu____3606 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3613 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___206_3615  ->
                           match uu___206_3615 with
                           | FStar_Syntax_Syntax.RecordType uu____3616 ->
                               true
                           | uu____3621 -> false)) in
                 if uu____3613
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3649,univs1,term,uu____3652,num,uu____3654)
                         ->
                         let uu____3657 =
                           let uu____3658 = FStar_Syntax_Subst.compress term in
                           uu____3658.FStar_Syntax_Syntax.n in
                         (match uu____3657 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3667) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3698  ->
                                        match uu____3698 with
                                        | (b,qual) ->
                                            let uu____3707 =
                                              let uu____3708 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3708 in
                                            let uu____3709 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3707, uu____3709, None))) in
                              FStar_List.append mfields fields
                          | uu____3715 -> failwith "unexpected")
                     | uu____3721 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3788,num,uu____3790) ->
                          let c =
                            let uu____3800 =
                              let uu____3802 = resugar_term term in
                              Some uu____3802 in
                            ((l.FStar_Ident.ident), uu____3800, None, false) in
                          c :: constructors
                      | uu____3811 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3850 ->
          failwith
            "Impossible : only Sig_inductive_typ can be resugared as types"
let mk_decl:
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____3864 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3864;
          FStar_Parser_AST.attrs = []
        }
let decl'_to_decl:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
let resugar_tscheme':
  Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun name  ->
    fun ts  ->
      let uu____3877 = ts in
      match uu____3877 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3883 =
            let uu____3884 =
              let uu____3891 =
                let uu____3896 =
                  let uu____3900 =
                    let uu____3901 =
                      let uu____3908 = resugar_term typ in
                      (name1, [], None, uu____3908) in
                    FStar_Parser_AST.TyconAbbrev uu____3901 in
                  (uu____3900, None) in
                [uu____3896] in
              (false, uu____3891) in
            FStar_Parser_AST.Tycon uu____3884 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3883
let resugar_tscheme: FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl =
  fun ts  -> resugar_tscheme' "tsheme" ts
let resugar_eff_decl:
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let resugar_action d for_free1 =
            let action_params =
              FStar_Syntax_Subst.open_binders
                d.FStar_Syntax_Syntax.action_params in
            let uu____3947 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3947 with
            | (bs,action_defn) ->
                let uu____3952 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3952 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3958 = FStar_Options.print_implicits () in
                       if uu____3958
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3962 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3962 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____3971 =
                           let uu____3977 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3977,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3971 in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un in
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2, None, t)), None)]))
                     else
                       mk_decl r q
                         (FStar_Parser_AST.Tycon
                            (false,
                              [((FStar_Parser_AST.TyconAbbrev
                                   (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                     action_params2, None, action_defn1)),
                                 None)]))) in
          let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident in
          let uu____4016 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4016 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4022 = FStar_Options.print_implicits () in
                if uu____4022 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4026 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4026 FStar_List.rev in
              let eff_typ1 = resugar_term eff_typ in
              let ret_wp =
                resugar_tscheme' "ret_wp" ed.FStar_Syntax_Syntax.ret_wp in
              let bind_wp =
                resugar_tscheme' "bind_wp" ed.FStar_Syntax_Syntax.ret_wp in
              let if_then_else1 =
                resugar_tscheme' "if_then_else"
                  ed.FStar_Syntax_Syntax.if_then_else in
              let ite_wp =
                resugar_tscheme' "ite_wp" ed.FStar_Syntax_Syntax.ite_wp in
              let stronger =
                resugar_tscheme' "stronger" ed.FStar_Syntax_Syntax.stronger in
              let close_wp =
                resugar_tscheme' "close_wp" ed.FStar_Syntax_Syntax.close_wp in
              let assert_p =
                resugar_tscheme' "assert_p" ed.FStar_Syntax_Syntax.assert_p in
              let assume_p =
                resugar_tscheme' "assume_p" ed.FStar_Syntax_Syntax.assume_p in
              let null_wp =
                resugar_tscheme' "null_wp" ed.FStar_Syntax_Syntax.null_wp in
              let trivial =
                resugar_tscheme' "trivial" ed.FStar_Syntax_Syntax.trivial in
              let repr =
                resugar_tscheme' "repr" ([], (ed.FStar_Syntax_Syntax.repr)) in
              let return_repr =
                resugar_tscheme' "return_repr"
                  ed.FStar_Syntax_Syntax.return_repr in
              let bind_repr =
                resugar_tscheme' "bind_repr" ed.FStar_Syntax_Syntax.bind_repr in
              let mandatory_members_decls =
                if for_free
                then [repr; return_repr; bind_repr]
                else
                  [repr;
                  return_repr;
                  bind_repr;
                  ret_wp;
                  bind_wp;
                  if_then_else1;
                  ite_wp;
                  stronger;
                  close_wp;
                  assert_p;
                  assume_p;
                  null_wp;
                  trivial] in
              let actions =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                  (FStar_List.map (fun a  -> resugar_action a false)) in
              let decls = FStar_List.append mandatory_members_decls actions in
              mk_decl r q
                (FStar_Parser_AST.NewEffect
                   (FStar_Parser_AST.DefineEffect
                      (eff_name, eff_binders2, eff_typ1, decls)))
let resugar_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Parser_AST.decl option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4067) ->
        let uu____4072 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4083 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4092 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4096 -> false
                  | uu____4104 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4072 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4124 se1 =
               match uu____4124 with
               | (datacon_ses1,tycons) ->
                   let uu____4139 = resugar_typ datacon_ses1 se1 in
                   (match uu____4139 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4148 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4148 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4167 =
                         let uu____4168 =
                           let uu____4169 =
                             let uu____4176 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4176) in
                           FStar_Parser_AST.Tycon uu____4169 in
                         decl'_to_decl se uu____4168 in
                       Some uu____4167
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4193,uu____4194,uu____4195,uu____4196,uu____4197)
                            ->
                            let uu____4200 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4200
                        | uu____4202 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4204 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4208,attrs) ->
        let uu____4214 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___207_4216  ->
                  match uu___207_4216 with
                  | FStar_Syntax_Syntax.Projector (uu____4217,uu____4218) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4219 -> true
                  | uu____4220 -> false)) in
        if uu____4214
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4245) ->
               let uu____4252 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4252
           | uu____4256 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4260 =
          let uu____4261 =
            let uu____4262 =
              let uu____4265 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4265) in
            FStar_Parser_AST.Assume uu____4262 in
          decl'_to_decl se uu____4261 in
        Some uu____4260
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4267 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4267
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4269 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4269
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4276,t) ->
              let uu____4283 = resugar_term t in Some uu____4283
          | uu____4284 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4289,t) ->
              let uu____4296 = resugar_term t in Some uu____4296
          | uu____4297 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4312 -> failwith "Should not happen hopefully" in
        let uu____4317 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4317
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4325 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4325 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4332 = FStar_Options.print_implicits () in
               if uu____4332 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4338 =
               let uu____4339 =
                 let uu____4340 =
                   let uu____4347 =
                     let uu____4352 =
                       let uu____4356 =
                         let uu____4357 =
                           let uu____4364 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4364) in
                         FStar_Parser_AST.TyconAbbrev uu____4357 in
                       (uu____4356, None) in
                     [uu____4352] in
                   (false, uu____4347) in
                 FStar_Parser_AST.Tycon uu____4340 in
               decl'_to_decl se uu____4339 in
             Some uu____4338)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4379 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4379
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4383 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___208_4385  ->
                  match uu___208_4385 with
                  | FStar_Syntax_Syntax.Projector (uu____4386,uu____4387) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4388 -> true
                  | uu____4389 -> false)) in
        if uu____4383
        then None
        else
          (let uu____4392 =
             let uu____4393 =
               let uu____4394 =
                 let uu____4397 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4397) in
               FStar_Parser_AST.Val uu____4394 in
             decl'_to_decl se uu____4393 in
           Some uu____4392)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4398 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4407 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4415 -> None