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
           | uu____240 ->
               let op =
                 let uu____243 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | Some (op,uu____260) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____243 in
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
      let uu____358 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____358 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
      | uu____383 ->
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
                (let uu____432 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____432
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
    let uu____445 =
      let uu____446 = FStar_Syntax_Subst.compress t in
      uu____446.FStar_Syntax_Syntax.n in
    match uu____445 with
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
        let uu____480 = string_to_op s in
        (match uu____480 with | Some t1 -> Some t1 | uu____494 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____504 -> None
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____510 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____514 -> true
    | uu____515 -> false
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
      let uu____543 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____543 in
    let var a r =
      let uu____551 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____551 in
    let uu____552 =
      let uu____553 = FStar_Syntax_Subst.compress t in
      uu____553.FStar_Syntax_Syntax.n in
    match uu____552 with
    | FStar_Syntax_Syntax.Tm_delayed uu____556 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____579 = let uu____581 = bv_as_unique_ident x in [uu____581] in
          FStar_Ident.lid_of_ids uu____579 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____584 = let uu____586 = bv_as_unique_ident x in [uu____586] in
          FStar_Ident.lid_of_ids uu____584 in
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
          let uu____618 =
            let uu____619 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____619 in
          mk1 uu____618
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
             | uu____632 -> failwith "wrong projector format")
          else
            (let uu____635 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____636 =
                    let uu____637 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____637 in
                  let uu____638 = FStar_String.get s (Prims.parse_int "0") in
                  uu____636 <> uu____638) in
             if uu____635
             then
               let uu____639 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____639
             else
               (let uu____641 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____641))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____648 = FStar_Options.print_universes () in
        if uu____648
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 let uu____652 =
                   let uu____653 =
                     let uu____657 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____657, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____653 in
                 mk1 uu____652) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____660 = FStar_Syntax_Syntax.is_teff t in
        if uu____660
        then
          let uu____661 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____661
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
             let uu____664 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____664
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____665 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____665
         | uu____666 ->
             let uu____667 = FStar_Options.print_universes () in
             if uu____667
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
               (let uu____678 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____678))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____681) ->
        let uu____704 = FStar_Syntax_Subst.open_term xs body in
        (match uu____704 with
         | (xs1,body1) ->
             let xs2 =
               let uu____710 = FStar_Options.print_implicits () in
               if uu____710 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____717  ->
                       match uu____717 with
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
        let uu____737 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____737 with
         | (xs1,body1) ->
             let xs2 =
               let uu____743 = FStar_Options.print_implicits () in
               if uu____743 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____748 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____748 FStar_List.rev in
             let rec aux body3 uu___197_761 =
               match uu___197_761 with
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        let uu____774 =
          let uu____777 =
            let uu____778 = FStar_Syntax_Syntax.mk_binder x in [uu____778] in
          FStar_Syntax_Subst.open_term uu____777 phi in
        (match uu____774 with
         | (x1,phi1) ->
             let b =
               let uu____782 = FStar_List.hd x1 in
               resugar_binder uu____782 t.FStar_Syntax_Syntax.pos in
             let uu____785 =
               let uu____786 =
                 let uu____789 = resugar_term phi1 in (b, uu____789) in
               FStar_Parser_AST.Refine uu____786 in
             mk1 uu____785)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___198_819 =
          match uu___198_819 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____866 -> failwith "last of an empty list" in
        let rec last_two uu___199_890 =
          match uu___199_890 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____910::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____962::t1 -> last_two t1 in
        let rec last_three uu___200_990 =
          match uu___200_990 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1010::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1028::uu____1029::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1102::t1 -> last_three t1 in
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
                 (fun uu____1138  ->
                    match uu____1138 with | (e2,qual) -> resugar_term e2)) in
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
          let uu____1152 = FStar_Options.print_implicits () in
          if uu____1152 then args else filter_imp args in
        let uu____1161 = resugar_term_as_op e in
        (match uu____1161 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1167) ->
             (match args1 with
              | (fst1,uu____1171)::(snd1,uu____1173)::rest ->
                  let e1 =
                    let uu____1197 =
                      let uu____1198 =
                        let uu____1202 =
                          let uu____1204 = resugar_term fst1 in
                          let uu____1205 =
                            let uu____1207 = resugar_term snd1 in
                            [uu____1207] in
                          uu____1204 :: uu____1205 in
                        ((FStar_Ident.id_of_text "*"), uu____1202) in
                      FStar_Parser_AST.Op uu____1198 in
                    mk1 uu____1197 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1212  ->
                         match uu____1212 with
                         | (x,uu____1216) ->
                             let uu____1217 =
                               let uu____1218 =
                                 let uu____1222 =
                                   let uu____1224 =
                                     let uu____1226 = resugar_term x in
                                     [uu____1226] in
                                   e1 :: uu____1224 in
                                 ((FStar_Ident.id_of_text "*"), uu____1222) in
                               FStar_Parser_AST.Op uu____1218 in
                             mk1 uu____1217) e1 rest
              | uu____1228 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1234) when
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
               | (b,uu____1259)::[] -> b
               | uu____1272 -> failwith "wrong arguments to dtuple" in
             let uu____1280 =
               let uu____1281 = FStar_Syntax_Subst.compress body in
               uu____1281.FStar_Syntax_Syntax.n in
             (match uu____1280 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1286) ->
                  let uu____1309 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1309 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1315 = FStar_Options.print_implicits () in
                         if uu____1315 then xs1 else filter_imp xs1 in
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
              | uu____1323 ->
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1334  ->
                            match uu____1334 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
         | Some ("dtuple",uu____1342) -> resugar_as_app e args1
         | Some (ref_read,uu____1346) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1349 = FStar_List.hd args1 in
             (match uu____1349 with
              | (t1,uu____1359) ->
                  let uu____1364 =
                    let uu____1365 = FStar_Syntax_Subst.compress t1 in
                    uu____1365.FStar_Syntax_Syntax.n in
                  (match uu____1364 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
                       let uu____1378 =
                         let uu____1379 =
                           let uu____1382 = resugar_term t1 in
                           (uu____1382, f) in
                         FStar_Parser_AST.Project uu____1379 in
                       mk1 uu____1378
                   | uu____1383 -> resugar_term t1))
         | Some ("try_with",uu____1384) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1403 =
               match new_args with
               | (a1,uu____1417)::(a2,uu____1419)::[] -> (a1, a2)
               | uu____1444 -> failwith "wrong arguments to try_with" in
             (match uu____1403 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1470 =
                      let uu____1471 = FStar_Syntax_Subst.compress term in
                      uu____1471.FStar_Syntax_Syntax.n in
                    match uu____1470 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1476) ->
                        let uu____1499 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1499 with | (x1,e2) -> e2)
                    | uu____1504 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1506 = decomp body in resugar_term uu____1506 in
                  let handler1 =
                    let uu____1508 = decomp handler in
                    resugar_term uu____1508 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1514,uu____1515,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1532,uu____1533,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1546 =
                          let uu____1547 =
                            let uu____1552 = resugar_body t11 in
                            (uu____1552, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1547 in
                        mk1 uu____1546
                    | uu____1554 ->
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
                    | uu____1587 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1603) -> resugar_as_app e args1
         | Some (op,uu____1607) when (op = "forall") || (op = "exists") ->
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | uu____1658 -> (xs, pat, t1) in
             let resugar body =
               let uu____1666 =
                 let uu____1667 = FStar_Syntax_Subst.compress body in
                 uu____1667.FStar_Syntax_Syntax.n in
               match uu____1666 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1672) ->
                   let uu____1695 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1695 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1701 = FStar_Options.print_implicits () in
                          if uu____1701 then xs1 else filter_imp xs1 in
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                        let uu____1707 =
                          let uu____1712 =
                            let uu____1713 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1713.FStar_Syntax_Syntax.n in
                          match uu____1712 with
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
                                              (fun uu____1753  ->
                                                 match uu____1753 with
                                                 | (e2,uu____1757) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1760) ->
                                    let uu____1761 =
                                      let uu____1763 =
                                        let uu____1764 = name s r in
                                        mk1 uu____1764 in
                                      [uu____1763] in
                                    [uu____1761]
                                | uu____1767 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1772 ->
                              let uu____1773 = resugar_term body2 in
                              ([], uu____1773) in
                        (match uu____1707 with
                         | (pats,body3) ->
                             let uu____1783 = uncurry xs3 pats body3 in
                             (match uu____1783 with
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
               | uu____1810 ->
                   if op = "forall"
                   then
                     let uu____1811 =
                       let uu____1812 =
                         let uu____1819 = resugar_term body in
                         ([], [[]], uu____1819) in
                       FStar_Parser_AST.QForall uu____1812 in
                     mk1 uu____1811
                   else
                     (let uu____1826 =
                        let uu____1827 =
                          let uu____1834 = resugar_term body in
                          ([], [[]], uu____1834) in
                        FStar_Parser_AST.QExists uu____1827 in
                      mk1 uu____1826) in
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1857)::[] -> resugar b
                | uu____1870 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1877) ->
             let uu____1880 = FStar_List.hd args1 in
             (match uu____1880 with | (e1,uu____1890) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
                    (fun uu____1917  ->
                       match uu____1917 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1922 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1922 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1933 =
                         let uu____1934 =
                           let uu____1938 =
                             let uu____1940 = last1 args1 in
                             resugar uu____1940 in
                           (op1, uu____1938) in
                         FStar_Parser_AST.Op uu____1934 in
                       mk1 uu____1933
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1955 =
                         let uu____1956 =
                           let uu____1960 =
                             let uu____1962 = last_two args1 in
                             resugar uu____1962 in
                           (op1, uu____1960) in
                         FStar_Parser_AST.Op uu____1956 in
                       mk1 uu____1955
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1977 =
                         let uu____1978 =
                           let uu____1982 =
                             let uu____1984 = last_three args1 in
                             resugar uu____1984 in
                           (op1, uu____1982) in
                         FStar_Parser_AST.Op uu____1978 in
                       mk1 uu____1977
                   | uu____1989 -> resugar_as_app e args1)
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____2000 =
                    let uu____2001 =
                      let uu____2005 =
                        let uu____2007 = last_two args1 in resugar uu____2007 in
                      (op1, uu____2005) in
                    FStar_Parser_AST.Op uu____2001 in
                  mk1 uu____2000
              | uu____2012 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____2015,t1)::[]) ->
        let bnds =
          let uu____2070 =
            let uu____2073 = resugar_pat pat in
            let uu____2074 = resugar_term e in (uu____2073, uu____2074) in
          [uu____2070] in
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
        (e,(pat1,uu____2085,t1)::(pat2,uu____2088,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2163 =
          let uu____2164 =
            let uu____2168 = resugar_term e in
            let uu____2169 = resugar_term t1 in
            let uu____2170 = resugar_term t2 in
            (uu____2168, uu____2169, uu____2170) in
          FStar_Parser_AST.If uu____2164 in
        mk1 uu____2163
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2210 =
          match uu____2210 with
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
                    let uu____2229 = resugar_term e1 in Some uu____2229 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2232 =
          let uu____2233 =
            let uu____2241 = resugar_term e in
            let uu____2242 = FStar_List.map resugar_branch branches in
            (uu____2241, uu____2242) in
          FStar_Parser_AST.Match uu____2233 in
        mk1 uu____2232
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2264) ->
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
        let uu____2317 =
          let uu____2318 =
            let uu____2323 = resugar_term e in (uu____2323, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2318 in
        mk1 uu____2317
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2341 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2341 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2357 =
                 let uu____2360 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2360 in
               match uu____2357 with
               | (univs1,td) ->
                   let uu____2367 =
                     let uu____2374 =
                       let uu____2375 = FStar_Syntax_Subst.compress td in
                       uu____2375.FStar_Syntax_Syntax.n in
                     match uu____2374 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2384,(t1,uu____2386)::(d,uu____2388)::[]) ->
                         (t1, d)
                     | uu____2422 -> failwith "wrong let binding format" in
                   (match uu____2367 with
                    | (typ,def) ->
                        let uu____2443 =
                          let uu____2447 =
                            let uu____2448 = FStar_Syntax_Subst.compress def in
                            uu____2448.FStar_Syntax_Syntax.n in
                          match uu____2447 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2456) ->
                              let uu____2479 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2479 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2488 =
                                       FStar_Options.print_implicits () in
                                     if uu____2488 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2490 -> ([], def, false) in
                        (match uu____2443 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2511 =
                                 FStar_Options.print_universes () in
                               if uu____2511
                               then
                                 let uu____2512 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2512
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2517 =
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
                                   let uu____2528 =
                                     let uu____2529 =
                                       let uu____2530 =
                                         let uu____2534 =
                                           bv_as_unique_ident bv in
                                         (uu____2534, None) in
                                       FStar_Parser_AST.PatVar uu____2530 in
                                     mk_pat uu____2529 in
                                   (uu____2528, term) in
                             (match uu____2517 with
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
                                           (fun uu____2551  ->
                                              match uu____2551 with
                                              | (bv,uu____2555) ->
                                                  let uu____2556 =
                                                    let uu____2557 =
                                                      let uu____2561 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2561, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2557 in
                                                  mk_pat uu____2556)) in
                                    let uu____2563 =
                                      let uu____2566 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2566) in
                                    let uu____2568 =
                                      universe_to_string univs1 in
                                    (uu____2563, uu____2568)
                                  else
                                    (let uu____2572 =
                                       let uu____2575 = resugar_term term1 in
                                       (pat, uu____2575) in
                                     let uu____2576 =
                                       universe_to_string univs1 in
                                     (uu____2572, uu____2576))))) in
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2615) ->
        let s =
          let uu____2629 =
            let uu____2630 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2630 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2629 in
        let uu____2631 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2631
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___201_2641 =
          match uu___201_2641 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2642 =
                let uu____2643 = FStar_Syntax_Subst.compress e in
                uu____2643.FStar_Syntax_Syntax.n in
              (match uu____2642 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2669 =
                       let uu____2670 = FStar_Syntax_Subst.compress h in
                       uu____2670.FStar_Syntax_Syntax.n in
                     match uu____2669 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2677 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2677, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2685 = aux h1 in
                         (match uu____2685 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2697 -> failwith "wrong Data_app head format" in
                   let uu____2701 = aux head1 in
                   (match uu____2701 with
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
                               let uu____2716 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2716, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2725  ->
                               match uu____2725 with
                               | (t1,uu____2731) ->
                                   let uu____2732 = resugar_term t1 in
                                   (uu____2732, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2733 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2733
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2738 = FStar_Options.print_universes () in
                           if uu____2738
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
               | FStar_Syntax_Syntax.Tm_meta (uu____2748,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2754,uu____2755) -> resugar_term e
                    | uu____2760 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2761 -> failwith "wrong Data_app format")
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
                | FStar_Parser_AST.Let (uu____2767,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2783 =
                      let uu____2784 =
                        let uu____2789 = resugar_seq t11 in
                        (uu____2789, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2784 in
                    mk1 uu____2783
                | uu____2791 -> t1 in
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
               | uu____2804 ->
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
              let uu____2806 =
                let uu____2807 = FStar_Syntax_Subst.compress e in
                uu____2807.FStar_Syntax_Syntax.n in
              (match uu____2806 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2811;
                      FStar_Syntax_Syntax.pos = uu____2812;
                      FStar_Syntax_Syntax.vars = uu____2813;_},(term,uu____2815)::[])
                   -> resugar_term term
               | uu____2837 -> failwith "mutable_rval should have app term") in
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2859  ->
                       match uu____2859 with
                       | (x,uu____2863) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2865,p) ->
             let uu____2867 =
               let uu____2868 =
                 let uu____2872 = resugar_term e in (uu____2872, l, p) in
               FStar_Parser_AST.Labeled uu____2868 in
             mk1 uu____2867
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____2874,s) ->
             let uu____2876 =
               FStar_Util.format1
                 "fatal: we should never try to resugar an alien (%s)" s in
             failwith uu____2876
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
             let uu____2884 =
               let uu____2885 =
                 let uu____2890 = resugar_term e in
                 let uu____2891 =
                   let uu____2892 =
                     let uu____2893 =
                       let uu____2899 =
                         let uu____2903 =
                           let uu____2906 = resugar_term t1 in
                           (uu____2906, FStar_Parser_AST.Nothing) in
                         [uu____2903] in
                       (name1, uu____2899) in
                     FStar_Parser_AST.Construct uu____2893 in
                   mk1 uu____2892 in
                 (uu____2890, uu____2891, None) in
               FStar_Parser_AST.Ascribed uu____2885 in
             mk1 uu____2884
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2916,t1) ->
             let uu____2922 =
               let uu____2923 =
                 let uu____2928 = resugar_term e in
                 let uu____2929 =
                   let uu____2930 =
                     let uu____2931 =
                       let uu____2937 =
                         let uu____2941 =
                           let uu____2944 = resugar_term t1 in
                           (uu____2944, FStar_Parser_AST.Nothing) in
                         [uu____2941] in
                       (name1, uu____2937) in
                     FStar_Parser_AST.Construct uu____2931 in
                   mk1 uu____2930 in
                 (uu____2928, uu____2929, None) in
               FStar_Parser_AST.Ascribed uu____2923 in
             mk1 uu____2922)
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
             let uu____2975 = FStar_Options.print_universes () in
             if uu____2975
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
             let uu____3011 = FStar_Options.print_universes () in
             if uu____3011
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
          let uu____3034 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____3034, FStar_Parser_AST.Nothing) in
        let uu____3035 = FStar_Options.print_effect_args () in
        if uu____3035
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
              let rec aux l uu___202_3075 =
                match uu___202_3075 with
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
                     | FStar_Syntax_Syntax.Tm_meta uu____3117 -> aux l tl1
                     | uu____3122 -> aux ((t, aq) :: l) tl1) in
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
              (fun uu____3142  ->
                 match uu____3142 with
                 | (e,uu____3148) ->
                     let uu____3149 = resugar_term e in
                     (uu____3149, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___203_3163 =
            match uu___203_3163 with
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
                       let uu____3183 = resugar_term e in
                       (uu____3183, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3186 -> aux l tl1) in
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
      let uu____3210 = b in
      match uu____3210 with
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
               let uu____3214 =
                 let uu____3215 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3215 in
               FStar_Parser_AST.mk_binder uu____3214 r
                 FStar_Parser_AST.Type_level None
           | uu____3216 ->
               let uu____3217 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3217
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
                 (let uu____3219 =
                    let uu____3220 =
                      let uu____3223 = bv_as_unique_ident x in
                      (uu____3223, e) in
                    FStar_Parser_AST.Annotated uu____3220 in
                  FStar_Parser_AST.mk_binder uu____3219 r
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
        let uu____3231 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3231 in
      let uu____3232 =
        let uu____3233 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3233.FStar_Syntax_Syntax.n in
      match uu____3232 with
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
            let uu____3239 = mk1 FStar_Parser_AST.PatWild in Some uu____3239
          else
            (let uu____3241 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3241
               (fun aq  ->
                  let uu____3247 =
                    let uu____3248 =
                      let uu____3249 =
                        let uu____3253 = bv_as_unique_ident x in
                        (uu____3253, aq) in
                      FStar_Parser_AST.PatVar uu____3249 in
                    mk1 uu____3248 in
                  Some uu____3247))
      | uu____3255 ->
          let uu____3256 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3256
            (fun aq  ->
               let pat =
                 let uu____3263 =
                   let uu____3264 =
                     let uu____3268 = bv_as_unique_ident x in
                     (uu____3268, aq) in
                   FStar_Parser_AST.PatVar uu____3264 in
                 mk1 uu____3263 in
               let uu____3270 = FStar_Options.print_bound_var_types () in
               if uu____3270
               then
                 let uu____3272 =
                   let uu____3273 =
                     let uu____3274 =
                       let uu____3277 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3277) in
                     FStar_Parser_AST.PatAscribed uu____3274 in
                   mk1 uu____3273 in
                 Some uu____3272
               else Some pat)
and resugar_pat: FStar_Syntax_Syntax.pat -> FStar_Parser_AST.pattern =
  fun p  ->
    let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
    let rec aux p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          mk1 (FStar_Parser_AST.PatConst c)
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
              (fun uu____3323  -> match uu____3323 with | (p2,b) -> aux p2)
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
              (fun uu____3352  -> match uu____3352 with | (p2,b) -> aux p2)
              args in
          let uu____3357 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3357
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3365;
             FStar_Syntax_Syntax.fv_delta = uu____3366;
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
            let uu____3387 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3387 FStar_List.rev in
          let args1 =
            let uu____3396 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3406  ->
                      match uu____3406 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3396 FStar_List.rev in
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
                let uu____3448 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3448
            | (hd1::tl1,hd2::tl2) ->
                let uu____3462 = map21 tl1 tl2 in (hd1, hd2) :: uu____3462 in
          let args2 =
            let uu____3472 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3472 FStar_List.rev in
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
              (fun uu____3500  -> match uu____3500 with | (p2,b) -> aux p2)
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
          let uu____3511 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3511 with
           | Some (op,uu____3516) ->
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
               let uu____3521 =
                 let uu____3522 =
                   let uu____3526 = bv_as_unique_ident v1 in
                   (uu____3526, None) in
                 FStar_Parser_AST.PatVar uu____3522 in
               mk1 uu____3521)
      | FStar_Syntax_Syntax.Pat_wild uu____3528 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3536 =
              let uu____3537 =
                let uu____3541 = bv_as_unique_ident bv in (uu____3541, None) in
              FStar_Parser_AST.PatVar uu____3537 in
            mk1 uu____3536 in
          let uu____3543 = FStar_Options.print_bound_var_types () in
          if uu____3543
          then
            let uu____3544 =
              let uu____3545 =
                let uu____3548 = resugar_term term in (pat, uu____3548) in
              FStar_Parser_AST.PatAscribed uu____3545 in
            mk1 uu____3544
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
  fun uu___204_3553  ->
    match uu___204_3553 with
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
    | FStar_Syntax_Syntax.Reflectable uu____3559 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3560 -> None
    | FStar_Syntax_Syntax.Projector uu____3561 -> None
    | FStar_Syntax_Syntax.RecordType uu____3564 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3569 -> None
    | FStar_Syntax_Syntax.Action uu____3574 -> None
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
  fun uu___205_3577  ->
    match uu___205_3577 with
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
          (tylid,uvs,bs,t,uu____3599,datacons) ->
          let uu____3605 =
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____3616,uu____3617,uu____3618,inductive_lid,uu____3620,uu____3621)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3624 -> failwith "unexpected")) in
          (match uu____3605 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3635 = FStar_Options.print_implicits () in
                 if uu____3635 then bs else filter_imp bs in
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
                 let uu____3642 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___206_3644  ->
                           match uu___206_3644 with
                           | FStar_Syntax_Syntax.RecordType uu____3645 ->
                               true
                           | uu____3650 -> false)) in
                 if uu____3642
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____3678,univs1,term,uu____3681,num,uu____3683)
                         ->
                         let uu____3686 =
                           let uu____3687 = FStar_Syntax_Subst.compress term in
                           uu____3687.FStar_Syntax_Syntax.n in
                         (match uu____3686 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3696) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3727  ->
                                        match uu____3727 with
                                        | (b,qual) ->
                                            let uu____3736 =
                                              let uu____3737 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3737 in
                                            let uu____3738 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3736, uu____3738, None))) in
                              FStar_List.append mfields fields
                          | uu____3744 -> failwith "unexpected")
                     | uu____3750 -> failwith "unexpected" in
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (l,univs1,term,uu____3817,num,uu____3819) ->
                          let c =
                            let uu____3829 =
                              let uu____3831 = resugar_term term in
                              Some uu____3831 in
                            ((l.FStar_Ident.ident), uu____3829, None, false) in
                          c :: constructors
                      | uu____3840 -> failwith "unexpected" in
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
      | uu____3879 ->
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
        let uu____3893 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
          FStar_Parser_AST.quals = uu____3893;
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
      let uu____3906 = ts in
      match uu____3906 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3912 =
            let uu____3913 =
              let uu____3920 =
                let uu____3925 =
                  let uu____3929 =
                    let uu____3930 =
                      let uu____3937 = resugar_term typ in
                      (name1, [], None, uu____3937) in
                    FStar_Parser_AST.TyconAbbrev uu____3930 in
                  (uu____3929, None) in
                [uu____3925] in
              (false, uu____3920) in
            FStar_Parser_AST.Tycon uu____3913 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3912
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
            let uu____3976 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3976 with
            | (bs,action_defn) ->
                let uu____3981 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3981 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3987 = FStar_Options.print_implicits () in
                       if uu____3987
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3991 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3991 FStar_List.rev in
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
                         let uu____4000 =
                           let uu____4006 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____4006,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____4000 in
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
          let uu____4045 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____4045 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4051 = FStar_Options.print_implicits () in
                if uu____4051 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4055 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4055 FStar_List.rev in
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
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4096) ->
        let uu____4101 =
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4112 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4121 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4125 -> false
                  | uu____4133 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4101 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4153 se1 =
               match uu____4153 with
               | (datacon_ses1,tycons) ->
                   let uu____4168 = resugar_typ datacon_ses1 se1 in
                   (match uu____4168 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4177 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4177 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4196 =
                         let uu____4197 =
                           let uu____4198 =
                             let uu____4205 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4205) in
                           FStar_Parser_AST.Tycon uu____4198 in
                         decl'_to_decl se uu____4197 in
                       Some uu____4196
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4222,uu____4223,uu____4224,uu____4225,uu____4226)
                            ->
                            let uu____4229 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4229
                        | uu____4231 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4233 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4237,attrs) ->
        let uu____4243 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___207_4245  ->
                  match uu___207_4245 with
                  | FStar_Syntax_Syntax.Projector (uu____4246,uu____4247) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4248 -> true
                  | uu____4249 -> false)) in
        if uu____4243
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Let (isrec,lets,uu____4274) ->
               let uu____4281 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4281
           | uu____4285 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4289 =
          let uu____4290 =
            let uu____4291 =
              let uu____4294 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4294) in
            FStar_Parser_AST.Assume uu____4291 in
          decl'_to_decl se uu____4290 in
        Some uu____4289
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4296 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4296
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4298 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4298
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
          | Some (uu____4305,t) ->
              let uu____4312 = resugar_term t in Some uu____4312
          | uu____4313 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4318,t) ->
              let uu____4325 = resugar_term t in Some uu____4325
          | uu____4326 -> None in
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
          | uu____4341 -> failwith "Should not happen hopefully" in
        let uu____4346 =
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
        Some uu____4346
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4354 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4354 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4361 = FStar_Options.print_implicits () in
               if uu____4361 then bs1 else filter_imp bs1 in
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
             let uu____4367 =
               let uu____4368 =
                 let uu____4369 =
                   let uu____4376 =
                     let uu____4381 =
                       let uu____4385 =
                         let uu____4386 =
                           let uu____4393 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4393) in
                         FStar_Parser_AST.TyconAbbrev uu____4386 in
                       (uu____4385, None) in
                     [uu____4381] in
                   (false, uu____4376) in
                 FStar_Parser_AST.Tycon uu____4369 in
               decl'_to_decl se uu____4368 in
             Some uu____4367)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4408 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4408
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4412 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___208_4414  ->
                  match uu___208_4414 with
                  | FStar_Syntax_Syntax.Projector (uu____4415,uu____4416) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4417 -> true
                  | uu____4418 -> false)) in
        if uu____4412
        then None
        else
          (let uu____4421 =
             let uu____4422 =
               let uu____4423 =
                 let uu____4426 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4426) in
               FStar_Parser_AST.Val uu____4423 in
             decl'_to_decl se uu____4422 in
           Some uu____4421)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4427 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4436 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4444 -> None