open Prims
let bv_as_unique_ident: FStar_Syntax_Syntax.bv -> FStar_Ident.ident =
  fun x  ->
    let unique_name =
      if
        FStar_Util.starts_with FStar_Ident.reserved_prefix
          (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      then
        let uu____6 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____6
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
<<<<<<< HEAD
       (fun uu___184_40  ->
          match uu___184_40 with
=======
       (fun uu___196_40  ->
          match uu___196_40 with
>>>>>>> origin/guido_tactics
          | (uu____44,Some (FStar_Syntax_Syntax.Implicit uu____45)) -> false
          | uu____47 -> true))
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
<<<<<<< HEAD
      | uu____81 -> (n1, u)
=======
      | uu____84 -> (n1, u)
>>>>>>> origin/guido_tactics
let rec resugar_universe:
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ("0", None))) r
<<<<<<< HEAD
      | FStar_Syntax_Syntax.U_succ uu____100 ->
          let uu____101 = universe_to_int (Prims.parse_int "0") u in
          (match uu____101 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____106 =
                      let uu____107 =
                        let uu____108 =
                          let uu____114 = FStar_Util.string_of_int n1 in
                          (uu____114, None) in
                        FStar_Const.Const_int uu____108 in
                      FStar_Parser_AST.Const uu____107 in
                    mk1 uu____106 r
                | uu____120 ->
                    let e1 =
                      let uu____122 =
                        let uu____123 =
                          let uu____124 =
                            let uu____130 = FStar_Util.string_of_int n1 in
                            (uu____130, None) in
                          FStar_Const.Const_int uu____124 in
                        FStar_Parser_AST.Const uu____123 in
                      mk1 uu____122 r in
=======
      | FStar_Syntax_Syntax.U_succ uu____105 ->
          let uu____106 = universe_to_int (Prims.parse_int "0") u in
          (match uu____106 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____111 =
                      let uu____112 =
                        let uu____113 =
                          let uu____119 = FStar_Util.string_of_int n1 in
                          (uu____119, None) in
                        FStar_Const.Const_int uu____113 in
                      FStar_Parser_AST.Const uu____112 in
                    mk1 uu____111 r
                | uu____125 ->
                    let e1 =
                      let uu____127 =
                        let uu____128 =
                          let uu____129 =
                            let uu____135 = FStar_Util.string_of_int n1 in
                            (uu____135, None) in
                          FStar_Const.Const_int uu____129 in
                        FStar_Parser_AST.Const uu____128 in
                      mk1 uu____127 r in
>>>>>>> origin/guido_tactics
                    let e2 = resugar_universe u1 r in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
<<<<<<< HEAD
           | uu____140 ->
               let t =
                 let uu____143 =
                   let uu____144 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____144 in
                 mk1 uu____143 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____150 =
                        let uu____151 =
                          let uu____155 = resugar_universe x r in
                          (acc, uu____155, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____151 in
                      mk1 uu____150 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____157 -> mk1 FStar_Parser_AST.Wild r
=======
           | uu____145 ->
               let t =
                 let uu____148 =
                   let uu____149 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____149 in
                 mk1 uu____148 r in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____152 =
                        let uu____153 =
                          let uu____157 = resugar_universe x r in
                          (acc, uu____157, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____153 in
                      mk1 uu____152 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____159 -> mk1 FStar_Parser_AST.Wild r
>>>>>>> origin/guido_tactics
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____164 =
              let uu____167 =
                let uu____168 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____168 in
              (uu____167, r) in
            FStar_Ident.mk_ident uu____164 in
          mk1 (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r
let string_to_op: Prims.string -> (Prims.string* Prims.int) option =
  fun s  ->
<<<<<<< HEAD
    let name_of_op uu___185_181 =
      match uu___185_181 with
=======
    let name_of_op uu___197_182 =
      match uu___197_182 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | uu____219 -> None in
=======
      | uu____220 -> None in
>>>>>>> origin/guido_tactics
    match s with
    | "op_String_Assignment" -> Some (".[]<-", (Prims.parse_int "0"))
    | "op_Array_Assignment" -> Some (".()<-", (Prims.parse_int "0"))
    | "op_String_Access" -> Some (".[]", (Prims.parse_int "0"))
    | "op_Array_Access" -> Some (".()", (Prims.parse_int "0"))
<<<<<<< HEAD
    | uu____233 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____239 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____239 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____246 ->
               let op =
                 let uu____249 = FStar_List.map name_of_op s1 in
=======
    | uu____234 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____240 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____240 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____249 ->
               let op =
                 let uu____252 = FStar_List.map name_of_op s1 in
>>>>>>> origin/guido_tactics
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
<<<<<<< HEAD
                        | Some (op,uu____270) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____249 in
=======
                        | Some (op,uu____269) -> Prims.strcat acc op
                        | None  -> failwith "wrong composed operator format")
                   "" uu____252 in
>>>>>>> origin/guido_tactics
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
      let uu____368 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  -> FStar_Syntax_Syntax.fv_eq_lid fv (fst d))) in
      match uu____368 with
      | Some op -> Some ((snd op), (Prims.parse_int "0"))
<<<<<<< HEAD
      | uu____394 ->
=======
      | uu____393 ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                (let uu____425 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____425
=======
                (let uu____442 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.sread_lid in
                 if uu____442
>>>>>>> origin/guido_tactics
                 then
                   Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       (Prims.parse_int "0"))
                 else None) in
<<<<<<< HEAD
    let uu____434 =
      let uu____435 = FStar_Syntax_Subst.compress t in
      uu____435.FStar_Syntax_Syntax.n in
    match uu____434 with
=======
    let uu____455 =
      let uu____456 = FStar_Syntax_Subst.compress t in
      uu____456.FStar_Syntax_Syntax.n in
    match uu____455 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____451 = string_to_op s in
        (match uu____451 with | Some t1 -> Some t1 | uu____465 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____475 -> None
=======
        let uu____490 = string_to_op s in
        (match uu____490 with | Some t1 -> Some t1 | uu____504 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____514 -> None
>>>>>>> origin/guido_tactics
let is_true_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
<<<<<<< HEAD
    | uu____481 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____485 -> true
    | uu____486 -> false
=======
    | uu____521 -> false
let is_wild_pat: FStar_Syntax_Syntax.pat -> Prims.bool =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____526 -> true
    | uu____527 -> false
>>>>>>> origin/guido_tactics
let rec resugar_term: FStar_Syntax_Syntax.term -> FStar_Parser_AST.term =
  fun t  ->
    let mk1 a =
      FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
        FStar_Parser_AST.Un in
    let name a r =
<<<<<<< HEAD
      let uu____514 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____514 in
    let var a r =
      let uu____522 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____522 in
    let uu____523 =
      let uu____524 = FStar_Syntax_Subst.compress t in
      uu____524.FStar_Syntax_Syntax.n in
    match uu____523 with
    | FStar_Syntax_Syntax.Tm_delayed uu____527 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____550 = let uu____552 = bv_as_unique_ident x in [uu____552] in
          FStar_Ident.lid_of_ids uu____550 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____555 = let uu____557 = bv_as_unique_ident x in [uu____557] in
          FStar_Ident.lid_of_ids uu____555 in
=======
      let uu____555 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Name uu____555 in
    let var a r =
      let uu____563 = FStar_Ident.lid_of_path [a] r in
      FStar_Parser_AST.Var uu____563 in
    let uu____564 =
      let uu____565 = FStar_Syntax_Subst.compress t in
      uu____565.FStar_Syntax_Syntax.n in
    match uu____564 with
    | FStar_Syntax_Syntax.Tm_delayed uu____568 ->
        failwith "Tm_delayed is impossible after compress"
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let l =
          let uu____585 = let uu____587 = bv_as_unique_ident x in [uu____587] in
          FStar_Ident.lid_of_ids uu____585 in
        mk1 (FStar_Parser_AST.Var l)
    | FStar_Syntax_Syntax.Tm_name x ->
        let l =
          let uu____590 = let uu____592 = bv_as_unique_ident x in [uu____592] in
          FStar_Ident.lid_of_ids uu____590 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          let uu____573 =
            let uu____574 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____574 in
          mk1 uu____573
=======
          let uu____624 =
            let uu____625 =
              FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
            FStar_Parser_AST.Discrim uu____625 in
          mk1 uu____624
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
             | uu____585 -> failwith "wrong projector format")
          else
            (let uu____588 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____591 =
                    let uu____592 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____592 in
                  let uu____593 = FStar_String.get s (Prims.parse_int "0") in
                  uu____591 <> uu____593) in
             if uu____588
             then
               let uu____594 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____594
             else
               (let uu____596 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____596))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____603 = FStar_Options.print_universes () in
        if uu____603
=======
             | uu____638 -> failwith "wrong projector format")
          else
            (let uu____641 =
               ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
                  (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid))
                 ||
                 (let uu____642 =
                    let uu____643 = FStar_String.get s (Prims.parse_int "0") in
                    FStar_Char.uppercase uu____643 in
                  let uu____644 = FStar_String.get s (Prims.parse_int "0") in
                  uu____642 <> uu____644) in
             if uu____641
             then
               let uu____645 =
                 var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
               mk1 uu____645
             else
               (let uu____647 =
                  name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos in
                mk1 uu____647))
    | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
        let uu____654 = FStar_Options.print_universes () in
        if uu____654
>>>>>>> origin/guido_tactics
        then
          let e1 = resugar_term e in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
<<<<<<< HEAD
                 let uu____610 =
                   let uu____611 =
                     let uu____615 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____615, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____611 in
                 mk1 uu____610) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____618 = FStar_Syntax_Syntax.is_teff t in
        if uu____618
        then
          let uu____619 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____619
=======
                 let uu____658 =
                   let uu____659 =
                     let uu____663 =
                       resugar_universe x t.FStar_Syntax_Syntax.pos in
                     (acc, uu____663, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____659 in
                 mk1 uu____658) e1 universes
        else resugar_term e
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____666 = FStar_Syntax_Syntax.is_teff t in
        if uu____666
        then
          let uu____667 = name "Effect" t.FStar_Syntax_Syntax.pos in
          mk1 uu____667
>>>>>>> origin/guido_tactics
        else mk1 (FStar_Parser_AST.Const c)
    | FStar_Syntax_Syntax.Tm_type u ->
        (match u with
         | FStar_Syntax_Syntax.U_zero  ->
<<<<<<< HEAD
             let uu____622 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____622
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____623 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____623
         | uu____624 ->
             let uu____625 = FStar_Options.print_universes () in
             if uu____625
=======
             let uu____670 = name "Type0" t.FStar_Syntax_Syntax.pos in
             mk1 uu____670
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____671 = name "Type" t.FStar_Syntax_Syntax.pos in
             mk1 uu____671
         | uu____672 ->
             let uu____673 = FStar_Options.print_universes () in
             if uu____673
>>>>>>> origin/guido_tactics
             then
               let u1 = resugar_universe u t.FStar_Syntax_Syntax.pos in
               let l =
                 FStar_Ident.lid_of_path ["Type"] t.FStar_Syntax_Syntax.pos in
               mk1
                 (FStar_Parser_AST.Construct
                    (l, [(u1, FStar_Parser_AST.UnivApp)]))
             else
<<<<<<< HEAD
               (let uu____636 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____636))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____639) ->
        let uu____662 = FStar_Syntax_Subst.open_term xs body in
        (match uu____662 with
         | (xs1,body1) ->
             let xs2 =
               let uu____668 = FStar_Options.print_implicits () in
               if uu____668 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____678  ->
                       match uu____678 with
=======
               (let uu____684 = name "Type" t.FStar_Syntax_Syntax.pos in
                mk1 uu____684))
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____687) ->
        let uu____700 = FStar_Syntax_Subst.open_term xs body in
        (match uu____700 with
         | (xs1,body1) ->
             let xs2 =
               let uu____706 = FStar_Options.print_implicits () in
               if uu____706 then xs1 else filter_imp xs1 in
             let patterns =
               FStar_All.pipe_right xs2
                 (FStar_List.choose
                    (fun uu____713  ->
                       match uu____713 with
>>>>>>> origin/guido_tactics
                       | (x,qual) -> resugar_bv_as_pat x qual)) in
             let body2 = resugar_term body1 in
             mk1 (FStar_Parser_AST.Abs (patterns, body2)))
    | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
<<<<<<< HEAD
        let uu____698 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____698 with
         | (xs1,body1) ->
             let xs2 =
               let uu____704 = FStar_Options.print_implicits () in
               if uu____704 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____709 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____709 FStar_List.rev in
             let rec aux body3 uu___186_723 =
               match uu___186_723 with
=======
        let uu____733 = FStar_Syntax_Subst.open_comp xs body in
        (match uu____733 with
         | (xs1,body1) ->
             let xs2 =
               let uu____739 = FStar_Options.print_implicits () in
               if uu____739 then xs1 else filter_imp xs1 in
             let body2 = resugar_comp body1 in
             let xs3 =
               let uu____744 =
                 FStar_All.pipe_right xs2
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               FStar_All.pipe_right uu____744 FStar_List.rev in
             let rec aux body3 uu___198_757 =
               match uu___198_757 with
>>>>>>> origin/guido_tactics
               | [] -> body3
               | hd1::tl1 ->
                   let body4 = mk1 (FStar_Parser_AST.Product ([hd1], body3)) in
                   aux body4 tl1 in
             aux body2 xs3)
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
<<<<<<< HEAD
        let uu____736 =
          let uu____739 =
            let uu____740 = FStar_Syntax_Syntax.mk_binder x in [uu____740] in
          FStar_Syntax_Subst.open_term uu____739 phi in
        (match uu____736 with
         | (x1,phi1) ->
             let b =
               let uu____744 = FStar_List.hd x1 in
               resugar_binder uu____744 t.FStar_Syntax_Syntax.pos in
             let uu____747 =
               let uu____748 =
                 let uu____751 = resugar_term phi1 in (b, uu____751) in
               FStar_Parser_AST.Refine uu____748 in
             mk1 uu____747)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___187_781 =
          match uu___187_781 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____828 -> failwith "last of an empty list" in
        let rec last_two uu___188_852 =
          match uu___188_852 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____872::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____924::t1 -> last_two t1 in
        let rec last_three uu___189_952 =
          match uu___189_952 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____972::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____990::uu____991::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1064::t1 -> last_three t1 in
=======
        let uu____770 =
          let uu____773 =
            let uu____774 = FStar_Syntax_Syntax.mk_binder x in [uu____774] in
          FStar_Syntax_Subst.open_term uu____773 phi in
        (match uu____770 with
         | (x1,phi1) ->
             let b =
               let uu____778 = FStar_List.hd x1 in
               resugar_binder uu____778 t.FStar_Syntax_Syntax.pos in
             let uu____781 =
               let uu____782 =
                 let uu____785 = resugar_term phi1 in (b, uu____785) in
               FStar_Parser_AST.Refine uu____782 in
             mk1 uu____781)
    | FStar_Syntax_Syntax.Tm_app (e,args) ->
        let rec last1 uu___199_815 =
          match uu___199_815 with
          | hd1::[] -> [hd1]
          | hd1::tl1 -> last1 tl1
          | uu____862 -> failwith "last of an empty list" in
        let rec last_two uu___200_886 =
          match uu___200_886 with
          | [] ->
              failwith
                "last two elements of a list with less than two elements "
          | uu____906::[] ->
              failwith
                "last two elements of a list with less than two elements "
          | a1::a2::[] -> [a1; a2]
          | uu____958::t1 -> last_two t1 in
        let rec last_three uu___201_986 =
          match uu___201_986 with
          | [] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1006::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | uu____1024::uu____1025::[] ->
              failwith
                "last three elements of a list with less than three elements "
          | a1::a2::a3::[] -> [a1; a2; a3]
          | uu____1098::t1 -> last_three t1 in
>>>>>>> origin/guido_tactics
        let resugar_as_app e1 args1 =
          let args2 =
            FStar_All.pipe_right args1
              (FStar_List.map
<<<<<<< HEAD
                 (fun uu____1103  ->
                    match uu____1103 with | (e2,qual) -> resugar_term e2)) in
=======
                 (fun uu____1134  ->
                    match uu____1134 with | (e2,qual) -> resugar_term e2)) in
>>>>>>> origin/guido_tactics
          let e2 = resugar_term e1 in
          FStar_List.fold_left
            (fun acc  ->
               fun x  ->
                 mk1
                   (FStar_Parser_AST.App (acc, x, FStar_Parser_AST.Nothing)))
            e2 args2 in
        let args1 =
<<<<<<< HEAD
          let uu____1119 = FStar_Options.print_implicits () in
          if uu____1119 then args else filter_imp args in
        let uu____1128 = resugar_term_as_op e in
        (match uu____1128 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1134) ->
             (match args1 with
              | (fst1,uu____1138)::(snd1,uu____1140)::rest ->
                  let e1 =
                    let uu____1164 =
                      let uu____1165 =
                        let uu____1169 =
                          let uu____1171 = resugar_term fst1 in
                          let uu____1172 =
                            let uu____1174 = resugar_term snd1 in
                            [uu____1174] in
                          uu____1171 :: uu____1172 in
                        ((FStar_Ident.id_of_text "*"), uu____1169) in
                      FStar_Parser_AST.Op uu____1165 in
                    mk1 uu____1164 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1184  ->
                         match uu____1184 with
                         | (x,uu____1188) ->
                             let uu____1189 =
                               let uu____1190 =
                                 let uu____1194 =
                                   let uu____1196 =
                                     let uu____1198 = resugar_term x in
                                     [uu____1198] in
                                   e1 :: uu____1196 in
                                 ((FStar_Ident.id_of_text "*"), uu____1194) in
                               FStar_Parser_AST.Op uu____1190 in
                             mk1 uu____1189) e1 rest
              | uu____1200 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1206) when
=======
          let uu____1148 = FStar_Options.print_implicits () in
          if uu____1148 then args else filter_imp args in
        let uu____1157 = resugar_term_as_op e in
        (match uu____1157 with
         | None  -> resugar_as_app e args1
         | Some ("tuple",uu____1163) ->
             (match args1 with
              | (fst1,uu____1167)::(snd1,uu____1169)::rest ->
                  let e1 =
                    let uu____1193 =
                      let uu____1194 =
                        let uu____1198 =
                          let uu____1200 = resugar_term fst1 in
                          let uu____1201 =
                            let uu____1203 = resugar_term snd1 in
                            [uu____1203] in
                          uu____1200 :: uu____1201 in
                        ((FStar_Ident.id_of_text "*"), uu____1198) in
                      FStar_Parser_AST.Op uu____1194 in
                    mk1 uu____1193 in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun uu____1208  ->
                         match uu____1208 with
                         | (x,uu____1212) ->
                             let uu____1213 =
                               let uu____1214 =
                                 let uu____1218 =
                                   let uu____1220 =
                                     let uu____1222 = resugar_term x in
                                     [uu____1222] in
                                   e1 :: uu____1220 in
                                 ((FStar_Ident.id_of_text "*"), uu____1218) in
                               FStar_Parser_AST.Op uu____1214 in
                             mk1 uu____1213) e1 rest
              | uu____1224 -> resugar_as_app e args1)
         | Some ("dtuple",uu____1230) when
>>>>>>> origin/guido_tactics
             (FStar_List.length args1) > (Prims.parse_int "0") ->
             let args2 = last1 args1 in
             let body =
               match args2 with
<<<<<<< HEAD
               | (b,uu____1228)::[] -> b
               | uu____1241 -> failwith "wrong arguments to dtuple" in
             let uu____1249 =
               let uu____1250 = FStar_Syntax_Subst.compress body in
               uu____1250.FStar_Syntax_Syntax.n in
             (match uu____1249 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1255) ->
                  let uu____1278 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1278 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1284 = FStar_Options.print_implicits () in
                         if uu____1284 then xs1 else filter_imp xs1 in
=======
               | (b,uu____1255)::[] -> b
               | uu____1268 -> failwith "wrong arguments to dtuple" in
             let uu____1276 =
               let uu____1277 = FStar_Syntax_Subst.compress body in
               uu____1277.FStar_Syntax_Syntax.n in
             (match uu____1276 with
              | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1282) ->
                  let uu____1295 = FStar_Syntax_Subst.open_term xs body1 in
                  (match uu____1295 with
                   | (xs1,body2) ->
                       let xs2 =
                         let uu____1301 = FStar_Options.print_implicits () in
                         if uu____1301 then xs1 else filter_imp xs1 in
>>>>>>> origin/guido_tactics
                       let xs3 =
                         FStar_All.pipe_right xs2
                           (FStar_List.map
                              (fun b  ->
                                 resugar_binder b t.FStar_Syntax_Syntax.pos)) in
                       let body3 = resugar_term body2 in
                       mk1 (FStar_Parser_AST.Sum (xs3, body3)))
<<<<<<< HEAD
              | uu____1293 ->
=======
              | uu____1309 ->
>>>>>>> origin/guido_tactics
                  let args3 =
                    FStar_All.pipe_right args2
                      (FStar_List.map
                         (fun uu____1320  ->
                            match uu____1320 with
                            | (e1,qual) -> resugar_term e1)) in
                  let e1 = resugar_term e in
                  FStar_List.fold_left
                    (fun acc  ->
                       fun x  ->
                         mk1
                           (FStar_Parser_AST.App
                              (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
<<<<<<< HEAD
         | Some ("dtuple",uu____1317) -> resugar_as_app e args1
         | Some (ref_read,uu____1321) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1324 = FStar_List.hd args1 in
             (match uu____1324 with
              | (t1,uu____1334) ->
                  let uu____1339 =
                    let uu____1340 = FStar_Syntax_Subst.compress t1 in
                    uu____1340.FStar_Syntax_Syntax.n in
                  (match uu____1339 with
=======
         | Some ("dtuple",uu____1328) -> resugar_as_app e args1
         | Some (ref_read,uu____1332) when
             ref_read = FStar_Syntax_Const.sread_lid.FStar_Ident.str ->
             let uu____1335 = FStar_List.hd args1 in
             (match uu____1335 with
              | (t1,uu____1345) ->
                  let uu____1350 =
                    let uu____1351 = FStar_Syntax_Subst.compress t1 in
                    uu____1351.FStar_Syntax_Syntax.n in
                  (match uu____1350 with
>>>>>>> origin/guido_tactics
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Util.field_projector_contains_constructor
                         ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       ->
                       let f =
                         FStar_Ident.lid_of_path
                           [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                           t1.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
                       let uu____1345 =
                         let uu____1346 =
                           let uu____1349 = resugar_term t1 in
                           (uu____1349, f) in
                         FStar_Parser_AST.Project uu____1346 in
                       mk1 uu____1345
                   | uu____1350 -> resugar_term t1))
         | Some ("try_with",uu____1351) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1367 =
               match new_args with
               | (a1,uu____1381)::(a2,uu____1383)::[] -> (a1, a2)
               | uu____1408 -> failwith "wrong arguments to try_with" in
             (match uu____1367 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1434 =
                      let uu____1435 = FStar_Syntax_Subst.compress term in
                      uu____1435.FStar_Syntax_Syntax.n in
                    match uu____1434 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1440) ->
                        let uu____1463 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1463 with | (x1,e2) -> e2)
                    | uu____1468 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1470 = decomp body in resugar_term uu____1470 in
                  let handler1 =
                    let uu____1472 = decomp handler in
                    resugar_term uu____1472 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1478,uu____1479,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1496,uu____1497,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1510 =
                          let uu____1511 =
                            let uu____1516 = resugar_body t11 in
                            (uu____1516, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1511 in
                        mk1 uu____1510
                    | uu____1518 ->
=======
                       let uu____1364 =
                         let uu____1365 =
                           let uu____1368 = resugar_term t1 in
                           (uu____1368, f) in
                         FStar_Parser_AST.Project uu____1365 in
                       mk1 uu____1364
                   | uu____1369 -> resugar_term t1))
         | Some ("try_with",uu____1370) when
             (FStar_List.length args1) > (Prims.parse_int "1") ->
             let new_args = last_two args1 in
             let uu____1389 =
               match new_args with
               | (a1,uu____1403)::(a2,uu____1405)::[] -> (a1, a2)
               | uu____1430 -> failwith "wrong arguments to try_with" in
             (match uu____1389 with
              | (body,handler) ->
                  let decomp term =
                    let uu____1456 =
                      let uu____1457 = FStar_Syntax_Subst.compress term in
                      uu____1457.FStar_Syntax_Syntax.n in
                    match uu____1456 with
                    | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____1462) ->
                        let uu____1475 = FStar_Syntax_Subst.open_term x e1 in
                        (match uu____1475 with | (x1,e2) -> e2)
                    | uu____1480 ->
                        failwith "wrong argument format to try_with" in
                  let body1 =
                    let uu____1482 = decomp body in resugar_term uu____1482 in
                  let handler1 =
                    let uu____1484 = decomp handler in
                    resugar_term uu____1484 in
                  let rec resugar_body t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match
                        (e1,(uu____1490,uu____1491,b)::[]) -> b
                    | FStar_Parser_AST.Let (uu____1508,uu____1509,b) -> b
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        let uu____1522 =
                          let uu____1523 =
                            let uu____1528 = resugar_body t11 in
                            (uu____1528, t2, t3) in
                          FStar_Parser_AST.Ascribed uu____1523 in
                        mk1 uu____1522
                    | uu____1530 ->
>>>>>>> origin/guido_tactics
                        failwith "unexpected body format to try_with" in
                  let e1 = resugar_body body1 in
                  let rec resugar_branches t1 =
                    match t1.FStar_Parser_AST.tm with
                    | FStar_Parser_AST.Match (e2,branches) -> branches
                    | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                        resugar_branches t11
<<<<<<< HEAD
                    | uu____1551 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1567) -> resugar_as_app e args1
         | Some (op,uu____1571) when (op = "forall") || (op = "exists") ->
=======
                    | uu____1563 -> [] in
                  let branches = resugar_branches handler1 in
                  mk1 (FStar_Parser_AST.TryWith (e1, branches)))
         | Some ("try_with",uu____1579) -> resugar_as_app e args1
         | Some (op,uu____1583) when (op = "forall") || (op = "exists") ->
>>>>>>> origin/guido_tactics
             let rec uncurry xs pat t1 =
               match t1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.QExists (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
               | FStar_Parser_AST.QForall (x,p,body) ->
                   uncurry (FStar_List.append x xs) (FStar_List.append p pat)
                     body
<<<<<<< HEAD
               | uu____1622 -> (xs, pat, t1) in
             let resugar body =
               let uu____1630 =
                 let uu____1631 = FStar_Syntax_Subst.compress body in
                 uu____1631.FStar_Syntax_Syntax.n in
               match uu____1630 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1636) ->
                   let uu____1659 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1659 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1665 = FStar_Options.print_implicits () in
                          if uu____1665 then xs1 else filter_imp xs1 in
=======
               | uu____1634 -> (xs, pat, t1) in
             let resugar body =
               let uu____1642 =
                 let uu____1643 = FStar_Syntax_Subst.compress body in
                 uu____1643.FStar_Syntax_Syntax.n in
               match uu____1642 with
               | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____1648) ->
                   let uu____1661 = FStar_Syntax_Subst.open_term xs body1 in
                   (match uu____1661 with
                    | (xs1,body2) ->
                        let xs2 =
                          let uu____1667 = FStar_Options.print_implicits () in
                          if uu____1667 then xs1 else filter_imp xs1 in
>>>>>>> origin/guido_tactics
                        let xs3 =
                          FStar_All.pipe_right xs2
                            (FStar_List.map
                               (fun b  ->
                                  resugar_binder b t.FStar_Syntax_Syntax.pos)) in
<<<<<<< HEAD
                        let uu____1672 =
                          let uu____1677 =
                            let uu____1678 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1678.FStar_Syntax_Syntax.n in
                          match uu____1677 with
=======
                        let uu____1673 =
                          let uu____1678 =
                            let uu____1679 =
                              FStar_Syntax_Subst.compress body2 in
                            uu____1679.FStar_Syntax_Syntax.n in
                          match uu____1678 with
>>>>>>> origin/guido_tactics
                          | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                              let body3 = resugar_term e1 in
                              let pats =
                                match m with
                                | FStar_Syntax_Syntax.Meta_pattern pats ->
                                    FStar_List.map
                                      (fun es  ->
                                         FStar_All.pipe_right es
                                           (FStar_List.map
<<<<<<< HEAD
                                              (fun uu____1722  ->
                                                 match uu____1722 with
                                                 | (e2,uu____1726) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1729) ->
                                    let uu____1730 =
                                      let uu____1732 =
                                        let uu____1733 = name s r in
                                        mk1 uu____1733 in
                                      [uu____1732] in
                                    [uu____1730]
                                | uu____1736 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1741 ->
                              let uu____1742 = resugar_term body2 in
                              ([], uu____1742) in
                        (match uu____1672 with
                         | (pats,body3) ->
                             let uu____1752 = uncurry xs3 pats body3 in
                             (match uu____1752 with
=======
                                              (fun uu____1719  ->
                                                 match uu____1719 with
                                                 | (e2,uu____1723) ->
                                                     resugar_term e2))) pats
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (s,r,uu____1726) ->
                                    let uu____1727 =
                                      let uu____1729 =
                                        let uu____1730 = name s r in
                                        mk1 uu____1730 in
                                      [uu____1729] in
                                    [uu____1727]
                                | uu____1733 ->
                                    failwith
                                      "wrong pattern format for QForall/QExists" in
                              (pats, body3)
                          | uu____1738 ->
                              let uu____1739 = resugar_term body2 in
                              ([], uu____1739) in
                        (match uu____1673 with
                         | (pats,body3) ->
                             let uu____1749 = uncurry xs3 pats body3 in
                             (match uu____1749 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
               | uu____1779 ->
                   if op = "forall"
                   then
                     let uu____1780 =
                       let uu____1781 =
                         let uu____1788 = resugar_term body in
                         ([], [[]], uu____1788) in
                       FStar_Parser_AST.QForall uu____1781 in
                     mk1 uu____1780
                   else
                     (let uu____1795 =
                        let uu____1796 =
                          let uu____1803 = resugar_term body in
                          ([], [[]], uu____1803) in
                        FStar_Parser_AST.QExists uu____1796 in
                      mk1 uu____1795) in
=======
               | uu____1776 ->
                   if op = "forall"
                   then
                     let uu____1777 =
                       let uu____1778 =
                         let uu____1785 = resugar_term body in
                         ([], [[]], uu____1785) in
                       FStar_Parser_AST.QForall uu____1778 in
                     mk1 uu____1777
                   else
                     (let uu____1792 =
                        let uu____1793 =
                          let uu____1800 = resugar_term body in
                          ([], [[]], uu____1800) in
                        FStar_Parser_AST.QExists uu____1793 in
                      mk1 uu____1792) in
>>>>>>> origin/guido_tactics
             if (FStar_List.length args1) > (Prims.parse_int "0")
             then
               let args2 = last1 args1 in
               (match args2 with
                | (b,uu____1823)::[] -> resugar b
                | uu____1836 -> failwith "wrong args format to QForall")
             else resugar_as_app e args1
         | Some ("alloc",uu____1843) ->
             let uu____1846 = FStar_List.hd args1 in
             (match uu____1846 with | (e1,uu____1856) -> resugar_term e1)
         | Some (op,arity) ->
             let op1 = FStar_Ident.id_of_text op in
             let resugar args2 =
               FStar_All.pipe_right args2
                 (FStar_List.map
<<<<<<< HEAD
                    (fun uu____1886  ->
                       match uu____1886 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_28 when _0_28 = (Prims.parse_int "0") ->
                  let uu____1891 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1891 with
                   | _0_29 when
                       (_0_29 = (Prims.parse_int "1")) &&
=======
                    (fun uu____1883  ->
                       match uu____1883 with | (e1,qual) -> resugar_term e1)) in
             (match arity with
              | _0_38 when _0_38 = (Prims.parse_int "0") ->
                  let uu____1888 =
                    FStar_Parser_ToDocument.handleable_args_length op1 in
                  (match uu____1888 with
                   | _0_39 when
                       (_0_39 = (Prims.parse_int "1")) &&
>>>>>>> origin/guido_tactics
                         ((FStar_List.length args1) > (Prims.parse_int "0"))
                       ->
                       let uu____1899 =
                         let uu____1900 =
                           let uu____1904 =
                             let uu____1906 = last1 args1 in
                             resugar uu____1906 in
                           (op1, uu____1904) in
                         FStar_Parser_AST.Op uu____1900 in
                       mk1 uu____1899
<<<<<<< HEAD
                   | _0_30 when
                       (_0_30 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1918 =
                         let uu____1919 =
                           let uu____1923 =
                             let uu____1925 = last_two args1 in
                             resugar uu____1925 in
                           (op1, uu____1923) in
                         FStar_Parser_AST.Op uu____1919 in
                       mk1 uu____1918
                   | _0_31 when
                       (_0_31 = (Prims.parse_int "3")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "2"))
                       ->
                       let uu____1937 =
                         let uu____1938 =
                           let uu____1942 =
                             let uu____1944 = last_three args1 in
                             resugar uu____1944 in
                           (op1, uu____1942) in
                         FStar_Parser_AST.Op uu____1938 in
                       mk1 uu____1937
                   | uu____1949 -> resugar_as_app e args1)
              | _0_32 when
                  (_0_32 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1957 =
                    let uu____1958 =
                      let uu____1962 =
                        let uu____1964 = last_two args1 in resugar uu____1964 in
                      (op1, uu____1962) in
                    FStar_Parser_AST.Op uu____1958 in
                  mk1 uu____1957
              | uu____1969 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1972,t1)::[]) ->
        let bnds =
          let uu____2022 =
            let uu____2025 = resugar_pat pat in
            let uu____2026 = resugar_term e in (uu____2025, uu____2026) in
          [uu____2022] in
=======
                   | _0_40 when
                       (_0_40 = (Prims.parse_int "2")) &&
                         ((FStar_List.length args1) > (Prims.parse_int "1"))
                       ->
                       let uu____1921 =
                         let uu____1922 =
                           let uu____1926 =
                             let uu____1928 = last_two args1 in
                             resugar uu____1928 in
                           (op1, uu____1926) in
                         FStar_Parser_AST.Op uu____1922 in
                       mk1 uu____1921
                   | _0_41 when
                       (_0_41 = (Prims.parse_int "3")) &&
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
              | _0_42 when
                  (_0_42 = (Prims.parse_int "2")) &&
                    ((FStar_List.length args1) > (Prims.parse_int "1"))
                  ->
                  let uu____1966 =
                    let uu____1967 =
                      let uu____1971 =
                        let uu____1973 = last_two args1 in resugar uu____1973 in
                      (op1, uu____1971) in
                    FStar_Parser_AST.Op uu____1967 in
                  mk1 uu____1966
              | uu____1978 -> resugar_as_app e args1))
    | FStar_Syntax_Syntax.Tm_match (e,(pat,uu____1981,t1)::[]) ->
        let bnds =
          let uu____2036 =
            let uu____2039 = resugar_pat pat in
            let uu____2040 = resugar_term e in (uu____2039, uu____2040) in
          [uu____2036] in
>>>>>>> origin/guido_tactics
        let body = resugar_term t1 in
        mk1
          (FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, bnds, body))
    | FStar_Syntax_Syntax.Tm_match
<<<<<<< HEAD
        (e,(pat1,uu____2037,t1)::(pat2,uu____2040,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2107 =
          let uu____2108 =
            let uu____2112 = resugar_term e in
            let uu____2113 = resugar_term t1 in
            let uu____2114 = resugar_term t2 in
            (uu____2112, uu____2113, uu____2114) in
          FStar_Parser_AST.If uu____2108 in
        mk1 uu____2107
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2152 =
          match uu____2152 with
=======
        (e,(pat1,uu____2051,t1)::(pat2,uu____2054,t2)::[]) when
        (is_true_pat pat1) && (is_wild_pat pat2) ->
        let uu____2129 =
          let uu____2130 =
            let uu____2134 = resugar_term e in
            let uu____2135 = resugar_term t1 in
            let uu____2136 = resugar_term t2 in
            (uu____2134, uu____2135, uu____2136) in
          FStar_Parser_AST.If uu____2130 in
        mk1 uu____2129
    | FStar_Syntax_Syntax.Tm_match (e,branches) ->
        let resugar_branch uu____2176 =
          match uu____2176 with
>>>>>>> origin/guido_tactics
          | (pat,wopt,b) ->
              let pat1 = resugar_pat pat in
              let wopt1 =
                match wopt with
                | None  -> None
                | Some e1 ->
<<<<<<< HEAD
                    let uu____2171 = resugar_term e1 in Some uu____2171 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2174 =
          let uu____2175 =
            let uu____2183 = resugar_term e in
            let uu____2184 = FStar_List.map resugar_branch branches in
            (uu____2183, uu____2184) in
          FStar_Parser_AST.Match uu____2175 in
        mk1 uu____2174
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2206) ->
=======
                    let uu____2195 = resugar_term e1 in Some uu____2195 in
              let b1 = resugar_term b in (pat1, wopt1, b1) in
        let uu____2198 =
          let uu____2199 =
            let uu____2207 = resugar_term e in
            let uu____2208 = FStar_List.map resugar_branch branches in
            (uu____2207, uu____2208) in
          FStar_Parser_AST.Match uu____2199 in
        mk1 uu____2198
    | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____2230) ->
>>>>>>> origin/guido_tactics
        let term =
          match asc with
          | FStar_Util.Inl n1 -> resugar_term n1
          | FStar_Util.Inr n1 -> resugar_comp n1 in
        let tac_opt1 = FStar_Option.map resugar_term tac_opt in
<<<<<<< HEAD
        let uu____2259 =
          let uu____2260 =
            let uu____2265 = resugar_term e in (uu____2265, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2260 in
        mk1 uu____2259
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2283 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2283 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2299 =
                 let uu____2302 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2302 in
               match uu____2299 with
               | (univs1,td) ->
                   let uu____2309 =
                     let uu____2316 =
                       let uu____2317 = FStar_Syntax_Subst.compress td in
                       uu____2317.FStar_Syntax_Syntax.n in
                     match uu____2316 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2326,(t1,uu____2328)::(d,uu____2330)::[]) ->
                         (t1, d)
                     | uu____2364 -> failwith "wrong let binding format" in
                   (match uu____2309 with
                    | (typ,def) ->
                        let uu____2385 =
                          let uu____2389 =
                            let uu____2390 = FStar_Syntax_Subst.compress def in
                            uu____2390.FStar_Syntax_Syntax.n in
                          match uu____2389 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2398) ->
                              let uu____2421 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2421 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2430 =
                                       FStar_Options.print_implicits () in
                                     if uu____2430 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2432 -> ([], def, false) in
                        (match uu____2385 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2453 =
                                 FStar_Options.print_universes () in
                               if uu____2453
                               then
                                 let uu____2454 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2454
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2460 =
=======
        let uu____2283 =
          let uu____2284 =
            let uu____2289 = resugar_term e in (uu____2289, term, tac_opt1) in
          FStar_Parser_AST.Ascribed uu____2284 in
        mk1 uu____2283
    | FStar_Syntax_Syntax.Tm_let ((is_rec,bnds),body) ->
        let mk_pat a =
          FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
        let uu____2307 = FStar_Syntax_Subst.open_let_rec bnds body in
        (match uu____2307 with
         | (bnds1,body1) ->
             let resugar_one_binding bnd =
               let uu____2323 =
                 let uu____2326 =
                   FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                     bnd.FStar_Syntax_Syntax.lbdef in
                 FStar_Syntax_Subst.open_univ_vars
                   bnd.FStar_Syntax_Syntax.lbunivs uu____2326 in
               match uu____2323 with
               | (univs1,td) ->
                   let uu____2333 =
                     let uu____2340 =
                       let uu____2341 = FStar_Syntax_Subst.compress td in
                       uu____2341.FStar_Syntax_Syntax.n in
                     match uu____2340 with
                     | FStar_Syntax_Syntax.Tm_app
                         (uu____2350,(t1,uu____2352)::(d,uu____2354)::[]) ->
                         (t1, d)
                     | uu____2388 -> failwith "wrong let binding format" in
                   (match uu____2333 with
                    | (typ,def) ->
                        let uu____2409 =
                          let uu____2413 =
                            let uu____2414 = FStar_Syntax_Subst.compress def in
                            uu____2414.FStar_Syntax_Syntax.n in
                          match uu____2413 with
                          | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____2422) ->
                              let uu____2435 =
                                FStar_Syntax_Subst.open_term b t1 in
                              (match uu____2435 with
                               | (b1,t2) ->
                                   let b2 =
                                     let uu____2444 =
                                       FStar_Options.print_implicits () in
                                     if uu____2444 then b1 else filter_imp b1 in
                                   (b2, t2, true))
                          | uu____2446 -> ([], def, false) in
                        (match uu____2409 with
                         | (binders,term,is_pat_app) ->
                             let universe_to_string univs2 =
                               let uu____2467 =
                                 FStar_Options.print_universes () in
                               if uu____2467
                               then
                                 let uu____2468 =
                                   FStar_List.map
                                     (fun x  -> x.FStar_Ident.idText) univs2 in
                                 FStar_All.pipe_right uu____2468
                                   (FStar_String.concat ", ")
                               else "" in
                             let uu____2473 =
>>>>>>> origin/guido_tactics
                               match bnd.FStar_Syntax_Syntax.lbname with
                               | FStar_Util.Inr fv ->
                                   ((mk_pat
                                       (FStar_Parser_AST.PatName
                                          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                     term)
                               | FStar_Util.Inl bv ->
<<<<<<< HEAD
                                   let uu____2467 =
                                     let uu____2468 =
                                       let uu____2469 =
                                         let uu____2473 =
                                           bv_as_unique_ident bv in
                                         (uu____2473, None) in
                                       FStar_Parser_AST.PatVar uu____2469 in
                                     mk_pat uu____2468 in
                                   (uu____2467, term) in
                             (match uu____2460 with
=======
                                   let uu____2484 =
                                     let uu____2485 =
                                       let uu____2486 =
                                         let uu____2490 =
                                           bv_as_unique_ident bv in
                                         (uu____2490, None) in
                                       FStar_Parser_AST.PatVar uu____2486 in
                                     mk_pat uu____2485 in
                                   (uu____2484, term) in
                             (match uu____2473 with
>>>>>>> origin/guido_tactics
                              | (pat,term1) ->
                                  if is_pat_app
                                  then
                                    let args =
                                      FStar_All.pipe_right binders
                                        (FStar_List.map
<<<<<<< HEAD
                                           (fun uu____2494  ->
                                              match uu____2494 with
                                              | (bv,uu____2498) ->
                                                  let uu____2499 =
                                                    let uu____2500 =
                                                      let uu____2504 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2504, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2500 in
                                                  mk_pat uu____2499)) in
                                    let uu____2506 =
                                      let uu____2509 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2509) in
                                    let uu____2511 =
                                      universe_to_string univs1 in
                                    (uu____2506, uu____2511)
                                  else
                                    (let uu____2515 =
                                       let uu____2518 = resugar_term term1 in
                                       (pat, uu____2518) in
                                     let uu____2519 =
                                       universe_to_string univs1 in
                                     (uu____2515, uu____2519))))) in
=======
                                           (fun uu____2507  ->
                                              match uu____2507 with
                                              | (bv,uu____2511) ->
                                                  let uu____2512 =
                                                    let uu____2513 =
                                                      let uu____2517 =
                                                        bv_as_unique_ident bv in
                                                      (uu____2517, None) in
                                                    FStar_Parser_AST.PatVar
                                                      uu____2513 in
                                                  mk_pat uu____2512)) in
                                    let uu____2519 =
                                      let uu____2522 = resugar_term term1 in
                                      ((mk_pat
                                          (FStar_Parser_AST.PatApp
                                             (pat, args))), uu____2522) in
                                    let uu____2524 =
                                      universe_to_string univs1 in
                                    (uu____2519, uu____2524)
                                  else
                                    (let uu____2528 =
                                       let uu____2531 = resugar_term term1 in
                                       (pat, uu____2531) in
                                     let uu____2532 =
                                       universe_to_string univs1 in
                                     (uu____2528, uu____2532))))) in
>>>>>>> origin/guido_tactics
             let r = FStar_List.map resugar_one_binding bnds1 in
             let bnds2 = FStar_List.map FStar_Pervasives.fst r in
             let comments = FStar_List.map FStar_Pervasives.snd r in
             let body2 = resugar_term body1 in
             mk1
               (FStar_Parser_AST.Let
                  ((if is_rec
                    then FStar_Parser_AST.Rec
                    else FStar_Parser_AST.NoLetQualifier), bnds2, body2)))
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2558) ->
        let s =
          let uu____2576 =
            let uu____2577 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2577 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2576 in
        let uu____2578 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2578
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___190_2588 =
          match uu___190_2588 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2589 =
                let uu____2590 = FStar_Syntax_Subst.compress e in
                uu____2590.FStar_Syntax_Syntax.n in
              (match uu____2589 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2616 =
                       let uu____2617 = FStar_Syntax_Subst.compress h in
                       uu____2617.FStar_Syntax_Syntax.n in
                     match uu____2616 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2624 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2624, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2632 = aux h1 in
                         (match uu____2632 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2644 -> failwith "wrong Data_app head format" in
                   let uu____2648 = aux head1 in
                   (match uu____2648 with
=======
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____2571) ->
        let s =
          let uu____2585 =
            let uu____2586 = FStar_Syntax_Unionfind.uvar_id u in
            FStar_All.pipe_right uu____2586 FStar_Util.string_of_int in
          Prims.strcat "uu___unification_ " uu____2585 in
        let uu____2587 = var s t.FStar_Syntax_Syntax.pos in mk1 uu____2587
    | FStar_Syntax_Syntax.Tm_meta (e,m) ->
        let resugar_meta_desugared uu___202_2597 =
          match uu___202_2597 with
          | FStar_Syntax_Syntax.Data_app  ->
              let uu____2598 =
                let uu____2599 = FStar_Syntax_Subst.compress e in
                uu____2599.FStar_Syntax_Syntax.n in
              (match uu____2598 with
               | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                   let rec aux h =
                     let uu____2625 =
                       let uu____2626 = FStar_Syntax_Subst.compress h in
                       uu____2626.FStar_Syntax_Syntax.n in
                     match uu____2625 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2633 = FStar_Syntax_Syntax.lid_of_fv fv in
                         (uu____2633, [])
                     | FStar_Syntax_Syntax.Tm_uinst (h1,u) ->
                         let uu____2641 = aux h1 in
                         (match uu____2641 with
                          | (h2,l) -> (h2, (FStar_List.append l u)))
                     | uu____2653 -> failwith "wrong Data_app head format" in
                   let uu____2657 = aux head1 in
                   (match uu____2657 with
>>>>>>> origin/guido_tactics
                    | (head2,universes) ->
                        let universes1 =
                          FStar_List.map
                            (fun u  ->
<<<<<<< HEAD
                               let uu____2665 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2665, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2678  ->
                               match uu____2678 with
                               | (t1,uu____2684) ->
                                   let uu____2685 = resugar_term t1 in
                                   (uu____2685, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2686 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2686
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2691 = FStar_Options.print_universes () in
                           if uu____2691
=======
                               let uu____2672 =
                                 resugar_universe u t.FStar_Syntax_Syntax.pos in
                               (uu____2672, FStar_Parser_AST.UnivApp))
                            universes in
                        let args1 =
                          FStar_List.map
                            (fun uu____2681  ->
                               match uu____2681 with
                               | (t1,uu____2687) ->
                                   let uu____2688 = resugar_term t1 in
                                   (uu____2688, FStar_Parser_AST.Nothing))
                            args in
                        let uu____2689 =
                          FStar_Syntax_Util.is_tuple_data_lid' head2 in
                        if uu____2689
                        then mk1 (FStar_Parser_AST.Construct (head2, args1))
                        else
                          (let uu____2694 = FStar_Options.print_universes () in
                           if uu____2694
>>>>>>> origin/guido_tactics
                           then
                             mk1
                               (FStar_Parser_AST.Construct
                                  (head2,
                                    (FStar_List.append args1 universes1)))
                           else
                             mk1 (FStar_Parser_AST.Construct (head2, args1))))
<<<<<<< HEAD
               | FStar_Syntax_Syntax.Tm_meta (uu____2701,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2707,uu____2708) -> resugar_term e
                    | uu____2713 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2714 -> failwith "wrong Data_app format")
=======
               | FStar_Syntax_Syntax.Tm_meta (uu____2704,m1) ->
                   (match m1 with
                    | FStar_Syntax_Syntax.Meta_monadic
                        (uu____2710,uu____2711) -> resugar_term e
                    | uu____2716 ->
                        failwith "wrong Tm_meta format in Meta_desugared")
               | uu____2717 -> failwith "wrong Data_app format")
>>>>>>> origin/guido_tactics
          | FStar_Syntax_Syntax.Sequence  ->
              let term = resugar_term e in
              let rec resugar_seq t1 =
                match t1.FStar_Parser_AST.tm with
<<<<<<< HEAD
                | FStar_Parser_AST.Let (uu____2720,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2736 =
                      let uu____2737 =
                        let uu____2742 = resugar_seq t11 in
                        (uu____2742, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2737 in
                    mk1 uu____2736
                | uu____2744 -> t1 in
=======
                | FStar_Parser_AST.Let (uu____2723,(p,t11)::[],t2) ->
                    mk1 (FStar_Parser_AST.Seq (t11, t2))
                | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                    let uu____2739 =
                      let uu____2740 =
                        let uu____2745 = resugar_seq t11 in
                        (uu____2745, t2, t3) in
                      FStar_Parser_AST.Ascribed uu____2740 in
                    mk1 uu____2739
                | uu____2747 -> t1 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
               | uu____2757 ->
=======
               | uu____2760 ->
>>>>>>> origin/guido_tactics
                   failwith
                     "mutable_alloc should have let term with no qualifier")
          | FStar_Syntax_Syntax.Mutable_rval  ->
              let fv =
                FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
                  FStar_Syntax_Syntax.Delta_constant None in
<<<<<<< HEAD
              let uu____2759 =
                let uu____2760 = FStar_Syntax_Subst.compress e in
                uu____2760.FStar_Syntax_Syntax.n in
              (match uu____2759 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2764;
                      FStar_Syntax_Syntax.pos = uu____2765;
                      FStar_Syntax_Syntax.vars = uu____2766;_},(term,uu____2768)::[])
                   -> resugar_term term
               | uu____2790 -> failwith "mutable_rval should have app term") in
=======
              let uu____2762 =
                let uu____2763 = FStar_Syntax_Subst.compress e in
                uu____2763.FStar_Syntax_Syntax.n in
              (match uu____2762 with
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                      FStar_Syntax_Syntax.tk = uu____2767;
                      FStar_Syntax_Syntax.pos = uu____2768;
                      FStar_Syntax_Syntax.vars = uu____2769;_},(term,uu____2771)::[])
                   -> resugar_term term
               | uu____2793 -> failwith "mutable_rval should have app term") in
>>>>>>> origin/guido_tactics
        (match m with
         | FStar_Syntax_Syntax.Meta_pattern pats ->
             let pats1 =
               FStar_All.pipe_right (FStar_List.flatten pats)
                 (FStar_List.map
                    (fun uu____2815  ->
                       match uu____2815 with
                       | (x,uu____2819) -> resugar_term x)) in
             mk1 (FStar_Parser_AST.Attributes pats1)
         | FStar_Syntax_Syntax.Meta_labeled (l,uu____2821,p) ->
             let uu____2823 =
               let uu____2824 =
                 let uu____2828 = resugar_term e in (uu____2828, l, p) in
               FStar_Parser_AST.Labeled uu____2824 in
             mk1 uu____2823
         | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
         | FStar_Syntax_Syntax.Meta_alien (uu____2830,s) -> resugar_term e
         | FStar_Syntax_Syntax.Meta_named t1 ->
             mk1 (FStar_Parser_AST.Name t1)
         | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
<<<<<<< HEAD
             let uu____2837 =
               let uu____2838 =
                 let uu____2843 = resugar_term e in
                 let uu____2844 =
                   let uu____2845 =
                     let uu____2846 =
                       let uu____2852 =
                         let uu____2856 =
                           let uu____2859 = resugar_term t1 in
                           (uu____2859, FStar_Parser_AST.Nothing) in
                         [uu____2856] in
                       (name1, uu____2852) in
                     FStar_Parser_AST.Construct uu____2846 in
                   mk1 uu____2845 in
                 (uu____2843, uu____2844, None) in
               FStar_Parser_AST.Ascribed uu____2838 in
             mk1 uu____2837
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2869,t1) ->
             let uu____2875 =
               let uu____2876 =
                 let uu____2881 = resugar_term e in
                 let uu____2882 =
                   let uu____2883 =
                     let uu____2884 =
                       let uu____2890 =
                         let uu____2894 =
                           let uu____2897 = resugar_term t1 in
                           (uu____2897, FStar_Parser_AST.Nothing) in
                         [uu____2894] in
                       (name1, uu____2890) in
                     FStar_Parser_AST.Construct uu____2884 in
                   mk1 uu____2883 in
                 (uu____2881, uu____2882, None) in
               FStar_Parser_AST.Ascribed uu____2876 in
             mk1 uu____2875)
=======
             let uu____2839 =
               let uu____2840 =
                 let uu____2845 = resugar_term e in
                 let uu____2846 =
                   let uu____2847 =
                     let uu____2848 =
                       let uu____2854 =
                         let uu____2858 =
                           let uu____2861 = resugar_term t1 in
                           (uu____2861, FStar_Parser_AST.Nothing) in
                         [uu____2858] in
                       (name1, uu____2854) in
                     FStar_Parser_AST.Construct uu____2848 in
                   mk1 uu____2847 in
                 (uu____2845, uu____2846, None) in
               FStar_Parser_AST.Ascribed uu____2840 in
             mk1 uu____2839
         | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____2871,t1) ->
             let uu____2877 =
               let uu____2878 =
                 let uu____2883 = resugar_term e in
                 let uu____2884 =
                   let uu____2885 =
                     let uu____2886 =
                       let uu____2892 =
                         let uu____2896 =
                           let uu____2899 = resugar_term t1 in
                           (uu____2899, FStar_Parser_AST.Nothing) in
                         [uu____2896] in
                       (name1, uu____2892) in
                     FStar_Parser_AST.Construct uu____2886 in
                   mk1 uu____2885 in
                 (uu____2883, uu____2884, None) in
               FStar_Parser_AST.Ascribed uu____2878 in
             mk1 uu____2877)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
             let uu____2928 = FStar_Options.print_universes () in
             if uu____2928
=======
             let uu____2930 = FStar_Options.print_universes () in
             if uu____2930
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
             let uu____2964 = FStar_Options.print_universes () in
             if uu____2964
=======
             let uu____2966 = FStar_Options.print_universes () in
             if uu____2966
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          let uu____2987 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2987, FStar_Parser_AST.Nothing) in
        let uu____2988 = FStar_Options.print_effect_args () in
        if uu____2988
=======
          let uu____2989 = resugar_term c1.FStar_Syntax_Syntax.result_typ in
          (uu____2989, FStar_Parser_AST.Nothing) in
        let uu____2990 = FStar_Options.print_effect_args () in
        if uu____2990
>>>>>>> origin/guido_tactics
        then
          let universe =
            FStar_List.map (fun u  -> resugar_universe u)
              c1.FStar_Syntax_Syntax.comp_univs in
          let args =
            if
              FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                FStar_Syntax_Const.effect_Lemma_lid
            then
<<<<<<< HEAD
              let rec aux l uu___191_3029 =
                match uu___191_3029 with
=======
              let rec aux l uu___203_3030 =
                match uu___203_3030 with
>>>>>>> origin/guido_tactics
                | [] -> l
                | (t,aq)::tl1 ->
                    (match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Syntax_Const.true_lid
                         -> aux l tl1
<<<<<<< HEAD
                     | FStar_Syntax_Syntax.Tm_meta uu____3071 -> aux l tl1
                     | uu____3076 -> aux ((t, aq) :: l) tl1) in
=======
                     | FStar_Syntax_Syntax.Tm_meta uu____3072 -> aux l tl1
                     | uu____3077 -> aux ((t, aq) :: l) tl1) in
>>>>>>> origin/guido_tactics
              aux [] c1.FStar_Syntax_Syntax.effect_args
            else c1.FStar_Syntax_Syntax.effect_args in
          let args1 =
            FStar_List.map
<<<<<<< HEAD
              (fun uu____3100  ->
                 match uu____3100 with
                 | (e,uu____3106) ->
                     let uu____3107 = resugar_term e in
                     (uu____3107, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___192_3121 =
            match uu___192_3121 with
=======
              (fun uu____3097  ->
                 match uu____3097 with
                 | (e,uu____3103) ->
                     let uu____3104 = resugar_term e in
                     (uu____3104, FStar_Parser_AST.Nothing)) args in
          let rec aux l uu___204_3118 =
            match uu___204_3118 with
>>>>>>> origin/guido_tactics
            | [] -> l
            | hd1::tl1 ->
                (match hd1 with
                 | FStar_Syntax_Syntax.DECREASES e ->
                     let e1 =
<<<<<<< HEAD
                       let uu____3141 = resugar_term e in
                       (uu____3141, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3144 -> aux l tl1) in
=======
                       let uu____3138 = resugar_term e in
                       (uu____3138, FStar_Parser_AST.Nothing) in
                     aux (e1 :: l) tl1
                 | uu____3141 -> aux l tl1) in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____3168 = b in
      match uu____3168 with
=======
      let uu____3165 = b in
      match uu____3165 with
>>>>>>> origin/guido_tactics
      | (x,imp) ->
          let e = resugar_term x.FStar_Syntax_Syntax.sort in
          (match e.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Wild  ->
<<<<<<< HEAD
               let uu____3172 =
                 let uu____3173 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3173 in
               FStar_Parser_AST.mk_binder uu____3172 r
                 FStar_Parser_AST.Type_level None
           | uu____3174 ->
               let uu____3175 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3175
=======
               let uu____3169 =
                 let uu____3170 = bv_as_unique_ident x in
                 FStar_Parser_AST.Variable uu____3170 in
               FStar_Parser_AST.mk_binder uu____3169 r
                 FStar_Parser_AST.Type_level None
           | uu____3171 ->
               let uu____3172 = FStar_Syntax_Syntax.is_null_bv x in
               if uu____3172
>>>>>>> origin/guido_tactics
               then
                 FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e) r
                   FStar_Parser_AST.Type_level None
               else
<<<<<<< HEAD
                 (let uu____3177 =
                    let uu____3178 =
                      let uu____3181 = bv_as_unique_ident x in
                      (uu____3181, e) in
                    FStar_Parser_AST.Annotated uu____3178 in
                  FStar_Parser_AST.mk_binder uu____3177 r
=======
                 (let uu____3174 =
                    let uu____3175 =
                      let uu____3178 = bv_as_unique_ident x in
                      (uu____3178, e) in
                    FStar_Parser_AST.Annotated uu____3175 in
                  FStar_Parser_AST.mk_binder uu____3174 r
>>>>>>> origin/guido_tactics
                    FStar_Parser_AST.Type_level None))
and resugar_bv_as_pat:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.aqual -> FStar_Parser_AST.pattern option
  =
  fun x  ->
    fun qual  ->
      let mk1 a =
<<<<<<< HEAD
        let uu____3189 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3189 in
      let uu____3190 =
        let uu____3191 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3191.FStar_Syntax_Syntax.n in
      match uu____3190 with
=======
        let uu____3186 = FStar_Syntax_Syntax.range_of_bv x in
        FStar_Parser_AST.mk_pattern a uu____3186 in
      let uu____3187 =
        let uu____3188 =
          FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
        uu____3188.FStar_Syntax_Syntax.n in
      match uu____3187 with
>>>>>>> origin/guido_tactics
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let i =
            FStar_String.compare
              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
              FStar_Ident.reserved_prefix in
          if i = (Prims.parse_int "0")
          then
<<<<<<< HEAD
            let uu____3197 = mk1 FStar_Parser_AST.PatWild in Some uu____3197
          else
            (let uu____3199 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3199
               (fun aq  ->
                  let uu____3207 =
                    let uu____3208 =
                      let uu____3209 =
                        let uu____3213 = bv_as_unique_ident x in
                        (uu____3213, aq) in
                      FStar_Parser_AST.PatVar uu____3209 in
                    mk1 uu____3208 in
                  Some uu____3207))
      | uu____3215 ->
          let uu____3216 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3216
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
=======
            let uu____3194 = mk1 FStar_Parser_AST.PatWild in Some uu____3194
          else
            (let uu____3196 = resugar_arg_qual qual in
             FStar_Util.bind_opt uu____3196
               (fun aq  ->
                  let uu____3202 =
                    let uu____3203 =
                      let uu____3204 =
                        let uu____3208 = bv_as_unique_ident x in
                        (uu____3208, aq) in
                      FStar_Parser_AST.PatVar uu____3204 in
                    mk1 uu____3203 in
                  Some uu____3202))
      | uu____3210 ->
          let uu____3211 = resugar_arg_qual qual in
          FStar_Util.bind_opt uu____3211
            (fun aq  ->
               let pat =
                 let uu____3218 =
                   let uu____3219 =
                     let uu____3223 = bv_as_unique_ident x in
                     (uu____3223, aq) in
                   FStar_Parser_AST.PatVar uu____3219 in
                 mk1 uu____3218 in
               let uu____3225 = FStar_Options.print_bound_var_types () in
               if uu____3225
               then
                 let uu____3227 =
                   let uu____3228 =
                     let uu____3229 =
                       let uu____3232 =
                         resugar_term x.FStar_Syntax_Syntax.sort in
                       (pat, uu____3232) in
                     FStar_Parser_AST.PatAscribed uu____3229 in
                   mk1 uu____3228 in
                 Some uu____3227
>>>>>>> origin/guido_tactics
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
              (fun uu____3278  -> match uu____3278 with | (p2,b) -> aux p2)
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
<<<<<<< HEAD
              (fun uu____3300  -> match uu____3300 with | (p2,b) -> aux p2)
              args in
          let uu____3305 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3305
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3309;
             FStar_Syntax_Syntax.fv_delta = uu____3310;
=======
              (fun uu____3307  -> match uu____3307 with | (p2,b) -> aux p2)
              args in
          let uu____3312 =
            FStar_Syntax_Util.is_dtuple_data_lid'
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          if uu____3312
          then mk1 (FStar_Parser_AST.PatTuple (args1, true))
          else mk1 (FStar_Parser_AST.PatTuple (args1, false))
      | FStar_Syntax_Syntax.Pat_cons
          ({ FStar_Syntax_Syntax.fv_name = uu____3320;
             FStar_Syntax_Syntax.fv_delta = uu____3321;
>>>>>>> origin/guido_tactics
             FStar_Syntax_Syntax.fv_qual = Some
               (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
          ->
          let fields1 =
<<<<<<< HEAD
            let uu____3326 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3326 FStar_List.rev in
          let args1 =
            let uu____3336 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3348  ->
                      match uu____3348 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3336 FStar_List.rev in
=======
            let uu____3342 =
              FStar_All.pipe_right fields
                (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f])) in
            FStar_All.pipe_right uu____3342 FStar_List.rev in
          let args1 =
            let uu____3351 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3361  ->
                      match uu____3361 with | (p2,b) -> aux p2)) in
            FStar_All.pipe_right uu____3351 FStar_List.rev in
>>>>>>> origin/guido_tactics
          let rec map21 l1 l2 =
            match (l1, l2) with
            | ([],[]) -> []
            | ([],hd1::tl1) -> []
            | (hd1::tl1,[]) ->
<<<<<<< HEAD
                let uu____3390 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3390
            | (hd1::tl1,hd2::tl2) ->
                let uu____3404 = map21 tl1 tl2 in (hd1, hd2) :: uu____3404 in
          let args2 =
            let uu____3414 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3414 FStar_List.rev in
=======
                let uu____3403 = map21 tl1 [] in
                (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____3403
            | (hd1::tl1,hd2::tl2) ->
                let uu____3417 = map21 tl1 tl2 in (hd1, hd2) :: uu____3417 in
          let args2 =
            let uu____3427 = map21 fields1 args1 in
            FStar_All.pipe_right uu____3427 FStar_List.rev in
>>>>>>> origin/guido_tactics
          mk1 (FStar_Parser_AST.PatRecord args2)
      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
          let args1 =
            FStar_List.map
<<<<<<< HEAD
              (fun uu____3443  -> match uu____3443 with | (p2,b) -> aux p2)
=======
              (fun uu____3455  -> match uu____3455 with | (p2,b) -> aux p2)
>>>>>>> origin/guido_tactics
              args in
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args1))
      | FStar_Syntax_Syntax.Pat_var v1 ->
<<<<<<< HEAD
          let uu____3450 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3450 with
           | Some (op,uu____3455) ->
=======
          let uu____3466 =
            string_to_op (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
          (match uu____3466 with
           | Some (op,uu____3471) ->
>>>>>>> origin/guido_tactics
               mk1
                 (FStar_Parser_AST.PatOp
                    (FStar_Ident.mk_ident
                       (op,
                         ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
           | None  ->
<<<<<<< HEAD
               let uu____3460 =
                 let uu____3461 =
                   let uu____3465 = bv_as_unique_ident v1 in
                   (uu____3465, None) in
                 FStar_Parser_AST.PatVar uu____3461 in
               mk1 uu____3460)
      | FStar_Syntax_Syntax.Pat_wild uu____3467 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3475 =
              let uu____3476 =
                let uu____3480 = bv_as_unique_ident bv in (uu____3480, None) in
              FStar_Parser_AST.PatVar uu____3476 in
            mk1 uu____3475 in
          let uu____3482 = FStar_Options.print_bound_var_types () in
          if uu____3482
          then
            let uu____3483 =
              let uu____3484 =
                let uu____3487 = resugar_term term in (pat, uu____3487) in
              FStar_Parser_AST.PatAscribed uu____3484 in
            mk1 uu____3483
=======
               let uu____3476 =
                 let uu____3477 =
                   let uu____3481 = bv_as_unique_ident v1 in
                   (uu____3481, None) in
                 FStar_Parser_AST.PatVar uu____3477 in
               mk1 uu____3476)
      | FStar_Syntax_Syntax.Pat_wild uu____3483 ->
          mk1 FStar_Parser_AST.PatWild
      | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
          let pat =
            let uu____3491 =
              let uu____3492 =
                let uu____3496 = bv_as_unique_ident bv in (uu____3496, None) in
              FStar_Parser_AST.PatVar uu____3492 in
            mk1 uu____3491 in
          let uu____3498 = FStar_Options.print_bound_var_types () in
          if uu____3498
          then
            let uu____3499 =
              let uu____3500 =
                let uu____3503 = resugar_term term in (pat, uu____3503) in
              FStar_Parser_AST.PatAscribed uu____3500 in
            mk1 uu____3499
>>>>>>> origin/guido_tactics
          else pat in
    aux p
let resugar_qualifier:
  FStar_Syntax_Syntax.qualifier -> FStar_Parser_AST.qualifier option =
<<<<<<< HEAD
  fun uu___193_3492  ->
    match uu___193_3492 with
=======
  fun uu___205_3509  ->
    match uu___205_3509 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Reflectable uu____3498 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3499 -> None
    | FStar_Syntax_Syntax.Projector uu____3500 -> None
    | FStar_Syntax_Syntax.RecordType uu____3503 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3508 -> None
    | FStar_Syntax_Syntax.Action uu____3513 -> None
=======
    | FStar_Syntax_Syntax.Reflectable uu____3515 ->
        Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____3516 -> None
    | FStar_Syntax_Syntax.Projector uu____3517 -> None
    | FStar_Syntax_Syntax.RecordType uu____3520 -> None
    | FStar_Syntax_Syntax.RecordConstructor uu____3525 -> None
    | FStar_Syntax_Syntax.Action uu____3530 -> None
>>>>>>> origin/guido_tactics
    | FStar_Syntax_Syntax.ExceptionConstructor  -> None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> None
    | FStar_Syntax_Syntax.Effect  -> Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> None
let resugar_pragma: FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma =
<<<<<<< HEAD
  fun uu___194_3516  ->
    match uu___194_3516 with
=======
  fun uu___206_3534  ->
    match uu___206_3534 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          (tylid,uvs,bs,t,uu____3536,datacons) ->
          let uu____3542 =
=======
          (tylid,uvs,bs,t,uu____3558,datacons) ->
          let uu____3564 =
>>>>>>> origin/guido_tactics
            FStar_All.pipe_right datacon_ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
                        (uu____3560,uu____3561,uu____3562,inductive_lid,uu____3564,uu____3565)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3568 -> failwith "unexpected")) in
          (match uu____3542 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3580 = FStar_Options.print_implicits () in
                 if uu____3580 then bs else filter_imp bs in
=======
                        (uu____3575,uu____3576,uu____3577,inductive_lid,uu____3579,uu____3580)
                        -> FStar_Ident.lid_equals inductive_lid tylid
                    | uu____3583 -> failwith "unexpected")) in
          (match uu____3564 with
           | (current_datacons,other_datacons) ->
               let bs1 =
                 let uu____3594 = FStar_Options.print_implicits () in
                 if uu____3594 then bs else filter_imp bs in
>>>>>>> origin/guido_tactics
               let bs2 =
                 FStar_All.pipe_right bs1
                   (FStar_List.map
                      (fun b  -> resugar_binder b t.FStar_Syntax_Syntax.pos)) in
               let tyc =
<<<<<<< HEAD
                 let uu____3588 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___195_3592  ->
                           match uu___195_3592 with
                           | FStar_Syntax_Syntax.RecordType uu____3593 ->
                               true
                           | uu____3598 -> false)) in
                 if uu____3588
=======
                 let uu____3601 =
                   FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                     (FStar_Util.for_some
                        (fun uu___207_3603  ->
                           match uu___207_3603 with
                           | FStar_Syntax_Syntax.RecordType uu____3604 ->
                               true
                           | uu____3609 -> false)) in
                 if uu____3601
>>>>>>> origin/guido_tactics
                 then
                   let resugar_datacon_as_fields fields se1 =
                     match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
                         (uu____3626,univs1,term,uu____3629,num,uu____3631)
                         ->
                         let uu____3634 =
                           let uu____3635 = FStar_Syntax_Subst.compress term in
                           uu____3635.FStar_Syntax_Syntax.n in
                         (match uu____3634 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3644) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3680  ->
                                        match uu____3680 with
                                        | (b,qual) ->
                                            let uu____3689 =
                                              let uu____3690 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3690 in
                                            let uu____3691 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3689, uu____3691, None))) in
                              FStar_List.append mfields fields
                          | uu____3697 -> failwith "unexpected")
                     | uu____3703 -> failwith "unexpected" in
=======
                         (uu____3637,univs1,term,uu____3640,num,uu____3642)
                         ->
                         let uu____3645 =
                           let uu____3646 = FStar_Syntax_Subst.compress term in
                           uu____3646.FStar_Syntax_Syntax.n in
                         (match uu____3645 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____3655) ->
                              let mfields =
                                FStar_All.pipe_right bs3
                                  (FStar_List.map
                                     (fun uu____3686  ->
                                        match uu____3686 with
                                        | (b,qual) ->
                                            let uu____3695 =
                                              let uu____3696 =
                                                bv_as_unique_ident b in
                                              FStar_Syntax_Util.unmangle_field_name
                                                uu____3696 in
                                            let uu____3697 =
                                              resugar_term
                                                b.FStar_Syntax_Syntax.sort in
                                            (uu____3695, uu____3697, None))) in
                              FStar_List.append mfields fields
                          | uu____3703 -> failwith "unexpected")
                     | uu____3709 -> failwith "unexpected" in
>>>>>>> origin/guido_tactics
                   let fields =
                     FStar_List.fold_left resugar_datacon_as_fields []
                       current_datacons in
                   FStar_Parser_AST.TyconRecord
                     ((tylid.FStar_Ident.ident), bs2, None, fields)
                 else
                   (let resugar_datacon constructors se1 =
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
                          (l,univs1,term,uu____3770,num,uu____3772) ->
                          let c =
                            let uu____3782 =
                              let uu____3784 = resugar_term term in
                              Some uu____3784 in
                            ((l.FStar_Ident.ident), uu____3782, None, false) in
                          c :: constructors
                      | uu____3793 -> failwith "unexpected" in
=======
                          (l,univs1,term,uu____3776,num,uu____3778) ->
                          let c =
                            let uu____3788 =
                              let uu____3790 = resugar_term term in
                              Some uu____3790 in
                            ((l.FStar_Ident.ident), uu____3788, None, false) in
                          c :: constructors
                      | uu____3799 -> failwith "unexpected" in
>>>>>>> origin/guido_tactics
                    let constructors =
                      FStar_List.fold_left resugar_datacon []
                        current_datacons in
                    FStar_Parser_AST.TyconVariant
                      ((tylid.FStar_Ident.ident), bs2, None, constructors)) in
               (other_datacons, tyc))
<<<<<<< HEAD
      | uu____3832 ->
=======
      | uu____3838 ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____3846 = FStar_List.choose resugar_qualifier q in
=======
        let uu____3855 = FStar_List.choose resugar_qualifier q in
>>>>>>> origin/guido_tactics
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = None;
<<<<<<< HEAD
          FStar_Parser_AST.quals = uu____3846;
=======
          FStar_Parser_AST.quals = uu____3855;
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____3859 = ts in
      match uu____3859 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3865 =
            let uu____3866 =
              let uu____3873 =
                let uu____3878 =
                  let uu____3882 =
                    let uu____3883 =
                      let uu____3890 = resugar_term typ in
                      (name1, [], None, uu____3890) in
                    FStar_Parser_AST.TyconAbbrev uu____3883 in
                  (uu____3882, None) in
                [uu____3878] in
              (false, uu____3873) in
            FStar_Parser_AST.Tycon uu____3866 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3865
=======
      let uu____3872 = ts in
      match uu____3872 with
      | (univs1,typ) ->
          let name1 =
            FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
          let uu____3878 =
            let uu____3879 =
              let uu____3886 =
                let uu____3891 =
                  let uu____3895 =
                    let uu____3896 =
                      let uu____3903 = resugar_term typ in
                      (name1, [], None, uu____3903) in
                    FStar_Parser_AST.TyconAbbrev uu____3896 in
                  (uu____3895, None) in
                [uu____3891] in
              (false, uu____3886) in
            FStar_Parser_AST.Tycon uu____3879 in
          mk_decl typ.FStar_Syntax_Syntax.pos [] uu____3878
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            let uu____3929 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____3929 with
            | (bs,action_defn) ->
                let uu____3934 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____3934 with
                 | (bs1,action_typ) ->
                     let action_params1 =
                       let uu____3940 = FStar_Options.print_implicits () in
                       if uu____3940
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____3944 =
                         FStar_All.pipe_right action_params1
                           (FStar_List.map (fun b  -> resugar_binder b r)) in
                       FStar_All.pipe_right uu____3944 FStar_List.rev in
=======
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
>>>>>>> origin/guido_tactics
                     let action_defn1 = resugar_term action_defn in
                     let action_typ1 = resugar_term action_typ in
                     if for_free1
                     then
                       let a =
<<<<<<< HEAD
                         let uu____3954 =
                           let uu____3960 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3960,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3954 in
=======
                         let uu____3971 =
                           let uu____3977 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____3977,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____3971 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          let uu____3999 =
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              ed.FStar_Syntax_Syntax.signature in
          match uu____3999 with
          | (eff_binders,eff_typ) ->
              let eff_binders1 =
                let uu____4005 = FStar_Options.print_implicits () in
                if uu____4005 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____4009 =
                  FStar_All.pipe_right eff_binders1
                    (FStar_List.map (fun b  -> resugar_binder b r)) in
                FStar_All.pipe_right uu____4009 FStar_List.rev in
=======
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
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4051) ->
        let uu____4056 =
=======
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4068) ->
        let uu____4073 =
>>>>>>> origin/guido_tactics
          FStar_All.pipe_right ses
            (FStar_List.partition
               (fun se1  ->
                  match se1.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4069 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4078 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4082 -> false
                  | uu____4090 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4056 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4110 se1 =
               match uu____4110 with
               | (datacon_ses1,tycons) ->
                   let uu____4125 = resugar_typ datacon_ses1 se1 in
                   (match uu____4125 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4134 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4134 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4153 =
                         let uu____4154 =
                           let uu____4155 =
                             let uu____4162 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4162) in
                           FStar_Parser_AST.Tycon uu____4155 in
                         decl'_to_decl se uu____4154 in
                       Some uu____4153
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4180,uu____4181,uu____4182,uu____4183,uu____4184)
                            ->
                            let uu____4187 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4187
                        | uu____4189 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4191 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4195,attrs) ->
        let uu____4201 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___196_4206  ->
                  match uu___196_4206 with
                  | FStar_Syntax_Syntax.Projector (uu____4207,uu____4208) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4209 -> true
                  | uu____4210 -> false)) in
        if uu____4201
=======
                  | FStar_Syntax_Syntax.Sig_inductive_typ uu____4084 -> true
                  | FStar_Syntax_Syntax.Sig_declare_typ uu____4093 -> true
                  | FStar_Syntax_Syntax.Sig_datacon uu____4097 -> false
                  | uu____4105 ->
                      failwith
                        "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
        (match uu____4073 with
         | (decl_typ_ses,datacon_ses) ->
             let retrieve_datacons_and_resugar uu____4125 se1 =
               match uu____4125 with
               | (datacon_ses1,tycons) ->
                   let uu____4140 = resugar_typ datacon_ses1 se1 in
                   (match uu____4140 with
                    | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons))) in
             let uu____4149 =
               FStar_List.fold_left retrieve_datacons_and_resugar
                 (datacon_ses, []) decl_typ_ses in
             (match uu____4149 with
              | (leftover_datacons,tycons) ->
                  (match leftover_datacons with
                   | [] ->
                       let uu____4168 =
                         let uu____4169 =
                           let uu____4170 =
                             let uu____4177 =
                               FStar_List.map (fun tyc  -> (tyc, None))
                                 tycons in
                             (false, uu____4177) in
                           FStar_Parser_AST.Tycon uu____4170 in
                         decl'_to_decl se uu____4169 in
                       Some uu____4168
                   | se1::[] ->
                       (match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,uu____4194,uu____4195,uu____4196,uu____4197,uu____4198)
                            ->
                            let uu____4201 =
                              decl'_to_decl se1
                                (FStar_Parser_AST.Exception
                                   ((l.FStar_Ident.ident), None)) in
                            Some uu____4201
                        | uu____4203 ->
                            failwith "wrong format for resguar to Exception")
                   | uu____4205 -> failwith "Should not happen hopefully")))
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____4209,attrs) ->
        let uu____4215 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___208_4217  ->
                  match uu___208_4217 with
                  | FStar_Syntax_Syntax.Projector (uu____4218,uu____4219) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4220 -> true
                  | uu____4221 -> false)) in
        if uu____4215
>>>>>>> origin/guido_tactics
        then None
        else
          (let mk1 e =
             FStar_Syntax_Syntax.mk e None se.FStar_Syntax_Syntax.sigrng in
           let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown in
           let desugared_let = mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
           let t = resugar_term desugared_let in
           match t.FStar_Parser_AST.tm with
<<<<<<< HEAD
           | FStar_Parser_AST.Let (isrec,lets,uu____4235) ->
               let uu____4242 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4242
           | uu____4246 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____4249,fml) ->
        let uu____4251 =
          let uu____4252 =
            let uu____4253 =
              let uu____4256 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4256) in
            FStar_Parser_AST.Assume uu____4253 in
          decl'_to_decl se uu____4252 in
        Some uu____4251
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4258 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4258
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4260 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4260
=======
           | FStar_Parser_AST.Let (isrec,lets,uu____4246) ->
               let uu____4253 =
                 decl'_to_decl se
                   (FStar_Parser_AST.TopLevelLet (isrec, lets)) in
               Some uu____4253
           | uu____4257 -> failwith "Should not happen hopefully")
    | FStar_Syntax_Syntax.Sig_assume (lid,fml) ->
        let uu____4261 =
          let uu____4262 =
            let uu____4263 =
              let uu____4266 = resugar_term fml in
              ((lid.FStar_Ident.ident), uu____4266) in
            FStar_Parser_AST.Assume uu____4263 in
          decl'_to_decl se uu____4262 in
        Some uu____4261
    | FStar_Syntax_Syntax.Sig_new_effect ed ->
        let uu____4268 =
          resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4268
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        let uu____4270 =
          resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng
            se.FStar_Syntax_Syntax.sigquals ed in
        Some uu____4270
>>>>>>> origin/guido_tactics
    | FStar_Syntax_Syntax.Sig_sub_effect e ->
        let src = e.FStar_Syntax_Syntax.source in
        let dst = e.FStar_Syntax_Syntax.target in
        let lift_wp =
          match e.FStar_Syntax_Syntax.lift_wp with
<<<<<<< HEAD
          | Some (uu____4267,t) ->
              let uu____4274 = resugar_term t in Some uu____4274
          | uu____4275 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4280,t) ->
              let uu____4287 = resugar_term t in Some uu____4287
          | uu____4288 -> None in
=======
          | Some (uu____4277,t) ->
              let uu____4284 = resugar_term t in Some uu____4284
          | uu____4285 -> None in
        let lift =
          match e.FStar_Syntax_Syntax.lift with
          | Some (uu____4290,t) ->
              let uu____4297 = resugar_term t in Some uu____4297
          | uu____4298 -> None in
>>>>>>> origin/guido_tactics
        let op =
          match (lift_wp, lift) with
          | (Some t,None ) -> FStar_Parser_AST.NonReifiableLift t
          | (Some wp,Some t) -> FStar_Parser_AST.ReifiableLift (wp, t)
          | (None ,Some t) -> FStar_Parser_AST.LiftForFree t
<<<<<<< HEAD
          | uu____4303 -> failwith "Should not happen hopefully" in
        let uu____4308 =
=======
          | uu____4313 -> failwith "Should not happen hopefully" in
        let uu____4318 =
>>>>>>> origin/guido_tactics
          decl'_to_decl se
            (FStar_Parser_AST.SubEffect
               {
                 FStar_Parser_AST.msource = src;
                 FStar_Parser_AST.mdest = dst;
                 FStar_Parser_AST.lift_op = op
               }) in
<<<<<<< HEAD
        Some uu____4308
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4316 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4316 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4323 = FStar_Options.print_implicits () in
               if uu____4323 then bs1 else filter_imp bs1 in
=======
        Some uu____4318
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
        let uu____4326 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____4326 with
         | (bs1,c1) ->
             let bs2 =
               let uu____4333 = FStar_Options.print_implicits () in
               if uu____4333 then bs1 else filter_imp bs1 in
>>>>>>> origin/guido_tactics
             let bs3 =
               FStar_All.pipe_right bs2
                 (FStar_List.map
                    (fun b  -> resugar_binder b se.FStar_Syntax_Syntax.sigrng)) in
<<<<<<< HEAD
             let uu____4330 =
               let uu____4331 =
                 let uu____4332 =
                   let uu____4339 =
                     let uu____4344 =
                       let uu____4348 =
                         let uu____4349 =
                           let uu____4356 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4356) in
                         FStar_Parser_AST.TyconAbbrev uu____4349 in
                       (uu____4348, None) in
                     [uu____4344] in
                   (false, uu____4339) in
                 FStar_Parser_AST.Tycon uu____4332 in
               decl'_to_decl se uu____4331 in
             Some uu____4330)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4371 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4371
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4375 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___197_4380  ->
                  match uu___197_4380 with
                  | FStar_Syntax_Syntax.Projector (uu____4381,uu____4382) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4383 -> true
                  | uu____4384 -> false)) in
        if uu____4375
        then None
        else
          (let uu____4387 =
             let uu____4388 =
               let uu____4389 =
                 let uu____4392 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4392) in
               FStar_Parser_AST.Val uu____4389 in
             decl'_to_decl se uu____4388 in
           Some uu____4387)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4393 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4402 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4410 -> None
=======
             let uu____4339 =
               let uu____4340 =
                 let uu____4341 =
                   let uu____4348 =
                     let uu____4353 =
                       let uu____4357 =
                         let uu____4358 =
                           let uu____4365 = resugar_comp c1 in
                           ((lid.FStar_Ident.ident), bs3, None, uu____4365) in
                         FStar_Parser_AST.TyconAbbrev uu____4358 in
                       (uu____4357, None) in
                     [uu____4353] in
                   (false, uu____4348) in
                 FStar_Parser_AST.Tycon uu____4341 in
               decl'_to_decl se uu____4340 in
             Some uu____4339)
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu____4380 =
          decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
        Some uu____4380
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
        let uu____4384 =
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___209_4386  ->
                  match uu___209_4386 with
                  | FStar_Syntax_Syntax.Projector (uu____4387,uu____4388) ->
                      true
                  | FStar_Syntax_Syntax.Discriminator uu____4389 -> true
                  | uu____4390 -> false)) in
        if uu____4384
        then None
        else
          (let uu____4393 =
             let uu____4394 =
               let uu____4395 =
                 let uu____4398 = resugar_term t in
                 ((lid.FStar_Ident.ident), uu____4398) in
               FStar_Parser_AST.Val uu____4395 in
             decl'_to_decl se uu____4394 in
           Some uu____4393)
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4399 -> None
    | FStar_Syntax_Syntax.Sig_datacon uu____4408 -> None
    | FStar_Syntax_Syntax.Sig_main uu____4416 -> None
>>>>>>> origin/guido_tactics
