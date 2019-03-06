open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____52024 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____52024
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____52032 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____52032
  
let map_opt :
  'Auu____52042 'Auu____52043 .
    unit ->
      ('Auu____52042 -> 'Auu____52043 FStar_Pervasives_Native.option) ->
        'Auu____52042 Prims.list -> 'Auu____52043 Prims.list
  = fun uu____52059  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____52068 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____52068
      then
        let uu____52072 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____52072
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____52082 .
    ('Auu____52082 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____52082 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_52137  ->
            match uu___429_52137 with
            | (uu____52145,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52152,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52153)) -> false
            | (uu____52158,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52159)) -> false
            | uu____52165 -> true))
  
let filter_pattern_imp :
  'Auu____52178 .
    ('Auu____52178 * Prims.bool) Prims.list ->
      ('Auu____52178 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____52213  ->
         match uu____52213 with
         | (uu____52220,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe))
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____52270 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____52283 = FStar_Options.print_universes ()  in
    if uu____52283
    then
      let uu____52287 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____52287 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r

and (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____52351 ->
          let uu____52352 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____52352 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____52363 =
                      let uu____52364 =
                        let uu____52365 =
                          let uu____52377 = FStar_Util.string_of_int n1  in
                          (uu____52377, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____52365  in
                      FStar_Parser_AST.Const uu____52364  in
                    mk1 uu____52363 r
                | uu____52390 ->
                    let e1 =
                      let uu____52392 =
                        let uu____52393 =
                          let uu____52394 =
                            let uu____52406 = FStar_Util.string_of_int n1  in
                            (uu____52406, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____52394  in
                        FStar_Parser_AST.Const uu____52393  in
                      mk1 uu____52392 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____52420 =
                      let uu____52421 =
                        let uu____52428 = FStar_Ident.id_of_text "+"  in
                        (uu____52428, [e1; e2])  in
                      FStar_Parser_AST.Op uu____52421  in
                    mk1 uu____52420 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____52436 ->
               let t =
                 let uu____52440 =
                   let uu____52441 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____52441  in
                 mk1 uu____52440 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____52450 =
                        let uu____52451 =
                          let uu____52458 = resugar_universe x r  in
                          (acc, uu____52458, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____52451  in
                      mk1 uu____52450 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____52460 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____52472 =
              let uu____52478 =
                let uu____52480 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____52480  in
              (uu____52478, r)  in
            FStar_Ident.mk_ident uu____52472  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_52518 =
      match uu___430_52518 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some ("+", FStar_Pervasives_Native.None)
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.parse_int "2")))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some ("/", FStar_Pervasives_Native.None)
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some ("<", FStar_Pervasives_Native.None)
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", FStar_Pervasives_Native.None)
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | uu____52846 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".[||]<-", FStar_Pervasives_Native.None)
    | "op_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".(||)<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Access" ->
        FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
    | "op_Lens_Access" ->
        FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
    | uu____52986 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____53004 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____53004 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____53022 ->
               let op =
                 let uu____53028 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____53082) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____53028
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string * expected_arity) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____53409 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____53409 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____53479 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          if FStar_Util.starts_with str "dtuple"
          then
            FStar_Pervasives_Native.Some
              ("dtuple", FStar_Pervasives_Native.None)
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some
                ("tuple", FStar_Pervasives_Native.None)
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", FStar_Pervasives_Native.None)
              else
                (let uu____53581 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____53581
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____53617 =
      let uu____53618 = FStar_Syntax_Subst.compress t  in
      uu____53618.FStar_Syntax_Syntax.n  in
    match uu____53617 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____53639 = string_to_op s  in
        (match uu____53639 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____53679 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____53696 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____53713 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____53724 -> true
    | uu____53726 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____53747 ->
        let uu____53749 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____53749
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____53763 = may_shorten lid  in
      if uu____53763 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____53908 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____53908  in
      let uu____53911 =
        let uu____53912 = FStar_Syntax_Subst.compress t  in
        uu____53912.FStar_Syntax_Syntax.n  in
      match uu____53911 with
      | FStar_Syntax_Syntax.Tm_delayed uu____53915 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____53940 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____53940
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____53943 =
              let uu____53946 = bv_as_unique_ident x  in [uu____53946]  in
            FStar_Ident.lid_of_ids uu____53943  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____53949 =
              let uu____53952 = bv_as_unique_ident x  in [uu____53952]  in
            FStar_Ident.lid_of_ids uu____53949  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = (Prims.parse_int "0")
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____53971 =
              let uu____53972 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____53972  in
            mk1 uu____53971
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix)
                  in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                  in
               match r with
               | fst1::snd1::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk1 (FStar_Parser_AST.Projector (l, r1))
               | uu____53996 -> failwith "wrong projector format")
            else
              (let uu____54003 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____54007 =
                      let uu____54009 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____54009  in
                    let uu____54012 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____54007 <> uu____54012)
                  in
               if uu____54003
               then
                 let uu____54017 =
                   let uu____54018 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____54018  in
                 mk1 uu____54017
               else
                 (let uu____54021 =
                    let uu____54022 =
                      let uu____54033 = maybe_shorten_fv env fv  in
                      (uu____54033, [])  in
                    FStar_Parser_AST.Construct uu____54022  in
                  mk1 uu____54021))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____54051 = FStar_Options.print_universes ()  in
          if uu____54051
          then
            let univs1 =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____54082 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____54082  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____54105 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____54113 = FStar_Syntax_Syntax.is_teff t  in
          if uu____54113
          then
            let uu____54116 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____54116
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____54121 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____54142 -> ("Type", true)  in
          (match uu____54121 with
           | (nm,needs_app) ->
               let typ =
                 let uu____54154 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____54154  in
               let uu____54155 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____54155
               then
                 let uu____54158 =
                   let uu____54159 =
                     let uu____54166 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____54166, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____54159  in
                 mk1 uu____54158
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____54171) ->
          let uu____54196 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____54196 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____54212 = FStar_Options.print_implicits ()  in
                 if uu____54212 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____54250  ->
                         match uu____54250 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____54290 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____54290 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____54300 = FStar_Options.print_implicits ()  in
                 if uu____54300 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____54311 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____54311 FStar_List.rev  in
               let rec aux body3 uu___431_54336 =
                 match uu___431_54336 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____54352 =
            let uu____54357 =
              let uu____54358 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____54358]  in
            FStar_Syntax_Subst.open_term uu____54357 phi  in
          (match uu____54352 with
           | (x1,phi1) ->
               let b =
                 let uu____54380 =
                   let uu____54383 = FStar_List.hd x1  in
                   resugar_binder' env uu____54383 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____54380  in
               let uu____54390 =
                 let uu____54391 =
                   let uu____54396 = resugar_term' env phi1  in
                   (b, uu____54396)  in
                 FStar_Parser_AST.Refine uu____54391  in
               mk1 uu____54390)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____54398;
             FStar_Syntax_Syntax.vars = uu____54399;_},(e,uu____54401)::[])
          when
          (let uu____54442 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____54442) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_54491 =
            match uu___432_54491 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____54561 -> failwith "last of an empty list"  in
          let rec last_two uu___433_54600 =
            match uu___433_54600 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____54632::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____54710::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____54781  ->
                   match uu____54781 with
                   | (e2,qual) ->
                       let uu____54798 = resugar_term' env e2  in
                       let uu____54799 = resugar_imp env qual  in
                       (uu____54798, uu____54799)) args1
               in
            let uu____54800 = resugar_term' env e1  in
            match uu____54800 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____54837  ->
                       match uu____54837 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____54853 = FStar_Options.print_implicits ()  in
            if uu____54853 then args else filter_imp args  in
          let uu____54868 = resugar_term_as_op e  in
          (match uu____54868 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____54881) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____54906  ->
                        match uu____54906 with
                        | (x,uu____54918) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____54927 =
                                   let uu____54928 =
                                     let uu____54929 =
                                       let uu____54936 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____54936, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____54929  in
                                   mk1 uu____54928  in
                                 FStar_Pervasives_Native.Some uu____54927))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____54940) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____54966)::[] -> b
                 | uu____54983 -> failwith "wrong arguments to dtuple"  in
               let uu____54993 =
                 let uu____54994 = FStar_Syntax_Subst.compress body  in
                 uu____54994.FStar_Syntax_Syntax.n  in
               (match uu____54993 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54999) ->
                    let uu____55024 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____55024 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____55034 = FStar_Options.print_implicits ()
                              in
                           if uu____55034 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____55051 =
                           let uu____55052 =
                             let uu____55063 =
                               FStar_List.map
                                 (fun _55074  -> FStar_Util.Inl _55074) xs3
                                in
                             (uu____55063, body3)  in
                           FStar_Parser_AST.Sum uu____55052  in
                         mk1 uu____55051)
                | uu____55081 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____55104  ->
                              match uu____55104 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____55122) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____55131) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____55140 = FStar_List.hd args1  in
               (match uu____55140 with
                | (t1,uu____55154) ->
                    let uu____55159 =
                      let uu____55160 = FStar_Syntax_Subst.compress t1  in
                      uu____55160.FStar_Syntax_Syntax.n  in
                    (match uu____55159 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____55167 =
                           let uu____55168 =
                             let uu____55173 = resugar_term' env t1  in
                             (uu____55173, f)  in
                           FStar_Parser_AST.Project uu____55168  in
                         mk1 uu____55167
                     | uu____55174 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____55175) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____55199 =
                 match new_args with
                 | (a1,uu____55209)::(a2,uu____55211)::[] -> (a1, a2)
                 | uu____55238 -> failwith "wrong arguments to try_with"  in
               (match uu____55199 with
                | (body,handler) ->
                    let decomp term =
                      let uu____55260 =
                        let uu____55261 = FStar_Syntax_Subst.compress term
                           in
                        uu____55261.FStar_Syntax_Syntax.n  in
                      match uu____55260 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____55266) ->
                          let uu____55291 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____55291 with | (x1,e2) -> e2)
                      | uu____55298 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____55301 = decomp body  in
                      resugar_term' env uu____55301  in
                    let handler1 =
                      let uu____55303 = decomp handler  in
                      resugar_term' env uu____55303  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____55311,uu____55312,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____55344,uu____55345,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____55382 =
                            let uu____55383 =
                              let uu____55392 = resugar_body t11  in
                              (uu____55392, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____55383  in
                          mk1 uu____55382
                      | uu____55395 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____55453 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____55483) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____55492) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____55513) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____55611 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____55624 =
                   let uu____55625 = FStar_Syntax_Subst.compress body  in
                   uu____55625.FStar_Syntax_Syntax.n  in
                 match uu____55624 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____55630) ->
                     let uu____55655 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____55655 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____55665 =
                              FStar_Options.print_implicits ()  in
                            if uu____55665 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____55681 =
                            let uu____55690 =
                              let uu____55691 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____55691.FStar_Syntax_Syntax.n  in
                            match uu____55690 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____55709 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____55739 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____55783  ->
                                                     match uu____55783 with
                                                     | (e2,uu____55791) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____55739, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____55807 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____55807)
                                  | uu____55816 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____55709 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____55848 ->
                                let uu____55849 = resugar_term' env body2  in
                                ([], uu____55849)
                             in
                          (match uu____55681 with
                           | (pats,body3) ->
                               let uu____55866 = uncurry xs3 pats body3  in
                               (match uu____55866 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      mk1
                                        (FStar_Parser_AST.QForall
                                           (xs5, pats1, body4))
                                    else
                                      mk1
                                        (FStar_Parser_AST.QExists
                                           (xs5, pats1, body4)))))
                 | uu____55918 ->
                     if op = "forall"
                     then
                       let uu____55922 =
                         let uu____55923 =
                           let uu____55936 = resugar_term' env body  in
                           ([], [[]], uu____55936)  in
                         FStar_Parser_AST.QForall uu____55923  in
                       mk1 uu____55922
                     else
                       (let uu____55949 =
                          let uu____55950 =
                            let uu____55963 = resugar_term' env body  in
                            ([], [[]], uu____55963)  in
                          FStar_Parser_AST.QExists uu____55950  in
                        mk1 uu____55949)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____55992)::[] -> resugar b
                  | uu____56009 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____56021) ->
               let uu____56029 = FStar_List.hd args1  in
               (match uu____56029 with
                | (e1,uu____56043) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____56115  ->
                         match uu____56115 with
                         | (e1,qual) ->
                             let uu____56132 = resugar_term' env e1  in
                             let uu____56133 = resugar_imp env qual  in
                             (uu____56132, uu____56133)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____56149 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____56149 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____56197 =
                               let uu____56198 =
                                 let uu____56205 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____56205)  in
                               FStar_Parser_AST.Op uu____56198  in
                             mk1 uu____56197  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____56223  ->
                                  match uu____56223 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____56242 =
                      let uu____56243 =
                        let uu____56250 =
                          let uu____56253 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____56253
                           in
                        (op1, uu____56250)  in
                      FStar_Parser_AST.Op uu____56243  in
                    mk1 uu____56242
                | uu____56266 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____56335 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____56335 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____56381 =
                   let uu____56394 =
                     let uu____56399 = resugar_pat' env pat1 branch_bv  in
                     let uu____56400 = resugar_term' env e  in
                     (uu____56399, uu____56400)  in
                   (FStar_Pervasives_Native.None, uu____56394)  in
                 [uu____56381]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____56452,t1)::(pat2,uu____56455,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____56551 =
            let uu____56552 =
              let uu____56559 = resugar_term' env e  in
              let uu____56560 = resugar_term' env t1  in
              let uu____56561 = resugar_term' env t2  in
              (uu____56559, uu____56560, uu____56561)  in
            FStar_Parser_AST.If uu____56552  in
          mk1 uu____56551
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____56627 =
            match uu____56627 with
            | (pat,wopt,b) ->
                let uu____56669 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____56669 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____56721 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____56721
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____56725 =
            let uu____56726 =
              let uu____56741 = resugar_term' env e  in
              let uu____56742 = FStar_List.map resugar_branch branches  in
              (uu____56741, uu____56742)  in
            FStar_Parser_AST.Match uu____56726  in
          mk1 uu____56725
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____56788) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____56857 =
            let uu____56858 =
              let uu____56867 = resugar_term' env e  in
              (uu____56867, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____56858  in
          mk1 uu____56857
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____56896 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____56896 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____56950 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____56950
                    in
                 let uu____56957 =
                   let uu____56962 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____56962
                    in
                 match uu____56957 with
                 | (univs1,td) ->
                     let uu____56982 =
                       let uu____56989 =
                         let uu____56990 = FStar_Syntax_Subst.compress td  in
                         uu____56990.FStar_Syntax_Syntax.n  in
                       match uu____56989 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____56999,(t1,uu____57001)::(d,uu____57003)::[])
                           -> (t1, d)
                       | uu____57060 -> failwith "wrong let binding format"
                        in
                     (match uu____56982 with
                      | (typ,def) ->
                          let uu____57091 =
                            let uu____57107 =
                              let uu____57108 =
                                FStar_Syntax_Subst.compress def  in
                              uu____57108.FStar_Syntax_Syntax.n  in
                            match uu____57107 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____57128)
                                ->
                                let uu____57153 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____57153 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____57184 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____57184
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____57207 -> ([], def, false)  in
                          (match uu____57091 with
                           | (binders,term,is_pat_app) ->
                               let uu____57262 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____57273 =
                                       let uu____57274 =
                                         let uu____57275 =
                                           let uu____57282 =
                                             bv_as_unique_ident bv  in
                                           (uu____57282,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____57275
                                          in
                                       mk_pat uu____57274  in
                                     (uu____57273, term)
                                  in
                               (match uu____57262 with
                                | (pat,term1) ->
                                    let uu____57304 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____57347  ->
                                                  match uu____57347 with
                                                  | (bv,q) ->
                                                      let uu____57362 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____57362
                                                        (fun q1  ->
                                                           let uu____57374 =
                                                             let uu____57375
                                                               =
                                                               let uu____57382
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____57382,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____57375
                                                              in
                                                           mk_pat uu____57374)))
                                           in
                                        let uu____57385 =
                                          let uu____57390 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____57390)
                                           in
                                        let uu____57393 =
                                          universe_to_string univs1  in
                                        (uu____57385, uu____57393)
                                      else
                                        (let uu____57402 =
                                           let uu____57407 =
                                             resugar_term' env term1  in
                                           (pat, uu____57407)  in
                                         let uu____57408 =
                                           universe_to_string univs1  in
                                         (uu____57402, uu____57408))
                                       in
                                    (attrs_opt, uu____57304))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____57514 =
                   match uu____57514 with
                   | (attrs,(pb,univs1)) ->
                       let uu____57574 =
                         let uu____57576 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____57576  in
                       if uu____57574
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____57657) ->
          let s =
            let uu____57676 =
              let uu____57678 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____57678 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____57676  in
          let uu____57683 = mk1 FStar_Parser_AST.Wild  in label s uu____57683
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____57691 =
            let uu____57692 =
              let uu____57697 = resugar_term' env tm  in (uu____57697, qi1)
               in
            FStar_Parser_AST.Quote uu____57692  in
          mk1 uu____57691
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_57709 =
            match uu___434_57709 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____57717,(uu____57718,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____57779 =
                        let uu____57780 =
                          let uu____57789 = resugar_seq t11  in
                          (uu____57789, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____57780  in
                      mk1 uu____57779
                  | uu____57792 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____57836  ->
                         match uu____57836 with
                         | (x,uu____57844) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____57849 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____57867,t1) ->
               resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____57907 = FStar_Options.print_universes ()  in
               if uu____57907
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____57971 = FStar_Options.print_universes ()  in
               if uu____57971
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____58015 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____58015, FStar_Parser_AST.Nothing)  in
          let uu____58016 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____58016
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____58039 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____58039
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____58124 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____58124, (FStar_Pervasives_Native.snd post))  in
                    let uu____58135 =
                      let uu____58144 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____58144 then [] else [pre]  in
                    let uu____58179 =
                      let uu____58188 =
                        let uu____58197 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____58197 then [] else [pats]  in
                      FStar_List.append [post1] uu____58188  in
                    FStar_List.append uu____58135 uu____58179
                | uu____58256 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____58290  ->
                   match uu____58290 with
                   | (e,uu____58302) ->
                       let uu____58307 = resugar_term' env e  in
                       (uu____58307, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_58332 =
              match uu___435_58332 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____58365 = resugar_term' env e  in
                         (uu____58365, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____58370 -> aux l tl1)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))

and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____58417 = b  in
        match uu____58417 with
        | (x,aq) ->
            let uu____58426 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____58426
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____58440 =
                       let uu____58441 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____58441  in
                     FStar_Parser_AST.mk_binder uu____58440 r
                       FStar_Parser_AST.Type_level imp
                 | uu____58442 ->
                     let uu____58443 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____58443
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____58448 =
                          let uu____58449 =
                            let uu____58454 = bv_as_unique_ident x  in
                            (uu____58454, e)  in
                          FStar_Parser_AST.Annotated uu____58449  in
                        FStar_Parser_AST.mk_binder uu____58448 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun v1  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk1 a =
              let uu____58474 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____58474  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____58478 =
                if used
                then
                  let uu____58480 =
                    let uu____58487 = bv_as_unique_ident v1  in
                    (uu____58487, aqual)  in
                  FStar_Parser_AST.PatVar uu____58480
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____58478  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____58494;
                  FStar_Syntax_Syntax.vars = uu____58495;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____58505 = FStar_Options.print_bound_var_types ()  in
                if uu____58505
                then
                  let uu____58508 =
                    let uu____58509 =
                      let uu____58520 =
                        let uu____58527 = resugar_term' env typ  in
                        (uu____58527, FStar_Pervasives_Native.None)  in
                      (pat, uu____58520)  in
                    FStar_Parser_AST.PatAscribed uu____58509  in
                  mk1 uu____58508
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____58548 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____58548
            (fun aqual  ->
               let uu____58560 =
                 let uu____58565 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _58576  -> FStar_Pervasives_Native.Some _58576)
                   uu____58565
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____58560)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____58638 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____58638) &&
            (let uu____58641 =
               FStar_List.existsML
                 (fun uu____58654  ->
                    match uu____58654 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____58676)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____58681 -> false
                          | uu____58683 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____58641)
           in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____58751 = may_drop_implicits args  in
            if uu____58751 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____58776  ->
                 match uu____58776 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____58831 =
                  let uu____58833 =
                    let uu____58835 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____58835  in
                  Prims.op_Negation uu____58833  in
                if uu____58831
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____58879 = filter_pattern_imp args  in
              (match uu____58879 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____58929 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____58929 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____58948 =
                       let uu____58954 =
                         let uu____58956 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____58956
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____58954)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____58948);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____59009  ->
                        match uu____59009 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____59026 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____59026)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____59034;
                 FStar_Syntax_Syntax.fv_delta = uu____59035;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____59064 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____59064 FStar_List.rev  in
              let args1 =
                let uu____59080 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____59100  ->
                          match uu____59100 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____59080 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____59178 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____59178
                | (hd1::tl1,hd2::tl2) ->
                    let uu____59201 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____59201
                 in
              let args2 =
                let uu____59219 = map21 fields1 args1  in
                FStar_All.pipe_right uu____59219 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____59263 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____59263 with
               | FStar_Pervasives_Native.Some (op,uu____59275) ->
                   let uu____59292 =
                     let uu____59293 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____59293  in
                   mk1 uu____59292
               | FStar_Pervasives_Native.None  ->
                   let uu____59303 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____59303 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____59308 ->
              let uu____59309 =
                let uu____59310 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____59310  in
              mk1 uu____59309
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

and (resugar_arg_qual :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
          if b
          then FStar_Pervasives_Native.None
          else
            FStar_Pervasives_Native.Some
              (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____59350 =
            let uu____59353 =
              let uu____59354 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____59354  in
            FStar_Pervasives_Native.Some uu____59353  in
          FStar_Pervasives_Native.Some uu____59350

and (resugar_imp :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.imp)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> FStar_Parser_AST.Hash
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____59366 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____59366

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_59374  ->
    match uu___436_59374 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____59381 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____59382 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____59383 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____59388 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____59397 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____59406 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_59412  ->
    match uu___437_59412 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon))
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____59455,datacons) ->
            let uu____59465 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____59493,uu____59494,uu____59495,inductive_lid,uu____59497,uu____59498)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____59505 -> failwith "unexpected"))
               in
            (match uu____59465 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____59526 = FStar_Options.print_implicits ()  in
                   if uu____59526 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____59543 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_59550  ->
                             match uu___438_59550 with
                             | FStar_Syntax_Syntax.RecordType uu____59552 ->
                                 true
                             | uu____59562 -> false))
                      in
                   if uu____59543
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____59616,univs1,term,uu____59619,num,uu____59621)
                           ->
                           let uu____59628 =
                             let uu____59629 =
                               FStar_Syntax_Subst.compress term  in
                             uu____59629.FStar_Syntax_Syntax.n  in
                           (match uu____59628 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____59643)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____59712  ->
                                          match uu____59712 with
                                          | (b,qual) ->
                                              let uu____59733 =
                                                bv_as_unique_ident b  in
                                              let uu____59734 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____59733, uu____59734,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____59745 -> failwith "unexpected")
                       | uu____59757 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     FStar_Parser_AST.TyconRecord
                       ((tylid.FStar_Ident.ident), bs2,
                         FStar_Pervasives_Native.None, fields)
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs1,term,uu____59888,num,uu____59890) ->
                            let c =
                              let uu____59911 =
                                let uu____59914 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____59914  in
                              ((l.FStar_Ident.ident), uu____59911,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____59934 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____60014 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
  
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____60040 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____60040;
          FStar_Parser_AST.attrs = []
        }
  
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____60070 = ts  in
        match uu____60070 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____60083 =
              let uu____60084 =
                let uu____60101 =
                  let uu____60110 =
                    let uu____60117 =
                      let uu____60118 =
                        let uu____60131 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____60131)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____60118  in
                    (uu____60117, FStar_Pervasives_Native.None)  in
                  [uu____60110]  in
                (false, false, uu____60101)  in
              FStar_Parser_AST.Tycon uu____60084  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____60083
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tscheme" ts 
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun for_free  ->
      fun r  ->
        fun q  ->
          fun ed  ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params
                 in
              let uu____60220 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____60220 with
              | (bs,action_defn) ->
                  let uu____60227 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____60227 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____60237 = FStar_Options.print_implicits ()
                            in
                         if uu____60237
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____60247 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____60247 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____60264 =
                             let uu____60275 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____60275,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____60264  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None, t)),
                                   FStar_Pervasives_Native.None)]))
                       else
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None,
                                       action_defn1)),
                                   FStar_Pervasives_Native.None)])))
               in
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____60359 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____60359 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____60369 = FStar_Options.print_implicits ()  in
                  if uu____60369 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____60379 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____60379 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.bind_wp
                   in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else
                   in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp
                   in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger
                   in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp
                   in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p
                   in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p
                   in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr))
                   in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr
                   in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr
                   in
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
                    trivial]
                   in
                let actions =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                    (FStar_List.map (fun a  -> resugar_action a false))
                   in
                let decls = FStar_List.append mandatory_members_decls actions
                   in
                mk_decl r q
                  (FStar_Parser_AST.NewEffect
                     (FStar_Parser_AST.DefineEffect
                        (eff_name, eff_binders2, eff_typ1, decls)))
  
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60464) ->
          let uu____60473 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60496 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____60514 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____60522 -> false
                    | uu____60539 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____60473 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____60577 se1 =
                 match uu____60577 with
                 | (datacon_ses1,tycons) ->
                     let uu____60603 = resugar_typ env datacon_ses1 se1  in
                     (match uu____60603 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____60618 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____60618 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____60653 =
                           let uu____60654 =
                             let uu____60655 =
                               let uu____60672 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____60672)  in
                             FStar_Parser_AST.Tycon uu____60655  in
                           decl'_to_decl se uu____60654  in
                         FStar_Pervasives_Native.Some uu____60653
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____60707,uu____60708,uu____60709,uu____60710,uu____60711)
                              ->
                              let uu____60718 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____60718
                          | uu____60721 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____60725 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60732) ->
          let uu____60737 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_60745  ->
                    match uu___439_60745 with
                    | FStar_Syntax_Syntax.Projector (uu____60747,uu____60748)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60750 -> true
                    | uu____60752 -> false))
             in
          if uu____60737
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))  in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____60787) ->
                 let uu____60816 =
                   let uu____60817 =
                     let uu____60818 =
                       let uu____60829 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____60829)  in
                     FStar_Parser_AST.TopLevelLet uu____60818  in
                   decl'_to_decl se uu____60817  in
                 FStar_Pervasives_Native.Some uu____60816
             | uu____60866 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____60871,fml) ->
          let uu____60873 =
            let uu____60874 =
              let uu____60875 =
                let uu____60880 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____60880)  in
              FStar_Parser_AST.Assume uu____60875  in
            decl'_to_decl se uu____60874  in
          FStar_Pervasives_Native.Some uu____60873
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60882 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60882
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____60885 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60885
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____60895,t) ->
                let uu____60905 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60905
            | uu____60906 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____60914,t) ->
                let uu____60924 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60924
            | uu____60925 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____60949 -> failwith "Should not happen hopefully"  in
          let uu____60959 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____60959
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____60969 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____60969 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____60981 = FStar_Options.print_implicits ()  in
                 if uu____60981 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____60997 =
                 let uu____60998 =
                   let uu____60999 =
                     let uu____61016 =
                       let uu____61025 =
                         let uu____61032 =
                           let uu____61033 =
                             let uu____61046 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____61046)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____61033  in
                         (uu____61032, FStar_Pervasives_Native.None)  in
                       [uu____61025]  in
                     (false, false, uu____61016)  in
                   FStar_Parser_AST.Tycon uu____60999  in
                 decl'_to_decl se uu____60998  in
               FStar_Pervasives_Native.Some uu____60997)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____61078 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____61078
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____61082 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_61090  ->
                    match uu___440_61090 with
                    | FStar_Syntax_Syntax.Projector (uu____61092,uu____61093)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____61095 -> true
                    | uu____61097 -> false))
             in
          if uu____61082
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____61105 =
                 (let uu____61109 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____61109) || (FStar_List.isEmpty uvs)
                  in
               if uu____61105
               then resugar_term' env t
               else
                 (let uu____61114 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____61114 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____61123 = resugar_term' env t1  in
                      label universes uu____61123)
                in
             let uu____61124 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____61124)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____61131 =
            let uu____61132 =
              let uu____61133 =
                let uu____61140 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____61145 = resugar_term' env t  in
                (uu____61140, uu____61145)  in
              FStar_Parser_AST.Splice uu____61133  in
            decl'_to_decl se uu____61132  in
          FStar_Pervasives_Native.Some uu____61131
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____61148 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____61165 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____61181 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____61205 = noenv resugar_term'  in uu____61205 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____61223 = noenv resugar_sigelt'  in uu____61223 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____61241 = noenv resugar_comp'  in uu____61241 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____61264 = noenv resugar_pat'  in uu____61264 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____61298 = noenv resugar_binder'  in uu____61298 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____61323 = noenv resugar_tscheme'  in uu____61323 ts 
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____61358 = noenv resugar_eff_decl'  in
          uu____61358 for_free r q ed
  