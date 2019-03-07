open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____51293 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____51293
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____51301 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____51301
  
let map_opt :
  'Auu____51311 'Auu____51312 .
    unit ->
      ('Auu____51311 -> 'Auu____51312 FStar_Pervasives_Native.option) ->
        'Auu____51311 Prims.list -> 'Auu____51312 Prims.list
  = fun uu____51328  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____51337 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____51337
      then
        let uu____51341 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____51341
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____51351 .
    ('Auu____51351 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51351 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_51406  ->
            match uu___429_51406 with
            | (uu____51414,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____51421,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____51422)) -> false
            | (uu____51427,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____51428)) -> false
            | uu____51434 -> true))
  
let filter_pattern_imp :
  'Auu____51447 .
    ('Auu____51447 * Prims.bool) Prims.list ->
      ('Auu____51447 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____51482  ->
         match uu____51482 with
         | (uu____51489,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____51539 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____51552 = FStar_Options.print_universes ()  in
    if uu____51552
    then
      let uu____51556 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____51556 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____51620 ->
          let uu____51621 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____51621 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____51632 =
                      let uu____51633 =
                        let uu____51634 =
                          let uu____51646 = FStar_Util.string_of_int n1  in
                          (uu____51646, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____51634  in
                      FStar_Parser_AST.Const uu____51633  in
                    mk1 uu____51632 r
                | uu____51659 ->
                    let e1 =
                      let uu____51661 =
                        let uu____51662 =
                          let uu____51663 =
                            let uu____51675 = FStar_Util.string_of_int n1  in
                            (uu____51675, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____51663  in
                        FStar_Parser_AST.Const uu____51662  in
                      mk1 uu____51661 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____51689 =
                      let uu____51690 =
                        let uu____51697 = FStar_Ident.id_of_text "+"  in
                        (uu____51697, [e1; e2])  in
                      FStar_Parser_AST.Op uu____51690  in
                    mk1 uu____51689 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____51705 ->
               let t =
                 let uu____51709 =
                   let uu____51710 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____51710  in
                 mk1 uu____51709 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____51719 =
                        let uu____51720 =
                          let uu____51727 = resugar_universe x r  in
                          (acc, uu____51727, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____51720  in
                      mk1 uu____51719 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____51729 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____51741 =
              let uu____51747 =
                let uu____51749 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____51749  in
              (uu____51747, r)  in
            FStar_Ident.mk_ident uu____51741  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_51787 =
      match uu___430_51787 with
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
      | uu____52115 -> FStar_Pervasives_Native.None  in
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
    | uu____52255 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____52273 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____52273 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____52291 ->
               let op =
                 let uu____52297 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____52351) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____52297
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
      let uu____52678 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____52678 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____52748 ->
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
                (let uu____52850 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____52850
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____52886 =
      let uu____52887 = FStar_Syntax_Subst.compress t  in
      uu____52887.FStar_Syntax_Syntax.n  in
    match uu____52886 with
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
        let uu____52908 = string_to_op s  in
        (match uu____52908 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____52948 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____52965 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____52982 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____52993 -> true
    | uu____52995 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____53016 ->
        let uu____53018 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____53018
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____53032 = may_shorten lid  in
      if uu____53032 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____53177 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____53177  in
      let uu____53180 =
        let uu____53181 = FStar_Syntax_Subst.compress t  in
        uu____53181.FStar_Syntax_Syntax.n  in
      match uu____53180 with
      | FStar_Syntax_Syntax.Tm_delayed uu____53184 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____53209 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____53209
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____53212 =
              let uu____53215 = bv_as_unique_ident x  in [uu____53215]  in
            FStar_Ident.lid_of_ids uu____53212  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____53218 =
              let uu____53221 = bv_as_unique_ident x  in [uu____53221]  in
            FStar_Ident.lid_of_ids uu____53218  in
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
            let uu____53240 =
              let uu____53241 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____53241  in
            mk1 uu____53240
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
               | uu____53265 -> failwith "wrong projector format")
            else
              (let uu____53272 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____53276 =
                      let uu____53278 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____53278  in
                    let uu____53281 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____53276 <> uu____53281)
                  in
               if uu____53272
               then
                 let uu____53286 =
                   let uu____53287 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____53287  in
                 mk1 uu____53286
               else
                 (let uu____53290 =
                    let uu____53291 =
                      let uu____53302 = maybe_shorten_fv env fv  in
                      (uu____53302, [])  in
                    FStar_Parser_AST.Construct uu____53291  in
                  mk1 uu____53290))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____53320 = FStar_Options.print_universes ()  in
          if uu____53320
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
                   let uu____53351 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____53351  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____53374 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____53382 = FStar_Syntax_Syntax.is_teff t  in
          if uu____53382
          then
            let uu____53385 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____53385
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____53390 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____53411 -> ("Type", true)  in
          (match uu____53390 with
           | (nm,needs_app) ->
               let typ =
                 let uu____53423 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____53423  in
               let uu____53424 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____53424
               then
                 let uu____53427 =
                   let uu____53428 =
                     let uu____53435 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____53435, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____53428  in
                 mk1 uu____53427
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____53440) ->
          let uu____53465 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____53465 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53481 = FStar_Options.print_implicits ()  in
                 if uu____53481 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____53519  ->
                         match uu____53519 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____53559 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____53559 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53569 = FStar_Options.print_implicits ()  in
                 if uu____53569 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____53580 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____53580 FStar_List.rev  in
               let rec aux body3 uu___431_53605 =
                 match uu___431_53605 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____53621 =
            let uu____53626 =
              let uu____53627 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____53627]  in
            FStar_Syntax_Subst.open_term uu____53626 phi  in
          (match uu____53621 with
           | (x1,phi1) ->
               let b =
                 let uu____53649 =
                   let uu____53652 = FStar_List.hd x1  in
                   resugar_binder' env uu____53652 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____53649  in
               let uu____53659 =
                 let uu____53660 =
                   let uu____53665 = resugar_term' env phi1  in
                   (b, uu____53665)  in
                 FStar_Parser_AST.Refine uu____53660  in
               mk1 uu____53659)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____53667;
             FStar_Syntax_Syntax.vars = uu____53668;_},(e,uu____53670)::[])
          when
          (let uu____53711 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____53711) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_53760 =
            match uu___432_53760 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____53830 -> failwith "last of an empty list"  in
          let rec last_two uu___433_53869 =
            match uu___433_53869 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____53901::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____53979::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____54050  ->
                   match uu____54050 with
                   | (e2,qual) ->
                       let uu____54067 = resugar_term' env e2  in
                       let uu____54068 = resugar_imp env qual  in
                       (uu____54067, uu____54068)) args1
               in
            let uu____54069 = resugar_term' env e1  in
            match uu____54069 with
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
                     fun uu____54106  ->
                       match uu____54106 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____54122 = FStar_Options.print_implicits ()  in
            if uu____54122 then args else filter_imp args  in
          let uu____54137 = resugar_term_as_op e  in
          (match uu____54137 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____54150) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____54175  ->
                        match uu____54175 with
                        | (x,uu____54187) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____54196 =
                                   let uu____54197 =
                                     let uu____54198 =
                                       let uu____54205 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____54205, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____54198  in
                                   mk1 uu____54197  in
                                 FStar_Pervasives_Native.Some uu____54196))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____54209) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____54235)::[] -> b
                 | uu____54252 -> failwith "wrong arguments to dtuple"  in
               let uu____54262 =
                 let uu____54263 = FStar_Syntax_Subst.compress body  in
                 uu____54263.FStar_Syntax_Syntax.n  in
               (match uu____54262 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54268) ->
                    let uu____54293 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____54293 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____54303 = FStar_Options.print_implicits ()
                              in
                           if uu____54303 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____54320 =
                           let uu____54321 =
                             let uu____54332 =
                               FStar_List.map
                                 (fun _54343  -> FStar_Util.Inl _54343) xs3
                                in
                             (uu____54332, body3)  in
                           FStar_Parser_AST.Sum uu____54321  in
                         mk1 uu____54320)
                | uu____54350 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____54373  ->
                              match uu____54373 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____54391) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____54400) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____54409 = FStar_List.hd args1  in
               (match uu____54409 with
                | (t1,uu____54423) ->
                    let uu____54428 =
                      let uu____54429 = FStar_Syntax_Subst.compress t1  in
                      uu____54429.FStar_Syntax_Syntax.n  in
                    (match uu____54428 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____54436 =
                           let uu____54437 =
                             let uu____54442 = resugar_term' env t1  in
                             (uu____54442, f)  in
                           FStar_Parser_AST.Project uu____54437  in
                         mk1 uu____54436
                     | uu____54443 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____54444) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____54468 =
                 match new_args with
                 | (a1,uu____54478)::(a2,uu____54480)::[] -> (a1, a2)
                 | uu____54507 -> failwith "wrong arguments to try_with"  in
               (match uu____54468 with
                | (body,handler) ->
                    let decomp term =
                      let uu____54529 =
                        let uu____54530 = FStar_Syntax_Subst.compress term
                           in
                        uu____54530.FStar_Syntax_Syntax.n  in
                      match uu____54529 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____54535) ->
                          let uu____54560 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____54560 with | (x1,e2) -> e2)
                      | uu____54567 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____54570 = decomp body  in
                      resugar_term' env uu____54570  in
                    let handler1 =
                      let uu____54572 = decomp handler  in
                      resugar_term' env uu____54572  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____54580,uu____54581,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____54613,uu____54614,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____54651 =
                            let uu____54652 =
                              let uu____54661 = resugar_body t11  in
                              (uu____54661, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____54652  in
                          mk1 uu____54651
                      | uu____54664 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____54722 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____54752) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54761) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54782) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____54880 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____54893 =
                   let uu____54894 = FStar_Syntax_Subst.compress body  in
                   uu____54894.FStar_Syntax_Syntax.n  in
                 match uu____54893 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54899) ->
                     let uu____54924 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____54924 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____54934 =
                              FStar_Options.print_implicits ()  in
                            if uu____54934 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____54950 =
                            let uu____54959 =
                              let uu____54960 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____54960.FStar_Syntax_Syntax.n  in
                            match uu____54959 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____54978 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____55008 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____55052  ->
                                                     match uu____55052 with
                                                     | (e2,uu____55060) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____55008, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____55076 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____55076)
                                  | uu____55085 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____54978 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____55117 ->
                                let uu____55118 = resugar_term' env body2  in
                                ([], uu____55118)
                             in
                          (match uu____54950 with
                           | (pats,body3) ->
                               let uu____55135 = uncurry xs3 pats body3  in
                               (match uu____55135 with
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
                 | uu____55187 ->
                     if op = "forall"
                     then
                       let uu____55191 =
                         let uu____55192 =
                           let uu____55205 = resugar_term' env body  in
                           ([], [[]], uu____55205)  in
                         FStar_Parser_AST.QForall uu____55192  in
                       mk1 uu____55191
                     else
                       (let uu____55218 =
                          let uu____55219 =
                            let uu____55232 = resugar_term' env body  in
                            ([], [[]], uu____55232)  in
                          FStar_Parser_AST.QExists uu____55219  in
                        mk1 uu____55218)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____55261)::[] -> resugar b
                  | uu____55278 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____55290) ->
               let uu____55298 = FStar_List.hd args1  in
               (match uu____55298 with
                | (e1,uu____55312) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____55384  ->
                         match uu____55384 with
                         | (e1,qual) ->
                             let uu____55401 = resugar_term' env e1  in
                             let uu____55402 = resugar_imp env qual  in
                             (uu____55401, uu____55402)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____55418 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____55418 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____55466 =
                               let uu____55467 =
                                 let uu____55474 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____55474)  in
                               FStar_Parser_AST.Op uu____55467  in
                             mk1 uu____55466  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____55492  ->
                                  match uu____55492 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____55511 =
                      let uu____55512 =
                        let uu____55519 =
                          let uu____55522 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____55522
                           in
                        (op1, uu____55519)  in
                      FStar_Parser_AST.Op uu____55512  in
                    mk1 uu____55511
                | uu____55535 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____55604 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____55604 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____55650 =
                   let uu____55663 =
                     let uu____55668 = resugar_pat' env pat1 branch_bv  in
                     let uu____55669 = resugar_term' env e  in
                     (uu____55668, uu____55669)  in
                   (FStar_Pervasives_Native.None, uu____55663)  in
                 [uu____55650]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____55721,t1)::(pat2,uu____55724,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____55820 =
            let uu____55821 =
              let uu____55828 = resugar_term' env e  in
              let uu____55829 = resugar_term' env t1  in
              let uu____55830 = resugar_term' env t2  in
              (uu____55828, uu____55829, uu____55830)  in
            FStar_Parser_AST.If uu____55821  in
          mk1 uu____55820
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____55896 =
            match uu____55896 with
            | (pat,wopt,b) ->
                let uu____55938 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____55938 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____55990 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____55990
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____55994 =
            let uu____55995 =
              let uu____56010 = resugar_term' env e  in
              let uu____56011 = FStar_List.map resugar_branch branches  in
              (uu____56010, uu____56011)  in
            FStar_Parser_AST.Match uu____55995  in
          mk1 uu____55994
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____56057) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____56126 =
            let uu____56127 =
              let uu____56136 = resugar_term' env e  in
              (uu____56136, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____56127  in
          mk1 uu____56126
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____56165 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____56165 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____56219 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____56219
                    in
                 let uu____56226 =
                   let uu____56231 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____56231
                    in
                 match uu____56226 with
                 | (univs1,td) ->
                     let uu____56251 =
                       let uu____56258 =
                         let uu____56259 = FStar_Syntax_Subst.compress td  in
                         uu____56259.FStar_Syntax_Syntax.n  in
                       match uu____56258 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____56268,(t1,uu____56270)::(d,uu____56272)::[])
                           -> (t1, d)
                       | uu____56329 -> failwith "wrong let binding format"
                        in
                     (match uu____56251 with
                      | (typ,def) ->
                          let uu____56360 =
                            let uu____56376 =
                              let uu____56377 =
                                FStar_Syntax_Subst.compress def  in
                              uu____56377.FStar_Syntax_Syntax.n  in
                            match uu____56376 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____56397)
                                ->
                                let uu____56422 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____56422 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____56453 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____56453
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____56476 -> ([], def, false)  in
                          (match uu____56360 with
                           | (binders,term,is_pat_app) ->
                               let uu____56531 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____56542 =
                                       let uu____56543 =
                                         let uu____56544 =
                                           let uu____56551 =
                                             bv_as_unique_ident bv  in
                                           (uu____56551,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____56544
                                          in
                                       mk_pat uu____56543  in
                                     (uu____56542, term)
                                  in
                               (match uu____56531 with
                                | (pat,term1) ->
                                    let uu____56573 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____56616  ->
                                                  match uu____56616 with
                                                  | (bv,q) ->
                                                      let uu____56631 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____56631
                                                        (fun q1  ->
                                                           let uu____56643 =
                                                             let uu____56644
                                                               =
                                                               let uu____56651
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____56651,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____56644
                                                              in
                                                           mk_pat uu____56643)))
                                           in
                                        let uu____56654 =
                                          let uu____56659 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____56659)
                                           in
                                        let uu____56662 =
                                          universe_to_string univs1  in
                                        (uu____56654, uu____56662)
                                      else
                                        (let uu____56671 =
                                           let uu____56676 =
                                             resugar_term' env term1  in
                                           (pat, uu____56676)  in
                                         let uu____56677 =
                                           universe_to_string univs1  in
                                         (uu____56671, uu____56677))
                                       in
                                    (attrs_opt, uu____56573))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____56783 =
                   match uu____56783 with
                   | (attrs,(pb,univs1)) ->
                       let uu____56843 =
                         let uu____56845 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____56845  in
                       if uu____56843
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____56926) ->
          let s =
            let uu____56945 =
              let uu____56947 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____56947 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____56945  in
          let uu____56952 = mk1 FStar_Parser_AST.Wild  in label s uu____56952
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____56960 =
            let uu____56961 =
              let uu____56966 = resugar_term' env tm  in (uu____56966, qi1)
               in
            FStar_Parser_AST.Quote uu____56961  in
          mk1 uu____56960
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_56978 =
            match uu___434_56978 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____56986,(uu____56987,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____57048 =
                        let uu____57049 =
                          let uu____57058 = resugar_seq t11  in
                          (uu____57058, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____57049  in
                      mk1 uu____57048
                  | uu____57061 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____57105  ->
                         match uu____57105 with
                         | (x,uu____57113) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____57118 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____57136,t1) ->
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
               let uu____57176 = FStar_Options.print_universes ()  in
               if uu____57176
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
               let uu____57240 = FStar_Options.print_universes ()  in
               if uu____57240
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
            let uu____57284 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____57284, FStar_Parser_AST.Nothing)  in
          let uu____57285 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____57285
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____57308 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____57308
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____57393 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____57393, (FStar_Pervasives_Native.snd post))  in
                    let uu____57404 =
                      let uu____57413 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____57413 then [] else [pre]  in
                    let uu____57448 =
                      let uu____57457 =
                        let uu____57466 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____57466 then [] else [pats]  in
                      FStar_List.append [post1] uu____57457  in
                    FStar_List.append uu____57404 uu____57448
                | uu____57525 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____57559  ->
                   match uu____57559 with
                   | (e,uu____57571) ->
                       let uu____57576 = resugar_term' env e  in
                       (uu____57576, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_57601 =
              match uu___435_57601 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____57634 = resugar_term' env e  in
                         (uu____57634, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____57639 -> aux l tl1)
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
        let uu____57686 = b  in
        match uu____57686 with
        | (x,aq) ->
            let uu____57695 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____57695
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____57709 =
                       let uu____57710 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____57710  in
                     FStar_Parser_AST.mk_binder uu____57709 r
                       FStar_Parser_AST.Type_level imp
                 | uu____57711 ->
                     let uu____57712 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____57712
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____57717 =
                          let uu____57718 =
                            let uu____57723 = bv_as_unique_ident x  in
                            (uu____57723, e)  in
                          FStar_Parser_AST.Annotated uu____57718  in
                        FStar_Parser_AST.mk_binder uu____57717 r
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
              let uu____57743 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____57743  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____57747 =
                if used
                then
                  let uu____57749 =
                    let uu____57756 = bv_as_unique_ident v1  in
                    (uu____57756, aqual)  in
                  FStar_Parser_AST.PatVar uu____57749
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____57747  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____57763;
                  FStar_Syntax_Syntax.vars = uu____57764;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____57774 = FStar_Options.print_bound_var_types ()  in
                if uu____57774
                then
                  let uu____57777 =
                    let uu____57778 =
                      let uu____57789 =
                        let uu____57796 = resugar_term' env typ  in
                        (uu____57796, FStar_Pervasives_Native.None)  in
                      (pat, uu____57789)  in
                    FStar_Parser_AST.PatAscribed uu____57778  in
                  mk1 uu____57777
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
          let uu____57817 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____57817
            (fun aqual  ->
               let uu____57829 =
                 let uu____57834 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _57845  -> FStar_Pervasives_Native.Some _57845)
                   uu____57834
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____57829)

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
          (let uu____57907 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____57907) &&
            (let uu____57910 =
               FStar_List.existsML
                 (fun uu____57923  ->
                    match uu____57923 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____57945)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____57950 -> false
                          | uu____57952 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____57910)
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
            let uu____58020 = may_drop_implicits args  in
            if uu____58020 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____58045  ->
                 match uu____58045 with
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
              ((let uu____58100 =
                  let uu____58102 =
                    let uu____58104 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____58104  in
                  Prims.op_Negation uu____58102  in
                if uu____58100
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
              let uu____58148 = filter_pattern_imp args  in
              (match uu____58148 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____58198 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____58198 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____58217 =
                       let uu____58223 =
                         let uu____58225 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____58225
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____58223)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____58217);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____58278  ->
                        match uu____58278 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____58295 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____58295)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____58303;
                 FStar_Syntax_Syntax.fv_delta = uu____58304;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____58333 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____58333 FStar_List.rev  in
              let args1 =
                let uu____58349 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____58369  ->
                          match uu____58369 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____58349 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____58447 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____58447
                | (hd1::tl1,hd2::tl2) ->
                    let uu____58470 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____58470
                 in
              let args2 =
                let uu____58488 = map21 fields1 args1  in
                FStar_All.pipe_right uu____58488 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____58532 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____58532 with
               | FStar_Pervasives_Native.Some (op,uu____58544) ->
                   let uu____58561 =
                     let uu____58562 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____58562  in
                   mk1 uu____58561
               | FStar_Pervasives_Native.None  ->
                   let uu____58572 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____58572 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____58577 ->
              let uu____58578 =
                let uu____58579 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____58579  in
              mk1 uu____58578
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
          let uu____58619 =
            let uu____58622 =
              let uu____58623 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____58623  in
            FStar_Pervasives_Native.Some uu____58622  in
          FStar_Pervasives_Native.Some uu____58619

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
          let uu____58635 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____58635

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_58643  ->
    match uu___436_58643 with
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
    | FStar_Syntax_Syntax.Reflectable uu____58650 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____58651 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____58652 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____58657 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____58666 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____58675 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_58681  ->
    match uu___437_58681 with
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
            (tylid,uvs,bs,t,uu____58724,datacons) ->
            let uu____58734 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____58762,uu____58763,uu____58764,inductive_lid,uu____58766,uu____58767)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____58774 -> failwith "unexpected"))
               in
            (match uu____58734 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____58795 = FStar_Options.print_implicits ()  in
                   if uu____58795 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____58812 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_58819  ->
                             match uu___438_58819 with
                             | FStar_Syntax_Syntax.RecordType uu____58821 ->
                                 true
                             | uu____58831 -> false))
                      in
                   if uu____58812
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____58885,univs1,term,uu____58888,num,uu____58890)
                           ->
                           let uu____58897 =
                             let uu____58898 =
                               FStar_Syntax_Subst.compress term  in
                             uu____58898.FStar_Syntax_Syntax.n  in
                           (match uu____58897 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____58912)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____58981  ->
                                          match uu____58981 with
                                          | (b,qual) ->
                                              let uu____59002 =
                                                bv_as_unique_ident b  in
                                              let uu____59003 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____59002, uu____59003,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____59014 -> failwith "unexpected")
                       | uu____59026 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____59157,num,uu____59159) ->
                            let c =
                              let uu____59180 =
                                let uu____59183 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____59183  in
                              ((l.FStar_Ident.ident), uu____59180,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____59203 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____59283 ->
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
        let uu____59309 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____59309;
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
        let uu____59339 = ts  in
        match uu____59339 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____59352 =
              let uu____59353 =
                let uu____59370 =
                  let uu____59379 =
                    let uu____59386 =
                      let uu____59387 =
                        let uu____59400 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____59400)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____59387  in
                    (uu____59386, FStar_Pervasives_Native.None)  in
                  [uu____59379]  in
                (false, false, uu____59370)  in
              FStar_Parser_AST.Tycon uu____59353  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____59352
  
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
              let uu____59489 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____59489 with
              | (bs,action_defn) ->
                  let uu____59496 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____59496 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____59506 = FStar_Options.print_implicits ()
                            in
                         if uu____59506
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____59516 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____59516 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____59533 =
                             let uu____59544 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____59544,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____59533  in
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
            let uu____59628 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____59628 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____59638 = FStar_Options.print_implicits ()  in
                  if uu____59638 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____59648 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____59648 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59733) ->
          let uu____59742 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____59765 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____59783 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____59791 -> false
                    | uu____59808 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____59742 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____59846 se1 =
                 match uu____59846 with
                 | (datacon_ses1,tycons) ->
                     let uu____59872 = resugar_typ env datacon_ses1 se1  in
                     (match uu____59872 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____59887 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____59887 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____59922 =
                           let uu____59923 =
                             let uu____59924 =
                               let uu____59941 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____59941)  in
                             FStar_Parser_AST.Tycon uu____59924  in
                           decl'_to_decl se uu____59923  in
                         FStar_Pervasives_Native.Some uu____59922
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____59976,uu____59977,uu____59978,uu____59979,uu____59980)
                              ->
                              let uu____59987 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____59987
                          | uu____59990 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____59994 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60001) ->
          let uu____60006 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_60014  ->
                    match uu___439_60014 with
                    | FStar_Syntax_Syntax.Projector (uu____60016,uu____60017)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60019 -> true
                    | uu____60021 -> false))
             in
          if uu____60006
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
             | FStar_Parser_AST.Let (isrec,lets,uu____60056) ->
                 let uu____60085 =
                   let uu____60086 =
                     let uu____60087 =
                       let uu____60098 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____60098)  in
                     FStar_Parser_AST.TopLevelLet uu____60087  in
                   decl'_to_decl se uu____60086  in
                 FStar_Pervasives_Native.Some uu____60085
             | uu____60135 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____60140,fml) ->
          let uu____60142 =
            let uu____60143 =
              let uu____60144 =
                let uu____60149 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____60149)  in
              FStar_Parser_AST.Assume uu____60144  in
            decl'_to_decl se uu____60143  in
          FStar_Pervasives_Native.Some uu____60142
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60151 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60151
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____60154 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60154
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____60164,t) ->
                let uu____60174 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60174
            | uu____60175 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____60183,t) ->
                let uu____60193 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60193
            | uu____60194 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____60218 -> failwith "Should not happen hopefully"  in
          let uu____60228 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____60228
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____60238 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____60238 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____60250 = FStar_Options.print_implicits ()  in
                 if uu____60250 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____60266 =
                 let uu____60267 =
                   let uu____60268 =
                     let uu____60285 =
                       let uu____60294 =
                         let uu____60301 =
                           let uu____60302 =
                             let uu____60315 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____60315)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____60302  in
                         (uu____60301, FStar_Pervasives_Native.None)  in
                       [uu____60294]  in
                     (false, false, uu____60285)  in
                   FStar_Parser_AST.Tycon uu____60268  in
                 decl'_to_decl se uu____60267  in
               FStar_Pervasives_Native.Some uu____60266)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____60347 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____60347
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____60351 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_60359  ->
                    match uu___440_60359 with
                    | FStar_Syntax_Syntax.Projector (uu____60361,uu____60362)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60364 -> true
                    | uu____60366 -> false))
             in
          if uu____60351
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____60374 =
                 (let uu____60378 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____60378) || (FStar_List.isEmpty uvs)
                  in
               if uu____60374
               then resugar_term' env t
               else
                 (let uu____60383 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____60383 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____60392 = resugar_term' env t1  in
                      label universes uu____60392)
                in
             let uu____60393 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____60393)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____60400 =
            let uu____60401 =
              let uu____60402 =
                let uu____60409 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____60414 = resugar_term' env t  in
                (uu____60409, uu____60414)  in
              FStar_Parser_AST.Splice uu____60402  in
            decl'_to_decl se uu____60401  in
          FStar_Pervasives_Native.Some uu____60400
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____60417 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____60434 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____60450 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____60474 = noenv resugar_term'  in uu____60474 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____60492 = noenv resugar_sigelt'  in uu____60492 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____60510 = noenv resugar_comp'  in uu____60510 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____60533 = noenv resugar_pat'  in uu____60533 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____60567 = noenv resugar_binder'  in uu____60567 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____60592 = noenv resugar_tscheme'  in uu____60592 ts 
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
          let uu____60627 = noenv resugar_eff_decl'  in
          uu____60627 for_free r q ed
  