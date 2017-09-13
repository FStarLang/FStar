open Prims
let semi: FStar_Format.doc = FStar_Format.text ";"
let comma: FStar_Format.doc = FStar_Format.text ","
let dot: FStar_Format.doc = FStar_Format.text "."
let colon: FStar_Format.doc = FStar_Format.text ":"
let ws: FStar_Format.doc = FStar_Format.break1
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___95_11  ->
      match uu___95_11 with
      | c when c = 92 -> "\\\\"
      | c when c = 32 -> " "
      | c when c = 8 -> "\\b"
      | c when c = 9 -> "\\t"
      | c when c = 13 -> "\\r"
      | c when c = 10 -> "\\n"
      | c when c = 39 -> "\\'"
      | c when c = 34 -> "\\\""
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let jstr_escape: Prims.string -> Prims.string =
  fun s  -> FStar_String.collect (escape_or FStar_Util.string_of_char) s
let escape_char:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___96_40  ->
      match uu___96_40 with
      | c when c = 39 -> "_"
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let remove_chars_t: Prims.string -> Prims.string =
  fun s  -> FStar_String.collect (escape_char FStar_Util.string_of_char) s
let print_op_un: FStar_Extraction_JavaScript_Ast.op_un -> FStar_Format.doc =
  fun uu___97_55  ->
    match uu___97_55 with
    | FStar_Extraction_JavaScript_Ast.JSU_Minus  -> FStar_Format.text "-"
    | FStar_Extraction_JavaScript_Ast.JSU_Not  -> FStar_Format.text "!"
let print_op_bin: FStar_Extraction_JavaScript_Ast.op_bin -> FStar_Format.doc
  =
  fun uu___98_59  ->
    match uu___98_59 with
    | FStar_Extraction_JavaScript_Ast.JSB_Equal  -> FStar_Format.text "=="
    | FStar_Extraction_JavaScript_Ast.JSB_NotEqual  -> FStar_Format.text "!="
    | FStar_Extraction_JavaScript_Ast.JSB_LessThan  -> FStar_Format.text "<"
    | FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual  ->
        FStar_Format.text "<="
    | FStar_Extraction_JavaScript_Ast.JSB_GreaterThan  ->
        FStar_Format.text ">"
    | FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual  ->
        FStar_Format.text ">="
    | FStar_Extraction_JavaScript_Ast.JSB_Plus  -> FStar_Format.text "+"
    | FStar_Extraction_JavaScript_Ast.JSB_Minus  -> FStar_Format.text "-"
    | FStar_Extraction_JavaScript_Ast.JSB_Mult  -> FStar_Format.text "*"
    | FStar_Extraction_JavaScript_Ast.JSB_Div  -> FStar_Format.text "/"
    | FStar_Extraction_JavaScript_Ast.JSB_Mod  -> FStar_Format.text "%"
    | FStar_Extraction_JavaScript_Ast.JSB_StrictEqual  ->
        FStar_Format.text "==="
let print_op_log: FStar_Extraction_JavaScript_Ast.op_log -> FStar_Format.doc
  =
  fun uu___99_63  ->
    match uu___99_63 with
    | FStar_Extraction_JavaScript_Ast.JSL_Or  -> FStar_Format.text "||"
    | FStar_Extraction_JavaScript_Ast.JSL_And  -> FStar_Format.text "&&"
let keywords_js: Prims.string Prims.list =
  ["abstract";
  "arguments";
  "boolean";
  "break";
  "byte";
  "case";
  "catch";
  "char";
  "class";
  "const";
  "continue";
  "debugger";
  "default";
  "delete";
  "do";
  "double";
  "else";
  "enum";
  "eval";
  "export";
  "extends";
  "false";
  "final";
  "finally";
  "float";
  "for";
  "function";
  "goto";
  "if";
  "implements";
  "import";
  "in";
  "instanceof";
  "int";
  "interface";
  "let";
  "long";
  "native";
  "new";
  "null";
  "package";
  "private";
  "protected";
  "public";
  "return";
  "short";
  "static";
  "super";
  "switch";
  "synchronized";
  "this";
  "throw";
  "throws";
  "transient";
  "true";
  "try";
  "typeof";
  "var";
  "void";
  "volatile";
  "while";
  "with";
  "yield"]
let remove_chars: Prims.string -> FStar_Format.doc =
  fun s  ->
    if FStar_List.existsb (fun x  -> s = x) keywords_js
    then
      let v1 = FStar_List.tryFind (fun x  -> s = x) keywords_js in
      ((let uu____78 = FStar_Util.must v1 in
        FStar_Util.print1
          "Warning: this name is a keyword in JavaScript: %s \n" uu____78);
       (let uu____79 =
          let uu____82 =
            let uu____85 =
              let uu____86 = remove_chars_t s in FStar_Format.text uu____86 in
            [uu____85] in
          (FStar_Format.text "_") :: uu____82 in
        FStar_Format.reduce uu____79))
    else (let uu____88 = remove_chars_t s in FStar_Format.text uu____88)
let rec pretty_print: FStar_Extraction_JavaScript_Ast.t -> FStar_Format.doc =
  fun program  ->
    let uu____166 =
      let uu____169 =
        FStar_List.map
          (fun uu___100_175  ->
             match uu___100_175 with
             | FStar_Extraction_JavaScript_Ast.JS_Statement s ->
                 (match s with
                  | FStar_Extraction_JavaScript_Ast.JSS_Block l ->
                      pretty_print_statements l
                  | uu____180 -> pretty_print_statement s)) program in
      FStar_List.append
        [FStar_Format.text "/* @flow */"; FStar_Format.hardline] uu____169 in
    FStar_Format.reduce uu____166
and pretty_print_statement:
  FStar_Extraction_JavaScript_Ast.statement_t -> FStar_Format.doc =
  fun p  ->
    let optws s =
      match s with
      | FStar_Extraction_JavaScript_Ast.JSS_Block b ->
          pretty_print_statements b
      | uu____189 -> pretty_print_statement s in
    match p with
    | FStar_Extraction_JavaScript_Ast.JSS_Empty  -> semi
    | FStar_Extraction_JavaScript_Ast.JSS_Block l ->
        let uu____193 =
          let uu____196 =
            let uu____199 =
              let uu____202 = pretty_print_statements l in
              [uu____202; FStar_Format.text "}"; FStar_Format.hardline] in
            (FStar_Format.text "{") :: uu____199 in
          ws :: uu____196 in
        FStar_Format.reduce uu____193
    | FStar_Extraction_JavaScript_Ast.JSS_Expression e ->
        let uu____204 =
          let uu____207 =
            let uu____210 = pretty_print_exp e in
            [uu____210; semi; FStar_Format.hardline] in
          ws :: uu____207 in
        FStar_Format.reduce uu____204
    | FStar_Extraction_JavaScript_Ast.JSS_If (c,t,f) ->
        let uu____218 =
          let uu____221 =
            let uu____224 =
              let uu____227 =
                let uu____228 = pretty_print_exp c in
                FStar_Format.parens uu____228 in
              let uu____229 =
                let uu____232 =
                  let uu____235 =
                    let uu____238 = optws t in
                    let uu____239 =
                      let uu____242 =
                        let uu____245 =
                          match f with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Format.empty
                          | FStar_Pervasives_Native.Some s ->
                              let uu____247 =
                                let uu____250 =
                                  let uu____253 =
                                    let uu____256 =
                                      let uu____259 = optws s in
                                      [uu____259; FStar_Format.text "}"] in
                                    (FStar_Format.text "{") :: uu____256 in
                                  (FStar_Format.text "else") :: uu____253 in
                                ws :: uu____250 in
                              FStar_Format.reduce uu____247 in
                        [uu____245; FStar_Format.hardline] in
                      (FStar_Format.text "}") :: uu____242 in
                    uu____238 :: uu____239 in
                  FStar_Format.hardline :: uu____235 in
                (FStar_Format.text "{") :: uu____232 in
              uu____227 :: uu____229 in
            (FStar_Format.text "if") :: uu____224 in
          ws :: uu____221 in
        FStar_Format.reduce uu____218
    | FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id,uu____261),lt1,t) ->
        let uu____282 =
          let uu____285 =
            let uu____288 =
              let uu____291 = remove_chars id in
              let uu____292 =
                let uu____295 = print_decl_t lt1 in
                let uu____296 =
                  let uu____299 =
                    let uu____302 = print_typ t in
                    [uu____302; semi; FStar_Format.hardline] in
                  (FStar_Format.text "=") :: uu____299 in
                uu____295 :: uu____296 in
              uu____291 :: uu____292 in
            (FStar_Format.text "type ") :: uu____288 in
          ws :: uu____285 in
        FStar_Format.reduce uu____282
    | FStar_Extraction_JavaScript_Ast.JSS_Return e ->
        let uu____306 =
          let uu____309 =
            let uu____312 =
              let uu____315 =
                match e with
                | FStar_Pervasives_Native.None  -> FStar_Format.empty
                | FStar_Pervasives_Native.Some v1 ->
                    let uu____317 =
                      let uu____320 =
                        let uu____323 = pretty_print_exp v1 in [uu____323] in
                      ws :: uu____320 in
                    FStar_Format.reduce uu____317 in
              [uu____315; semi; FStar_Format.hardline] in
            (FStar_Format.text "return") :: uu____312 in
          ws :: uu____309 in
        FStar_Format.reduce uu____306
    | FStar_Extraction_JavaScript_Ast.JSS_Throw e ->
        let uu____325 =
          let uu____328 =
            let uu____331 =
              let uu____334 = pretty_print_exp e in [uu____334; semi] in
            (FStar_Format.text "throw ") :: uu____331 in
          ws :: uu____328 in
        FStar_Format.reduce uu____325
    | FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p1,e),k) ->
        (match p1 with
         | FStar_Extraction_JavaScript_Ast.JGP_Identifier (n1,uu____349) when
             n1 = "_" ->
             (match e with
              | FStar_Pervasives_Native.Some v1 when
                  v1 =
                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                       (FStar_Extraction_JavaScript_Ast.JSV_Null, ""))
                  -> FStar_Format.empty
              | FStar_Pervasives_Native.Some v1 ->
                  let uu____356 =
                    let uu____359 = pretty_print_exp v1 in
                    [uu____359; semi; FStar_Format.hardline] in
                  FStar_Format.reduce uu____356
              | FStar_Pervasives_Native.None  -> FStar_Format.empty)
         | uu____360 ->
             let uu____361 =
               let uu____364 = print_kind_var k in
               let uu____365 =
                 let uu____368 = print_pattern p1 true in
                 let uu____369 =
                   let uu____372 =
                     match e with
                     | FStar_Pervasives_Native.None  -> FStar_Format.empty
                     | FStar_Pervasives_Native.Some v1 ->
                         let uu____374 =
                           let uu____377 =
                             let uu____380 = pretty_print_exp v1 in
                             [uu____380] in
                           (FStar_Format.text "=") :: uu____377 in
                         FStar_Format.reduce uu____374 in
                   [uu____372; semi; FStar_Format.hardline] in
                 uu____368 :: uu____369 in
               uu____364 :: uu____365 in
             FStar_Format.reduce uu____361)
    | FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d,k) ->
        (match d with
         | FStar_Extraction_JavaScript_Ast.JSE_Declaration s ->
             (match s with
              | FStar_Extraction_JavaScript_Ast.JSS_Block l ->
                  let uu____387 =
                    FStar_List.map (fun x  -> print_export_stmt x) l in
                  FStar_Format.reduce uu____387
              | uu____392 ->
                  let uu____393 =
                    let uu____396 =
                      let uu____399 = optws s in
                      [uu____399; FStar_Format.hardline] in
                    (FStar_Format.text "export ") :: uu____396 in
                  FStar_Format.reduce uu____393)
         | FStar_Extraction_JavaScript_Ast.JSE_Expression e ->
             let uu____401 =
               let uu____404 =
                 let uu____407 = pretty_print_exp e in
                 [uu____407; FStar_Format.hardline] in
               (FStar_Format.text "export ") :: uu____404 in
             FStar_Format.reduce uu____401)
    | FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration d ->
        let uu____415 =
          let uu____418 =
            let uu____421 =
              let uu____422 = jstr_escape (FStar_Pervasives_Native.fst d) in
              FStar_Format.text uu____422 in
            let uu____425 =
              let uu____428 =
                let uu____431 =
                  let uu____434 =
                    let uu____435 =
                      jstr_escape (FStar_Pervasives_Native.fst d) in
                    FStar_Format.text uu____435 in
                  [uu____434;
                  FStar_Format.text "\"";
                  semi;
                  FStar_Format.hardline] in
                (FStar_Format.text "\"./") :: uu____431 in
              (FStar_Format.text " from ") :: uu____428 in
            uu____421 :: uu____425 in
          (FStar_Format.text "import * as ") :: uu____418 in
        FStar_Format.reduce uu____415
    | FStar_Extraction_JavaScript_Ast.JSS_Seq l -> pretty_print_statements l
and pretty_print_statements:
  FStar_Extraction_JavaScript_Ast.statement_t Prims.list -> FStar_Format.doc
  =
  fun l  ->
    let uu____444 = FStar_List.map pretty_print_statement l in
    FStar_Format.reduce uu____444
and print_export_stmt:
  FStar_Extraction_JavaScript_Ast.statement_t -> FStar_Format.doc =
  fun s  ->
    match s with
    | FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p,e),k) ->
        (match p with
         | FStar_Extraction_JavaScript_Ast.JGP_Identifier (n1,uu____462) when
             n1 = "_" ->
             (match e with
              | FStar_Pervasives_Native.Some v1 when
                  v1 =
                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                       (FStar_Extraction_JavaScript_Ast.JSV_Null, ""))
                  -> FStar_Format.empty
              | FStar_Pervasives_Native.Some v1 ->
                  let uu____469 =
                    let uu____472 = pretty_print_exp v1 in
                    [uu____472; semi; FStar_Format.hardline] in
                  FStar_Format.reduce uu____469
              | FStar_Pervasives_Native.None  -> FStar_Format.empty)
         | uu____473 ->
             let uu____474 =
               let uu____477 =
                 let uu____480 = pretty_print_statement s in
                 [uu____480; FStar_Format.hardline] in
               (FStar_Format.text "export ") :: uu____477 in
             FStar_Format.reduce uu____474)
    | uu____481 ->
        let uu____482 =
          let uu____485 =
            let uu____488 = pretty_print_statement s in
            [uu____488; FStar_Format.hardline] in
          (FStar_Format.text "export ") :: uu____485 in
        FStar_Format.reduce uu____482
and pretty_print_exp:
  FStar_Extraction_JavaScript_Ast.expression_t -> FStar_Format.doc =
  fun uu___101_489  ->
    match uu___101_489 with
    | FStar_Extraction_JavaScript_Ast.JSE_Array l ->
        (match l with
         | FStar_Pervasives_Native.Some v1 ->
             let uu____500 =
               let uu____503 =
                 let uu____506 =
                   let uu____507 = FStar_List.map pretty_print_exp v1 in
                   FStar_All.pipe_right uu____507
                     (FStar_Format.combine comma) in
                 [uu____506; FStar_Format.text "]"] in
               (FStar_Format.text "[") :: uu____503 in
             FStar_Format.reduce uu____500
         | FStar_Pervasives_Native.None  ->
             FStar_Format.reduce
               [FStar_Format.text "["; FStar_Format.text "]"])
    | FStar_Extraction_JavaScript_Ast.JSE_Object l ->
        let uu____517 =
          let uu____520 =
            let uu____523 =
              let uu____524 = FStar_List.map pretty_print_obj l in
              FStar_All.pipe_right uu____524 (FStar_Format.combine comma) in
            [uu____523; FStar_Format.text "}"] in
          (FStar_Format.text "{") :: uu____520 in
        FStar_Format.reduce uu____517
    | FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction
        (uu____529,args,body,ret_t,decl_vars) ->
        let uu____566 =
          let uu____569 = print_decl_t decl_vars in
          let uu____570 =
            let uu____573 =
              let uu____574 = print_body body in
              print_arrow_fun args uu____574 ret_t in
            [uu____573] in
          uu____569 :: uu____570 in
        FStar_Format.reduce uu____566
    | FStar_Extraction_JavaScript_Ast.JSE_Unary (o,e) ->
        let uu____577 =
          let uu____580 = let uu____583 = pretty_print_exp e in [uu____583] in
          (print_op_un o) :: uu____580 in
        FStar_Format.reduce uu____577
    | FStar_Extraction_JavaScript_Ast.JSE_Binary (o,e1,e2) ->
        let uu____587 =
          let uu____590 =
            let uu____593 = pretty_print_exp e1 in
            let uu____594 =
              let uu____597 =
                let uu____600 = pretty_print_exp e2 in
                [uu____600; FStar_Format.text ")"] in
              (print_op_bin o) :: uu____597 in
            uu____593 :: uu____594 in
          (FStar_Format.text "(") :: uu____590 in
        FStar_Format.reduce uu____587
    | FStar_Extraction_JavaScript_Ast.JSE_Assignment (p,e) ->
        (match p with
         | FStar_Extraction_JavaScript_Ast.JGP_Identifier (n1,uu____604) when
             n1 = "_" -> pretty_print_exp e
         | uu____609 ->
             let uu____610 =
               let uu____613 = print_pattern p false in
               let uu____614 =
                 let uu____617 =
                   let uu____620 = pretty_print_exp e in [uu____620] in
                 (FStar_Format.text "=") :: uu____617 in
               uu____613 :: uu____614 in
             FStar_Format.reduce uu____610)
    | FStar_Extraction_JavaScript_Ast.JSE_Logical (o,e1,e2) ->
        let uu____624 =
          let uu____627 = pretty_print_exp e1 in
          let uu____628 =
            let uu____631 =
              let uu____634 = pretty_print_exp e2 in [uu____634] in
            (print_op_log o) :: uu____631 in
          uu____627 :: uu____628 in
        FStar_Format.reduce uu____624
    | FStar_Extraction_JavaScript_Ast.JSE_Call (e,l) ->
        let le =
          let uu____642 =
            FStar_List.map
              (fun x  ->
                 let uu____648 = pretty_print_exp x in
                 FStar_Format.parens uu____648) l in
          FStar_All.pipe_right uu____642
            (FStar_Format.combine FStar_Format.empty) in
        let uu____651 =
          let uu____654 = pretty_print_exp e in
          [uu____654;
          (match l with | [] -> FStar_Format.text "()" | uu____655 -> le)] in
        FStar_Format.reduce uu____651
    | FStar_Extraction_JavaScript_Ast.JSE_Member (o,p) ->
        let uu____660 =
          let uu____663 = pretty_print_exp o in
          let uu____664 =
            let uu____667 = pretty_print_propmem p in [uu____667] in
          uu____663 :: uu____664 in
        FStar_Format.reduce uu____660
    | FStar_Extraction_JavaScript_Ast.JSE_Identifier (id,t) ->
        remove_chars id
    | FStar_Extraction_JavaScript_Ast.JSE_Literal l -> print_literal l
    | FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e,t) ->
        let uu____681 =
          let uu____684 =
            let uu____687 = pretty_print_exp e in
            let uu____688 =
              let uu____691 =
                let uu____694 = print_typ t in
                [uu____694; FStar_Format.text ")"] in
              colon :: uu____691 in
            uu____687 :: uu____688 in
          (FStar_Format.text "(") :: uu____684 in
        FStar_Format.reduce uu____681
and print_decl_t:
  Prims.string Prims.list FStar_Pervasives_Native.option -> FStar_Format.doc
  =
  fun lt1  ->
    match lt1 with
    | FStar_Pervasives_Native.Some l ->
        let uu____705 =
          let uu____708 =
            let uu____711 =
              let uu____712 = FStar_List.map (fun s  -> remove_chars s) l in
              FStar_All.pipe_right uu____712 (FStar_Format.combine comma) in
            [uu____711; FStar_Format.text ">"] in
          (FStar_Format.text "<") :: uu____708 in
        FStar_Format.reduce uu____705
    | FStar_Pervasives_Native.None  -> FStar_Format.empty
and print_arrow_fun:
  FStar_Extraction_JavaScript_Ast.pattern_t Prims.list ->
    FStar_Format.doc ->
      FStar_Extraction_JavaScript_Ast.typ FStar_Pervasives_Native.option ->
        FStar_Format.doc
  =
  fun args  ->
    fun body  ->
      fun ret_t  ->
        let ret_t1 =
          match ret_t with
          | FStar_Pervasives_Native.None  -> FStar_Format.empty
          | FStar_Pervasives_Native.Some v1 ->
              let uu____730 =
                let uu____733 =
                  let uu____736 =
                    let uu____737 = print_typ v1 in
                    FStar_Format.parens uu____737 in
                  [uu____736] in
                colon :: uu____733 in
              FStar_Format.reduce uu____730 in
        print_arrow_fun_p args body ret_t1 true
and print_arrow_fun_p:
  FStar_Extraction_JavaScript_Ast.pattern_t Prims.list ->
    FStar_Format.doc -> FStar_Format.doc -> Prims.bool -> FStar_Format.doc
  =
  fun args  ->
    fun body  ->
      fun ret_t  ->
        fun print_ret_t  ->
          let ret_t1 = if print_ret_t then ret_t else FStar_Format.empty in
          match args with
          | [] ->
              FStar_Format.reduce
                [FStar_Format.text "()"; FStar_Format.text "=>"; body]
          | x::[] ->
              let uu____747 =
                let uu____750 =
                  let uu____751 = print_pattern x true in
                  FStar_Format.parens uu____751 in
                [uu____750; ret_t1; FStar_Format.text "=>"; body] in
              FStar_Format.reduce uu____747
          | hd1::tl1 ->
              let uu____756 =
                let uu____759 =
                  let uu____760 = print_pattern hd1 true in
                  FStar_Format.parens uu____760 in
                let uu____761 =
                  let uu____764 =
                    let uu____767 =
                      let uu____770 =
                        let uu____771 =
                          print_arrow_fun_p tl1 body ret_t1 false in
                        FStar_Format.parens uu____771 in
                      [uu____770] in
                    (FStar_Format.text "=>") :: uu____767 in
                  ret_t1 :: uu____764 in
                uu____759 :: uu____761 in
              FStar_Format.reduce uu____756
and pretty_print_obj:
  FStar_Extraction_JavaScript_Ast.property_obj_t -> FStar_Format.doc =
  fun el  ->
    match el with
    | FStar_Extraction_JavaScript_Ast.JSPO_Property (k,e,uu____775) ->
        let uu____776 =
          let uu____779 = pretty_print_prop_key k in
          let uu____780 =
            let uu____783 = let uu____786 = pretty_print_exp e in [uu____786] in
            (FStar_Format.text ":") :: uu____783 in
          uu____779 :: uu____780 in
        FStar_Format.reduce uu____776
    | FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty e ->
        pretty_print_exp e
and pretty_print_prop_key:
  FStar_Extraction_JavaScript_Ast.object_prop_key_t -> FStar_Format.doc =
  fun k  ->
    match k with
    | FStar_Extraction_JavaScript_Ast.JSO_Literal l -> print_literal l
    | FStar_Extraction_JavaScript_Ast.JSO_Identifier (id,t) ->
        let uu____800 = jstr_escape id in FStar_Format.text uu____800
    | FStar_Extraction_JavaScript_Ast.JSO_Computed e -> pretty_print_exp e
and pretty_print_propmem:
  FStar_Extraction_JavaScript_Ast.propmem_t -> FStar_Format.doc =
  fun p  ->
    match p with
    | FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i,t) ->
        let uu____809 =
          let uu____812 =
            let uu____815 =
              let uu____816 = jstr_escape i in FStar_Format.text uu____816 in
            [uu____815] in
          (FStar_Format.text ".") :: uu____812 in
        FStar_Format.reduce uu____809
    | FStar_Extraction_JavaScript_Ast.JSPM_Expression e ->
        let uu____818 =
          let uu____821 =
            let uu____824 = pretty_print_exp e in
            [uu____824; FStar_Format.text "]"] in
          (FStar_Format.text "[") :: uu____821 in
        FStar_Format.reduce uu____818
and print_typ: FStar_Extraction_JavaScript_Ast.typ -> FStar_Format.doc =
  fun uu___102_825  ->
    match uu___102_825 with
    | FStar_Extraction_JavaScript_Ast.JST_Any  -> FStar_Format.text "any"
    | FStar_Extraction_JavaScript_Ast.JST_Void  -> FStar_Format.text "void"
    | FStar_Extraction_JavaScript_Ast.JST_Null  -> FStar_Format.text "null"
    | FStar_Extraction_JavaScript_Ast.JST_Number  ->
        FStar_Format.text "number"
    | FStar_Extraction_JavaScript_Ast.JST_String  ->
        FStar_Format.text "string"
    | FStar_Extraction_JavaScript_Ast.JST_Boolean  ->
        FStar_Format.text "boolean"
    | FStar_Extraction_JavaScript_Ast.JST_Function (args,ret_t,decl_vars) ->
        let uu____861 =
          let uu____864 = print_decl_t decl_vars in
          let uu____865 =
            let uu____868 = print_fun_typ args ret_t in [uu____868] in
          uu____864 :: uu____865 in
        FStar_Format.reduce uu____861
    | FStar_Extraction_JavaScript_Ast.JST_Object lp ->
        let uu____876 =
          let uu____879 =
            let uu____882 =
              let uu____883 =
                FStar_List.map
                  (fun uu____894  ->
                     match uu____894 with
                     | (k,t) ->
                         let uu____901 =
                           let uu____904 = pretty_print_prop_key k in
                           let uu____905 =
                             let uu____908 =
                               let uu____911 = print_typ t in [uu____911] in
                             (FStar_Format.text ":") :: uu____908 in
                           uu____904 :: uu____905 in
                         FStar_Format.reduce uu____901) lp in
              FStar_All.pipe_right uu____883 (FStar_Format.combine comma) in
            [uu____882; FStar_Format.text "}"] in
          (FStar_Format.text "{") :: uu____879 in
        FStar_Format.reduce uu____876
    | FStar_Extraction_JavaScript_Ast.JST_Array t ->
        let uu____915 =
          let uu____918 =
            let uu____921 =
              let uu____924 = print_typ t in
              [uu____924; FStar_Format.text ">"] in
            (FStar_Format.text "<") :: uu____921 in
          (FStar_Format.text "Array") :: uu____918 in
        FStar_Format.reduce uu____915
    | FStar_Extraction_JavaScript_Ast.JST_Union l ->
        let uu____928 =
          let uu____931 =
            let uu____932 = FStar_List.map print_typ l in
            FStar_All.pipe_right uu____932
              (FStar_Format.combine (FStar_Format.text "|")) in
          [uu____931] in
        FStar_Format.reduce uu____928
    | FStar_Extraction_JavaScript_Ast.JST_Intersection l ->
        let uu____940 =
          let uu____943 =
            let uu____944 = FStar_List.map print_typ l in
            FStar_All.pipe_right uu____944
              (FStar_Format.combine (FStar_Format.text "&")) in
          [uu____943] in
        FStar_Format.reduce uu____940
    | FStar_Extraction_JavaScript_Ast.JST_Tuple lt1 ->
        let uu____952 =
          let uu____955 =
            let uu____958 =
              let uu____959 = FStar_List.map print_typ lt1 in
              FStar_All.pipe_right uu____959 (FStar_Format.combine comma) in
            [uu____958; FStar_Format.text "]"] in
          (FStar_Format.text "[") :: uu____955 in
        FStar_Format.reduce uu____952
    | FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s,uu____965) ->
        let uu____966 =
          let uu____967 =
            let uu____968 = jstr_escape s in Prims.strcat uu____968 "\"" in
          Prims.strcat "\"" uu____967 in
        FStar_Format.text uu____966
    | FStar_Extraction_JavaScript_Ast.JST_Generic (n1,lt1) ->
        let print_lt =
          match lt1 with
          | FStar_Pervasives_Native.None  -> FStar_Format.empty
          | FStar_Pervasives_Native.Some v1 ->
              let uu____987 =
                let uu____990 =
                  let uu____993 =
                    let uu____994 = FStar_List.map print_typ v1 in
                    FStar_All.pipe_right uu____994
                      (FStar_Format.combine comma) in
                  [uu____993; FStar_Format.text ">"] in
                (FStar_Format.text "<") :: uu____990 in
              FStar_Format.reduce uu____987 in
        let uu____999 =
          let uu____1002 = remove_chars n1 in [uu____1002; print_lt] in
        FStar_Format.reduce uu____999
and print_fun_typ:
  ((Prims.string,FStar_Extraction_JavaScript_Ast.typ
                   FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2,FStar_Extraction_JavaScript_Ast.typ)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_JavaScript_Ast.typ -> FStar_Format.doc
  =
  fun args  ->
    fun ret_t  ->
      let print_arg uu____1030 =
        match uu____1030 with
        | ((id,uu____1042),t) ->
            let uu____1054 =
              let uu____1057 =
                let uu____1058 = jstr_escape id in
                FStar_Format.text uu____1058 in
              let uu____1059 =
                let uu____1062 = let uu____1065 = print_typ t in [uu____1065] in
                colon :: uu____1062 in
              uu____1057 :: uu____1059 in
            FStar_Format.reduce uu____1054 in
      match args with
      | [] ->
          let uu____1076 =
            let uu____1079 =
              let uu____1082 =
                let uu____1085 = print_typ ret_t in [uu____1085] in
              (FStar_Format.text "=>") :: uu____1082 in
            (FStar_Format.text "()") :: uu____1079 in
          FStar_Format.reduce uu____1076
      | x::[] ->
          let uu____1117 =
            let uu____1120 =
              let uu____1121 = print_arg x in FStar_Format.parens uu____1121 in
            let uu____1122 =
              let uu____1125 =
                let uu____1128 =
                  let uu____1129 = print_typ ret_t in
                  FStar_Format.parens uu____1129 in
                [uu____1128] in
              (FStar_Format.text "=>") :: uu____1125 in
            uu____1120 :: uu____1122 in
          FStar_Format.reduce uu____1117
      | hd1::tl1 ->
          let uu____1164 =
            let uu____1167 =
              let uu____1168 = print_arg hd1 in
              FStar_Format.parens uu____1168 in
            let uu____1169 =
              let uu____1172 =
                let uu____1175 =
                  let uu____1176 = print_fun_typ tl1 ret_t in
                  FStar_Format.parens uu____1176 in
                [uu____1175] in
              (FStar_Format.text "=>") :: uu____1172 in
            uu____1167 :: uu____1169 in
          FStar_Format.reduce uu____1164
and print_literal:
  (FStar_Extraction_JavaScript_Ast.value_t,Prims.string)
    FStar_Pervasives_Native.tuple2 -> FStar_Format.doc
  =
  fun uu____1177  ->
    match uu____1177 with
    | (v1,s) ->
        (match (v1, s) with
         | (FStar_Extraction_JavaScript_Ast.JSV_String s1,uu____1185) ->
             let uu____1186 =
               let uu____1187 =
                 let uu____1188 = jstr_escape s1 in
                 Prims.strcat uu____1188 "\"" in
               Prims.strcat "\"" uu____1187 in
             FStar_Format.text uu____1186
         | (FStar_Extraction_JavaScript_Ast.JSV_Boolean b,uu____1190) ->
             let uu____1191 = FStar_Util.string_of_bool b in
             FStar_Format.text uu____1191
         | (FStar_Extraction_JavaScript_Ast.JSV_Null ,uu____1192) ->
             FStar_Format.text "null"
         | (FStar_Extraction_JavaScript_Ast.JSV_Number f,s1) ->
             FStar_Format.text s1)
and print_kind_var:
  FStar_Extraction_JavaScript_Ast.kind_var_t -> FStar_Format.doc =
  fun uu___103_1195  ->
    match uu___103_1195 with
    | FStar_Extraction_JavaScript_Ast.JSV_Var  -> FStar_Format.text "var "
    | FStar_Extraction_JavaScript_Ast.JSV_Let  -> FStar_Format.text "let "
    | FStar_Extraction_JavaScript_Ast.JSV_Const  ->
        FStar_Format.text "const "
and print_pattern:
  FStar_Extraction_JavaScript_Ast.pattern_t -> Prims.bool -> FStar_Format.doc
  =
  fun p  ->
    fun print_t  ->
      match p with
      | FStar_Extraction_JavaScript_Ast.JGP_Expression e ->
          pretty_print_exp e
      | FStar_Extraction_JavaScript_Ast.JGP_Identifier (id,t) ->
          let r =
            match t with
            | FStar_Pervasives_Native.Some v1 ->
                let uu____1207 =
                  let uu____1210 =
                    let uu____1213 = print_typ v1 in [uu____1213] in
                  colon :: uu____1210 in
                FStar_Format.reduce uu____1207
            | FStar_Pervasives_Native.None  -> FStar_Format.empty in
          let uu____1214 =
            let uu____1217 = remove_chars id in
            [uu____1217; if print_t then r else FStar_Format.empty] in
          FStar_Format.reduce uu____1214
and print_body: FStar_Extraction_JavaScript_Ast.body_t -> FStar_Format.doc =
  fun uu___104_1219  ->
    match uu___104_1219 with
    | FStar_Extraction_JavaScript_Ast.JS_BodyBlock l ->
        let uu____1223 =
          let uu____1226 =
            let uu____1229 =
              let uu____1232 = pretty_print_statements l in
              [uu____1232; FStar_Format.text "}"] in
            FStar_Format.hardline :: uu____1229 in
          (FStar_Format.text "{") :: uu____1226 in
        FStar_Format.reduce uu____1223
    | FStar_Extraction_JavaScript_Ast.JS_BodyExpression e ->
        let uu____1234 = pretty_print_exp e in FStar_Format.parens uu____1234