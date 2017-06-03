open Prims
let intern_string: Prims.string -> Prims.string =
  let strings = FStar_Util.smap_create (Prims.parse_int "100") in
  fun s  ->
    let uu____6 = FStar_Util.smap_try_find strings s in
    match uu____6 with
    | Some res -> res
    | None  -> (FStar_Util.smap_add strings s s; s)
let default_string_finish endm b s = FStar_Parser_Parse.STRING s
let call_string_finish fin buf endm b =
  let _0_26 = FStar_Bytes.close buf in fin endm b _0_26
let add_string: FStar_Bytes.bytebuf -> Prims.string -> Prims.unit =
  fun buf  ->
    fun x  ->
      let uu____76 = FStar_Bytes.string_as_unicode_bytes x in
      FStar_Bytes.emit_bytes buf uu____76
let add_int_char: FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  ->
    fun c  ->
      FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256"));
      FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256"))
let add_unichar: FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  -> fun c  -> add_int_char buf c
let add_byte_char: FStar_Bytes.bytebuf -> FStar_BaseTypes.char -> Prims.unit
  =
  fun buf  ->
    fun c  ->
      add_int_char buf
        ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))
let stringbuf_as_bytes: FStar_Bytes.bytebuf -> FStar_Bytes.bytes =
  fun buf  ->
    let bytes = FStar_Bytes.close buf in
    let uu____100 =
      let uu____101 = FStar_Bytes.length bytes in
      uu____101 / (Prims.parse_int "2") in
    FStar_Bytes.make
      (fun i  ->
         FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))
      uu____100
let stringbuf_is_bytes: FStar_Bytes.bytebuf -> Prims.bool =
  fun buf  ->
    let bytes = FStar_Bytes.close buf in
    let ok = FStar_Util.mk_ref true in
    (let uu____117 =
       let uu____118 =
         let uu____119 = FStar_Bytes.length bytes in
         uu____119 / (Prims.parse_int "2") in
       uu____118 - (Prims.parse_int "1") in
     FStar_Util.for_range (Prims.parse_int "0") uu____117
       (fun i  ->
          let uu____127 =
            let uu____128 =
              FStar_Bytes.get bytes
                ((FStar_Mul.op_Star i (Prims.parse_int "2")) +
                   (Prims.parse_int "1")) in
            uu____128 <> (Prims.parse_int "0") in
          if uu____127 then FStar_ST.write ok false else ()));
    FStar_ST.read ok
let trigraph:
  FStar_BaseTypes.char ->
    FStar_BaseTypes.char -> FStar_BaseTypes.char -> FStar_BaseTypes.char
  =
  fun c1  ->
    fun c2  ->
      fun c3  ->
        let digit c =
          (FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0') in
        FStar_Util.char_of_int
          (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) +
              (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10")))
             + (digit c3))
let digit: FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d in
    if
      (dd >= (FStar_Util.int_of_char '0')) &&
        (dd <= (FStar_Util.int_of_char '9'))
    then (FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0')
    else failwith "digit"
let hexdigit: FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d in
    if
      (dd >= (FStar_Util.int_of_char '0')) &&
        (dd <= (FStar_Util.int_of_char '9'))
    then digit d
    else
      if
        (dd >= (FStar_Util.int_of_char 'a')) &&
          (dd <= (FStar_Util.int_of_char 'f'))
      then (dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10")
      else
        if
          (dd >= (FStar_Util.int_of_char 'A')) &&
            (dd <= (FStar_Util.int_of_char 'F'))
        then (dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10")
        else failwith "hexdigit"
let unicodegraph_short: Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "4")
    then failwith "unicodegraph"
    else
      (let uu____167 =
         let uu____168 =
           let uu____169 =
             let uu____170 =
               let uu____171 =
                 let uu____172 = FStar_Util.char_at s (Prims.parse_int "0") in
                 hexdigit uu____172 in
               FStar_Mul.op_Star uu____171 (Prims.parse_int "4096") in
             let uu____173 =
               let uu____174 =
                 let uu____175 = FStar_Util.char_at s (Prims.parse_int "1") in
                 hexdigit uu____175 in
               FStar_Mul.op_Star uu____174 (Prims.parse_int "256") in
             uu____170 + uu____173 in
           let uu____176 =
             let uu____177 =
               let uu____178 = FStar_Util.char_at s (Prims.parse_int "2") in
               hexdigit uu____178 in
             FStar_Mul.op_Star uu____177 (Prims.parse_int "16") in
           uu____169 + uu____176 in
         let uu____179 =
           let uu____180 = FStar_Util.char_at s (Prims.parse_int "3") in
           hexdigit uu____180 in
         uu____168 + uu____179 in
       FStar_Util.uint16_of_int uu____167)
let hexgraph_short: Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "2")
    then failwith "hexgraph"
    else
      (let uu____189 =
         let uu____190 =
           let uu____191 =
             let uu____192 = FStar_Util.char_at s (Prims.parse_int "0") in
             hexdigit uu____192 in
           FStar_Mul.op_Star uu____191 (Prims.parse_int "16") in
         let uu____193 =
           let uu____194 = FStar_Util.char_at s (Prims.parse_int "1") in
           hexdigit uu____194 in
         uu____190 + uu____193 in
       FStar_Util.uint16_of_int uu____189)
let unicodegraph_long:
  Prims.string -> (FStar_BaseTypes.uint16 option* FStar_BaseTypes.uint16) =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "8")
    then failwith "unicodegraph_long"
    else
      (let high =
         let uu____213 =
           let uu____214 =
             let uu____215 =
               let uu____216 =
                 let uu____217 = FStar_Util.char_at s (Prims.parse_int "0") in
                 hexdigit uu____217 in
               FStar_Mul.op_Star uu____216 (Prims.parse_int "4096") in
             let uu____218 =
               let uu____219 =
                 let uu____220 = FStar_Util.char_at s (Prims.parse_int "1") in
                 hexdigit uu____220 in
               FStar_Mul.op_Star uu____219 (Prims.parse_int "256") in
             uu____215 + uu____218 in
           let uu____221 =
             let uu____222 =
               let uu____223 = FStar_Util.char_at s (Prims.parse_int "2") in
               hexdigit uu____223 in
             FStar_Mul.op_Star uu____222 (Prims.parse_int "16") in
           uu____214 + uu____221 in
         let uu____224 =
           let uu____225 = FStar_Util.char_at s (Prims.parse_int "3") in
           hexdigit uu____225 in
         uu____213 + uu____224 in
       let low =
         let uu____227 =
           let uu____228 =
             let uu____229 =
               let uu____230 =
                 let uu____231 = FStar_Util.char_at s (Prims.parse_int "4") in
                 hexdigit uu____231 in
               FStar_Mul.op_Star uu____230 (Prims.parse_int "4096") in
             let uu____232 =
               let uu____233 =
                 let uu____234 = FStar_Util.char_at s (Prims.parse_int "5") in
                 hexdigit uu____234 in
               FStar_Mul.op_Star uu____233 (Prims.parse_int "256") in
             uu____229 + uu____232 in
           let uu____235 =
             let uu____236 =
               let uu____237 = FStar_Util.char_at s (Prims.parse_int "6") in
               hexdigit uu____237 in
             FStar_Mul.op_Star uu____236 (Prims.parse_int "16") in
           uu____228 + uu____235 in
         let uu____238 =
           let uu____239 = FStar_Util.char_at s (Prims.parse_int "7") in
           hexdigit uu____239 in
         uu____227 + uu____238 in
       if high = (Prims.parse_int "0")
       then (None, (FStar_Util.uint16_of_int low))
       else
         ((Some
             (FStar_Util.uint16_of_int
                ((Prims.parse_int "0xD800") +
                   ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) +
                        low)
                       - (Prims.parse_int "0x10000"))
                      / (Prims.parse_int "0x400"))))),
           (FStar_Util.uint16_of_int
              ((Prims.parse_int "0xDF30") +
                 ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) +
                      low)
                     - (Prims.parse_int "0x10000"))
                    mod (Prims.parse_int "0x400"))))))
let escape: FStar_Char.char -> FStar_Char.char =
  fun c  ->
    match c with
    | '\\' -> '\\'
    | '\'' -> '\''
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | c1 -> c1
type compatibilityMode =
  | ALWAYS
  | FSHARP
let uu___is_ALWAYS: compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | ALWAYS  -> true | uu____253 -> false
let uu___is_FSHARP: compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | FSHARP  -> true | uu____257 -> false
let keywords:
  (compatibilityMode* Prims.string* FStar_Parser_Parse.token) Prims.list =
  [(ALWAYS, "abstract", FStar_Parser_Parse.ABSTRACT);
  (ALWAYS, "attributes", FStar_Parser_Parse.ATTRIBUTES);
  (ALWAYS, "noeq", FStar_Parser_Parse.NOEQUALITY);
  (ALWAYS, "unopteq", FStar_Parser_Parse.UNOPTEQUALITY);
  (ALWAYS, "and", FStar_Parser_Parse.AND);
  (ALWAYS, "assert", FStar_Parser_Parse.ASSERT);
  (ALWAYS, "assume", FStar_Parser_Parse.ASSUME);
  (ALWAYS, "begin", FStar_Parser_Parse.BEGIN);
  (ALWAYS, "by", FStar_Parser_Parse.BY);
  (FSHARP, "default", FStar_Parser_Parse.DEFAULT);
  (ALWAYS, "effect", FStar_Parser_Parse.EFFECT);
  (ALWAYS, "else", FStar_Parser_Parse.ELSE);
  (ALWAYS, "end", FStar_Parser_Parse.END);
  (ALWAYS, "ensures", FStar_Parser_Parse.ENSURES);
  (ALWAYS, "exception", FStar_Parser_Parse.EXCEPTION);
  (ALWAYS, "exists", FStar_Parser_Parse.EXISTS);
  (ALWAYS, "false", FStar_Parser_Parse.FALSE);
  (ALWAYS, "False", FStar_Parser_Parse.L_FALSE);
  (ALWAYS, "forall", FStar_Parser_Parse.FORALL);
  (ALWAYS, "fun", FStar_Parser_Parse.FUN);
  (ALWAYS, "function", FStar_Parser_Parse.FUNCTION);
  (ALWAYS, "if", FStar_Parser_Parse.IF);
  (ALWAYS, "in", FStar_Parser_Parse.IN);
  (ALWAYS, "include", FStar_Parser_Parse.INCLUDE);
  (ALWAYS, "inline", FStar_Parser_Parse.INLINE);
  (ALWAYS, "inline_for_extraction", FStar_Parser_Parse.INLINE_FOR_EXTRACTION);
  (ALWAYS, "irreducible", FStar_Parser_Parse.IRREDUCIBLE);
  (ALWAYS, "let", (FStar_Parser_Parse.LET false));
  (ALWAYS, "logic", FStar_Parser_Parse.LOGIC);
  (ALWAYS, "match", FStar_Parser_Parse.MATCH);
  (ALWAYS, "module", FStar_Parser_Parse.MODULE);
  (ALWAYS, "mutable", FStar_Parser_Parse.MUTABLE);
  (ALWAYS, "new", FStar_Parser_Parse.NEW);
  (ALWAYS, "new_effect", FStar_Parser_Parse.NEW_EFFECT);
  (ALWAYS, "noextract", FStar_Parser_Parse.NOEXTRACT);
  (ALWAYS, "of", FStar_Parser_Parse.OF);
  (ALWAYS, "open", FStar_Parser_Parse.OPEN);
  (ALWAYS, "opaque", FStar_Parser_Parse.OPAQUE);
  (ALWAYS, "private", FStar_Parser_Parse.PRIVATE);
  (ALWAYS, "rec", FStar_Parser_Parse.REC);
  (ALWAYS, "reifiable", FStar_Parser_Parse.REIFIABLE);
  (ALWAYS, "reify", FStar_Parser_Parse.REIFY);
  (ALWAYS, "reflectable", FStar_Parser_Parse.REFLECTABLE);
  (ALWAYS, "requires", FStar_Parser_Parse.REQUIRES);
  (ALWAYS, "sub_effect", FStar_Parser_Parse.SUB_EFFECT);
  (ALWAYS, "then", FStar_Parser_Parse.THEN);
  (ALWAYS, "total", FStar_Parser_Parse.TOTAL);
  (ALWAYS, "true", FStar_Parser_Parse.TRUE);
  (ALWAYS, "True", FStar_Parser_Parse.L_TRUE);
  (ALWAYS, "try", FStar_Parser_Parse.TRY);
  (ALWAYS, "type", FStar_Parser_Parse.TYPE);
  (ALWAYS, "unfold", FStar_Parser_Parse.UNFOLD);
  (ALWAYS, "unfoldable", FStar_Parser_Parse.UNFOLDABLE);
  (ALWAYS, "val", FStar_Parser_Parse.VAL);
  (ALWAYS, "when", FStar_Parser_Parse.WHEN);
  (ALWAYS, "with", FStar_Parser_Parse.WITH);
  (ALWAYS, "_", FStar_Parser_Parse.UNDERSCORE)]
let stringKeywords: Prims.string Prims.list =
  FStar_List.map
    (fun uu____440  -> match uu____440 with | (uu____444,w,uu____446) -> w)
    keywords
let unreserve_words: Prims.string Prims.list =
  FStar_List.choose
    (fun uu____451  ->
       match uu____451 with
       | (mode,keyword,uu____458) ->
           if mode = FSHARP then Some keyword else None) keywords
let kwd_table: FStar_Parser_Parse.token FStar_Util.smap =
  let tab = FStar_Util.smap_create (Prims.parse_int "1000") in
  FStar_List.iter
    (fun uu____468  ->
       match uu____468 with
       | (mode,keyword,token) -> FStar_Util.smap_add tab keyword token)
    keywords;
  tab
let kwd: Prims.string -> FStar_Parser_Parse.token option =
  fun s  -> FStar_Util.smap_try_find kwd_table s
type lexargs =
  {
  getSourceDirectory: Prims.unit -> Prims.string;
  filename: Prims.string;
  contents: Prims.string;}
let mkLexargs:
  ((Prims.unit -> Prims.string)* Prims.string* Prims.string) -> lexargs =
  fun uu____515  ->
    match uu____515 with
    | (srcdir,filename,contents) ->
        { getSourceDirectory = srcdir; filename; contents }
let kwd_or_id:
  lexargs -> FStar_Range.range -> Prims.string -> FStar_Parser_Parse.token =
  fun args  ->
    fun r  ->
      fun s  ->
        let uu____537 = kwd s in
        match uu____537 with
        | Some v1 -> v1
        | None  ->
            (match s with
             | "__SOURCE_DIRECTORY__" ->
                 let uu____540 =
                   let uu____541 = args.getSourceDirectory () in
                   FStar_Bytes.string_as_unicode_bytes uu____541 in
                 FStar_Parser_Parse.STRING uu____540
             | "__SOURCE_FILE__" ->
                 let uu____542 =
                   let uu____543 = FStar_Range.file_of_range r in
                   FStar_Bytes.string_as_unicode_bytes uu____543 in
                 FStar_Parser_Parse.STRING uu____542
             | "__LINE__" ->
                 let uu____544 =
                   let uu____547 =
                     let uu____548 =
                       let uu____549 = FStar_Range.start_of_range r in
                       FStar_Range.line_of_pos uu____549 in
                     FStar_All.pipe_left FStar_Util.string_of_int uu____548 in
                   (uu____547, false) in
                 FStar_Parser_Parse.INT uu____544
             | uu____550 ->
                 if FStar_Util.starts_with s FStar_Ident.reserved_prefix
                 then
                   raise
                     (FStar_Errors.Error
                        ((Prims.strcat FStar_Ident.reserved_prefix
                            " is a reserved prefix for an identifier"), r))
                 else
                   (let uu____552 = intern_string s in
                    FStar_Parser_Parse.IDENT uu____552))