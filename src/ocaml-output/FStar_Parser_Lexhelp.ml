open Prims
let intern_string : Prims.string -> Prims.string =
  let strings = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun s  ->
    let uu____6 = FStar_Util.smap_try_find strings s  in
    match uu____6 with
    | Some res -> res
    | None  -> (FStar_Util.smap_add strings s s; s)
  
let default_string_finish endm b s = FStar_Parser_Parse.STRING s 
let call_string_finish fin buf endm b =
  let _0_286 = FStar_Bytes.close buf  in fin endm b _0_286 
let add_string : FStar_Bytes.bytebuf -> Prims.string -> Prims.unit =
  fun buf  ->
    fun x  ->
      let _0_287 = FStar_Bytes.string_as_unicode_bytes x  in
      FStar_Bytes.emit_bytes buf _0_287
  
let add_int_char : FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  ->
    fun c  ->
      FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256"));
      FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256"))
  
let add_unichar : FStar_Bytes.bytebuf -> Prims.int -> Prims.unit =
  fun buf  -> fun c  -> add_int_char buf c 
let add_byte_char : FStar_Bytes.bytebuf -> FStar_BaseTypes.char -> Prims.unit
  =
  fun buf  ->
    fun c  ->
      add_int_char buf
        ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))
  
let stringbuf_as_bytes : FStar_Bytes.bytebuf -> FStar_Bytes.bytes =
  fun buf  ->
    let bytes = FStar_Bytes.close buf  in
    let _0_289 =
      let _0_288 = FStar_Bytes.length bytes  in
      _0_288 / (Prims.parse_int "2")  in
    FStar_Bytes.make
      (fun i  ->
         FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))
      _0_289
  
let stringbuf_is_bytes : FStar_Bytes.bytebuf -> Prims.bool =
  fun buf  ->
    let bytes = FStar_Bytes.close buf  in
    let ok = FStar_Util.mk_ref true  in
    (let _0_293 =
       let _0_291 =
         let _0_290 = FStar_Bytes.length bytes  in
         _0_290 / (Prims.parse_int "2")  in
       _0_291 - (Prims.parse_int "1")  in
     FStar_Util.for_range (Prims.parse_int "0") _0_293
       (fun i  ->
          let uu____121 =
            let uu____122 =
              FStar_Bytes.get bytes
                ((FStar_Mul.op_Star i (Prims.parse_int "2")) +
                   (Prims.parse_int "1"))
               in
            _0_292 <> (Prims.parse_int "0")  in
          match uu____109 with
          | true  -> FStar_ST.write ok false
          | uu____112 -> ()));
    FStar_ST.read ok
  
let trigraph :
  FStar_BaseTypes.char ->
    FStar_BaseTypes.char -> FStar_BaseTypes.char -> FStar_BaseTypes.char
  =
  fun c1  ->
    fun c2  ->
      fun c3  ->
        let digit c =
          (FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')  in
        FStar_Util.char_of_int
          (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) +
              (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10")))
             + (digit c3))
  
let digit : FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d  in
    match (dd >= (FStar_Util.int_of_char '0')) &&
            (dd <= (FStar_Util.int_of_char '9'))
    with
    | true  -> (FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0')
    | uu____132 -> failwith "digit"
  
let hexdigit : FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d  in
    match (dd >= (FStar_Util.int_of_char '0')) &&
            (dd <= (FStar_Util.int_of_char '9'))
    with
    | true  -> digit d
    | uu____137 ->
        (match (dd >= (FStar_Util.int_of_char 'a')) &&
                 (dd <= (FStar_Util.int_of_char 'f'))
         with
         | true  ->
             (dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10")
         | uu____138 ->
             (match (dd >= (FStar_Util.int_of_char 'A')) &&
                      (dd <= (FStar_Util.int_of_char 'F'))
              with
              | true  ->
                  (dd - (FStar_Util.int_of_char 'A')) +
                    (Prims.parse_int "10")
              | uu____139 -> failwith "hexdigit"))
  
let unicodegraph_short : Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    match (FStar_String.length s) <> (Prims.parse_int "4") with
    | true  -> failwith "unicodegraph"
    | uu____145 ->
        FStar_Util.uint16_of_int
          (let _0_302 =
             let _0_300 =
               let _0_297 =
                 let _0_294 =
                   hexdigit (FStar_Util.char_at s (Prims.parse_int "0"))  in
                 FStar_Mul.op_Star _0_294 (Prims.parse_int "4096")  in
               let _0_296 =
                 let _0_295 =
                   hexdigit (FStar_Util.char_at s (Prims.parse_int "1"))  in
                 FStar_Mul.op_Star _0_295 (Prims.parse_int "256")  in
               _0_297 + _0_296  in
             let _0_299 =
               let _0_298 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "2"))  in
               FStar_Mul.op_Star _0_298 (Prims.parse_int "16")  in
             _0_300 + _0_299  in
           let _0_301 = hexdigit (FStar_Util.char_at s (Prims.parse_int "3"))
              in
           _0_302 + _0_301)
  
let hexgraph_short : Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    match (FStar_String.length s) <> (Prims.parse_int "2") with
    | true  -> failwith "hexgraph"
    | uu____151 ->
        FStar_Util.uint16_of_int
          (let _0_305 =
             let _0_303 =
               hexdigit (FStar_Util.char_at s (Prims.parse_int "0"))  in
             FStar_Mul.op_Star _0_303 (Prims.parse_int "16")  in
           let _0_304 = hexdigit (FStar_Util.char_at s (Prims.parse_int "1"))
              in
           _0_305 + _0_304)
  
let unicodegraph_long :
  Prims.string ->
    (FStar_BaseTypes.uint16 Prims.option * FStar_BaseTypes.uint16)
  =
  fun s  ->
    match (FStar_String.length s) <> (Prims.parse_int "8") with
    | true  -> failwith "unicodegraph_long"
    | uu____166 ->
        let high =
          let _0_314 =
            let _0_312 =
              let _0_309 =
                let _0_306 =
                  hexdigit (FStar_Util.char_at s (Prims.parse_int "0"))  in
                FStar_Mul.op_Star _0_306 (Prims.parse_int "4096")  in
              let _0_308 =
                let _0_307 =
                  hexdigit (FStar_Util.char_at s (Prims.parse_int "1"))  in
                FStar_Mul.op_Star _0_307 (Prims.parse_int "256")  in
              _0_309 + _0_308  in
            let _0_311 =
              let _0_310 =
                hexdigit (FStar_Util.char_at s (Prims.parse_int "2"))  in
              FStar_Mul.op_Star _0_310 (Prims.parse_int "16")  in
            _0_312 + _0_311  in
          let _0_313 = hexdigit (FStar_Util.char_at s (Prims.parse_int "3"))
             in
          _0_314 + _0_313  in
        let low =
          let _0_323 =
            let _0_321 =
              let _0_318 =
                let _0_315 =
                  hexdigit (FStar_Util.char_at s (Prims.parse_int "4"))  in
                FStar_Mul.op_Star _0_315 (Prims.parse_int "4096")  in
              let _0_317 =
                let _0_316 =
                  hexdigit (FStar_Util.char_at s (Prims.parse_int "5"))  in
                FStar_Mul.op_Star _0_316 (Prims.parse_int "256")  in
              _0_318 + _0_317  in
            let _0_320 =
              let _0_319 =
                hexdigit (FStar_Util.char_at s (Prims.parse_int "6"))  in
              FStar_Mul.op_Star _0_319 (Prims.parse_int "16")  in
            _0_321 + _0_320  in
          let _0_322 = hexdigit (FStar_Util.char_at s (Prims.parse_int "7"))
             in
          _0_323 + _0_322  in
        (match high = (Prims.parse_int "0") with
         | true  -> (None, (FStar_Util.uint16_of_int low))
         | uu____173 ->
             ((Some
                 (FStar_Util.uint16_of_int
                    ((Prims.parse_int "0xD800") +
                       (((FStar_Mul.op_Star high (Prims.parse_int "0x10000"))
                           + (low - (Prims.parse_int "0x10000")))
                          / (Prims.parse_int "0x400"))))),
               (FStar_Util.uint16_of_int
                  ((Prims.parse_int "0xDF30") +
                     (((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) +
                         (low - (Prims.parse_int "0x10000")))
                        mod (Prims.parse_int "0x400"))))))
  
let escape : FStar_Char.char -> FStar_Char.char =
  fun c  ->
    match c with
    | '\\' -> '\\'
    | '\'' -> '\''
    | 'n' -> '\n'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'r' -> '\r'
    | c -> c
  
type compatibilityMode =
  | ALWAYS 
  | FSHARP 
let uu___is_ALWAYS : compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | ALWAYS  -> true | uu____182 -> false
  
let uu___is_FSHARP : compatibilityMode -> Prims.bool =
  fun projectee  ->
    match projectee with | FSHARP  -> true | uu____186 -> false
  
let keywords :
  (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list =
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
let stringKeywords : Prims.string Prims.list =
  FStar_List.map
    (fun uu____428  -> match uu____428 with | (uu____432,w,uu____434) -> w)
    keywords
  
let unreserve_words : Prims.string Prims.list =
  FStar_List.choose
    (fun uu____383  ->
       match uu____383 with
       | (mode,keyword,uu____390) ->
           (match mode = FSHARP with
            | true  -> Some keyword
            | uu____392 -> None)) keywords
  
let kwd_table : FStar_Parser_Parse.token FStar_Util.smap =
  let tab = FStar_Util.smap_create (Prims.parse_int "1000")  in
  FStar_List.iter
    (fun uu____456  ->
       match uu____456 with
       | (mode,keyword,token) -> FStar_Util.smap_add tab keyword token)
    keywords;
  tab 
let kwd : Prims.string -> FStar_Parser_Parse.token Prims.option =
  fun s  -> FStar_Util.smap_try_find kwd_table s 
type lexargs =
  {
  getSourceDirectory: Prims.unit -> Prims.string ;
  filename: Prims.string ;
  contents: Prims.string }
let mkLexargs :
  ((Prims.unit -> Prims.string) * Prims.string * Prims.string) -> lexargs =
  fun uu____447  ->
    match uu____447 with
    | (srcdir,filename,contents) ->
        { getSourceDirectory = srcdir; filename; contents }
  
let kwd_or_id :
  lexargs -> FStar_Range.range -> Prims.string -> FStar_Parser_Parse.token =
  fun args  ->
    fun r  ->
      fun s  ->
        let uu____469 = kwd s  in
        match uu____469 with
        | Some v -> v
        | None  ->
            (match s with
             | "__SOURCE_DIRECTORY__" ->
                 let uu____528 =
                   let uu____529 = args.getSourceDirectory () in
                   FStar_Bytes.string_as_unicode_bytes uu____529 in
                 FStar_Parser_Parse.STRING uu____528
             | "__SOURCE_FILE__" ->
                 let uu____530 =
                   let uu____531 = FStar_Range.file_of_range r in
                   FStar_Bytes.string_as_unicode_bytes uu____531 in
                 FStar_Parser_Parse.STRING uu____530
             | "__LINE__" ->
                 FStar_Parser_Parse.INT
                   (let _0_325 =
                      let _0_324 =
                        FStar_Range.line_of_pos
                          (FStar_Range.start_of_range r)
                         in
                      FStar_All.pipe_left FStar_Util.string_of_int _0_324  in
                    (_0_325, false))
             | uu____472 ->
                 (match FStar_Util.starts_with s FStar_Ident.reserved_prefix
                  with
                  | true  ->
                      Prims.raise
                        (FStar_Errors.Error
                           ((Prims.strcat FStar_Ident.reserved_prefix
                               " is a reserved prefix for an identifier"), r))
                  | uu____473 -> FStar_Parser_Parse.IDENT (intern_string s)))
  