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
  let _0_337 = FStar_Bytes.close buf  in fin endm b _0_337 
let add_string : FStar_Bytes.bytebuf -> Prims.string -> Prims.unit =
  fun buf  ->
    fun x  ->
      let _0_338 = FStar_Bytes.string_as_unicode_bytes x  in
      FStar_Bytes.emit_bytes buf _0_338
  
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
    let _0_340 =
      let _0_339 = FStar_Bytes.length bytes  in
      _0_339 / (Prims.parse_int "2")  in
    FStar_Bytes.make
      (fun i  ->
         FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))
      _0_340
  
let stringbuf_is_bytes : FStar_Bytes.bytebuf -> Prims.bool =
  fun buf  ->
    let bytes = FStar_Bytes.close buf  in
    let ok = FStar_Util.mk_ref true  in
    (let _0_344 =
       let _0_342 =
         let _0_341 = FStar_Bytes.length bytes  in
         _0_341 / (Prims.parse_int "2")  in
       _0_342 - (Prims.parse_int "1")  in
     FStar_Util.for_range (Prims.parse_int "0") _0_344
       (fun i  ->
          let uu____109 =
            let _0_343 =
              FStar_Bytes.get bytes
                ((FStar_Mul.op_Star i (Prims.parse_int "2")) +
                   (Prims.parse_int "1"))
               in
            _0_343 <> (Prims.parse_int "0")  in
          if uu____109 then FStar_ST.write ok false else ()));
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
    if
      (dd >= (FStar_Util.int_of_char '0')) &&
        (dd <= (FStar_Util.int_of_char '9'))
    then (FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0')
    else failwith "digit"
  
let hexdigit : FStar_BaseTypes.char -> Prims.int =
  fun d  ->
    let dd = FStar_Util.int_of_char d  in
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
  
let unicodegraph_short : Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "4")
    then failwith "unicodegraph"
    else
      FStar_Util.uint16_of_int
        (let _0_353 =
           let _0_351 =
             let _0_348 =
               let _0_345 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "0"))  in
               FStar_Mul.op_Star _0_345 (Prims.parse_int "4096")  in
             let _0_347 =
               let _0_346 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "1"))  in
               FStar_Mul.op_Star _0_346 (Prims.parse_int "256")  in
             _0_348 + _0_347  in
           let _0_350 =
             let _0_349 =
               hexdigit (FStar_Util.char_at s (Prims.parse_int "2"))  in
             FStar_Mul.op_Star _0_349 (Prims.parse_int "16")  in
           _0_351 + _0_350  in
         let _0_352 = hexdigit (FStar_Util.char_at s (Prims.parse_int "3"))
            in
         _0_353 + _0_352)
  
let hexgraph_short : Prims.string -> FStar_BaseTypes.uint16 =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "2")
    then failwith "hexgraph"
    else
      FStar_Util.uint16_of_int
        (let _0_356 =
           let _0_354 = hexdigit (FStar_Util.char_at s (Prims.parse_int "0"))
              in
           FStar_Mul.op_Star _0_354 (Prims.parse_int "16")  in
         let _0_355 = hexdigit (FStar_Util.char_at s (Prims.parse_int "1"))
            in
         _0_356 + _0_355)
  
let unicodegraph_long :
  Prims.string ->
    (FStar_BaseTypes.uint16 Prims.option * FStar_BaseTypes.uint16)
  =
  fun s  ->
    if (FStar_String.length s) <> (Prims.parse_int "8")
    then failwith "unicodegraph_long"
    else
      (let high =
         let _0_365 =
           let _0_363 =
             let _0_360 =
               let _0_357 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "0"))  in
               FStar_Mul.op_Star _0_357 (Prims.parse_int "4096")  in
             let _0_359 =
               let _0_358 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "1"))  in
               FStar_Mul.op_Star _0_358 (Prims.parse_int "256")  in
             _0_360 + _0_359  in
           let _0_362 =
             let _0_361 =
               hexdigit (FStar_Util.char_at s (Prims.parse_int "2"))  in
             FStar_Mul.op_Star _0_361 (Prims.parse_int "16")  in
           _0_363 + _0_362  in
         let _0_364 = hexdigit (FStar_Util.char_at s (Prims.parse_int "3"))
            in
         _0_365 + _0_364  in
       let low =
         let _0_374 =
           let _0_372 =
             let _0_369 =
               let _0_366 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "4"))  in
               FStar_Mul.op_Star _0_366 (Prims.parse_int "4096")  in
             let _0_368 =
               let _0_367 =
                 hexdigit (FStar_Util.char_at s (Prims.parse_int "5"))  in
               FStar_Mul.op_Star _0_367 (Prims.parse_int "256")  in
             _0_369 + _0_368  in
           let _0_371 =
             let _0_370 =
               hexdigit (FStar_Util.char_at s (Prims.parse_int "6"))  in
             FStar_Mul.op_Star _0_370 (Prims.parse_int "16")  in
           _0_372 + _0_371  in
         let _0_373 = hexdigit (FStar_Util.char_at s (Prims.parse_int "7"))
            in
         _0_374 + _0_373  in
       if high = (Prims.parse_int "0")
       then (None, (FStar_Util.uint16_of_int low))
       else
         ((Some
             (FStar_Util.uint16_of_int
                ((Prims.parse_int "0xD800") +
                   (((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) +
                       (low - (Prims.parse_int "0x10000")))
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
  (FSHARP, "default", FStar_Parser_Parse.DEFAULT);
  (ALWAYS, "effect", FStar_Parser_Parse.EFFECT);
  (ALWAYS, "effect_actions", FStar_Parser_Parse.ACTIONS);
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
  (ALWAYS, "new_effect_for_free", FStar_Parser_Parse.NEW_EFFECT_FOR_FREE);
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
    (fun uu____372  -> match uu____372 with | (uu____376,w,uu____378) -> w)
    keywords
  
let unreserve_words : Prims.string Prims.list =
  FStar_List.choose
    (fun uu____383  ->
       match uu____383 with
       | (mode,keyword,uu____390) ->
           if mode = FSHARP then Some keyword else None) keywords
  
let kwd_table : FStar_Parser_Parse.token FStar_Util.smap =
  let tab = FStar_Util.smap_create (Prims.parse_int "1000")  in
  FStar_List.iter
    (fun uu____400  ->
       match uu____400 with
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
                 FStar_Parser_Parse.STRING
                   (FStar_Bytes.string_as_unicode_bytes
                      (args.getSourceDirectory ()))
             | "__SOURCE_FILE__" ->
                 FStar_Parser_Parse.STRING
                   (FStar_Bytes.string_as_unicode_bytes
                      (FStar_Range.file_of_range r))
             | "__LINE__" ->
                 FStar_Parser_Parse.INT
                   (let _0_376 =
                      let _0_375 =
                        FStar_Range.line_of_pos
                          (FStar_Range.start_of_range r)
                         in
                      FStar_All.pipe_left FStar_Util.string_of_int _0_375  in
                    (_0_376, false))
             | uu____472 ->
                 if FStar_Util.starts_with s FStar_Ident.reserved_prefix
                 then
                   Prims.raise
                     (FStar_Errors.Error
                        ((Prims.strcat FStar_Ident.reserved_prefix
                            " is a reserved prefix for an identifier"), r))
                 else FStar_Parser_Parse.IDENT (intern_string s))
  