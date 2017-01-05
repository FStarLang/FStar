
open Prims

let intern_string : Prims.string  ->  Prims.string = (

let strings = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun s -> (match ((FStar_Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(

let _70_6 = (FStar_Util.smap_add strings s s)
in s)
end)))


let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))


let call_string_finish = (fun fin buf endm b -> (let _169_19 = (FStar_Bytes.close buf)
in (fin endm b _169_19)))


let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (let _169_24 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf _169_24)))


let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (

let _70_19 = (FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256")))
in (FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256")))))


let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))


let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))))


let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (let _169_40 = ((FStar_Bytes.length bytes) / (Prims.parse_int "2"))
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (i * (Prims.parse_int "2")))) _169_40))))


let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let ok = (FStar_Util.mk_ref true)
in (

let _70_32 = (let _169_44 = (((FStar_Bytes.length bytes) / (Prims.parse_int "2")) - (Prims.parse_int "1"))
in (FStar_Util.for_range (Prims.parse_int "0") _169_44 (fun i -> if ((FStar_Bytes.get bytes ((i * (Prims.parse_int "2")) + (Prims.parse_int "1"))) <> (Prims.parse_int "0")) then begin
(FStar_ST.op_Colon_Equals ok false)
end else begin
()
end)))
in (FStar_ST.read ok)))))


let trigraph : FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char = (fun c1 c2 c3 -> (

let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int ((((digit c1) * (Prims.parse_int "100")) + ((digit c2) * (Prims.parse_int "10"))) + (digit c3)))))


let digit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end else begin
(failwith "digit")
end))


let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
(digit d)
end else begin
if ((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f'))) then begin
((dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10"))
end else begin
if ((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F'))) then begin
((dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10"))
end else begin
(failwith "hexdigit")
end
end
end))


let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> if ((FStar_String.length s) <> (Prims.parse_int "4")) then begin
(failwith "unicodegraph")
end else begin
(let _169_63 = (((((let _169_59 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit _169_59)) * (Prims.parse_int "4096")) + ((let _169_60 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit _169_60)) * (Prims.parse_int "256"))) + ((let _169_61 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit _169_61)) * (Prims.parse_int "16"))) + (let _169_62 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit _169_62)))
in (FStar_Util.uint16_of_int _169_63))
end)


let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> if ((FStar_String.length s) <> (Prims.parse_int "2")) then begin
(failwith "hexgraph")
end else begin
(let _169_68 = (((let _169_66 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit _169_66)) * (Prims.parse_int "16")) + (let _169_67 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit _169_67)))
in (FStar_Util.uint16_of_int _169_68))
end)


let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 Prims.option * FStar_BaseTypes.uint16) = (fun s -> if ((FStar_String.length s) <> (Prims.parse_int "8")) then begin
(failwith "unicodegraph_long")
end else begin
(

let high = (((((let _169_71 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit _169_71)) * (Prims.parse_int "4096")) + ((let _169_72 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit _169_72)) * (Prims.parse_int "256"))) + ((let _169_73 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit _169_73)) * (Prims.parse_int "16"))) + (let _169_74 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit _169_74)))
in (

let low = (((((let _169_75 = (FStar_Util.char_at s (Prims.parse_int "4"))
in (hexdigit _169_75)) * (Prims.parse_int "4096")) + ((let _169_76 = (FStar_Util.char_at s (Prims.parse_int "5"))
in (hexdigit _169_76)) * (Prims.parse_int "256"))) + ((let _169_77 = (FStar_Util.char_at s (Prims.parse_int "6"))
in (hexdigit _169_77)) * (Prims.parse_int "16"))) + (let _169_78 = (FStar_Util.char_at s (Prims.parse_int "7"))
in (hexdigit _169_78)))
in if (high = (Prims.parse_int "0")) then begin
((None), ((FStar_Util.uint16_of_int low)))
end else begin
((Some ((FStar_Util.uint16_of_int ((Prims.parse_int "0xD800") + (((high * (Prims.parse_int "0x10000")) + (low - (Prims.parse_int "0x10000"))) / (Prims.parse_int "0x400")))))), ((FStar_Util.uint16_of_int ((Prims.parse_int "0xDF30") + (((high * (Prims.parse_int "0x10000")) + (low - (Prims.parse_int "0x10000"))) mod (Prims.parse_int "0x400"))))))
end))
end)


let escape : FStar_Char.char  ->  FStar_Char.char = (fun c -> (match (c) with
| '\\' -> begin
'\\'
end
| '\'' -> begin
'\''
end
| 'n' -> begin
'\n'
end
| 't' -> begin
'\t'
end
| 'b' -> begin
'\b'
end
| 'r' -> begin
'\r'
end
| c -> begin
c
end))


type compatibilityMode =
| ALWAYS
| FSHARP


let is_ALWAYS = (fun _discr_ -> (match (_discr_) with
| ALWAYS (_) -> begin
true
end
| _ -> begin
false
end))


let is_FSHARP = (fun _discr_ -> (match (_discr_) with
| FSHARP (_) -> begin
true
end
| _ -> begin
false
end))


let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (((ALWAYS), ("abstract"), (FStar_Parser_Parse.ABSTRACT)))::(((ALWAYS), ("attributes"), (FStar_Parser_Parse.ATTRIBUTES)))::(((ALWAYS), ("noeq"), (FStar_Parser_Parse.NOEQUALITY)))::(((ALWAYS), ("unopteq"), (FStar_Parser_Parse.UNOPTEQUALITY)))::(((ALWAYS), ("and"), (FStar_Parser_Parse.AND)))::(((ALWAYS), ("assert"), (FStar_Parser_Parse.ASSERT)))::(((ALWAYS), ("assume"), (FStar_Parser_Parse.ASSUME)))::(((ALWAYS), ("begin"), (FStar_Parser_Parse.BEGIN)))::(((FSHARP), ("default"), (FStar_Parser_Parse.DEFAULT)))::(((ALWAYS), ("effect"), (FStar_Parser_Parse.EFFECT)))::(((ALWAYS), ("effect_actions"), (FStar_Parser_Parse.ACTIONS)))::(((ALWAYS), ("else"), (FStar_Parser_Parse.ELSE)))::(((ALWAYS), ("end"), (FStar_Parser_Parse.END)))::(((ALWAYS), ("ensures"), (FStar_Parser_Parse.ENSURES)))::(((ALWAYS), ("exception"), (FStar_Parser_Parse.EXCEPTION)))::(((ALWAYS), ("exists"), (FStar_Parser_Parse.EXISTS)))::(((ALWAYS), ("false"), (FStar_Parser_Parse.FALSE)))::(((ALWAYS), ("False"), (FStar_Parser_Parse.L_FALSE)))::(((ALWAYS), ("forall"), (FStar_Parser_Parse.FORALL)))::(((ALWAYS), ("fun"), (FStar_Parser_Parse.FUN)))::(((ALWAYS), ("function"), (FStar_Parser_Parse.FUNCTION)))::(((ALWAYS), ("if"), (FStar_Parser_Parse.IF)))::(((ALWAYS), ("kind"), (FStar_Parser_Parse.KIND)))::(((ALWAYS), ("in"), (FStar_Parser_Parse.IN)))::(((ALWAYS), ("include"), (FStar_Parser_Parse.INCLUDE)))::(((ALWAYS), ("inline"), (FStar_Parser_Parse.INLINE)))::(((ALWAYS), ("inline_for_extraction"), (FStar_Parser_Parse.INLINE_FOR_EXTRACTION)))::(((ALWAYS), ("irreducible"), (FStar_Parser_Parse.IRREDUCIBLE)))::(((ALWAYS), ("let"), (FStar_Parser_Parse.LET (false))))::(((ALWAYS), ("logic"), (FStar_Parser_Parse.LOGIC)))::(((ALWAYS), ("match"), (FStar_Parser_Parse.MATCH)))::(((ALWAYS), ("module"), (FStar_Parser_Parse.MODULE)))::(((ALWAYS), ("mutable"), (FStar_Parser_Parse.MUTABLE)))::(((ALWAYS), ("new"), (FStar_Parser_Parse.NEW)))::(((ALWAYS), ("new_effect"), (FStar_Parser_Parse.NEW_EFFECT)))::(((ALWAYS), ("new_effect_for_free"), (FStar_Parser_Parse.NEW_EFFECT_FOR_FREE)))::(((ALWAYS), ("noextract"), (FStar_Parser_Parse.NOEXTRACT)))::(((ALWAYS), ("of"), (FStar_Parser_Parse.OF)))::(((ALWAYS), ("open"), (FStar_Parser_Parse.OPEN)))::(((ALWAYS), ("opaque"), (FStar_Parser_Parse.OPAQUE)))::(((ALWAYS), ("private"), (FStar_Parser_Parse.PRIVATE)))::(((ALWAYS), ("rec"), (FStar_Parser_Parse.REC)))::(((ALWAYS), ("reifiable"), (FStar_Parser_Parse.REIFIABLE)))::(((ALWAYS), ("reify"), (FStar_Parser_Parse.REIFY)))::(((ALWAYS), ("reflectable"), (FStar_Parser_Parse.REFLECTABLE)))::(((ALWAYS), ("requires"), (FStar_Parser_Parse.REQUIRES)))::(((ALWAYS), ("sub_effect"), (FStar_Parser_Parse.SUB_EFFECT)))::(((ALWAYS), ("then"), (FStar_Parser_Parse.THEN)))::(((ALWAYS), ("total"), (FStar_Parser_Parse.TOTAL)))::(((ALWAYS), ("true"), (FStar_Parser_Parse.TRUE)))::(((ALWAYS), ("True"), (FStar_Parser_Parse.L_TRUE)))::(((ALWAYS), ("try"), (FStar_Parser_Parse.TRY)))::(((ALWAYS), ("type"), (FStar_Parser_Parse.TYPE)))::(((ALWAYS), ("unfold"), (FStar_Parser_Parse.UNFOLD)))::(((ALWAYS), ("unfoldable"), (FStar_Parser_Parse.UNFOLDABLE)))::(((ALWAYS), ("val"), (FStar_Parser_Parse.VAL)))::(((ALWAYS), ("when"), (FStar_Parser_Parse.WHEN)))::(((ALWAYS), ("with"), (FStar_Parser_Parse.WITH)))::(((ALWAYS), ("_"), (FStar_Parser_Parse.UNDERSCORE)))::[]


let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun _70_61 -> (match (_70_61) with
| (_70_57, w, _70_60) -> begin
w
end)) keywords)


let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun _70_66 -> (match (_70_66) with
| (mode, keyword, _70_65) -> begin
if (mode = FSHARP) then begin
Some (keyword)
end else begin
None
end
end)) keywords)


let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (

let tab = (FStar_Util.smap_create (Prims.parse_int "1000"))
in (

let _70_72 = (FStar_List.iter (fun _70_71 -> (match (_70_71) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords)
in tab))


let kwd : Prims.string  ->  FStar_Parser_Parse.token Prims.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))


type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; contents : Prims.string}


let is_Mklexargs : lexargs  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mklexargs"))))


let mkLexargs = (fun _70_81 -> (match (_70_81) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))


let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (match ((kwd s)) with
| Some (v) -> begin
v
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _169_115 = (let _169_114 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes _169_114))
in FStar_Parser_Parse.STRING (_169_115))
end
| "__SOURCE_FILE__" -> begin
(let _169_117 = (let _169_116 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes _169_116))
in FStar_Parser_Parse.STRING (_169_117))
end
| "__LINE__" -> begin
(let _169_121 = (let _169_120 = (let _169_119 = (let _169_118 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos _169_118))
in (FStar_All.pipe_left FStar_Util.string_of_int _169_119))
in ((_169_120), (false)))
in FStar_Parser_Parse.INT (_169_121))
end
| _70_92 -> begin
if (FStar_Util.starts_with s FStar_Ident.reserved_prefix) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier")), (r)))))
end else begin
(let _169_122 = (intern_string s)
in FStar_Parser_Parse.IDENT (_169_122))
end
end)
end))




