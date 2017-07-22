
open Prims
open FStar_Pervasives

let intern_string : Prims.string  ->  Prims.string = (

let strings = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun s -> (

let uu____8 = (FStar_Util.smap_try_find strings s)
in (match (uu____8) with
| FStar_Pervasives_Native.Some (res) -> begin
res
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.smap_add strings s s);
s;
)
end))))


let default_string_finish : 'Auu____23 'Auu____24 . 'Auu____24  ->  'Auu____23  ->  FStar_Parser_Parse.bytes  ->  FStar_Parser_Parse.token = (fun endm b s -> FStar_Parser_Parse.STRING (s))


let call_string_finish : 'Auu____51 'Auu____52 'Auu____53 . ('Auu____53  ->  'Auu____52  ->  FStar_Bytes.bytes  ->  'Auu____51)  ->  FStar_Bytes.bytebuf  ->  'Auu____53  ->  'Auu____52  ->  'Auu____51 = (fun fin buf endm b -> (let _0_26 = (FStar_Bytes.close buf)
in (fin endm b _0_26)))


let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (

let uu____93 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf uu____93)))


let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> ((FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256")));
(FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256")));
))


let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))


let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))))


let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let uu____124 = (

let uu____125 = (FStar_Bytes.length bytes)
in (uu____125 / (Prims.parse_int "2")))
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))) uu____124))))


let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let ok = (FStar_Util.mk_ref true)
in ((

let uu____144 = (

let uu____145 = (

let uu____146 = (FStar_Bytes.length bytes)
in (uu____146 / (Prims.parse_int "2")))
in (uu____145 - (Prims.parse_int "1")))
in (FStar_Util.for_range (Prims.parse_int "0") uu____144 (fun i -> (

let uu____156 = (

let uu____157 = (FStar_Bytes.get bytes ((FStar_Mul.op_Star i (Prims.parse_int "2")) + (Prims.parse_int "1")))
in (uu____157 <> (Prims.parse_int "0")))
in (match (uu____156) with
| true -> begin
(FStar_ST.write ok false)
end
| uu____160 -> begin
()
end)))));
(FStar_ST.read ok);
))))


let trigraph : FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char = (fun c1 c2 c3 -> (

let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) + (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10"))) + (digit c3)))))


let digit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end
| uu____184 -> begin
(failwith "digit")
end)))


let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
(digit d)
end
| uu____190 -> begin
(match (((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10"))
end
| uu____191 -> begin
(match (((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10"))
end
| uu____192 -> begin
(failwith "hexdigit")
end)
end)
end)))


let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "4"))) with
| true -> begin
(failwith "unicodegraph")
end
| uu____197 -> begin
(

let uu____198 = (

let uu____199 = (

let uu____200 = (

let uu____201 = (

let uu____202 = (

let uu____203 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____203))
in (FStar_Mul.op_Star uu____202 (Prims.parse_int "4096")))
in (

let uu____204 = (

let uu____205 = (

let uu____206 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____206))
in (FStar_Mul.op_Star uu____205 (Prims.parse_int "256")))
in (uu____201 + uu____204)))
in (

let uu____207 = (

let uu____208 = (

let uu____209 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____209))
in (FStar_Mul.op_Star uu____208 (Prims.parse_int "16")))
in (uu____200 + uu____207)))
in (

let uu____210 = (

let uu____211 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____211))
in (uu____199 + uu____210)))
in (FStar_Util.uint16_of_int uu____198))
end))


let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "2"))) with
| true -> begin
(failwith "hexgraph")
end
| uu____216 -> begin
(

let uu____217 = (

let uu____218 = (

let uu____219 = (

let uu____220 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____220))
in (FStar_Mul.op_Star uu____219 (Prims.parse_int "16")))
in (

let uu____221 = (

let uu____222 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____222))
in (uu____218 + uu____221)))
in (FStar_Util.uint16_of_int uu____217))
end))


let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 FStar_Pervasives_Native.option * FStar_BaseTypes.uint16) = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "8"))) with
| true -> begin
(failwith "unicodegraph_long")
end
| uu____245 -> begin
(

let high = (

let uu____247 = (

let uu____248 = (

let uu____249 = (

let uu____250 = (

let uu____251 = (FStar_Util.char_at s (Prims.parse_int "0"))
in (hexdigit uu____251))
in (FStar_Mul.op_Star uu____250 (Prims.parse_int "4096")))
in (

let uu____252 = (

let uu____253 = (

let uu____254 = (FStar_Util.char_at s (Prims.parse_int "1"))
in (hexdigit uu____254))
in (FStar_Mul.op_Star uu____253 (Prims.parse_int "256")))
in (uu____249 + uu____252)))
in (

let uu____255 = (

let uu____256 = (

let uu____257 = (FStar_Util.char_at s (Prims.parse_int "2"))
in (hexdigit uu____257))
in (FStar_Mul.op_Star uu____256 (Prims.parse_int "16")))
in (uu____248 + uu____255)))
in (

let uu____258 = (

let uu____259 = (FStar_Util.char_at s (Prims.parse_int "3"))
in (hexdigit uu____259))
in (uu____247 + uu____258)))
in (

let low = (

let uu____261 = (

let uu____262 = (

let uu____263 = (

let uu____264 = (

let uu____265 = (FStar_Util.char_at s (Prims.parse_int "4"))
in (hexdigit uu____265))
in (FStar_Mul.op_Star uu____264 (Prims.parse_int "4096")))
in (

let uu____266 = (

let uu____267 = (

let uu____268 = (FStar_Util.char_at s (Prims.parse_int "5"))
in (hexdigit uu____268))
in (FStar_Mul.op_Star uu____267 (Prims.parse_int "256")))
in (uu____263 + uu____266)))
in (

let uu____269 = (

let uu____270 = (

let uu____271 = (FStar_Util.char_at s (Prims.parse_int "6"))
in (hexdigit uu____271))
in (FStar_Mul.op_Star uu____270 (Prims.parse_int "16")))
in (uu____262 + uu____269)))
in (

let uu____272 = (

let uu____273 = (FStar_Util.char_at s (Prims.parse_int "7"))
in (hexdigit uu____273))
in (uu____261 + uu____272)))
in (match ((high = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Pervasives_Native.None), ((FStar_Util.uint16_of_int low)))
end
| uu____282 -> begin
((FStar_Pervasives_Native.Some ((FStar_Util.uint16_of_int ((Prims.parse_int "0xD800") + ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + low) - (Prims.parse_int "0x10000")) / (Prims.parse_int "0x400")))))), ((FStar_Util.uint16_of_int ((Prims.parse_int "0xDF30") + ((((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + low) - (Prims.parse_int "0x10000")) mod (Prims.parse_int "0x400"))))))
end)))
end))


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
| c1 -> begin
c1
end))

type compatibilityMode =
| ALWAYS
| FSHARP


let uu___is_ALWAYS : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ALWAYS -> begin
true
end
| uu____294 -> begin
false
end))


let uu___is_FSHARP : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSHARP -> begin
true
end
| uu____299 -> begin
false
end))


let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (((ALWAYS), ("abstract"), (FStar_Parser_Parse.ABSTRACT)))::(((ALWAYS), ("attributes"), (FStar_Parser_Parse.ATTRIBUTES)))::(((ALWAYS), ("noeq"), (FStar_Parser_Parse.NOEQUALITY)))::(((ALWAYS), ("unopteq"), (FStar_Parser_Parse.UNOPTEQUALITY)))::(((ALWAYS), ("and"), (FStar_Parser_Parse.AND)))::(((ALWAYS), ("assert"), (FStar_Parser_Parse.ASSERT)))::(((ALWAYS), ("assume"), (FStar_Parser_Parse.ASSUME)))::(((ALWAYS), ("begin"), (FStar_Parser_Parse.BEGIN)))::(((ALWAYS), ("by"), (FStar_Parser_Parse.BY)))::(((FSHARP), ("default"), (FStar_Parser_Parse.DEFAULT)))::(((ALWAYS), ("effect"), (FStar_Parser_Parse.EFFECT)))::(((ALWAYS), ("else"), (FStar_Parser_Parse.ELSE)))::(((ALWAYS), ("end"), (FStar_Parser_Parse.END)))::(((ALWAYS), ("ensures"), (FStar_Parser_Parse.ENSURES)))::(((ALWAYS), ("exception"), (FStar_Parser_Parse.EXCEPTION)))::(((ALWAYS), ("exists"), (FStar_Parser_Parse.EXISTS)))::(((ALWAYS), ("false"), (FStar_Parser_Parse.FALSE)))::(((ALWAYS), ("False"), (FStar_Parser_Parse.L_FALSE)))::(((ALWAYS), ("forall"), (FStar_Parser_Parse.FORALL)))::(((ALWAYS), ("fun"), (FStar_Parser_Parse.FUN)))::(((ALWAYS), ("function"), (FStar_Parser_Parse.FUNCTION)))::(((ALWAYS), ("if"), (FStar_Parser_Parse.IF)))::(((ALWAYS), ("in"), (FStar_Parser_Parse.IN)))::(((ALWAYS), ("include"), (FStar_Parser_Parse.INCLUDE)))::(((ALWAYS), ("inline"), (FStar_Parser_Parse.INLINE)))::(((ALWAYS), ("inline_for_extraction"), (FStar_Parser_Parse.INLINE_FOR_EXTRACTION)))::(((ALWAYS), ("irreducible"), (FStar_Parser_Parse.IRREDUCIBLE)))::(((ALWAYS), ("let"), (FStar_Parser_Parse.LET (false))))::(((ALWAYS), ("logic"), (FStar_Parser_Parse.LOGIC)))::(((ALWAYS), ("match"), (FStar_Parser_Parse.MATCH)))::(((ALWAYS), ("module"), (FStar_Parser_Parse.MODULE)))::(((ALWAYS), ("mutable"), (FStar_Parser_Parse.MUTABLE)))::(((ALWAYS), ("new"), (FStar_Parser_Parse.NEW)))::(((ALWAYS), ("new_effect"), (FStar_Parser_Parse.NEW_EFFECT)))::(((ALWAYS), ("noextract"), (FStar_Parser_Parse.NOEXTRACT)))::(((ALWAYS), ("of"), (FStar_Parser_Parse.OF)))::(((ALWAYS), ("open"), (FStar_Parser_Parse.OPEN)))::(((ALWAYS), ("opaque"), (FStar_Parser_Parse.OPAQUE)))::(((ALWAYS), ("private"), (FStar_Parser_Parse.PRIVATE)))::(((ALWAYS), ("rec"), (FStar_Parser_Parse.REC)))::(((ALWAYS), ("reifiable"), (FStar_Parser_Parse.REIFIABLE)))::(((ALWAYS), ("reify"), (FStar_Parser_Parse.REIFY)))::(((ALWAYS), ("reflectable"), (FStar_Parser_Parse.REFLECTABLE)))::(((ALWAYS), ("requires"), (FStar_Parser_Parse.REQUIRES)))::(((ALWAYS), ("sub_effect"), (FStar_Parser_Parse.SUB_EFFECT)))::(((ALWAYS), ("then"), (FStar_Parser_Parse.THEN)))::(((ALWAYS), ("total"), (FStar_Parser_Parse.TOTAL)))::(((ALWAYS), ("true"), (FStar_Parser_Parse.TRUE)))::(((ALWAYS), ("True"), (FStar_Parser_Parse.L_TRUE)))::(((ALWAYS), ("try"), (FStar_Parser_Parse.TRY)))::(((ALWAYS), ("type"), (FStar_Parser_Parse.TYPE)))::(((ALWAYS), ("unfold"), (FStar_Parser_Parse.UNFOLD)))::(((ALWAYS), ("unfoldable"), (FStar_Parser_Parse.UNFOLDABLE)))::(((ALWAYS), ("val"), (FStar_Parser_Parse.VAL)))::(((ALWAYS), ("when"), (FStar_Parser_Parse.WHEN)))::(((ALWAYS), ("with"), (FStar_Parser_Parse.WITH)))::(((ALWAYS), ("_"), (FStar_Parser_Parse.UNDERSCORE)))::[]


let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun uu____668 -> (match (uu____668) with
| (uu____675, w, uu____677) -> begin
w
end)) keywords)


let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun uu____690 -> (match (uu____690) with
| (mode, keyword, uu____701) -> begin
(match ((mode = FSHARP)) with
| true -> begin
FStar_Pervasives_Native.Some (keyword)
end
| uu____704 -> begin
FStar_Pervasives_Native.None
end)
end)) keywords)


let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (

let tab = (FStar_Util.smap_create (Prims.parse_int "1000"))
in ((FStar_List.iter (fun uu____721 -> (match (uu____721) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords);
tab;
))


let kwd : Prims.string  ->  FStar_Parser_Parse.token FStar_Pervasives_Native.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; filename : Prims.string; contents : Prims.string}


let __proj__Mklexargs__item__getSourceDirectory : lexargs  ->  Prims.unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {getSourceDirectory = __fname__getSourceDirectory; filename = __fname__filename; contents = __fname__contents} -> begin
__fname__getSourceDirectory
end))


let __proj__Mklexargs__item__filename : lexargs  ->  Prims.string = (fun projectee -> (match (projectee) with
| {getSourceDirectory = __fname__getSourceDirectory; filename = __fname__filename; contents = __fname__contents} -> begin
__fname__filename
end))


let __proj__Mklexargs__item__contents : lexargs  ->  Prims.string = (fun projectee -> (match (projectee) with
| {getSourceDirectory = __fname__getSourceDirectory; filename = __fname__filename; contents = __fname__contents} -> begin
__fname__contents
end))


let mkLexargs : ((Prims.unit  ->  Prims.string) * Prims.string * Prims.string)  ->  lexargs = (fun uu____797 -> (match (uu____797) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; filename = filename; contents = contents}
end))


let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (

let uu____825 = (kwd s)
in (match (uu____825) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(

let uu____829 = (

let uu____830 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes uu____830))
in FStar_Parser_Parse.STRING (uu____829))
end
| "__SOURCE_FILE__" -> begin
(

let uu____831 = (

let uu____832 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes uu____832))
in FStar_Parser_Parse.STRING (uu____831))
end
| "__LINE__" -> begin
(

let uu____833 = (

let uu____838 = (

let uu____839 = (

let uu____840 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos uu____840))
in (FStar_All.pipe_left FStar_Util.string_of_int uu____839))
in ((uu____838), (false)))
in FStar_Parser_Parse.INT (uu____833))
end
| uu____841 -> begin
(match ((FStar_Util.starts_with s FStar_Ident.reserved_prefix)) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier")), (r)))))
end
| uu____842 -> begin
(

let uu____843 = (intern_string s)
in FStar_Parser_Parse.IDENT (uu____843))
end)
end)
end)))




