
open Prims
# 38 "FStar.Parser.Lexhelp.fst"
let intern_string : Prims.string  ->  Prims.string = (
# 41 "FStar.Parser.Lexhelp.fst"
let strings = (FStar_Util.smap_create 100)
in (fun s -> (match ((FStar_Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(
# 45 "FStar.Parser.Lexhelp.fst"
let _65_6 = (FStar_Util.smap_add strings s s)
in s)
end)))

# 45 "FStar.Parser.Lexhelp.fst"
let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))

# 47 "FStar.Parser.Lexhelp.fst"
let call_string_finish = (fun fin buf endm b -> (let _154_19 = (FStar_Bytes.close buf)
in (fin endm b _154_19)))

# 49 "FStar.Parser.Lexhelp.fst"
let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (let _154_24 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf _154_24)))

# 51 "FStar.Parser.Lexhelp.fst"
let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (
# 54 "FStar.Parser.Lexhelp.fst"
let _65_19 = (FStar_Bytes.emit_int_as_byte buf (c % 256))
in (FStar_Bytes.emit_int_as_byte buf (c / 256))))

# 55 "FStar.Parser.Lexhelp.fst"
let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))

# 57 "FStar.Parser.Lexhelp.fst"
let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) % 256)))

# 58 "FStar.Parser.Lexhelp.fst"
let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (
# 66 "FStar.Parser.Lexhelp.fst"
let bytes = (FStar_Bytes.close buf)
in (let _154_40 = ((FStar_Bytes.length bytes) / 2)
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (i * 2))) _154_40))))

# 67 "FStar.Parser.Lexhelp.fst"
let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (
# 71 "FStar.Parser.Lexhelp.fst"
let bytes = (FStar_Bytes.close buf)
in (
# 72 "FStar.Parser.Lexhelp.fst"
let ok = (FStar_Util.mk_ref true)
in (
# 73 "FStar.Parser.Lexhelp.fst"
let _65_32 = (let _154_44 = (((FStar_Bytes.length bytes) / 2) - 1)
in (FStar_Util.for_range 0 _154_44 (fun i -> if ((FStar_Bytes.get bytes ((i * 2) + 1)) <> 0) then begin
(FStar_ST.op_Colon_Equals ok false)
end else begin
()
end)))
in (FStar_ST.read ok)))))

# 77 "FStar.Parser.Lexhelp.fst"
let trigraph : FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char = (fun c1 c2 c3 -> (
# 80 "FStar.Parser.Lexhelp.fst"
let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

# 81 "FStar.Parser.Lexhelp.fst"
let digit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (
# 84 "FStar.Parser.Lexhelp.fst"
let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end else begin
(FStar_All.failwith "digit")
end))

# 86 "FStar.Parser.Lexhelp.fst"
let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (
# 89 "FStar.Parser.Lexhelp.fst"
let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
(digit d)
end else begin
if ((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f'))) then begin
((dd - (FStar_Util.int_of_char 'a')) + 10)
end else begin
if ((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F'))) then begin
((dd - (FStar_Util.int_of_char 'A')) + 10)
end else begin
(FStar_All.failwith "hexdigit")
end
end
end))

# 93 "FStar.Parser.Lexhelp.fst"
let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> if ((FStar_String.length s) <> 4) then begin
(FStar_All.failwith "unicodegraph")
end else begin
(let _154_63 = (((let _154_59 = (FStar_Util.char_at s 0)
in (hexdigit _154_59)) * 4096) + (((let _154_60 = (FStar_Util.char_at s 1)
in (hexdigit _154_60)) * 256) + (((let _154_61 = (FStar_Util.char_at s 2)
in (hexdigit _154_61)) * 16) + (let _154_62 = (FStar_Util.char_at s 3)
in (hexdigit _154_62)))))
in (FStar_Util.uint16_of_int _154_63))
end)

# 98 "FStar.Parser.Lexhelp.fst"
let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> if ((FStar_String.length s) <> 2) then begin
(FStar_All.failwith "hexgraph")
end else begin
(let _154_68 = (((let _154_66 = (FStar_Util.char_at s 0)
in (hexdigit _154_66)) * 16) + (let _154_67 = (FStar_Util.char_at s 1)
in (hexdigit _154_67)))
in (FStar_Util.uint16_of_int _154_68))
end)

# 103 "FStar.Parser.Lexhelp.fst"
let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 Prims.option * FStar_BaseTypes.uint16) = (fun s -> if ((FStar_String.length s) <> 8) then begin
(FStar_All.failwith "unicodegraph_long")
end else begin
(
# 109 "FStar.Parser.Lexhelp.fst"
let high = (((let _154_71 = (FStar_Util.char_at s 0)
in (hexdigit _154_71)) * 4096) + (((let _154_72 = (FStar_Util.char_at s 1)
in (hexdigit _154_72)) * 256) + (((let _154_73 = (FStar_Util.char_at s 2)
in (hexdigit _154_73)) * 16) + (let _154_74 = (FStar_Util.char_at s 3)
in (hexdigit _154_74)))))
in (
# 110 "FStar.Parser.Lexhelp.fst"
let low = (((let _154_75 = (FStar_Util.char_at s 4)
in (hexdigit _154_75)) * 4096) + (((let _154_76 = (FStar_Util.char_at s 5)
in (hexdigit _154_76)) * 256) + (((let _154_77 = (FStar_Util.char_at s 6)
in (hexdigit _154_77)) * 16) + (let _154_78 = (FStar_Util.char_at s 7)
in (hexdigit _154_78)))))
in if (high = 0) then begin
(None, (FStar_Util.uint16_of_int low))
end else begin
(Some ((FStar_Util.uint16_of_int (0xD800 + (((high * 0x10000) + (low - 0x10000)) / 0x400)))), (FStar_Util.uint16_of_int (0xDF30 + (((high * 0x10000) + (low - 0x10000)) % 0x400))))
end))
end)

# 115 "FStar.Parser.Lexhelp.fst"
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

# 125 "FStar.Parser.Lexhelp.fst"
type compatibilityMode =
| ALWAYS
| FSHARP

# 132 "FStar.Parser.Lexhelp.fst"
let is_ALWAYS = (fun _discr_ -> (match (_discr_) with
| ALWAYS (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.Parser.Lexhelp.fst"
let is_FSHARP = (fun _discr_ -> (match (_discr_) with
| FSHARP (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.Parser.Lexhelp.fst"
let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (let _154_84 = (FStar_List.map (fun s -> (FSHARP, s, FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[]))
in (FStar_List.append (((ALWAYS, "abstract", FStar_Parser_Parse.ABSTRACT))::((ALWAYS, "and", FStar_Parser_Parse.AND))::((ALWAYS, "as", FStar_Parser_Parse.AS))::((ALWAYS, "assert", FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", FStar_Parser_Parse.BEGIN))::((FSHARP, "default", FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", FStar_Parser_Parse.ELSE))::((ALWAYS, "end", FStar_Parser_Parse.END))::((ALWAYS, "ensures", FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", FStar_Parser_Parse.FALSE))::((ALWAYS, "False", FStar_Parser_Parse.L_FALSE))::((ALWAYS, "finally", FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", FStar_Parser_Parse.FOR))::((ALWAYS, "forall", FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", FStar_Parser_Parse.FUN))::((ALWAYS, "function", FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", FStar_Parser_Parse.IF))::((ALWAYS, "kind", FStar_Parser_Parse.KIND))::((ALWAYS, "in", FStar_Parser_Parse.IN))::((ALWAYS, "inline", FStar_Parser_Parse.INLINE))::((ALWAYS, "irreducible", FStar_Parser_Parse.IRREDUCIBLE))::((ALWAYS, "lazy", FStar_Parser_Parse.LAZY))::((ALWAYS, "let", FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", FStar_Parser_Parse.MATCH))::((ALWAYS, "module", FStar_Parser_Parse.MODULE))::((ALWAYS, "new", FStar_Parser_Parse.NEW))::((ALWAYS, "new_effect", FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "new_effect_for_free", FStar_Parser_Parse.NEW_EFFECT_FOR_FREE))::((ALWAYS, "of", FStar_Parser_Parse.OF))::((ALWAYS, "open", FStar_Parser_Parse.OPEN))::((ALWAYS, "or", FStar_Parser_Parse.OR))::((ALWAYS, "opaque", FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", FStar_Parser_Parse.REC))::((ALWAYS, "requires", FStar_Parser_Parse.REQUIRES))::((ALWAYS, "sub_effect", FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "then", FStar_Parser_Parse.THEN))::((ALWAYS, "to", FStar_Parser_Parse.TO))::((ALWAYS, "total", FStar_Parser_Parse.TOTAL))::((ALWAYS, "true", FStar_Parser_Parse.TRUE))::((ALWAYS, "True", FStar_Parser_Parse.L_TRUE))::((ALWAYS, "try", FStar_Parser_Parse.TRY))::((ALWAYS, "type", FStar_Parser_Parse.TYPE))::((ALWAYS, "unfoldable", FStar_Parser_Parse.UNFOLDABLE))::((ALWAYS, "val", FStar_Parser_Parse.VAL))::((ALWAYS, "when", FStar_Parser_Parse.WHEN))::((ALWAYS, "with", FStar_Parser_Parse.WITH))::((ALWAYS, "_", FStar_Parser_Parse.UNDERSCORE))::[]) _154_84))

# 202 "FStar.Parser.Lexhelp.fst"
let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun _65_62 -> (match (_65_62) with
| (_65_58, w, _65_61) -> begin
w
end)) keywords)

# 203 "FStar.Parser.Lexhelp.fst"
let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun _65_67 -> (match (_65_67) with
| (mode, keyword, _65_66) -> begin
if (mode = FSHARP) then begin
Some (keyword)
end else begin
None
end
end)) keywords)

# 210 "FStar.Parser.Lexhelp.fst"
let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (
# 213 "FStar.Parser.Lexhelp.fst"
let tab = (FStar_Util.smap_create 1000)
in (
# 214 "FStar.Parser.Lexhelp.fst"
let _65_73 = (FStar_List.iter (fun _65_72 -> (match (_65_72) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords)
in tab))

# 215 "FStar.Parser.Lexhelp.fst"
let kwd : Prims.string  ->  FStar_Parser_Parse.token Prims.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

# 217 "FStar.Parser.Lexhelp.fst"
exception ReservedKeyword of ((Prims.string * FStar_Range.range))

# 217 "FStar.Parser.Lexhelp.fst"
let is_ReservedKeyword = (fun _discr_ -> (match (_discr_) with
| ReservedKeyword (_) -> begin
true
end
| _ -> begin
false
end))

# 217 "FStar.Parser.Lexhelp.fst"
let ___ReservedKeyword____0 = (fun projectee -> (match (projectee) with
| ReservedKeyword (_65_77) -> begin
_65_77
end))

# 218 "FStar.Parser.Lexhelp.fst"
exception IndentationProblem of ((Prims.string * FStar_Range.range))

# 218 "FStar.Parser.Lexhelp.fst"
let is_IndentationProblem = (fun _discr_ -> (match (_discr_) with
| IndentationProblem (_) -> begin
true
end
| _ -> begin
false
end))

# 218 "FStar.Parser.Lexhelp.fst"
let ___IndentationProblem____0 = (fun projectee -> (match (projectee) with
| IndentationProblem (_65_79) -> begin
_65_79
end))

# 218 "FStar.Parser.Lexhelp.fst"
type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; contents : Prims.string}

# 220 "FStar.Parser.Lexhelp.fst"
let is_Mklexargs : lexargs  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklexargs"))))

# 223 "FStar.Parser.Lexhelp.fst"
let mkLexargs = (fun _65_86 -> (match (_65_86) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

# 228 "FStar.Parser.Lexhelp.fst"
let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (match ((kwd s)) with
| Some (v) -> begin
if (v = FStar_Parser_Parse.RESERVED) then begin
(
# 235 "FStar.Parser.Lexhelp.fst"
let _65_92 = (let _154_127 = (let _154_126 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s _154_126))
in (FStar_Util.print_string _154_127))
in (let _154_128 = (intern_string s)
in FStar_Parser_Parse.IDENT (_154_128)))
end else begin
v
end
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _154_130 = (let _154_129 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes _154_129))
in FStar_Parser_Parse.STRING (_154_130))
end
| "__SOURCE_FILE__" -> begin
(let _154_132 = (let _154_131 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes _154_131))
in FStar_Parser_Parse.STRING (_154_132))
end
| "__LINE__" -> begin
(let _154_136 = (let _154_135 = (let _154_134 = (let _154_133 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos _154_133))
in (FStar_All.pipe_left FStar_Util.string_of_int _154_134))
in (_154_135, false))
in FStar_Parser_Parse.INT (_154_136))
end
| _65_99 -> begin
if (FStar_Util.starts_with s FStar_Ident.reserved_prefix) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier"), r))))
end else begin
(let _154_137 = (intern_string s)
in FStar_Parser_Parse.IDENT (_154_137))
end
end)
end))




