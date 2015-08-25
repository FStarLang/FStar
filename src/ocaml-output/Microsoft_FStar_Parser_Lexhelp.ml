
let intern_string = (let strings = (Microsoft_FStar_Util.smap_create 100)
in (fun s -> (match ((Microsoft_FStar_Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(let _45_6 = (Microsoft_FStar_Util.smap_add strings s s)
in s)
end)))

let default_string_finish = (fun endm b s -> Microsoft_FStar_Parser_Parse.STRING (s))

let call_string_finish = (fun fin buf endm b -> (let _111_19 = (Microsoft_FStar_Bytes.close buf)
in (fin endm b _111_19)))

let add_string = (fun buf x -> (let _111_24 = (Microsoft_FStar_Bytes.string_as_unicode_bytes x)
in (Microsoft_FStar_Bytes.emit_bytes buf _111_24)))

let add_int_char = (fun buf c -> (let _45_19 = (Microsoft_FStar_Bytes.emit_int_as_byte buf (Prims.op_Modulus c 256))
in (Microsoft_FStar_Bytes.emit_int_as_byte buf (c / 256))))

let add_unichar = (fun buf c -> (add_int_char buf c))

let add_byte_char = (fun buf c -> (add_int_char buf (Prims.op_Modulus (Microsoft_FStar_Util.int_of_char c) 256)))

let stringbuf_as_bytes = (fun buf -> (let bytes = (Microsoft_FStar_Bytes.close buf)
in (let _111_40 = ((Microsoft_FStar_Bytes.length bytes) / 2)
in (Microsoft_FStar_Bytes.make (fun i -> (Microsoft_FStar_Bytes.get bytes (i * 2))) _111_40))))

let stringbuf_is_bytes = (fun buf -> (let bytes = (Microsoft_FStar_Bytes.close buf)
in (let ok = (Microsoft_FStar_Util.mk_ref true)
in (let _45_32 = (let _111_44 = (((Microsoft_FStar_Bytes.length bytes) / 2) - 1)
in (Microsoft_FStar_Util.for_range 0 _111_44 (fun i -> (match (((Microsoft_FStar_Bytes.get bytes ((i * 2) + 1)) <> 0)) with
| true -> begin
(ST.op_Colon_Equals ok false)
end
| false -> begin
()
end))))
in (ST.read ok)))))

let trigraph = (fun c1 c2 c3 -> (let digit = (fun c -> ((Microsoft_FStar_Util.int_of_char c) - (Microsoft_FStar_Util.int_of_char '0')))
in (Microsoft_FStar_Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

let digit = (fun d -> (let dd = (Microsoft_FStar_Util.int_of_char d)
in (match (((dd >= (Microsoft_FStar_Util.int_of_char '0')) && (dd <= (Microsoft_FStar_Util.int_of_char '9')))) with
| true -> begin
((Microsoft_FStar_Util.int_of_char d) - (Microsoft_FStar_Util.int_of_char '0'))
end
| false -> begin
(All.failwith "digit")
end)))

let hexdigit = (fun d -> (let dd = (Microsoft_FStar_Util.int_of_char d)
in (match (((dd >= (Microsoft_FStar_Util.int_of_char '0')) && (dd <= (Microsoft_FStar_Util.int_of_char '9')))) with
| true -> begin
(digit d)
end
| false -> begin
(match (((dd >= (Microsoft_FStar_Util.int_of_char 'a')) && (dd <= (Microsoft_FStar_Util.int_of_char 'f')))) with
| true -> begin
((dd - (Microsoft_FStar_Util.int_of_char 'a')) + 10)
end
| false -> begin
(match (((dd >= (Microsoft_FStar_Util.int_of_char 'A')) && (dd <= (Microsoft_FStar_Util.int_of_char 'F')))) with
| true -> begin
((dd - (Microsoft_FStar_Util.int_of_char 'A')) + 10)
end
| false -> begin
(All.failwith "hexdigit")
end)
end)
end)))

let unicodegraph_short = (fun s -> (match (((Microsoft_FStar_String.length s) <> 4)) with
| true -> begin
(All.failwith "unicodegraph")
end
| false -> begin
(let _111_63 = (((let _111_59 = (Microsoft_FStar_Util.char_at s 0)
in (hexdigit _111_59)) * 4096) + (((let _111_60 = (Microsoft_FStar_Util.char_at s 1)
in (hexdigit _111_60)) * 256) + (((let _111_61 = (Microsoft_FStar_Util.char_at s 2)
in (hexdigit _111_61)) * 16) + (let _111_62 = (Microsoft_FStar_Util.char_at s 3)
in (hexdigit _111_62)))))
in (Microsoft_FStar_Util.uint16_of_int _111_63))
end))

let hexgraph_short = (fun s -> (match (((Microsoft_FStar_String.length s) <> 2)) with
| true -> begin
(All.failwith "hexgraph")
end
| false -> begin
(let _111_68 = (((let _111_66 = (Microsoft_FStar_Util.char_at s 0)
in (hexdigit _111_66)) * 16) + (let _111_67 = (Microsoft_FStar_Util.char_at s 1)
in (hexdigit _111_67)))
in (Microsoft_FStar_Util.uint16_of_int _111_68))
end))

let unicodegraph_long = (fun s -> (match (((Microsoft_FStar_String.length s) <> 8)) with
| true -> begin
(All.failwith "unicodegraph_long")
end
| false -> begin
(let high = (((let _111_71 = (Microsoft_FStar_Util.char_at s 0)
in (hexdigit _111_71)) * 4096) + (((let _111_72 = (Microsoft_FStar_Util.char_at s 1)
in (hexdigit _111_72)) * 256) + (((let _111_73 = (Microsoft_FStar_Util.char_at s 2)
in (hexdigit _111_73)) * 16) + (let _111_74 = (Microsoft_FStar_Util.char_at s 3)
in (hexdigit _111_74)))))
in (let low = (((let _111_75 = (Microsoft_FStar_Util.char_at s 4)
in (hexdigit _111_75)) * 4096) + (((let _111_76 = (Microsoft_FStar_Util.char_at s 5)
in (hexdigit _111_76)) * 256) + (((let _111_77 = (Microsoft_FStar_Util.char_at s 6)
in (hexdigit _111_77)) * 16) + (let _111_78 = (Microsoft_FStar_Util.char_at s 7)
in (hexdigit _111_78)))))
in (match ((high = 0)) with
| true -> begin
(None, (Microsoft_FStar_Util.uint16_of_int low))
end
| false -> begin
(Some ((Microsoft_FStar_Util.uint16_of_int (55296 + (((high * 65536) + (low - 65536)) / 1024)))), (Microsoft_FStar_Util.uint16_of_int (57136 + (Prims.op_Modulus ((high * 65536) + (low - 65536)) 1024))))
end)))
end))

let escape = (fun c -> (match (c) with
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
| ALWAYS -> begin
true
end
| _ -> begin
false
end))

let is_FSHARP = (fun _discr_ -> (match (_discr_) with
| FSHARP -> begin
true
end
| _ -> begin
false
end))

let keywords = (let _111_84 = (Microsoft_FStar_List.map (fun s -> (FSHARP, s, Microsoft_FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[]))
in (Microsoft_FStar_List.append (((ALWAYS, "and", Microsoft_FStar_Parser_Parse.AND))::((ALWAYS, "as", Microsoft_FStar_Parser_Parse.AS))::((ALWAYS, "assert", Microsoft_FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", Microsoft_FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", Microsoft_FStar_Parser_Parse.BEGIN))::((FSHARP, "default", Microsoft_FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", Microsoft_FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", Microsoft_FStar_Parser_Parse.ELSE))::((ALWAYS, "end", Microsoft_FStar_Parser_Parse.END))::((ALWAYS, "ensures", Microsoft_FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", Microsoft_FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", Microsoft_FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", Microsoft_FStar_Parser_Parse.FALSE))::((ALWAYS, "finally", Microsoft_FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", Microsoft_FStar_Parser_Parse.FOR))::((ALWAYS, "forall", Microsoft_FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", Microsoft_FStar_Parser_Parse.FUN))::((ALWAYS, "function", Microsoft_FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", Microsoft_FStar_Parser_Parse.IF))::((ALWAYS, "in", Microsoft_FStar_Parser_Parse.IN))::((ALWAYS, "lazy", Microsoft_FStar_Parser_Parse.LAZY))::((ALWAYS, "let", Microsoft_FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", Microsoft_FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", Microsoft_FStar_Parser_Parse.MATCH))::((ALWAYS, "module", Microsoft_FStar_Parser_Parse.MODULE))::((ALWAYS, "of", Microsoft_FStar_Parser_Parse.OF))::((ALWAYS, "open", Microsoft_FStar_Parser_Parse.OPEN))::((ALWAYS, "or", Microsoft_FStar_Parser_Parse.OR))::((ALWAYS, "opaque", Microsoft_FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", Microsoft_FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", Microsoft_FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", Microsoft_FStar_Parser_Parse.REC))::((ALWAYS, "requires", Microsoft_FStar_Parser_Parse.REQUIRES))::((ALWAYS, "then", Microsoft_FStar_Parser_Parse.THEN))::((ALWAYS, "to", Microsoft_FStar_Parser_Parse.TO))::((ALWAYS, "true", Microsoft_FStar_Parser_Parse.TRUE))::((ALWAYS, "try", Microsoft_FStar_Parser_Parse.TRY))::((ALWAYS, "type", Microsoft_FStar_Parser_Parse.TYPE))::((ALWAYS, "val", Microsoft_FStar_Parser_Parse.VAL))::((ALWAYS, "when", Microsoft_FStar_Parser_Parse.WHEN))::((ALWAYS, "with", Microsoft_FStar_Parser_Parse.WITH))::((ALWAYS, "new_effect", Microsoft_FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "sub_effect", Microsoft_FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "total", Microsoft_FStar_Parser_Parse.TOTAL))::((ALWAYS, "kind", Microsoft_FStar_Parser_Parse.KIND))::((ALWAYS, "_", Microsoft_FStar_Parser_Parse.UNDERSCORE))::[]) _111_84))

let stringKeywords = (Microsoft_FStar_List.map (fun _45_62 -> (match (_45_62) with
| (_45_58, w, _45_61) -> begin
w
end)) keywords)

let unreserve_words = (Microsoft_FStar_List.choose (fun _45_67 -> (match (_45_67) with
| (mode, keyword, _45_66) -> begin
(match ((mode = FSHARP)) with
| true -> begin
Some (keyword)
end
| false -> begin
None
end)
end)) keywords)

let kwd_table = (let tab = (Microsoft_FStar_Util.smap_create 1000)
in (let _45_73 = (Microsoft_FStar_List.iter (fun _45_72 -> (match (_45_72) with
| (mode, keyword, token) -> begin
(Microsoft_FStar_Util.smap_add tab keyword token)
end)) keywords)
in tab))

let kwd = (fun s -> (Microsoft_FStar_Util.smap_try_find kwd_table s))

exception ReservedKeyword of ((Prims.string * Microsoft_FStar_Range.range))

let is_ReservedKeyword = (fun _discr_ -> (match (_discr_) with
| ReservedKeyword (_) -> begin
true
end
| _ -> begin
false
end))

let ___ReservedKeyword____0 = (fun projectee -> (match (projectee) with
| ReservedKeyword (_45_77) -> begin
_45_77
end))

exception IndentationProblem of ((Prims.string * Microsoft_FStar_Range.range))

let is_IndentationProblem = (fun _discr_ -> (match (_discr_) with
| IndentationProblem (_) -> begin
true
end
| _ -> begin
false
end))

let ___IndentationProblem____0 = (fun projectee -> (match (projectee) with
| IndentationProblem (_45_79) -> begin
_45_79
end))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; contents : Prims.string}

let is_Mklexargs = (fun _ -> (All.failwith "Not yet implemented:is_Mklexargs"))

let mkLexargs = (fun _45_86 -> (match (_45_86) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

let kwd_or_id = (fun args r s -> (match ((kwd s)) with
| Some (v) -> begin
(match ((v = Microsoft_FStar_Parser_Parse.RESERVED)) with
| true -> begin
(let _45_92 = (let _111_127 = (let _111_126 = (Microsoft_FStar_Range.string_of_range r)
in (Microsoft_FStar_Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s _111_126))
in (Microsoft_FStar_Util.print_string _111_127))
in (let _111_128 = (intern_string s)
in Microsoft_FStar_Parser_Parse.IDENT (_111_128)))
end
| false -> begin
v
end)
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _111_130 = (let _111_129 = (args.getSourceDirectory ())
in (Microsoft_FStar_Bytes.string_as_unicode_bytes _111_129))
in Microsoft_FStar_Parser_Parse.STRING (_111_130))
end
| "__SOURCE_FILE__" -> begin
(let _111_132 = (let _111_131 = (Microsoft_FStar_Range.file_of_range r)
in (Microsoft_FStar_Bytes.string_as_unicode_bytes _111_131))
in Microsoft_FStar_Parser_Parse.STRING (_111_132))
end
| "__LINE__" -> begin
(let _111_136 = (let _111_135 = (let _111_134 = (let _111_133 = (Microsoft_FStar_Range.start_of_range r)
in (Microsoft_FStar_Range.line_of_pos _111_133))
in (All.pipe_left Microsoft_FStar_Util.string_of_int _111_134))
in (_111_135, false))
in Microsoft_FStar_Parser_Parse.INT (_111_136))
end
| _45_99 -> begin
(let _111_137 = (intern_string s)
in Microsoft_FStar_Parser_Parse.IDENT (_111_137))
end)
end))




