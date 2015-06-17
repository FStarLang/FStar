
let intern_string = (let strings = (Support.Microsoft.FStar.Util.smap_create 100)
in (fun s -> (match ((Support.Microsoft.FStar.Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(let _414667 = (Support.Microsoft.FStar.Util.smap_add strings s s)
in s)
end)))

let default_string_finish = (fun endm b s -> Microsoft_FStar_Parser_Parse.STRING (s))

let call_string_finish = (fun fin buf endm b -> (fin endm b (Support.Microsoft.FStar.Bytes.close buf)))

let add_string = (fun buf x -> (Support.Microsoft.FStar.Bytes.emit_bytes buf (Support.Microsoft.FStar.Bytes.string_as_unicode_bytes x)))

let add_int_char = (fun buf c -> (let _414680 = (Support.Microsoft.FStar.Bytes.emit_int_as_byte buf (c mod 256))
in (Support.Microsoft.FStar.Bytes.emit_int_as_byte buf (c / 256))))

let add_unichar = (fun buf c -> (add_int_char buf c))

let add_byte_char = (fun buf c -> (add_int_char buf ((Support.Microsoft.FStar.Util.int_of_char c) mod 256)))

let stringbuf_as_bytes = (fun buf -> (let bytes = (Support.Microsoft.FStar.Bytes.close buf)
in (Support.Microsoft.FStar.Bytes.make (fun i -> (Support.Microsoft.FStar.Bytes.get bytes (i * 2))) ((Support.Microsoft.FStar.Bytes.length bytes) / 2))))

let stringbuf_is_bytes = (fun buf -> (let bytes = (Support.Microsoft.FStar.Bytes.close buf)
in (let ok = (Support.Microsoft.FStar.Util.mk_ref true)
in (let _414693 = (Support.Microsoft.FStar.Util.for_range 0 (((Support.Microsoft.FStar.Bytes.length bytes) / 2) - 1) (fun i -> if ((Support.Microsoft.FStar.Bytes.get bytes ((i * 2) + 1)) <> 0) then begin
(ok := false)
end))
in (! (ok))))))

let trigraph = (fun c1 c2 c3 -> (let digit = (fun c -> ((Support.Microsoft.FStar.Util.int_of_char c) - (Support.Microsoft.FStar.Util.int_of_char '0')))
in (Support.Microsoft.FStar.Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

let digit = (fun d -> (let dd = (Support.Microsoft.FStar.Util.int_of_char d)
in if ((dd >= (Support.Microsoft.FStar.Util.int_of_char '0')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char '9'))) then begin
((Support.Microsoft.FStar.Util.int_of_char d) - (Support.Microsoft.FStar.Util.int_of_char '0'))
end else begin
(failwith "digit")
end))

let hexdigit = (fun d -> (let dd = (Support.Microsoft.FStar.Util.int_of_char d)
in if ((dd >= (Support.Microsoft.FStar.Util.int_of_char '0')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char '9'))) then begin
(digit d)
end else begin
if ((dd >= (Support.Microsoft.FStar.Util.int_of_char 'a')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char 'f'))) then begin
((dd - (Support.Microsoft.FStar.Util.int_of_char 'a')) + 10)
end else begin
if ((dd >= (Support.Microsoft.FStar.Util.int_of_char 'A')) && (dd <= (Support.Microsoft.FStar.Util.int_of_char 'F'))) then begin
((dd - (Support.Microsoft.FStar.Util.int_of_char 'A')) + 10)
end else begin
(failwith "hexdigit")
end
end
end))

let unicodegraph_short = (fun s -> if ((Support.String.length s) <> 4) then begin
(failwith "unicodegraph")
end else begin
(Support.Microsoft.FStar.Util.uint16_of_int (((hexdigit (Support.Microsoft.FStar.Util.char_at s 0)) * 4096) + (((hexdigit (Support.Microsoft.FStar.Util.char_at s 1)) * 256) + (((hexdigit (Support.Microsoft.FStar.Util.char_at s 2)) * 16) + (hexdigit (Support.Microsoft.FStar.Util.char_at s 3))))))
end)

let hexgraph_short = (fun s -> if ((Support.String.length s) <> 2) then begin
(failwith "hexgraph")
end else begin
(Support.Microsoft.FStar.Util.uint16_of_int (((hexdigit (Support.Microsoft.FStar.Util.char_at s 0)) * 16) + (hexdigit (Support.Microsoft.FStar.Util.char_at s 1))))
end)

let unicodegraph_long = (fun s -> if ((Support.String.length s) <> 8) then begin
(failwith "unicodegraph_long")
end else begin
(let high = (((hexdigit (Support.Microsoft.FStar.Util.char_at s 0)) * 4096) + (((hexdigit (Support.Microsoft.FStar.Util.char_at s 1)) * 256) + (((hexdigit (Support.Microsoft.FStar.Util.char_at s 2)) * 16) + (hexdigit (Support.Microsoft.FStar.Util.char_at s 3)))))
in (let low = (((hexdigit (Support.Microsoft.FStar.Util.char_at s 4)) * 4096) + (((hexdigit (Support.Microsoft.FStar.Util.char_at s 5)) * 256) + (((hexdigit (Support.Microsoft.FStar.Util.char_at s 6)) * 16) + (hexdigit (Support.Microsoft.FStar.Util.char_at s 7)))))
in if (high = 0) then begin
(None, (Support.Microsoft.FStar.Util.uint16_of_int low))
end else begin
(Some ((Support.Microsoft.FStar.Util.uint16_of_int (55296 + (((high * 65536) + (low - 65536)) / 1024)))), (Support.Microsoft.FStar.Util.uint16_of_int (57136 + (((high * 65536) + (low - 65536)) mod 1024))))
end))
end)

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

let keywords = (Support.List.append (((ALWAYS, "and", Microsoft_FStar_Parser_Parse.AND))::((ALWAYS, "as", Microsoft_FStar_Parser_Parse.AS))::((ALWAYS, "assert", Microsoft_FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", Microsoft_FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", Microsoft_FStar_Parser_Parse.BEGIN))::((FSHARP, "default", Microsoft_FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", Microsoft_FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", Microsoft_FStar_Parser_Parse.ELSE))::((ALWAYS, "end", Microsoft_FStar_Parser_Parse.END))::((ALWAYS, "ensures", Microsoft_FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", Microsoft_FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", Microsoft_FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", Microsoft_FStar_Parser_Parse.FALSE))::((ALWAYS, "finally", Microsoft_FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", Microsoft_FStar_Parser_Parse.FOR))::((ALWAYS, "forall", Microsoft_FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", Microsoft_FStar_Parser_Parse.FUN))::((ALWAYS, "function", Microsoft_FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", Microsoft_FStar_Parser_Parse.IF))::((ALWAYS, "in", Microsoft_FStar_Parser_Parse.IN))::((ALWAYS, "lazy", Microsoft_FStar_Parser_Parse.LAZY))::((ALWAYS, "let", Microsoft_FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", Microsoft_FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", Microsoft_FStar_Parser_Parse.MATCH))::((ALWAYS, "module", Microsoft_FStar_Parser_Parse.MODULE))::((ALWAYS, "of", Microsoft_FStar_Parser_Parse.OF))::((ALWAYS, "open", Microsoft_FStar_Parser_Parse.OPEN))::((ALWAYS, "or", Microsoft_FStar_Parser_Parse.OR))::((ALWAYS, "opaque", Microsoft_FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", Microsoft_FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", Microsoft_FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", Microsoft_FStar_Parser_Parse.REC))::((ALWAYS, "requires", Microsoft_FStar_Parser_Parse.REQUIRES))::((ALWAYS, "then", Microsoft_FStar_Parser_Parse.THEN))::((ALWAYS, "to", Microsoft_FStar_Parser_Parse.TO))::((ALWAYS, "true", Microsoft_FStar_Parser_Parse.TRUE))::((ALWAYS, "try", Microsoft_FStar_Parser_Parse.TRY))::((ALWAYS, "type", Microsoft_FStar_Parser_Parse.TYPE))::((ALWAYS, "val", Microsoft_FStar_Parser_Parse.VAL))::((ALWAYS, "when", Microsoft_FStar_Parser_Parse.WHEN))::((ALWAYS, "with", Microsoft_FStar_Parser_Parse.WITH))::((ALWAYS, "new_effect", Microsoft_FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "sub_effect", Microsoft_FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "total", Microsoft_FStar_Parser_Parse.TOTAL))::((ALWAYS, "kind", Microsoft_FStar_Parser_Parse.KIND))::((ALWAYS, "_", Microsoft_FStar_Parser_Parse.UNDERSCORE))::[]) (Support.List.map (fun s -> (FSHARP, s, Microsoft_FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[])))

let stringKeywords = (Support.List.map (fun _414723 -> (match (_414723) with
| (_, w, _) -> begin
w
end)) keywords)

let unreserve_words = (Support.List.choose (fun _414728 -> (match (_414728) with
| (mode, keyword, _) -> begin
if (mode = FSHARP) then begin
Some (keyword)
end else begin
None
end
end)) keywords)

let kwd_table = (let tab = (Support.Microsoft.FStar.Util.smap_create 1000)
in (let _414734 = (Support.List.iter (fun _414733 -> (match (_414733) with
| (mode, keyword, token) -> begin
(Support.Microsoft.FStar.Util.smap_add tab keyword token)
end)) keywords)
in tab))

let kwd = (fun s -> (Support.Microsoft.FStar.Util.smap_try_find kwd_table s))

exception ReservedKeyword of ((string * Support.Microsoft.FStar.Range.range))

exception IndentationProblem of ((string * Support.Microsoft.FStar.Range.range))

type lexargs =
{getSourceDirectory : unit  ->  string; contents : string}

let mkLexargs = (fun _414745 -> (match (_414745) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

let kwd_or_id = (fun args r s -> (match ((kwd s)) with
| Some (v) -> begin
if (v = Microsoft_FStar_Parser_Parse.RESERVED) then begin
(let _414751 = (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s (Support.Microsoft.FStar.Range.string_of_range r)))
in Microsoft_FStar_Parser_Parse.IDENT ((intern_string s)))
end else begin
v
end
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
Microsoft_FStar_Parser_Parse.STRING ((Support.Microsoft.FStar.Bytes.string_as_unicode_bytes (args.getSourceDirectory ())))
end
| "__SOURCE_FILE__" -> begin
Microsoft_FStar_Parser_Parse.STRING ((Support.Microsoft.FStar.Bytes.string_as_unicode_bytes (Support.Microsoft.FStar.Range.file_of_range r)))
end
| "__LINE__" -> begin
Microsoft_FStar_Parser_Parse.INT32 (((Support.Microsoft.FStar.Util.int32_of_int (Support.Microsoft.FStar.Range.line_of_pos (Support.Microsoft.FStar.Range.start_of_range r))), false))
end
| _ -> begin
Microsoft_FStar_Parser_Parse.IDENT ((intern_string s))
end)
end))




