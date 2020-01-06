
open Prims
open FStar_Pervasives

type position =
(Prims.string * Prims.int * Prims.int)

type sl_reponse =
{slr_name : Prims.string; slr_def_range : FStar_Range.range FStar_Pervasives_Native.option; slr_typ : Prims.string FStar_Pervasives_Native.option; slr_doc : Prims.string FStar_Pervasives_Native.option; slr_def : Prims.string FStar_Pervasives_Native.option}


let __proj__Mksl_reponse__item__slr_name : sl_reponse  ->  Prims.string = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_name
end))


let __proj__Mksl_reponse__item__slr_def_range : sl_reponse  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_def_range
end))


let __proj__Mksl_reponse__item__slr_typ : sl_reponse  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_typ
end))


let __proj__Mksl_reponse__item__slr_doc : sl_reponse  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_doc
end))


let __proj__Mksl_reponse__item__slr_def : sl_reponse  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_def
end))


let with_printed_effect_args : 'Auu____194 . (unit  ->  'Auu____194)  ->  'Auu____194 = (fun k -> (FStar_Options.with_saved_options (fun uu____207 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____225 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____235 -> (FStar_Syntax_Print.sigelt_to_string se))))


let symlookup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  position FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  sl_reponse FStar_Pervasives_Native.option = (fun tcenv symbol pos_opt requested_info -> (

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____293 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____293))
in (

let lid1 = (

let uu____299 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____299))
in (

let uu____304 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____304 (FStar_Util.map_option (fun uu____361 -> (match (uu____361) with
| ((uu____381, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____403 = (FStar_Syntax_DsEnv.try_lookup_doc tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____403 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____469 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____469 (fun uu___0_514 -> (match (uu___0_514) with
| (FStar_Util.Inr (se, uu____537), uu____538) -> begin
(

let uu____567 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____567))
end
| uu____570 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____619 -> (match (uu____619) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____669) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____730 -> begin
(info_of_lid_str symbol)
end)
end)
in (match (info_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name_or_lid, typ, rng) -> begin
(

let name = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
name
end
| FStar_Util.Inr (lid) -> begin
(FStar_Ident.string_of_lid lid)
end)
in (

let typ_str = (match ((FStar_List.mem "type" requested_info)) with
| true -> begin
(

let uu____787 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____787))
end
| uu____790 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____804 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____822 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range1 = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____837 -> begin
FStar_Pervasives_Native.None
end)
in FStar_Pervasives_Native.Some ({slr_name = name; slr_def_range = def_range1; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}))))))
end)))))))


let mod_filter : 'Auu____844 . ('Auu____844 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____844 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___1_859 -> (match (uu___1_859) with
| (uu____864, FStar_Interactive_CompletionTable.Namespace (uu____865)) -> begin
FStar_Pervasives_Native.None
end
| (uu____870, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____871; FStar_Interactive_CompletionTable.mod_path = uu____872; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____882 = (

let uu____887 = (

let uu____888 = (

let uu___99_889 = md
in (

let uu____890 = (

let uu____892 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.op_Hat uu____892 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____890; FStar_Interactive_CompletionTable.mod_path = uu___99_889.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___99_889.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____888))
in ((pth), (uu____887)))
in FStar_Pervasives_Native.Some (uu____882))
end))


let ck_completion : FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.FStar_Interactive_JsonHelper.repl_names needle mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.FStar_Interactive_JsonHelper.repl_names needle)
in (FStar_List.append lids mods_and_nss)))))


let deflookup : FStar_TypeChecker_Env.env  ->  FStar_Interactive_JsonHelper.txdoc_pos  ->  FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option = (fun env pos -> (

let uu____942 = (

let uu____945 = (

let uu____948 = (FStar_Interactive_JsonHelper.pos_munge pos)
in FStar_Pervasives_Native.Some (uu____948))
in (symlookup env "" uu____945 (("defined-at")::[])))
in (match (uu____942) with
| FStar_Pervasives_Native.Some ({slr_name = uu____955; slr_def_range = FStar_Pervasives_Native.Some (r); slr_typ = uu____957; slr_doc = uu____958; slr_def = uu____959}) -> begin
(

let uu____970 = (FStar_Interactive_JsonHelper.js_loclink r)
in (FStar_Interactive_JsonHelper.resultResponse uu____970))
end
| uu____971 -> begin
FStar_Interactive_JsonHelper.nullResponse
end)))


let hoverlookup : FStar_TypeChecker_Env.env  ->  FStar_Interactive_JsonHelper.txdoc_pos  ->  FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option = (fun env pos -> (

let uu____989 = (

let uu____992 = (

let uu____995 = (FStar_Interactive_JsonHelper.pos_munge pos)
in FStar_Pervasives_Native.Some (uu____995))
in (symlookup env "" uu____992 (("type")::("definition")::[])))
in (match (uu____989) with
| FStar_Pervasives_Native.Some ({slr_name = n1; slr_def_range = uu____1005; slr_typ = FStar_Pervasives_Native.Some (t); slr_doc = uu____1007; slr_def = FStar_Pervasives_Native.Some (d)}) -> begin
(

let hovertxt = (FStar_Util.format2 "```fstar\n%s\n````\n---\n```fstar\n%s\n```" t d)
in (FStar_Interactive_JsonHelper.resultResponse (FStar_Util.JsonAssoc (((("contents"), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("markdown"))))::((("value"), (FStar_Util.JsonStr (hovertxt))))::[]))))::[]))))
end
| uu____1054 -> begin
FStar_Interactive_JsonHelper.nullResponse
end)))


let complookup : FStar_Interactive_JsonHelper.repl_state  ->  FStar_Interactive_JsonHelper.txdoc_pos  ->  FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option = (fun st pos -> (

let uu____1072 = (FStar_Interactive_JsonHelper.pos_munge pos)
in (match (uu____1072) with
| (file, row, current_col) -> begin
(

let uu____1093 = (FStar_Parser_ParseIt.read_vfs_entry file)
in (match (uu____1093) with
| FStar_Pervasives_Native.Some (uu____1103, text) -> begin
(

let rec find_col = (fun l -> (match (l) with
| [] -> begin
(Prims.parse_int "0")
end
| (h)::t -> begin
(match (((Prims.op_Equality h 32 (* *)) && ((FStar_List.length t) < current_col))) with
| true -> begin
((FStar_List.length t) + (Prims.parse_int "1"))
end
| uu____1142 -> begin
(find_col t)
end)
end))
in (

let str = (FStar_List.nth (FStar_Util.splitlines text) (row - (Prims.parse_int "1")))
in (

let explode = (fun s -> (

let rec exp = (fun i l -> (match ((i < (Prims.parse_int "0"))) with
| true -> begin
l
end
| uu____1186 -> begin
(

let uu____1188 = (

let uu____1192 = (FStar_String.get s i)
in (uu____1192)::l)
in (exp (i - (Prims.parse_int "1")) uu____1188))
end))
in (exp ((FStar_String.length s) - (Prims.parse_int "1")) [])))
in (

let begin_col = (

let uu____1200 = (

let uu____1204 = (explode str)
in (FStar_List.rev uu____1204))
in (find_col uu____1200))
in (

let term = (FStar_Util.substring str begin_col (current_col - begin_col))
in (

let items = (ck_completion st term)
in (

let l = (FStar_List.map (fun r -> FStar_Util.JsonAssoc (((("label"), (FStar_Util.JsonStr (r.FStar_Interactive_CompletionTable.completion_candidate))))::[])) items)
in (FStar_Interactive_JsonHelper.resultResponse (FStar_Util.JsonList (l))))))))))
end))
end)))




