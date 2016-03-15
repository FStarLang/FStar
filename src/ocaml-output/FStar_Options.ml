
open Prims
# 25 "FStar.Options.fst"
type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of Prims.string

# 26 "FStar.Options.fst"
let is_Low = (fun _discr_ -> (match (_discr_) with
| Low (_) -> begin
true
end
| _ -> begin
false
end))

# 27 "FStar.Options.fst"
let is_Medium = (fun _discr_ -> (match (_discr_) with
| Medium (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Options.fst"
let is_High = (fun _discr_ -> (match (_discr_) with
| High (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.Options.fst"
let is_Extreme = (fun _discr_ -> (match (_discr_) with
| Extreme (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Options.fst"
let is_Other = (fun _discr_ -> (match (_discr_) with
| Other (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.Options.fst"
let ___Other____0 = (fun projectee -> (match (projectee) with
| Other (_20_4) -> begin
_20_4
end))

# 32 "FStar.Options.fst"
let show_signatures : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 33 "FStar.Options.fst"
let norm_then_print : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 34 "FStar.Options.fst"
let z3_exe : Prims.string FStar_ST.ref = (let _104_19 = (FStar_Platform.exe "z3")
in (FStar_Util.mk_ref _104_19))

# 35 "FStar.Options.fst"
let silent : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 36 "FStar.Options.fst"
let debug : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 37 "FStar.Options.fst"
let debug_level : debug_level_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 38 "FStar.Options.fst"
let dlevel : Prims.string  ->  debug_level_t = (fun _20_1 -> (match (_20_1) with
| "Low" -> begin
Low
end
| "Medium" -> begin
Medium
end
| "High" -> begin
High
end
| "Extreme" -> begin
Extreme
end
| s -> begin
Other (s)
end))

# 44 "FStar.Options.fst"
let one_debug_level_geq : debug_level_t  ->  debug_level_t  ->  Prims.bool = (fun l1 l2 -> (match (l1) with
| (Other (_)) | (Low) -> begin
(l1 = l2)
end
| Medium -> begin
((l2 = Low) || (l2 = Medium))
end
| High -> begin
(((l2 = Low) || (l2 = Medium)) || (l2 = High))
end
| Extreme -> begin
((((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme))
end))

# 50 "FStar.Options.fst"
let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (let _104_29 = (FStar_ST.read debug_level)
in (FStar_All.pipe_right _104_29 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq l1 l2))))))

# 51 "FStar.Options.fst"
let log_types : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 52 "FStar.Options.fst"
let print_effect_args : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 53 "FStar.Options.fst"
let print_real_names : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 54 "FStar.Options.fst"
let dump_module : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 55 "FStar.Options.fst"
let should_dump : Prims.string  ->  Prims.bool = (fun l -> (match ((FStar_ST.read dump_module)) with
| None -> begin
false
end
| Some (m) -> begin
(m = l)
end))

# 58 "FStar.Options.fst"
let logQueries : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 59 "FStar.Options.fst"
let z3exe : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 60 "FStar.Options.fst"
let outputDir : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (".")))

# 61 "FStar.Options.fst"
let fstar_home_opt : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 62 "FStar.Options.fst"
let _fstar_home : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")

# 63 "FStar.Options.fst"
let prims_ref : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 64 "FStar.Options.fst"
let z3timeout : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 5)

# 65 "FStar.Options.fst"
let admit_smt_queries : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 66 "FStar.Options.fst"
let pretype : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 67 "FStar.Options.fst"
let codegen : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 68 "FStar.Options.fst"
let no_extract : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 69 "FStar.Options.fst"
let codegen_libs : Prims.string Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 70 "FStar.Options.fst"
let trace_error : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 71 "FStar.Options.fst"
let verify : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 72 "FStar.Options.fst"
let full_context_dependency : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 73 "FStar.Options.fst"
let print_implicits : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 74 "FStar.Options.fst"
let print_bound_var_types : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 75 "FStar.Options.fst"
let print_universes : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 76 "FStar.Options.fst"
let hide_uvar_nums : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 77 "FStar.Options.fst"
let hide_genident_nums : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 78 "FStar.Options.fst"
let serialize_mods : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 79 "FStar.Options.fst"
let initial_fuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 2)

# 80 "FStar.Options.fst"
let initial_ifuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 1)

# 81 "FStar.Options.fst"
let max_fuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 8)

# 82 "FStar.Options.fst"
let min_fuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 1)

# 83 "FStar.Options.fst"
let max_ifuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 2)

# 84 "FStar.Options.fst"
let warn_top_level_effects : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 85 "FStar.Options.fst"
let no_slack : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 86 "FStar.Options.fst"
let eager_inference : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 87 "FStar.Options.fst"
let universes : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 88 "FStar.Options.fst"
let unthrottle_inductives : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 89 "FStar.Options.fst"
let use_eq_at_higher_order : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 90 "FStar.Options.fst"
let use_native_int : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 91 "FStar.Options.fst"
let fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 92 "FStar.Options.fst"
let n_cores : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 1)

# 93 "FStar.Options.fst"
let verify_module : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 94 "FStar.Options.fst"
let __temp_no_proj : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 95 "FStar.Options.fst"
let interactive : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 96 "FStar.Options.fst"
let interactive_context : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 97 "FStar.Options.fst"
let split_cases : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 98 "FStar.Options.fst"
let _include_path : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 99 "FStar.Options.fst"
let no_default_includes : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 100 "FStar.Options.fst"
let interactive_fsi : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 101 "FStar.Options.fst"
let print_fuels : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 102 "FStar.Options.fst"
let cardinality : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "off")

# 103 "FStar.Options.fst"
let timing : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 104 "FStar.Options.fst"
let inline_arith : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 105 "FStar.Options.fst"
let warn_cardinality : Prims.unit  ->  Prims.bool = (fun _20_26 -> (match (()) with
| () -> begin
(match ((FStar_ST.read cardinality)) with
| "warn" -> begin
true
end
| _20_29 -> begin
false
end)
end))

# 108 "FStar.Options.fst"
let check_cardinality : Prims.unit  ->  Prims.bool = (fun _20_30 -> (match (()) with
| () -> begin
(match ((FStar_ST.read cardinality)) with
| "check" -> begin
true
end
| _20_33 -> begin
false
end)
end))

# 111 "FStar.Options.fst"
let dep : Prims.string Prims.option FStar_ST.ref = (FStar_ST.alloc None)

# 112 "FStar.Options.fst"
let explicit_deps : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 113 "FStar.Options.fst"
let init_options : Prims.unit  ->  Prims.unit = (fun _20_34 -> (match (()) with
| () -> begin
(
# 114 "FStar.Options.fst"
let _20_35 = (FStar_ST.op_Colon_Equals show_signatures [])
in (
# 115 "FStar.Options.fst"
let _20_37 = (FStar_ST.op_Colon_Equals norm_then_print true)
in (
# 116 "FStar.Options.fst"
let _20_39 = (let _104_38 = (FStar_Platform.exe "z3")
in (FStar_ST.op_Colon_Equals z3_exe _104_38))
in (
# 117 "FStar.Options.fst"
let _20_41 = (FStar_ST.op_Colon_Equals silent false)
in (
# 118 "FStar.Options.fst"
let _20_43 = (FStar_ST.op_Colon_Equals debug [])
in (
# 119 "FStar.Options.fst"
let _20_45 = (FStar_ST.op_Colon_Equals debug_level [])
in (
# 120 "FStar.Options.fst"
let _20_47 = (FStar_ST.op_Colon_Equals log_types false)
in (
# 121 "FStar.Options.fst"
let _20_49 = (FStar_ST.op_Colon_Equals print_effect_args false)
in (
# 122 "FStar.Options.fst"
let _20_51 = (FStar_ST.op_Colon_Equals print_real_names false)
in (
# 123 "FStar.Options.fst"
let _20_53 = (FStar_ST.op_Colon_Equals dump_module None)
in (
# 124 "FStar.Options.fst"
let _20_55 = (FStar_ST.op_Colon_Equals logQueries false)
in (
# 125 "FStar.Options.fst"
let _20_57 = (FStar_ST.op_Colon_Equals z3exe true)
in (
# 126 "FStar.Options.fst"
let _20_59 = (FStar_ST.op_Colon_Equals outputDir (Some (".")))
in (
# 127 "FStar.Options.fst"
let _20_61 = (FStar_ST.op_Colon_Equals fstar_home_opt None)
in (
# 128 "FStar.Options.fst"
let _20_63 = (FStar_ST.op_Colon_Equals _fstar_home "")
in (
# 129 "FStar.Options.fst"
let _20_65 = (FStar_ST.op_Colon_Equals prims_ref None)
in (
# 130 "FStar.Options.fst"
let _20_67 = (FStar_ST.op_Colon_Equals z3timeout 5)
in (
# 131 "FStar.Options.fst"
let _20_69 = (FStar_ST.op_Colon_Equals admit_smt_queries false)
in (
# 132 "FStar.Options.fst"
let _20_71 = (FStar_ST.op_Colon_Equals pretype true)
in (
# 133 "FStar.Options.fst"
let _20_73 = (FStar_ST.op_Colon_Equals codegen None)
in (
# 134 "FStar.Options.fst"
let _20_75 = (FStar_ST.op_Colon_Equals codegen_libs [])
in (
# 135 "FStar.Options.fst"
let _20_77 = (FStar_ST.op_Colon_Equals no_extract [])
in (
# 136 "FStar.Options.fst"
let _20_79 = (FStar_ST.op_Colon_Equals trace_error false)
in (
# 137 "FStar.Options.fst"
let _20_81 = (FStar_ST.op_Colon_Equals verify true)
in (
# 138 "FStar.Options.fst"
let _20_83 = (FStar_ST.op_Colon_Equals full_context_dependency true)
in (
# 139 "FStar.Options.fst"
let _20_85 = (FStar_ST.op_Colon_Equals print_implicits false)
in (
# 140 "FStar.Options.fst"
let _20_87 = (FStar_ST.op_Colon_Equals print_bound_var_types false)
in (
# 141 "FStar.Options.fst"
let _20_89 = (FStar_ST.op_Colon_Equals print_universes false)
in (
# 142 "FStar.Options.fst"
let _20_91 = (FStar_ST.op_Colon_Equals hide_uvar_nums false)
in (
# 143 "FStar.Options.fst"
let _20_93 = (FStar_ST.op_Colon_Equals hide_genident_nums false)
in (
# 144 "FStar.Options.fst"
let _20_95 = (FStar_ST.op_Colon_Equals serialize_mods false)
in (
# 145 "FStar.Options.fst"
let _20_97 = (FStar_ST.op_Colon_Equals initial_fuel 2)
in (
# 146 "FStar.Options.fst"
let _20_99 = (FStar_ST.op_Colon_Equals initial_ifuel 1)
in (
# 147 "FStar.Options.fst"
let _20_101 = (FStar_ST.op_Colon_Equals max_fuel 8)
in (
# 148 "FStar.Options.fst"
let _20_103 = (FStar_ST.op_Colon_Equals min_fuel 1)
in (
# 149 "FStar.Options.fst"
let _20_105 = (FStar_ST.op_Colon_Equals max_ifuel 2)
in (
# 150 "FStar.Options.fst"
let _20_107 = (FStar_ST.op_Colon_Equals warn_top_level_effects false)
in (
# 151 "FStar.Options.fst"
let _20_109 = (FStar_ST.op_Colon_Equals no_slack false)
in (
# 152 "FStar.Options.fst"
let _20_111 = (FStar_ST.op_Colon_Equals eager_inference false)
in (
# 153 "FStar.Options.fst"
let _20_113 = (FStar_ST.op_Colon_Equals unthrottle_inductives false)
in (
# 154 "FStar.Options.fst"
let _20_115 = (FStar_ST.op_Colon_Equals use_eq_at_higher_order false)
in (
# 155 "FStar.Options.fst"
let _20_117 = (FStar_ST.op_Colon_Equals fs_typ_app false)
in (
# 156 "FStar.Options.fst"
let _20_119 = (FStar_ST.op_Colon_Equals n_cores 1)
in (
# 157 "FStar.Options.fst"
let _20_121 = (FStar_ST.op_Colon_Equals split_cases 0)
in (
# 158 "FStar.Options.fst"
let _20_123 = (FStar_ST.op_Colon_Equals verify_module [])
in (
# 159 "FStar.Options.fst"
let _20_125 = (FStar_ST.op_Colon_Equals __temp_no_proj [])
in (
# 160 "FStar.Options.fst"
let _20_127 = (FStar_ST.op_Colon_Equals _include_path [])
in (
# 161 "FStar.Options.fst"
let _20_129 = (FStar_ST.op_Colon_Equals no_default_includes false)
in (
# 162 "FStar.Options.fst"
let _20_131 = (FStar_ST.op_Colon_Equals print_fuels false)
in (
# 163 "FStar.Options.fst"
let _20_133 = (FStar_ST.op_Colon_Equals use_native_int false)
in (
# 164 "FStar.Options.fst"
let _20_135 = (FStar_ST.op_Colon_Equals explicit_deps false)
in (
# 165 "FStar.Options.fst"
let _20_137 = (FStar_ST.op_Colon_Equals dep None)
in (
# 166 "FStar.Options.fst"
let _20_139 = (FStar_ST.op_Colon_Equals timing false)
in (FStar_ST.op_Colon_Equals inline_arith false))))))))))))))))))))))))))))))))))))))))))))))))))))))
end))

# 169 "FStar.Options.fst"
let set_fstar_home : Prims.unit  ->  Prims.string = (fun _20_141 -> (match (()) with
| () -> begin
(
# 170 "FStar.Options.fst"
let fh = (match ((FStar_ST.read fstar_home_opt)) with
| None -> begin
(
# 172 "FStar.Options.fst"
let x = (FStar_Util.get_exec_dir ())
in (
# 173 "FStar.Options.fst"
let x = (Prims.strcat x "/..")
in (
# 174 "FStar.Options.fst"
let _20_145 = (FStar_ST.op_Colon_Equals _fstar_home x)
in (
# 175 "FStar.Options.fst"
let _20_147 = (FStar_ST.op_Colon_Equals fstar_home_opt (Some (x)))
in x))))
end
| Some (x) -> begin
(
# 177 "FStar.Options.fst"
let _20_151 = (FStar_ST.op_Colon_Equals _fstar_home x)
in x)
end)
in fh)
end))

# 179 "FStar.Options.fst"
let get_fstar_home : Prims.unit  ->  Prims.string = (fun _20_154 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fstar_home_opt)) with
| None -> begin
(
# 180 "FStar.Options.fst"
let _20_156 = (let _104_43 = (set_fstar_home ())
in (FStar_All.pipe_left Prims.ignore _104_43))
in (FStar_ST.read _fstar_home))
end
| Some (x) -> begin
x
end)
end))

# 183 "FStar.Options.fst"
let include_path_base_dirs : Prims.string Prims.list = ("/lib")::("/lib/fstar")::("/stdlib")::("/stdlib/fstar")::[]

# 186 "FStar.Options.fst"
let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::[]

# 189 "FStar.Options.fst"
let get_include_path : Prims.unit  ->  Prims.string Prims.list = (fun _20_160 -> (match (()) with
| () -> begin
if (FStar_ST.read no_default_includes) then begin
(FStar_ST.read _include_path)
end else begin
(
# 195 "FStar.Options.fst"
let h = (get_fstar_home ())
in (
# 196 "FStar.Options.fst"
let defs = if (FStar_ST.read universes) then begin
universe_include_path_base_dirs
end else begin
include_path_base_dirs
end
in (let _104_49 = (FStar_ST.read _include_path)
in (let _104_48 = (let _104_47 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (".")::_104_47)
in (FStar_List.append _104_49 _104_48)))))
end
end))

# 199 "FStar.Options.fst"
let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> (
# 200 "FStar.Options.fst"
let search_path = (get_include_path ())
in (FStar_All.try_with (fun _20_167 -> (match (()) with
| () -> begin
(let _104_54 = if (FStar_Util.is_path_absolute filename) then begin
if (FStar_Util.file_exists filename) then begin
Some (filename)
end else begin
None
end
end else begin
(FStar_Util.find_map search_path (fun p -> (
# 213 "FStar.Options.fst"
let path = (FStar_Util.join_paths p filename)
in if (FStar_Util.file_exists path) then begin
Some (path)
end else begin
None
end)))
end
in (FStar_Util.map_option FStar_Util.normalize_file_path _104_54))
end)) (fun _20_166 -> (match (_20_166) with
| _20_170 -> begin
None
end)))))

# 221 "FStar.Options.fst"
let prims : Prims.unit  ->  Prims.string = (fun _20_175 -> (match (()) with
| () -> begin
(match ((FStar_ST.read prims_ref)) with
| None -> begin
(
# 223 "FStar.Options.fst"
let filen = "prims.fst"
in (match ((find_file filen)) with
| Some (result) -> begin
result
end
| None -> begin
(let _104_59 = (let _104_58 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filen)
in FStar_Util.Failure (_104_58))
in (Prims.raise _104_59))
end))
end
| Some (x) -> begin
x
end)
end))

# 231 "FStar.Options.fst"
let prependOutputDir : Prims.string  ->  Prims.string = (fun fname -> (match ((FStar_ST.read outputDir)) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat (Prims.strcat x "/") fname)
end))

# 235 "FStar.Options.fst"
let display_version : Prims.unit  ->  Prims.unit = (fun _20_187 -> (match (()) with
| () -> begin
(let _104_64 = (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)
in (FStar_Util.print_string _104_64))
end))

# 239 "FStar.Options.fst"
let display_usage = (fun specs -> (
# 240 "FStar.Options.fst"
let _20_189 = (FStar_Util.print_string "fstar [option] file...\n")
in (FStar_List.iter (fun _20_196 -> (match (_20_196) with
| (_20_192, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
if (doc = "") then begin
(let _104_69 = (let _104_68 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" _104_68))
in (FStar_Util.print_string _104_69))
end else begin
(let _104_71 = (let _104_70 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" _104_70 doc))
in (FStar_Util.print_string _104_71))
end
end
| FStar_Getopt.OneArg (_20_200, argname) -> begin
if (doc = "") then begin
(let _104_75 = (let _104_74 = (FStar_Util.colorize_bold flag)
in (let _104_73 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" _104_74 _104_73)))
in (FStar_Util.print_string _104_75))
end else begin
(let _104_78 = (let _104_77 = (FStar_Util.colorize_bold flag)
in (let _104_76 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" _104_77 _104_76 doc)))
in (FStar_Util.print_string _104_78))
end
end)
end)) specs)))

# 252 "FStar.Options.fst"
let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun _20_204 -> (match (()) with
| () -> begin
(
# 253 "FStar.Options.fst"
let specs = ((FStar_Getopt.noshort, "admit_smt_queries", FStar_Getopt.OneArg (((fun s -> (let _104_87 = if (s = "true") then begin
true
end else begin
if (s = "false") then begin
false
end else begin
(FStar_All.failwith "Invalid argument to --admit_smt_queries")
end
end
in (FStar_ST.op_Colon_Equals admit_smt_queries _104_87))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((FStar_Getopt.noshort, "cardinality", FStar_Getopt.OneArg (((fun x -> (let _104_91 = (validate_cardinality x)
in (FStar_ST.op_Colon_Equals cardinality _104_91))), "off|warn|check")), "Check cardinality constraints on inductive data types (default \'off\')"))::((FStar_Getopt.noshort, "codegen", FStar_Getopt.OneArg (((fun s -> (let _104_95 = (parse_codegen s)
in (FStar_ST.op_Colon_Equals codegen _104_95))), "OCaml|FSharp")), "Generate code for execution"))::((FStar_Getopt.noshort, "codegen-lib", FStar_Getopt.OneArg (((fun s -> (let _104_100 = (let _104_99 = (FStar_ST.read codegen_libs)
in ((FStar_Util.split s "."))::_104_99)
in (FStar_ST.op_Colon_Equals codegen_libs _104_100))), "namespace")), "External runtime library library"))::((FStar_Getopt.noshort, "debug", FStar_Getopt.OneArg (((fun x -> (let _104_105 = (let _104_104 = (FStar_ST.read debug)
in (x)::_104_104)
in (FStar_ST.op_Colon_Equals debug _104_105))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((FStar_Getopt.noshort, "debug_level", FStar_Getopt.OneArg (((fun x -> (let _104_110 = (let _104_109 = (FStar_ST.read debug_level)
in ((dlevel x))::_104_109)
in (FStar_ST.op_Colon_Equals debug_level _104_110))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((FStar_Getopt.noshort, "dep", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals dep (Some (x)))), "make|nubuild")), "Output the transitive closure of the dependency graph in a format suitable for the given tool"))::((FStar_Getopt.noshort, "dump_module", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((FStar_Getopt.noshort, "eager_inference", FStar_Getopt.ZeroArgs ((fun _20_213 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((FStar_Getopt.noshort, "explicit_deps", FStar_Getopt.ZeroArgs ((fun _20_214 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals explicit_deps true)
end))), "tell FStar to not find dependencies automatically because the user provides them on the command-line"))::((FStar_Getopt.noshort, "fs_typ_app", FStar_Getopt.ZeroArgs ((fun _20_215 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((FStar_Getopt.noshort, "fsi", FStar_Getopt.ZeroArgs ((fun _20_216 -> (match (()) with
| () -> begin
(set_interactive_fsi ())
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::((FStar_Getopt.noshort, "fstar_home", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((FStar_Getopt.noshort, "hide_genident_nums", FStar_Getopt.ZeroArgs ((fun _20_218 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((FStar_Getopt.noshort, "hide_uvar_nums", FStar_Getopt.ZeroArgs ((fun _20_219 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((FStar_Getopt.noshort, "in", FStar_Getopt.ZeroArgs ((fun _20_220 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((FStar_Getopt.noshort, "in_context", FStar_Getopt.OneArg (((fun s -> (
# 270 "FStar.Options.fst"
let _20_222 = (FStar_ST.op_Colon_Equals interactive true)
in (FStar_ST.op_Colon_Equals interactive_context (Some (s))))), "name")), "Specify the context of an interactive session; needed for --auto_deps to work with interactive mode."))::((FStar_Getopt.noshort, "include", FStar_Getopt.OneArg (((fun s -> (let _104_134 = (let _104_133 = (FStar_ST.read _include_path)
in (FStar_List.append _104_133 ((s)::[])))
in (FStar_ST.op_Colon_Equals _include_path _104_134))), "path")), "A directory in which to search for files included on the command line"))::((FStar_Getopt.noshort, "initial_fuel", FStar_Getopt.OneArg (((fun x -> (let _104_138 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals initial_fuel _104_138))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((FStar_Getopt.noshort, "initial_ifuel", FStar_Getopt.OneArg (((fun x -> (let _104_142 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals initial_ifuel _104_142))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((FStar_Getopt.noshort, "inline_arith", FStar_Getopt.ZeroArgs ((fun _20_227 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals inline_arith true)
end))), "Inline definitions of arithmetic functions in the SMT encoding"))::((FStar_Getopt.noshort, "lax", FStar_Getopt.ZeroArgs ((fun _20_228 -> (match (()) with
| () -> begin
(
# 275 "FStar.Options.fst"
let _20_229 = (FStar_ST.op_Colon_Equals pretype true)
in (FStar_ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((FStar_Getopt.noshort, "log_types", FStar_Getopt.ZeroArgs ((fun _20_231 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((FStar_Getopt.noshort, "log_queries", FStar_Getopt.ZeroArgs ((fun _20_232 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((FStar_Getopt.noshort, "max_fuel", FStar_Getopt.OneArg (((fun x -> (let _104_150 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals max_fuel _104_150))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((FStar_Getopt.noshort, "max_ifuel", FStar_Getopt.OneArg (((fun x -> (let _104_154 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals max_ifuel _104_154))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 2)"))::((FStar_Getopt.noshort, "min_fuel", FStar_Getopt.OneArg (((fun x -> (let _104_158 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals min_fuel _104_158))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((FStar_Getopt.noshort, "MLish", FStar_Getopt.ZeroArgs ((fun _20_236 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((FStar_Getopt.noshort, "n_cores", FStar_Getopt.OneArg (((fun x -> (let _104_163 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals n_cores _104_163))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((FStar_Getopt.noshort, "no_default_includes", FStar_Getopt.ZeroArgs ((fun _20_238 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals no_default_includes true)
end))), "Ignore the default module search paths"))::((FStar_Getopt.noshort, "no_extract", FStar_Getopt.OneArg (((fun x -> (let _104_169 = (let _104_168 = (FStar_ST.read no_extract)
in (x)::_104_168)
in (FStar_ST.op_Colon_Equals no_extract _104_169))), "module name")), "Do not extract code from this module"))::((FStar_Getopt.noshort, "no_fs_typ_app", FStar_Getopt.ZeroArgs ((fun _20_240 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals fs_typ_app false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((FStar_Getopt.noshort, "odir", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((FStar_Getopt.noshort, "prims", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((FStar_Getopt.noshort, "print_before_norm", FStar_Getopt.ZeroArgs ((fun _20_243 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((FStar_Getopt.noshort, "print_bound_var_types", FStar_Getopt.ZeroArgs ((fun _20_244 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_bound_var_types true)
end))), "Print the types of bound variables"))::((FStar_Getopt.noshort, "print_effect_args", FStar_Getopt.ZeroArgs ((fun _20_245 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((FStar_Getopt.noshort, "print_fuels", FStar_Getopt.ZeroArgs ((fun _20_246 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_fuels true)
end))), "Print the fuel amounts used for each successful query"))::((FStar_Getopt.noshort, "print_implicits", FStar_Getopt.ZeroArgs ((fun _20_247 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((FStar_Getopt.noshort, "print_universes", FStar_Getopt.ZeroArgs ((fun _20_248 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_universes true)
end))), "Print universes"))::((FStar_Getopt.noshort, "prn", FStar_Getopt.ZeroArgs ((fun _20_249 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with log_queries"))::((FStar_Getopt.noshort, "show_signatures", FStar_Getopt.OneArg (((fun x -> (let _104_188 = (let _104_187 = (FStar_ST.read show_signatures)
in (x)::_104_187)
in (FStar_ST.op_Colon_Equals show_signatures _104_188))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((FStar_Getopt.noshort, "silent", FStar_Getopt.ZeroArgs ((fun _20_251 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals silent true)
end))), " "))::((FStar_Getopt.noshort, "smt", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((FStar_Getopt.noshort, "split_cases", FStar_Getopt.OneArg (((fun n -> (let _104_196 = (FStar_Util.int_of_string n)
in (FStar_ST.op_Colon_Equals split_cases _104_196))), "t")), "Partition VC of a match into groups of n cases"))::((FStar_Getopt.noshort, "timing", FStar_Getopt.ZeroArgs ((fun _20_254 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals timing true)
end))), "Print the time it takes to verify each top-level definition"))::((FStar_Getopt.noshort, "trace_error", FStar_Getopt.ZeroArgs ((fun _20_255 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((FStar_Getopt.noshort, "universes", FStar_Getopt.ZeroArgs ((fun _20_256 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals universes true)
end))), "Use the (experimental) support for universes"))::((FStar_Getopt.noshort, "unthrottle_inductives", FStar_Getopt.ZeroArgs ((fun _20_257 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals unthrottle_inductives true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((FStar_Getopt.noshort, "use_eq_at_higher_order", FStar_Getopt.ZeroArgs ((fun _20_258 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals use_eq_at_higher_order true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((FStar_Getopt.noshort, "use_native_int", FStar_Getopt.ZeroArgs ((fun _20_259 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals use_native_int true)
end))), "Extract the \'int\' type to platform-specific native int; you will need to link the generated code with the appropriate version of the prims library"))::((FStar_Getopt.noshort, "verify_module", FStar_Getopt.OneArg (((fun x -> (let _104_207 = (let _104_206 = (FStar_ST.read verify_module)
in (x)::_104_206)
in (FStar_ST.op_Colon_Equals verify_module _104_207))), "string")), "Name of the module to verify"))::((FStar_Getopt.noshort, "__temp_no_proj", FStar_Getopt.OneArg (((fun x -> (let _104_212 = (let _104_211 = (FStar_ST.read __temp_no_proj)
in (x)::_104_211)
in (FStar_ST.op_Colon_Equals __temp_no_proj _104_212))), "string")), "Don\'t generate projectors for this module"))::(('v', "version", FStar_Getopt.ZeroArgs ((fun _20_262 -> (
# 307 "FStar.Options.fst"
let _20_264 = (display_version ())
in (FStar_All.exit 0)))), "Display version number"))::((FStar_Getopt.noshort, "warn_top_level_effects", FStar_Getopt.ZeroArgs ((fun _20_266 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((FStar_Getopt.noshort, "z3timeout", FStar_Getopt.OneArg (((fun s -> (let _104_218 = (FStar_Util.int_of_string s)
in (FStar_ST.op_Colon_Equals z3timeout _104_218))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::[]
in (('h', "help", FStar_Getopt.ZeroArgs ((fun x -> (
# 311 "FStar.Options.fst"
let _20_270 = (display_usage specs)
in (FStar_All.exit 0)))), "Display this information"))::specs)
end))
and parse_codegen : Prims.string  ->  Prims.string Prims.option = (fun s -> (match (s) with
| ("OCaml") | ("FSharp") -> begin
Some (s)
end
| _20_276 -> begin
(
# 317 "FStar.Options.fst"
let _20_277 = (FStar_Util.print_string "Wrong argument to codegen flag\n")
in (
# 318 "FStar.Options.fst"
let _20_279 = (let _104_221 = (specs ())
in (display_usage _104_221))
in (FStar_All.exit 1)))
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| _20_286 -> begin
(
# 323 "FStar.Options.fst"
let _20_287 = (FStar_Util.print_string "Wrong argument to cardinality flag\n")
in (
# 324 "FStar.Options.fst"
let _20_289 = (let _104_223 = (specs ())
in (display_usage _104_223))
in (FStar_All.exit 1)))
end))
and set_interactive_fsi : Prims.unit  ->  Prims.unit = (fun _20_291 -> if (FStar_ST.read interactive) then begin
(FStar_ST.op_Colon_Equals interactive_fsi true)
end else begin
(
# 328 "FStar.Options.fst"
let _20_293 = (FStar_Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (
# 329 "FStar.Options.fst"
let _20_295 = (let _104_225 = (specs ())
in (display_usage _104_225))
in (FStar_All.exit 1)))
end)

# 331 "FStar.Options.fst"
let should_verify : Prims.string  ->  Prims.bool = (fun m -> ((FStar_ST.read verify) && (match ((FStar_ST.read verify_module)) with
| [] -> begin
true
end
| l -> begin
(FStar_List.contains m l)
end)))

# 337 "FStar.Options.fst"
let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (let _104_230 = (FStar_ST.read __temp_no_proj)
in (FStar_List.contains m _104_230)))

# 339 "FStar.Options.fst"
let should_print_message : Prims.string  ->  Prims.bool = (fun m -> ((should_verify m) && (m <> "Prims")))

# 343 "FStar.Options.fst"
let set_options : Prims.string  ->  FStar_Getopt.parse_cmdline_res = (
# 346 "FStar.Options.fst"
let no_smt_specs = (let _104_235 = (specs ())
in (FStar_All.pipe_right _104_235 (FStar_List.filter (fun _20_309 -> (match (_20_309) with
| (_20_303, name, _20_306, _20_308) -> begin
(name <> "smt")
end)))))
in (fun s -> (FStar_Getopt.parse_string no_smt_specs (fun _20_312 -> ()) s)))

# 349 "FStar.Options.fst"
let reset_options_string : Prims.string Prims.option FStar_ST.ref = (FStar_ST.alloc None)

# 350 "FStar.Options.fst"
let reset_options : Prims.unit  ->  FStar_Getopt.parse_cmdline_res = (fun _20_314 -> (match (()) with
| () -> begin
(
# 351 "FStar.Options.fst"
let _20_315 = (init_options ())
in (
# 352 "FStar.Options.fst"
let res = (let _104_241 = (specs ())
in (FStar_Getopt.parse_cmdline _104_241 (fun x -> ())))
in (match ((FStar_ST.read reset_options_string)) with
| Some (x) -> begin
(set_options x)
end
| _20_322 -> begin
res
end)))
end))




