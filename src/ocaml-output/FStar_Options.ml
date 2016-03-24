
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
| Other (_20_5) -> begin
_20_5
end))

# 32 "FStar.Options.fst"
let show_signatures : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 33 "FStar.Options.fst"
let norm_then_print : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 34 "FStar.Options.fst"
let z3_exe : Prims.string FStar_ST.ref = (let _105_19 = (FStar_Platform.exe "z3")
in (FStar_Util.mk_ref _105_19))

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
let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (let _105_29 = (FStar_ST.read debug_level)
in (FStar_All.pipe_right _105_29 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq l1 l2))))))

# 51 "FStar.Options.fst"
let log_types : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 52 "FStar.Options.fst"
let print_effect_args : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 53 "FStar.Options.fst"
let print_real_names : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 54 "FStar.Options.fst"
let detail_errors : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 55 "FStar.Options.fst"
let dump_module : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 56 "FStar.Options.fst"
let should_dump : Prims.string  ->  Prims.bool = (fun l -> (match ((FStar_ST.read dump_module)) with
| None -> begin
false
end
| Some (m) -> begin
(m = l)
end))

# 59 "FStar.Options.fst"
let logQueries : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 60 "FStar.Options.fst"
let z3exe : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 61 "FStar.Options.fst"
let outputDir : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref (Some (".")))

# 62 "FStar.Options.fst"
let fstar_home_opt : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 63 "FStar.Options.fst"
let _fstar_home : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")

# 64 "FStar.Options.fst"
let prims_ref : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 65 "FStar.Options.fst"
let z3timeout : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 5)

# 66 "FStar.Options.fst"
let admit_smt_queries : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 67 "FStar.Options.fst"
let pretype : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 68 "FStar.Options.fst"
let codegen : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 69 "FStar.Options.fst"
let no_extract : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 70 "FStar.Options.fst"
let no_location_info : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 71 "FStar.Options.fst"
let codegen_libs : Prims.string Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 72 "FStar.Options.fst"
let trace_error : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 73 "FStar.Options.fst"
let verify : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 74 "FStar.Options.fst"
let full_context_dependency : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref true)

# 75 "FStar.Options.fst"
let print_implicits : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 76 "FStar.Options.fst"
let print_bound_var_types : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 77 "FStar.Options.fst"
let print_universes : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 78 "FStar.Options.fst"
let hide_uvar_nums : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 79 "FStar.Options.fst"
let hide_genident_nums : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 80 "FStar.Options.fst"
let serialize_mods : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 81 "FStar.Options.fst"
let initial_fuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 2)

# 82 "FStar.Options.fst"
let initial_ifuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 1)

# 83 "FStar.Options.fst"
let max_fuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 8)

# 84 "FStar.Options.fst"
let min_fuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 1)

# 85 "FStar.Options.fst"
let max_ifuel : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 2)

# 86 "FStar.Options.fst"
let warn_top_level_effects : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 87 "FStar.Options.fst"
let no_slack : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 88 "FStar.Options.fst"
let eager_inference : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 89 "FStar.Options.fst"
let universes : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 90 "FStar.Options.fst"
let unthrottle_inductives : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 91 "FStar.Options.fst"
let use_eq_at_higher_order : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 92 "FStar.Options.fst"
let use_native_int : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 93 "FStar.Options.fst"
let fs_typ_app : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 94 "FStar.Options.fst"
let n_cores : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 1)

# 95 "FStar.Options.fst"
let verify_module : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 96 "FStar.Options.fst"
let __temp_no_proj : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 97 "FStar.Options.fst"
let interactive : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 98 "FStar.Options.fst"
let interactive_context : Prims.string Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 99 "FStar.Options.fst"
let interleave : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 100 "FStar.Options.fst"
let split_cases : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 101 "FStar.Options.fst"
let _include_path : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 102 "FStar.Options.fst"
let no_default_includes : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 103 "FStar.Options.fst"
let interactive_fsi : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 104 "FStar.Options.fst"
let print_fuels : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 105 "FStar.Options.fst"
let cardinality : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "off")

# 106 "FStar.Options.fst"
let timing : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 107 "FStar.Options.fst"
let inline_arith : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 108 "FStar.Options.fst"
let warn_cardinality : Prims.unit  ->  Prims.bool = (fun _20_27 -> (match (()) with
| () -> begin
(match ((FStar_ST.read cardinality)) with
| "warn" -> begin
true
end
| _20_30 -> begin
false
end)
end))

# 111 "FStar.Options.fst"
let check_cardinality : Prims.unit  ->  Prims.bool = (fun _20_31 -> (match (()) with
| () -> begin
(match ((FStar_ST.read cardinality)) with
| "check" -> begin
true
end
| _20_34 -> begin
false
end)
end))

# 114 "FStar.Options.fst"
let dep : Prims.string Prims.option FStar_ST.ref = (FStar_ST.alloc None)

# 115 "FStar.Options.fst"
let explicit_deps : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

# 116 "FStar.Options.fst"
let init_options : Prims.unit  ->  Prims.unit = (fun _20_35 -> (match (()) with
| () -> begin
(
# 117 "FStar.Options.fst"
let _20_36 = (FStar_ST.op_Colon_Equals show_signatures [])
in (
# 118 "FStar.Options.fst"
let _20_38 = (FStar_ST.op_Colon_Equals norm_then_print true)
in (
# 119 "FStar.Options.fst"
let _20_40 = (let _105_38 = (FStar_Platform.exe "z3")
in (FStar_ST.op_Colon_Equals z3_exe _105_38))
in (
# 120 "FStar.Options.fst"
let _20_42 = (FStar_ST.op_Colon_Equals silent false)
in (
# 121 "FStar.Options.fst"
let _20_44 = (FStar_ST.op_Colon_Equals debug [])
in (
# 122 "FStar.Options.fst"
let _20_46 = (FStar_ST.op_Colon_Equals debug_level [])
in (
# 123 "FStar.Options.fst"
let _20_48 = (FStar_ST.op_Colon_Equals log_types false)
in (
# 124 "FStar.Options.fst"
let _20_50 = (FStar_ST.op_Colon_Equals print_effect_args false)
in (
# 125 "FStar.Options.fst"
let _20_52 = (FStar_ST.op_Colon_Equals print_real_names false)
in (
# 126 "FStar.Options.fst"
let _20_54 = (FStar_ST.op_Colon_Equals dump_module None)
in (
# 127 "FStar.Options.fst"
let _20_56 = (FStar_ST.op_Colon_Equals logQueries false)
in (
# 128 "FStar.Options.fst"
let _20_58 = (FStar_ST.op_Colon_Equals z3exe true)
in (
# 129 "FStar.Options.fst"
let _20_60 = (FStar_ST.op_Colon_Equals outputDir (Some (".")))
in (
# 130 "FStar.Options.fst"
let _20_62 = (FStar_ST.op_Colon_Equals fstar_home_opt None)
in (
# 131 "FStar.Options.fst"
let _20_64 = (FStar_ST.op_Colon_Equals _fstar_home "")
in (
# 132 "FStar.Options.fst"
let _20_66 = (FStar_ST.op_Colon_Equals prims_ref None)
in (
# 133 "FStar.Options.fst"
let _20_68 = (FStar_ST.op_Colon_Equals z3timeout 5)
in (
# 134 "FStar.Options.fst"
let _20_70 = (FStar_ST.op_Colon_Equals admit_smt_queries false)
in (
# 135 "FStar.Options.fst"
let _20_72 = (FStar_ST.op_Colon_Equals pretype true)
in (
# 136 "FStar.Options.fst"
let _20_74 = (FStar_ST.op_Colon_Equals codegen None)
in (
# 137 "FStar.Options.fst"
let _20_76 = (FStar_ST.op_Colon_Equals codegen_libs [])
in (
# 138 "FStar.Options.fst"
let _20_78 = (FStar_ST.op_Colon_Equals no_extract [])
in (
# 139 "FStar.Options.fst"
let _20_80 = (FStar_ST.op_Colon_Equals trace_error false)
in (
# 140 "FStar.Options.fst"
let _20_82 = (FStar_ST.op_Colon_Equals verify true)
in (
# 141 "FStar.Options.fst"
let _20_84 = (FStar_ST.op_Colon_Equals full_context_dependency true)
in (
# 142 "FStar.Options.fst"
let _20_86 = (FStar_ST.op_Colon_Equals print_implicits false)
in (
# 143 "FStar.Options.fst"
let _20_88 = (FStar_ST.op_Colon_Equals print_bound_var_types false)
in (
# 144 "FStar.Options.fst"
let _20_90 = (FStar_ST.op_Colon_Equals print_universes false)
in (
# 145 "FStar.Options.fst"
let _20_92 = (FStar_ST.op_Colon_Equals hide_uvar_nums false)
in (
# 146 "FStar.Options.fst"
let _20_94 = (FStar_ST.op_Colon_Equals hide_genident_nums false)
in (
# 147 "FStar.Options.fst"
let _20_96 = (FStar_ST.op_Colon_Equals serialize_mods false)
in (
# 148 "FStar.Options.fst"
let _20_98 = (FStar_ST.op_Colon_Equals initial_fuel 2)
in (
# 149 "FStar.Options.fst"
let _20_100 = (FStar_ST.op_Colon_Equals initial_ifuel 1)
in (
# 150 "FStar.Options.fst"
let _20_102 = (FStar_ST.op_Colon_Equals max_fuel 8)
in (
# 151 "FStar.Options.fst"
let _20_104 = (FStar_ST.op_Colon_Equals min_fuel 1)
in (
# 152 "FStar.Options.fst"
let _20_106 = (FStar_ST.op_Colon_Equals max_ifuel 2)
in (
# 153 "FStar.Options.fst"
let _20_108 = (FStar_ST.op_Colon_Equals warn_top_level_effects false)
in (
# 154 "FStar.Options.fst"
let _20_110 = (FStar_ST.op_Colon_Equals no_slack false)
in (
# 155 "FStar.Options.fst"
let _20_112 = (FStar_ST.op_Colon_Equals eager_inference false)
in (
# 156 "FStar.Options.fst"
let _20_114 = (FStar_ST.op_Colon_Equals unthrottle_inductives false)
in (
# 157 "FStar.Options.fst"
let _20_116 = (FStar_ST.op_Colon_Equals use_eq_at_higher_order false)
in (
# 158 "FStar.Options.fst"
let _20_118 = (FStar_ST.op_Colon_Equals fs_typ_app false)
in (
# 159 "FStar.Options.fst"
let _20_120 = (FStar_ST.op_Colon_Equals n_cores 1)
in (
# 160 "FStar.Options.fst"
let _20_122 = (FStar_ST.op_Colon_Equals split_cases 0)
in (
# 161 "FStar.Options.fst"
let _20_124 = (FStar_ST.op_Colon_Equals verify_module [])
in (
# 162 "FStar.Options.fst"
let _20_126 = (FStar_ST.op_Colon_Equals __temp_no_proj [])
in (
# 163 "FStar.Options.fst"
let _20_128 = (FStar_ST.op_Colon_Equals _include_path [])
in (
# 164 "FStar.Options.fst"
let _20_130 = (FStar_ST.op_Colon_Equals no_default_includes false)
in (
# 165 "FStar.Options.fst"
let _20_132 = (FStar_ST.op_Colon_Equals print_fuels false)
in (
# 166 "FStar.Options.fst"
let _20_134 = (FStar_ST.op_Colon_Equals use_native_int false)
in (
# 167 "FStar.Options.fst"
let _20_136 = (FStar_ST.op_Colon_Equals explicit_deps false)
in (
# 168 "FStar.Options.fst"
let _20_138 = (FStar_ST.op_Colon_Equals dep None)
in (
# 169 "FStar.Options.fst"
let _20_140 = (FStar_ST.op_Colon_Equals timing false)
in (FStar_ST.op_Colon_Equals inline_arith false))))))))))))))))))))))))))))))))))))))))))))))))))))))
end))

# 172 "FStar.Options.fst"
let set_fstar_home : Prims.unit  ->  Prims.string = (fun _20_142 -> (match (()) with
| () -> begin
(
# 173 "FStar.Options.fst"
let fh = (match ((FStar_ST.read fstar_home_opt)) with
| None -> begin
(
# 175 "FStar.Options.fst"
let x = (FStar_Util.get_exec_dir ())
in (
# 176 "FStar.Options.fst"
let x = (Prims.strcat x "/..")
in (
# 177 "FStar.Options.fst"
let _20_146 = (FStar_ST.op_Colon_Equals _fstar_home x)
in (
# 178 "FStar.Options.fst"
let _20_148 = (FStar_ST.op_Colon_Equals fstar_home_opt (Some (x)))
in x))))
end
| Some (x) -> begin
(
# 180 "FStar.Options.fst"
let _20_152 = (FStar_ST.op_Colon_Equals _fstar_home x)
in x)
end)
in fh)
end))

# 182 "FStar.Options.fst"
let get_fstar_home : Prims.unit  ->  Prims.string = (fun _20_155 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fstar_home_opt)) with
| None -> begin
(
# 183 "FStar.Options.fst"
let _20_157 = (let _105_43 = (set_fstar_home ())
in (FStar_All.pipe_left Prims.ignore _105_43))
in (FStar_ST.read _fstar_home))
end
| Some (x) -> begin
x
end)
end))

# 186 "FStar.Options.fst"
let include_path_base_dirs : Prims.string Prims.list = ("/lib")::("/lib/fstar")::("/stdlib")::("/stdlib/fstar")::[]

# 189 "FStar.Options.fst"
let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::[]

# 192 "FStar.Options.fst"
let get_include_path : Prims.unit  ->  Prims.string Prims.list = (fun _20_161 -> (match (()) with
| () -> begin
if (FStar_ST.read no_default_includes) then begin
(FStar_ST.read _include_path)
end else begin
(
# 198 "FStar.Options.fst"
let h = (get_fstar_home ())
in (
# 199 "FStar.Options.fst"
let defs = if (FStar_ST.read universes) then begin
universe_include_path_base_dirs
end else begin
include_path_base_dirs
end
in (let _105_50 = (let _105_49 = (let _105_47 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right _105_47 (FStar_List.filter FStar_Util.file_exists)))
in (let _105_48 = (FStar_ST.read _include_path)
in (FStar_List.append _105_49 _105_48)))
in (FStar_List.append _105_50 ((".")::[])))))
end
end))

# 202 "FStar.Options.fst"
let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> (
# 203 "FStar.Options.fst"
let search_path = (get_include_path ())
in (FStar_All.try_with (fun _20_168 -> (match (()) with
| () -> begin
(let _105_55 = if (FStar_Util.is_path_absolute filename) then begin
if (FStar_Util.file_exists filename) then begin
Some (filename)
end else begin
None
end
end else begin
(FStar_Util.find_map search_path (fun p -> (
# 216 "FStar.Options.fst"
let path = (FStar_Util.join_paths p filename)
in if (FStar_Util.file_exists path) then begin
Some (path)
end else begin
None
end)))
end
in (FStar_Util.map_option FStar_Util.normalize_file_path _105_55))
end)) (fun _20_167 -> (match (_20_167) with
| _20_171 -> begin
None
end)))))

# 224 "FStar.Options.fst"
let prims : Prims.unit  ->  Prims.string = (fun _20_176 -> (match (()) with
| () -> begin
(match ((FStar_ST.read prims_ref)) with
| None -> begin
(
# 226 "FStar.Options.fst"
let filen = "prims.fst"
in (match ((find_file filen)) with
| Some (result) -> begin
result
end
| None -> begin
(let _105_60 = (let _105_59 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filen)
in FStar_Util.Failure (_105_59))
in (Prims.raise _105_60))
end))
end
| Some (x) -> begin
x
end)
end))

# 234 "FStar.Options.fst"
let prependOutputDir : Prims.string  ->  Prims.string = (fun fname -> (match ((FStar_ST.read outputDir)) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat (Prims.strcat x "/") fname)
end))

# 238 "FStar.Options.fst"
let display_version : Prims.unit  ->  Prims.unit = (fun _20_188 -> (match (()) with
| () -> begin
(let _105_65 = (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)
in (FStar_Util.print_string _105_65))
end))

# 242 "FStar.Options.fst"
let display_usage = (fun specs -> (
# 243 "FStar.Options.fst"
let _20_190 = (FStar_Util.print_string "fstar [option] file...\n")
in (FStar_List.iter (fun _20_197 -> (match (_20_197) with
| (_20_193, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
if (doc = "") then begin
(let _105_70 = (let _105_69 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" _105_69))
in (FStar_Util.print_string _105_70))
end else begin
(let _105_72 = (let _105_71 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" _105_71 doc))
in (FStar_Util.print_string _105_72))
end
end
| FStar_Getopt.OneArg (_20_201, argname) -> begin
if (doc = "") then begin
(let _105_76 = (let _105_75 = (FStar_Util.colorize_bold flag)
in (let _105_74 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" _105_75 _105_74)))
in (FStar_Util.print_string _105_76))
end else begin
(let _105_79 = (let _105_78 = (FStar_Util.colorize_bold flag)
in (let _105_77 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" _105_78 _105_77 doc)))
in (FStar_Util.print_string _105_79))
end
end)
end)) specs)))

# 255 "FStar.Options.fst"
let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun _20_205 -> (match (()) with
| () -> begin
(
# 256 "FStar.Options.fst"
let specs = ((FStar_Getopt.noshort, "admit_smt_queries", FStar_Getopt.OneArg (((fun s -> (let _105_88 = if (s = "true") then begin
true
end else begin
if (s = "false") then begin
false
end else begin
(FStar_All.failwith "Invalid argument to --admit_smt_queries")
end
end
in (FStar_ST.op_Colon_Equals admit_smt_queries _105_88))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((FStar_Getopt.noshort, "cardinality", FStar_Getopt.OneArg (((fun x -> (let _105_92 = (validate_cardinality x)
in (FStar_ST.op_Colon_Equals cardinality _105_92))), "off|warn|check")), "Check cardinality constraints on inductive data types (default \'off\')"))::((FStar_Getopt.noshort, "codegen", FStar_Getopt.OneArg (((fun s -> (let _105_96 = (parse_codegen s)
in (FStar_ST.op_Colon_Equals codegen _105_96))), "OCaml|FSharp")), "Generate code for execution"))::((FStar_Getopt.noshort, "codegen-lib", FStar_Getopt.OneArg (((fun s -> (let _105_101 = (let _105_100 = (FStar_ST.read codegen_libs)
in ((FStar_Util.split s "."))::_105_100)
in (FStar_ST.op_Colon_Equals codegen_libs _105_101))), "namespace")), "External runtime library library"))::((FStar_Getopt.noshort, "debug", FStar_Getopt.OneArg (((fun x -> (let _105_106 = (let _105_105 = (FStar_ST.read debug)
in (x)::_105_105)
in (FStar_ST.op_Colon_Equals debug _105_106))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((FStar_Getopt.noshort, "debug_level", FStar_Getopt.OneArg (((fun x -> (let _105_111 = (let _105_110 = (FStar_ST.read debug_level)
in ((dlevel x))::_105_110)
in (FStar_ST.op_Colon_Equals debug_level _105_111))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((FStar_Getopt.noshort, "dep", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals dep (Some (x)))), "make|nubuild")), "Output the transitive closure of the dependency graph in a format suitable for the given tool"))::((FStar_Getopt.noshort, "detail_errors", FStar_Getopt.ZeroArgs ((fun _20_213 -> (match (()) with
| () -> begin
(
# 264 "FStar.Options.fst"
let _20_214 = (FStar_ST.op_Colon_Equals detail_errors true)
in (FStar_ST.op_Colon_Equals n_cores 1))
end))), "Emit a detailed error report by asking the SMT solver many queries; will take longer; implies n_cores=1; requires --universes"))::((FStar_Getopt.noshort, "dump_module", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((FStar_Getopt.noshort, "eager_inference", FStar_Getopt.ZeroArgs ((fun _20_217 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((FStar_Getopt.noshort, "explicit_deps", FStar_Getopt.ZeroArgs ((fun _20_218 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals explicit_deps true)
end))), "tell FStar to not find dependencies automatically because the user provides them on the command-line"))::((FStar_Getopt.noshort, "fs_typ_app", FStar_Getopt.ZeroArgs ((fun _20_219 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((FStar_Getopt.noshort, "fsi", FStar_Getopt.ZeroArgs ((fun _20_220 -> (match (()) with
| () -> begin
(set_interactive_fsi ())
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::((FStar_Getopt.noshort, "fstar_home", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((FStar_Getopt.noshort, "hide_genident_nums", FStar_Getopt.ZeroArgs ((fun _20_222 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((FStar_Getopt.noshort, "hide_uvar_nums", FStar_Getopt.ZeroArgs ((fun _20_223 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((FStar_Getopt.noshort, "in", FStar_Getopt.ZeroArgs ((fun _20_224 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((FStar_Getopt.noshort, "in_context", FStar_Getopt.OneArg (((fun s -> (
# 274 "FStar.Options.fst"
let _20_226 = (FStar_ST.op_Colon_Equals interactive true)
in (FStar_ST.op_Colon_Equals interactive_context (Some (s))))), "name")), "Specify the context of an interactive session; needed for --auto_deps to work with interactive mode."))::((FStar_Getopt.noshort, "include", FStar_Getopt.OneArg (((fun s -> (let _105_136 = (let _105_135 = (FStar_ST.read _include_path)
in (FStar_List.append _105_135 ((s)::[])))
in (FStar_ST.op_Colon_Equals _include_path _105_136))), "path")), "A directory in which to search for files included on the command line"))::((FStar_Getopt.noshort, "initial_fuel", FStar_Getopt.OneArg (((fun x -> (let _105_140 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals initial_fuel _105_140))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((FStar_Getopt.noshort, "initial_ifuel", FStar_Getopt.OneArg (((fun x -> (let _105_144 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals initial_ifuel _105_144))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((FStar_Getopt.noshort, "inline_arith", FStar_Getopt.ZeroArgs ((fun _20_231 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals inline_arith true)
end))), "Inline definitions of arithmetic functions in the SMT encoding"))::((FStar_Getopt.noshort, "interleave", FStar_Getopt.ZeroArgs ((fun _20_232 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals interleave true)
end))), "Interleave \'val\' declarations with the definitions in the module before type-checking"))::((FStar_Getopt.noshort, "lax", FStar_Getopt.ZeroArgs ((fun _20_233 -> (match (()) with
| () -> begin
(
# 280 "FStar.Options.fst"
let _20_234 = (FStar_ST.op_Colon_Equals pretype true)
in (FStar_ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((FStar_Getopt.noshort, "log_types", FStar_Getopt.ZeroArgs ((fun _20_236 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((FStar_Getopt.noshort, "log_queries", FStar_Getopt.ZeroArgs ((fun _20_237 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((FStar_Getopt.noshort, "max_fuel", FStar_Getopt.OneArg (((fun x -> (let _105_153 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals max_fuel _105_153))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((FStar_Getopt.noshort, "max_ifuel", FStar_Getopt.OneArg (((fun x -> (let _105_157 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals max_ifuel _105_157))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 2)"))::((FStar_Getopt.noshort, "min_fuel", FStar_Getopt.OneArg (((fun x -> (let _105_161 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals min_fuel _105_161))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((FStar_Getopt.noshort, "MLish", FStar_Getopt.ZeroArgs ((fun _20_241 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((FStar_Getopt.noshort, "n_cores", FStar_Getopt.OneArg (((fun x -> (
# 287 "FStar.Options.fst"
let _20_243 = (let _105_166 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals n_cores _105_166))
in (FStar_ST.op_Colon_Equals detail_errors false))), "positive integer")), "Maximum number of cores to use for the solver (default 1); implied detail_errors = false"))::((FStar_Getopt.noshort, "no_default_includes", FStar_Getopt.ZeroArgs ((fun _20_245 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals no_default_includes true)
end))), "Ignore the default module search paths"))::((FStar_Getopt.noshort, "no_extract", FStar_Getopt.OneArg (((fun x -> (let _105_172 = (let _105_171 = (FStar_ST.read no_extract)
in (x)::_105_171)
in (FStar_ST.op_Colon_Equals no_extract _105_172))), "module name")), "Do not extract code from this module"))::((FStar_Getopt.noshort, "no_location_info", FStar_Getopt.ZeroArgs ((fun _20_247 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals no_location_info true)
end))), "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)"))::((FStar_Getopt.noshort, "odir", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((FStar_Getopt.noshort, "prims", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((FStar_Getopt.noshort, "print_before_norm", FStar_Getopt.ZeroArgs ((fun _20_250 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((FStar_Getopt.noshort, "print_bound_var_types", FStar_Getopt.ZeroArgs ((fun _20_251 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_bound_var_types true)
end))), "Print the types of bound variables"))::((FStar_Getopt.noshort, "print_effect_args", FStar_Getopt.ZeroArgs ((fun _20_252 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((FStar_Getopt.noshort, "print_fuels", FStar_Getopt.ZeroArgs ((fun _20_253 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_fuels true)
end))), "Print the fuel amounts used for each successful query"))::((FStar_Getopt.noshort, "print_implicits", FStar_Getopt.ZeroArgs ((fun _20_254 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((FStar_Getopt.noshort, "print_universes", FStar_Getopt.ZeroArgs ((fun _20_255 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_universes true)
end))), "Print universes"))::((FStar_Getopt.noshort, "prn", FStar_Getopt.ZeroArgs ((fun _20_256 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with log_queries"))::((FStar_Getopt.noshort, "show_signatures", FStar_Getopt.OneArg (((fun x -> (let _105_191 = (let _105_190 = (FStar_ST.read show_signatures)
in (x)::_105_190)
in (FStar_ST.op_Colon_Equals show_signatures _105_191))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((FStar_Getopt.noshort, "silent", FStar_Getopt.ZeroArgs ((fun _20_258 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals silent true)
end))), " "))::((FStar_Getopt.noshort, "smt", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((FStar_Getopt.noshort, "split_cases", FStar_Getopt.OneArg (((fun n -> (let _105_199 = (FStar_Util.int_of_string n)
in (FStar_ST.op_Colon_Equals split_cases _105_199))), "t")), "Partition VC of a match into groups of n cases"))::((FStar_Getopt.noshort, "timing", FStar_Getopt.ZeroArgs ((fun _20_261 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals timing true)
end))), "Print the time it takes to verify each top-level definition"))::((FStar_Getopt.noshort, "trace_error", FStar_Getopt.ZeroArgs ((fun _20_262 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((FStar_Getopt.noshort, "universes", FStar_Getopt.ZeroArgs ((fun _20_263 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals universes true)
end))), "Use the (experimental) support for universes"))::((FStar_Getopt.noshort, "unthrottle_inductives", FStar_Getopt.ZeroArgs ((fun _20_264 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals unthrottle_inductives true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((FStar_Getopt.noshort, "use_eq_at_higher_order", FStar_Getopt.ZeroArgs ((fun _20_265 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals use_eq_at_higher_order true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((FStar_Getopt.noshort, "use_native_int", FStar_Getopt.ZeroArgs ((fun _20_266 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals use_native_int true)
end))), "Extract the \'int\' type to platform-specific native int; you will need to link the generated code with the appropriate version of the prims library"))::((FStar_Getopt.noshort, "verify_module", FStar_Getopt.OneArg (((fun x -> (let _105_210 = (let _105_209 = (FStar_ST.read verify_module)
in (x)::_105_209)
in (FStar_ST.op_Colon_Equals verify_module _105_210))), "string")), "Name of the module to verify"))::((FStar_Getopt.noshort, "__temp_no_proj", FStar_Getopt.OneArg (((fun x -> (let _105_215 = (let _105_214 = (FStar_ST.read __temp_no_proj)
in (x)::_105_214)
in (FStar_ST.op_Colon_Equals __temp_no_proj _105_215))), "string")), "Don\'t generate projectors for this module"))::(('v', "version", FStar_Getopt.ZeroArgs ((fun _20_269 -> (
# 312 "FStar.Options.fst"
let _20_271 = (display_version ())
in (FStar_All.exit 0)))), "Display version number"))::((FStar_Getopt.noshort, "warn_top_level_effects", FStar_Getopt.ZeroArgs ((fun _20_273 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((FStar_Getopt.noshort, "z3timeout", FStar_Getopt.OneArg (((fun s -> (let _105_221 = (FStar_Util.int_of_string s)
in (FStar_ST.op_Colon_Equals z3timeout _105_221))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::[]
in (('h', "help", FStar_Getopt.ZeroArgs ((fun x -> (
# 316 "FStar.Options.fst"
let _20_277 = (display_usage specs)
in (FStar_All.exit 0)))), "Display this information"))::specs)
end))
and parse_codegen : Prims.string  ->  Prims.string Prims.option = (fun s -> (match (s) with
| ("OCaml") | ("FSharp") -> begin
Some (s)
end
| _20_283 -> begin
(
# 322 "FStar.Options.fst"
let _20_284 = (FStar_Util.print_string "Wrong argument to codegen flag\n")
in (
# 323 "FStar.Options.fst"
let _20_286 = (let _105_224 = (specs ())
in (display_usage _105_224))
in (FStar_All.exit 1)))
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| _20_293 -> begin
(
# 328 "FStar.Options.fst"
let _20_294 = (FStar_Util.print_string "Wrong argument to cardinality flag\n")
in (
# 329 "FStar.Options.fst"
let _20_296 = (let _105_226 = (specs ())
in (display_usage _105_226))
in (FStar_All.exit 1)))
end))
and set_interactive_fsi : Prims.unit  ->  Prims.unit = (fun _20_298 -> if (FStar_ST.read interactive) then begin
(FStar_ST.op_Colon_Equals interactive_fsi true)
end else begin
(
# 333 "FStar.Options.fst"
let _20_300 = (FStar_Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (
# 334 "FStar.Options.fst"
let _20_302 = (let _105_228 = (specs ())
in (display_usage _105_228))
in (FStar_All.exit 1)))
end)

# 336 "FStar.Options.fst"
let should_verify : Prims.string  ->  Prims.bool = (fun m -> ((FStar_ST.read verify) && (match ((FStar_ST.read verify_module)) with
| [] -> begin
true
end
| l -> begin
(FStar_List.contains m l)
end)))

# 342 "FStar.Options.fst"
let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (let _105_233 = (FStar_ST.read __temp_no_proj)
in (FStar_List.contains m _105_233)))

# 344 "FStar.Options.fst"
let should_print_message : Prims.string  ->  Prims.bool = (fun m -> ((should_verify m) && (m <> "Prims")))

# 348 "FStar.Options.fst"
type options =
| Set
| Reset
| Restore

# 349 "FStar.Options.fst"
let is_Set = (fun _discr_ -> (match (_discr_) with
| Set (_) -> begin
true
end
| _ -> begin
false
end))

# 350 "FStar.Options.fst"
let is_Reset = (fun _discr_ -> (match (_discr_) with
| Reset (_) -> begin
true
end
| _ -> begin
false
end))

# 351 "FStar.Options.fst"
let is_Restore = (fun _discr_ -> (match (_discr_) with
| Restore (_) -> begin
true
end
| _ -> begin
false
end))

# 353 "FStar.Options.fst"
let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (
# 356 "FStar.Options.fst"
let settable = (fun _20_2 -> (match (_20_2) with
| ("admit_smt_queries") | ("cardinality") | ("debug") | ("debug_level") | ("detail_errors") | ("eager_inference") | ("hide_genident_nums") | ("hide_uvar_nums") | ("initial_fuel") | ("initial_ifuel") | ("inline_arith") | ("lax") | ("log_types") | ("log_queries") | ("max_fuel") | ("max_ifuel") | ("min_fuel") | ("print_before_norm") | ("print_bound_var_types") | ("print_effect_args") | ("print_fuels") | ("print_implicits") | ("print_universes") | ("prn") | ("show_signatures") | ("silent") | ("split_cases") | ("timing") | ("trace_error") | ("unthrottle_inductives") | ("use_eq_at_higher_order") | ("__temp_no_proj") | ("warn_top_level_effects") -> begin
true
end
| _20_344 -> begin
false
end))
in (
# 391 "FStar.Options.fst"
let resettable = (fun s -> ((settable s) || (s = "z3timeout")))
in (
# 392 "FStar.Options.fst"
let all_specs = (specs ())
in (
# 393 "FStar.Options.fst"
let settable_specs = (FStar_All.pipe_right all_specs (FStar_List.filter (fun _20_356 -> (match (_20_356) with
| (_20_350, x, _20_353, _20_355) -> begin
(((settable x)))
end))))
in (
# 394 "FStar.Options.fst"
let resettable_specs = (FStar_All.pipe_right all_specs (FStar_List.filter (fun _20_365 -> (match (_20_365) with
| (_20_359, x, _20_362, _20_364) -> begin
(((resettable x)))
end))))
in (fun o s -> (
# 396 "FStar.Options.fst"
let specs = (match (o) with
| Set -> begin
settable_specs
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_Getopt.parse_string specs (fun _20_373 -> ()) s))))))))

# 402 "FStar.Options.fst"
let restore_cmd_line_options : Prims.unit  ->  FStar_Getopt.parse_cmdline_res = (fun _20_375 -> (match (()) with
| () -> begin
(
# 403 "FStar.Options.fst"
let _20_376 = (init_options ())
in (let _105_253 = (specs ())
in (FStar_Getopt.parse_cmdline _105_253 (fun x -> ()))))
end))




