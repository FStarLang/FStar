
open Prims
open FStar_Pervasives

let find_deps_if_needed : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun verify_mode files -> (

let uu____12 = (FStar_Options.explicit_deps ())
in (match (uu____12) with
| true -> begin
files
end
| uu____14 -> begin
(

let uu____15 = (FStar_Parser_Dep.collect verify_mode files)
in (match (uu____15) with
| (uu____29, deps, uu____31) -> begin
(match (deps) with
| [] -> begin
((FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided");
files;
)
end
| uu____52 -> begin
(

let deps1 = (FStar_List.rev deps)
in (

let deps2 = (

let prims1 = (FStar_Options.prims_basename ())
in (

let uu____59 = (

let uu____60 = (

let uu____61 = (FStar_List.hd deps1)
in (FStar_Util.basename uu____61))
in (uu____60 = prims1))
in (match (uu____59) with
| true -> begin
(FStar_List.tl deps1)
end
| uu____63 -> begin
((FStar_Util.print1_error "dependency analysis did not find prims module %s?!" prims1);
(FStar_All.exit (Prims.parse_int "1"));
)
end)))
in deps2))
end)
end))
end)))




