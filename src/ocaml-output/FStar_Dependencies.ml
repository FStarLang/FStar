
open Prims
open FStar_Pervasives

let find_deps_if_needed : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun verify_mode files -> (

let uu____10 = (FStar_Options.explicit_deps ())
in (match (uu____10) with
| true -> begin
files
end
| uu____12 -> begin
(

let uu____13 = (FStar_Parser_Dep.collect verify_mode files)
in (match (uu____13) with
| (uu____27, deps, uu____29) -> begin
(match (deps) with
| [] -> begin
((FStar_Util.print_error "Dependency analysis failed; reverting to using only the files provided");
files;
)
end
| uu____50 -> begin
(

let deps1 = (FStar_List.rev deps)
in (

let deps2 = (

let prims1 = (FStar_Options.prims_basename ())
in (

let uu____57 = (

let uu____58 = (

let uu____59 = (FStar_List.hd deps1)
in (FStar_Util.basename uu____59))
in (uu____58 = prims1))
in (match (uu____57) with
| true -> begin
(FStar_List.tl deps1)
end
| uu____61 -> begin
((FStar_Util.print1_error "dependency analysis did not find prims module %s?!" prims1);
(FStar_All.exit (Prims.parse_int "1"));
)
end)))
in deps2))
end)
end))
end)))




