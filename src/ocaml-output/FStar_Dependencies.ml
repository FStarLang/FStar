
open Prims

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

let deps = (FStar_List.rev deps)
in (

let deps = (

let uu____56 = (

let uu____57 = (

let uu____58 = (FStar_List.hd deps)
in (FStar_Util.basename uu____58))
in (uu____57 = "prims.fst"))
in (match (uu____56) with
| true -> begin
(FStar_List.tl deps)
end
| uu____60 -> begin
((FStar_Util.print_error "dependency analysis did not find prims.fst?!");
(FStar_All.exit (Prims.parse_int "1"));
)
end))
in deps))
end)
end))
end)))




