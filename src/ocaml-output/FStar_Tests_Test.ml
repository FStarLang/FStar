
open Prims
open FStar_Pervasives

let main : 'Auu____7 'Auu____8 . 'Auu____7  ->  'Auu____8 = (fun argv -> ((FStar_Util.print_string "Initializing ...\n");
(FStar_All.try_with (fun uu___80_19 -> (match (()) with
| () -> begin
((

let uu____21 = (FStar_Tests_Pars.init ())
in (FStar_All.pipe_right uu____21 (fun a248 -> ())));
(FStar_Tests_Norm.run_all ());
(

let uu____24 = (FStar_Tests_Unif.run_all ())
in (match (uu____24) with
| true -> begin
()
end
| uu____25 -> begin
(FStar_All.exit (Prims.parse_int "1"))
end));
(FStar_All.exit (Prims.parse_int "0"));
)
end)) (fun uu___79_31 -> (match (uu___79_31) with
| FStar_Errors.Error (err, msg, r) when (

let uu____35 = (FStar_Options.trace_error ())
in (FStar_All.pipe_left Prims.op_Negation uu____35)) -> begin
((match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(FStar_Util.print_string msg)
end
| uu____37 -> begin
(

let uu____38 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" uu____38 msg))
end);
(FStar_All.exit (Prims.parse_int "1"));
)
end)));
))




