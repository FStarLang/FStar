
open Prims
open FStar_Pervasives

let main : 'Auu____6 'Auu____7 . 'Auu____6  ->  'Auu____7 = (fun argv -> ((FStar_Util.print_string "Initializing ...\n");
(FStar_All.try_with (fun uu___3_19 -> (match (()) with
| () -> begin
((

let uu____21 = (FStar_Tests_Pars.init ())
in (FStar_All.pipe_right uu____21 (fun a1 -> ())));
(FStar_Tests_Norm.run_all ());
(

let uu____24 = (FStar_Tests_Unif.run_all ())
in (match (uu____24) with
| true -> begin
()
end
| uu____27 -> begin
(FStar_All.exit (Prims.parse_int "1"))
end));
(FStar_All.exit (Prims.parse_int "0"));
)
end)) (fun uu___2_36 -> (match (uu___2_36) with
| FStar_Errors.Error (err, msg, r) when (

let uu____42 = (FStar_Options.trace_error ())
in (FStar_All.pipe_left Prims.op_Negation uu____42)) -> begin
((match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(FStar_Util.print_string msg)
end
| uu____48 -> begin
(

let uu____50 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" uu____50 msg))
end);
(FStar_All.exit (Prims.parse_int "1"));
)
end)));
))




