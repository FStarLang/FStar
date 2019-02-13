
open Prims
open FStar_Pervasives

let main : 'Auu____7 'Auu____8 . 'Auu____7  ->  'Auu____8 = (fun argv -> ((FStar_Util.print_string "Initializing ...\n");
(FStar_All.try_with (fun uu___485_21 -> (match (()) with
| () -> begin
((FStar_Main.setup_hooks ());
(

let uu____24 = (FStar_Tests_Pars.init ())
in (FStar_All.pipe_right uu____24 (fun a1 -> ())));
(FStar_Tests_Norm.run_all ());
(

let uu____27 = (FStar_Tests_Unif.run_all ())
in (match (uu____27) with
| true -> begin
()
end
| uu____30 -> begin
(FStar_All.exit (Prims.parse_int "1"))
end));
(FStar_All.exit (Prims.parse_int "0"));
)
end)) (fun uu___484_39 -> (match (uu___484_39) with
| FStar_Errors.Error (err, msg, r) when (

let uu____45 = (FStar_Options.trace_error ())
in (FStar_All.pipe_left Prims.op_Negation uu____45)) -> begin
((match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(FStar_Util.print_string msg)
end
| uu____51 -> begin
(

let uu____53 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" uu____53 msg))
end);
(FStar_All.exit (Prims.parse_int "1"));
)
end)));
))




