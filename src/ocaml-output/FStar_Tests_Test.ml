
open Prims
open FStar_Pervasives

let main : 'Auu____4 'Auu____5 . 'Auu____4  ->  'Auu____5 = (fun argv -> ((FStar_Util.print_string "Initializing ...\n");
(FStar_All.try_with (fun uu___79_15 -> (match (()) with
| () -> begin
((

let uu____17 = (FStar_Tests_Pars.init ())
in (FStar_All.pipe_right uu____17 FStar_Pervasives.ignore));
(FStar_Tests_Norm.run_all ());
(FStar_Tests_Unif.run_all ());
(FStar_All.exit (Prims.parse_int "0"));
)
end)) (fun uu___78_25 -> (match (uu___78_25) with
| FStar_Errors.Error (err, msg, r) when (

let uu____29 = (FStar_Options.trace_error ())
in (FStar_All.pipe_left Prims.op_Negation uu____29)) -> begin
((match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(FStar_Util.print_string msg)
end
| uu____31 -> begin
(

let uu____32 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" uu____32 msg))
end);
(FStar_All.exit (Prims.parse_int "1"));
)
end)));
))




