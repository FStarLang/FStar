module SepApp
open SepLib
open FStar.List.Tot

let main () : FStar.All.ML unit =
  FStar.IO.print_string (string_of_int (sum_areas [Circle 2; Rect 3 4]));
  FStar.IO.print_string " ";
  FStar.IO.print_string (string_of_int (area (Circle 5)));
  FStar.IO.print_string " ";
  FStar.IO.print_string (string_of_int (bump ({ untag = 41 })).untag);
  FStar.IO.print_string "\n"
