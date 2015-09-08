module Hello
open FStar.IO

let print_message x =
    print_string x

;;

(* The "main" expression is delimited
   from the rest of the module by ';;' *)
   
print_message "Hello F*!\n"


