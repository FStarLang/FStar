module Hello
open FStar.IO

let print_message x =
    print_string x

let main =
  print_message "Hello F*!\n"
