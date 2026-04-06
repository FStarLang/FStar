module ParseTest

(** Regression test for GitHub issue #4103:
    FStar.Parse module was not implemented at runtime. *)

open FStar.IO
open FStar.All
open FStar.Parse

let check (name: string) (b: bool) : ML unit =
  if b then
    print_string ("OK: " ^ name ^ "\n")
  else begin
    print_string ("FAIL: " ^ name ^ "\n");
    failwith ("Test failed: " ^ name)
  end

(* Use a helper to prevent F* from reducing the calls at verification time,
   so the extracted code actually exercises FStar_Parse at runtime. *)
let parse_int (s: string) : ML (option int) = int_of_string s
let parse_bool (s: string) : ML (option bool) = bool_of_string s

let _ =
  (* int_of_string tests *)
  check "int_of_string empty" (parse_int "" = None);
  check "int_of_string 1" (parse_int "1" = Some 1);
  check "int_of_string -1" (parse_int "-1" = Some (0 - 1));
  check "int_of_string 1234567890" (parse_int "1234567890" = Some 1234567890);
  check "int_of_string 15x1" (parse_int "15x1" = None);
  check "int_of_string x1" (parse_int "x1" = None);
  check "int_of_string 0x100" (parse_int "0x100" = Some 256);
  check "int_of_string 0b100" (parse_int "0b100" = Some 4);

  (* bool_of_string tests *)
  check "bool_of_string true" (parse_bool "true" = Some true);
  check "bool_of_string false" (parse_bool "false" = Some false);
  check "bool_of_string empty" (parse_bool "" = None);
  check "bool_of_string yes" (parse_bool "yes" = None);

  (* The repro from issue #4103: using int_of_string at runtime *)
  (match parse_int "35" with
   | None -> failwith "int_of_string 35 returned None"
   | Some n -> print_string (string_of_int n ^ "\n"))
