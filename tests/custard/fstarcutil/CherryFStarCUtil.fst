module CherryFStarCUtil

(* FStarC.Util-c.cherry.fst: the string and number functions, files and
   directories, processes, the command line and the environment, [exit] and
   [raise_notrace].  CHERRY_UTIL_TMP names a fresh directory to work in. *)
open FStarC.Effect
module U = FStarC.Util
module IA = FStar.ImmutableArray

let check (b:bool) (n:int) (acc:int) : int = if b then acc else acc * 100 + n

let fails (#a:Type) (f:unit -> ML a) : ML bool =
  try_with (fun () -> let _ = f () in false)
           (fun e -> match e with Failure _ -> true | _ -> false)

let main () : ML FStar.UInt32.t =
  let e = 0 in
  (* Strings, as Batteries. *)
  let e = check (U.trim_string " \t a b \n\x0c" = "a b" && U.trim_string "\x0bx" = "\x0bx"
                 && U.trim_string "   " = "") 1 e in
  let e = check (U.starts_with "hello" "he" && not (U.starts_with "he" "hello")
                 && U.ends_with "hello" "llo" && U.ends_with "x" "" && not (U.ends_with "lo" "hello")
                 && U.contains "hello" "ll" && U.contains "" "" && not (U.contains "hello" "lol")) 2 e in
  let s1 = U.substring_from "abc" 5 in
  let s2 = U.substring "hello" 1 3 in
  let f1 = fails (fun () -> U.substring_from "abc" (-1)) in
  let f2 = fails (fun () -> U.substring "abc" 2 5) in
  let e = check (s1 = "" && s2 = "ell" && f1 && f2) 3 e in
  let e = check (U.replace_char "a.b.c" '.' '/' = "a/b/c" && U.replace_chars "a.b." '.' "::" = "a::b::"
                 && U.split "a,b" "," = ["a"; "b"] && U.splitlines "" = [""]
                 && U.concat_dir_filename "a" "b" = "a/b" && U.concat_dir_filename "a/" "b" = "a/b"
                 && U.concat_dir_filename "" "b" = "b") 4 e in
  (* Integers, as Zarith. *)
  let i1 = U.int_of_string "0x1F" in
  let i2 = U.int_of_string "-0b101" in
  let i3 = U.int_of_string "1_000" in
  let i4 = U.int_of_string "" in
  let i5 = U.int_of_string "123456789012345678901234567890" in
  let f1 = fails (fun () -> U.int_of_string "1e3") in
  let f2 = fails (fun () -> U.int_of_string " 1") in
  let e = check (i1 = 31 && i2 = -5 && i3 = 1000 && i4 = 0 && f1 && f2
                 && string_of_int i5 = "123456789012345678901234567890") 5 e in
  let e = check (U.safe_int_of_string "" = None && U.safe_int_of_string "+12" = Some 12
                 && U.safe_int_of_string "z" = None && U.ensure_decimal "0xff" = "255") 6 e in
  (* Floats and conversions. *)
  let f1 = fails (fun () -> U.float_of_string "junk") in
  let e = check (U.string_of_float (U.float_of_string "1.5") = "1.5"
                 && U.string_of_float (U.float_of_int64 3L) = "3."
                 && U.string_of_float (U.float_of_string "-0") = "-0." && f1) 7 e in
  let e = check (U.hex_string_of_byte 10uy = "0a" && U.hex_string_of_byte 255uy = "ff"
                 && U.int32_of_int 0x80000000 = (-2147483648l) && U.int_of_char 'A' = 65
                 && U.char_of_int 0xe9 = '\u00e9' && U.uint16_of_int 65537 = 1us) 8 e in
  (* Base64 without padding, MD5. *)
  let b1 = U.base64_encode "hello" in
  let b2 = U.base64_decode "aGVsbG8" in
  let f1 = fails (fun () -> U.base64_decode "aGVsbG8=") in
  let d1 = U.digest_of_string "" in
  let d2 = U.digest_of_string "abc" in
  let e = check (b1 = "aGVsbG8" && b2 = "hello" && f1
                 && d1 = "d41d8cd98f00b204e9800998ecf8427e"
                 && d2 = "900150983cd24fb0d6963f7d28e17f72") 9 e in
  (* Files and directories. *)
  let tmp = match U.expand_environment_variable "CHERRY_UTIL_TMP" with Some d -> d | None -> "" in
  let none = U.expand_environment_variable "CHERRY_UTIL_UNSET" in
  let e = check (tmp <> "" && None? none) 10 e in
  let f = tmp ^ "/a/b/f.txt" in
  U.write_file f "x\ny";
  let c = U.file_get_contents f in
  let ls = U.file_get_lines f in
  U.copy_file f (tmp ^ "/a/g.txt");
  let dg = U.digest_of_file (tmp ^ "/a/g.txt") in
  let e = check (c = "x\ny\n" && ls = ["x"; "y"] && dg = U.digest_of_string "x\ny\n") 11 e in
  U.delete_file f;
  let f1 = fails (fun () -> U.file_get_contents f) in
  U.mkdir true false (tmp ^ "/a");
  let f2 = fails (fun () -> U.file_get_contents (tmp ^ "/a/g.txt")) in
  let f3 = fails (fun () -> U.mkdir false false (tmp ^ "/x/y")) in
  let oc = U.open_file_for_appending (tmp ^ "/a/h.txt") in
  U.append_to_file oc "1";
  U.close_out_channel oc;
  let oc = U.open_file_for_appending (tmp ^ "/a/h.txt") in
  U.append_to_file oc "2";
  U.close_out_channel oc;
  let h = U.file_get_contents (tmp ^ "/a/h.txt") in
  let e = check (f1 && f2 && f3 && h = "1\n2\n") 12 e in
  (* Processes. *)
  let r1 = U.run_process "t" "sh" ["-c"; "tr a-z A-Z; echo err >&2"] (Some "in") in
  let r2 = U.system_run "exit 3" in
  let pid = U.create_process "sh" ["sh"; "-c"; "exit 4"] in
  let w = U.waitpid pid in
  let e = check (r1 = "IN" && r2 = 3 && w = Inl 4) 13 e in
  let p = U.start_process "t" "cat" [] (fun s -> s = "done") in
  let a1 = U.ask_process p "  hello \ndone\n" (fun () -> "EOF") (fun _ -> ()) in
  let a2 = U.ask_process p "bye\ndone\n" (fun () -> "EOF") (fun _ -> ()) in
  U.kill_process p;
  let e = check (a1 = "hello\n" && a2 = "bye\n" && U.proc_prog p = "cat") 14 e in
  (* The command line. *)
  let args = U.get_cmd_args () in
  let e = check (args = [U.argv0; "arg1"] && U.ends_with U.exec_name "CherryFStarCUtil.chexe"
                 && U.ends_with (U.get_exec_dir ()) "fstarcutil") 15 e in
  (* Exceptions. *)
  let m = U.message_of_exn (Failure "boom") in
  let r = try_with (fun () -> (raise_notrace (Failure "x") <: string)) (fun e -> match e with Failure s -> s | _ -> "") in
  let fin = mk_ref 0 in
  let f1 = fails (fun () -> U.finally (fun () -> fin := !fin + 1) (fun () -> (failwith "y" <: int))) in
  let v = U.finally (fun () -> fin := !fin + 10) (fun () -> 7) in
  let e = check (m = "Failure(\"boom\")" && r = "x" && f1 && v = 7 && !fin = 11) 16 e in
  (* Lists and arrays. *)
  let f1 = fails (fun () -> U.first_N 5 [1]) in
  let f2 = fails (fun () -> U.array_index (IA.of_list [1]) 1) in
  let e = check (U.first_N 2 [1; 2; 3] = ([1; 2], [3]) && U.prefix [1; 2; 3] = ([1; 2], 3)
                 && U.nth_tail 2 [1; 2; 3] = [3] && f1 && f2
                 && U.print_array string_of_int (IA.of_list [1; 2]) = "[| 1; 2 |]"
                 && U.array_length (IA.of_list [1; 2]) = 2) 17 e in
  let l = [1; 2] in
  let e = check (U.physical_equality l l && U.is_symbol '~' && not (U.is_symbol '_')
                 && U.is_letter 'q' && not (U.is_letter '\u00e9') && U.is_punctuation ';'
                 && U.hashcode "abc" = U.hashcode "abc" && U.hashcode "abc" >= 0) 18 e in
  U.set_sigint_handler U.sigint_ignore;
  let k = U.with_sigint_handler U.sigint_raise (fun () -> 5) in
  U.set_sigint_handler U.sigint_raise;
  let e = check (k = 5) 19 e in
  if e <> 0 then (U.print_endline (string_of_int e); 1ul)
  else (exit 0; 1ul)
