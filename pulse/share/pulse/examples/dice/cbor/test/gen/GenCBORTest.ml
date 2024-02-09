type c = [
| `If of string
| `Instr of string
| `Block of c list
]

let gen_int (x: int) (name: string) : c list =
  let major_type, count =
    if x >= 0
    then ("UINT64", x)
    else ("NEG_INT64", -1-x)
  in
  [`Instr ("cbor " ^ name ^ " = cbor_constr_int64(CBOR_MAJOR_TYPE_" ^ major_type ^ "," ^ string_of_int count ^ ")")]

let quote_string s = Yojson.Safe.to_string (`String s)

let gen_string (s: string) (name: string) : c list =
  [`Instr ("cbor " ^ name ^ " = cbor_constr_string(CBOR_MAJOR_TYPE_TEXT_STRING, (uint8_t *" ^ ")" ^ quote_string s ^ ", " ^ string_of_int (String.length s) ^ ")")]

let gen_map (gen: Yojson.Safe.t -> string -> c list) (l: (string * Yojson.Safe.t) list) (name: string) : c list =
  let len = List.length l in
  let elt i = name ^ "_map[" ^ string_of_int i ^ "]" in
  let accu = [`Instr ("cbor " ^ name ^ " = cbor_constr_map(" ^ name ^ "_map, " ^ string_of_int len ^ ")")] in
  let rec aux accu i = function
  | [] -> accu
  | (s, x) :: q->
    let key_name = name ^ "_map_" ^ string_of_int i ^ "_key" in
    let value_name = name ^ "_map_" ^ string_of_int i ^ "_value" in
    let accu' =
      gen_string s key_name @
      gen x value_name @
      `Instr (elt i ^ " = (cbor_map_entry) {.cbor_map_entry_key = " ^ key_name ^ ", .cbor_map_entry_value = " ^ value_name ^ "}") ::
      accu
    in
    aux accu' (i + 1) q
  in
  let accu' = aux accu 0 l in
  let accu' = `Instr ("cbor_map_entry " ^ elt len) :: accu' in
  accu'

let gen_array (gen: Yojson.Safe.t -> string -> c list) (l: Yojson.Safe.t list) (name: string) : c list =
  let len = List.length l in
  let elt i = name ^ "_array[" ^ string_of_int i ^ "]" in
  let accu = [`Instr ("cbor " ^ name ^ " = cbor_constr_array(" ^ name ^ "_array, " ^ string_of_int len ^ ")")] in
  let rec aux accu i = function
  | [] -> accu
  | x :: q->
    let value_name = name ^ "_map_" ^ string_of_int i in
    let accu' =
      gen x value_name @
      `Instr (elt i ^ " = " ^ value_name) ::
      accu
    in
    aux accu' (i + 1) q
  in
  let accu' = aux accu 0 l in
  let accu' = `Instr ("cbor " ^ elt len) :: accu' in
  accu'

exception GenUnsupported

let rec gen (x: Yojson.Safe.t) (name: string) : c list =
  match x with
  | `Int x -> gen_int x name
  | `String x -> gen_string x name
  | `Assoc x -> gen_map gen x name
  | `List x -> gen_array gen x name
  | _ -> raise GenUnsupported

let gen_hex (l: string) (name: string) : int * string =
  let len = String.length l in
  let (l, len) =
    if len mod 2 = 0
    then (l, len)
    else ("0" ^ l, 1 + len)
  in
  let count = len / 2 in
  let accu = "uint8_t " ^ name ^ "[" ^ string_of_int count ^ "] = {" in
  let rec aux accu x =
    if x = len
    then accu
    else if x = len - 2
    then accu ^ "0x" ^ String.sub l x 2
    else
      let accu' = accu ^ "0x" ^ String.sub l x 2 ^ ", " in
      aux accu' (x + 2)
  in
  (count, aux accu 0 ^ "}")

let list_assoc x l =
  try
    Some (List.assoc x l)
  with Not_found -> None

let gen_encoding_test_c
  (count: int)
  (num: int ref)
  (item: Yojson.Safe.t * string * (c list))
: c
= num := !num + 1;
  let (decoded, hex_encoded, decoded_c) = item in
  let decoded_s = quote_string (Yojson.Safe.to_string decoded) in
  let (size, source_bytes) = gen_hex hex_encoded "source_bytes" in
  let size_s = string_of_int size in
  `Block (
    `Instr ("printf(\"Test " ^ string_of_int !num ^ " out of " ^ string_of_int count ^ "\\n\")") ::
    `Instr ("printf(\"Testing: \"" ^ decoded_s ^ "\"\\n\")") ::
    `Instr source_bytes ::
    decoded_c @
    `Instr ("uint8_t target_bytes[" ^ size_s ^ "]") ::
    `Instr ("size_t target_bytes_written = cbor_write (source_cbor, target_bytes, " ^ size_s ^ ")") ::
    `If ("target_bytes_written != " ^ size_s) ::
    `Block (
        `Instr ("printf(\"Encoding failed: expected " ^ size_s ^ " bytes, wrote %ld\\n\", target_bytes_written)") ::
        `Instr ("dump_encoding_test_failure(target_bytes, target_bytes_written)") ::
        `Instr ("return 1") ::
        []
     ) ::
    `Instr ("int compare_encoding = memcmp(source_bytes, target_bytes, " ^ size_s ^ ")") ::
    `If ("compare_encoding != 0") ::
    `Block (
        `Instr ("printf(\"Encoding mismatch: expected " ^ hex_encoded ^ "\\n\")") ::
        `Instr ("dump_encoding_test_failure(target_bytes, target_bytes_written)") ::
        `Instr ("return 1") ::
        []
     ) ::
    `Instr ("printf(\"Encoding succeeded!\\n\")") ::
    `Instr ("cbor_read_t target_cbor = cbor_read(source_bytes, " ^ size_s ^ ")") ::
    `If ("! (target_cbor.cbor_read_is_success)") ::
    `Block (
        `Instr ("printf(\"Decoding failed!\\n\")") ::
        `Instr ("return 1") ::
        []
    ) ::
    `If ("! (CBOR_Pulse_cbor_is_equal(source_cbor, target_cbor.cbor_read_payload))") ::
    `Block (
        `Instr ("printf(\"Decoding mismatch!\\n\")") ::
        `Instr ("return 1") ::
        []
    ) ::
    `Instr ("printf(\"Decoding succeeded!\\n\")") ::
    []
  )

let extract_encoding_test
  (item0: Yojson.Safe.t)
: Yojson.Safe.t * string * c list
=
match item0 with
| `Assoc item -> 
  begin match list_assoc "roundtrip" item with
  | Some (`Bool true) ->
     begin match list_assoc "decoded" item with
     | Some decoded ->
        begin match list_assoc "hex" item with
        | Some (`String hex) ->
          begin try
              (decoded, hex, gen decoded "source_cbor")
          with GenUnsupported -> begin
              prerr_endline ("skipping unsupported encoding test: " ^ Yojson.Safe.to_string item0);
              (decoded, "", [])
              end
          end
        | _ -> failwith ("Not a valid test case assoc (hex):" ^ Yojson.Safe.to_string item0)
        end
     | None ->
        prerr_endline ("skipping no-decoded test case: " ^ Yojson.Safe.to_string item0);
        (item0, "", [])
     end
  | Some (`Bool false) ->
     prerr_endline ("skipping non-roundtrip test case: " ^ Yojson.Safe.to_string item0);
     (item0, "", [])
  | _ ->
     failwith ("Not a valid test case assoc (roundtrip): " ^ Yojson.Safe.to_string item0)
  end
| _ -> failwith ("Not a valid test case (expected map): " ^ Yojson.Safe.to_string item0)

let gen_encoding_tests
  (x: Yojson.Safe.t)
: c list
= match x with
  | `List items ->
     let l = List.map extract_encoding_test items in
     let len = List.length l in
     let l' = List.filter (function (_, _, []) -> false | _ -> true) l in
     let len' = List.length l' in
     prerr_endline (string_of_int len' ^ " tests supported out of a total " ^ string_of_int len);
     let num = ref 0 in
     List.map (gen_encoding_test_c len' num) l'
  | _ -> failwith ("Not a valid test suite: (expected array): " ^ Yojson.Safe.to_string x)

let rec c_to_string
  (indent: string)
  (x: c)
: string
= match x with
  | `If x -> indent ^ "if (" ^ x ^ ")\n"
  | `Instr x -> indent ^ x ^ ";\n"
  | `Block x -> indent ^ "{\n" ^ c_list_to_string (indent ^ "  ") "" x ^ indent ^ "}\n"

and c_list_to_string
  (indent: string)
  (accu: string)
  (l: c list)
= match l with
  | [] -> accu
  | a :: q -> c_list_to_string indent (accu ^ c_to_string indent a) q

let mk_prog (x: c list) = "
#include <string.h>
#include <stdio.h>
#include <inttypes.h>
#include \"CBOR.h\"
#include \"CBOR_Pulse.h\"

char * hex_digits[16] = {\"0\", \"1\", \"2\", \"3\", \"4\", \"5\", \"6\", \"7\", \"8\", \"9\", \"a\", \"b\", \"c\", \"d\", \"e\", \"f\"};

void dump_encoding_test_failure (uint8_t *bytes, size_t len) {
  size_t pos = 0;
  printf(\"Encoded bytes: \");
  while (pos < len) {
    uint8_t x = bytes[pos];
    printf(\"%s%s\", hex_digits[x / 16], hex_digits[x % 16]);
    pos += 1;
  };
  printf(\"\\n\");
}

int main(void) {
"
  ^ c_list_to_string "  " "" x ^ "
  return 0;
}
"

let _ =
  let rec aux accu i =
    if i = Array.length Sys.argv
    then accu
    else
      let accu' = accu @ gen_encoding_tests (Yojson.Safe.from_file Sys.argv.(i)) in
      aux accu' (i + 1)
  in
  let body = aux [] 1 in (* skip argv[0] *)
  let prog = mk_prog body in
  print_endline prog
