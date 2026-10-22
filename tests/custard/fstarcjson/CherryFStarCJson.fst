module CherryFStarCJson

(* FStarC.Json-c.cherry.fst.  Parses each input, printing it back or NONE,
   then prints two values.  The expected output, CherryFStarCJson.expected,
   is what Yojson.Basic gives for the same inputs in the OCaml build, a
   float counting as NONE since [json] has none. *)

open FStar.All
open FStarC.Json
module S = FStarC.String

let inputs : list string = [
  "null";
  " \t\r\n true ";
  "false";
  "0";
  "-0";
  "1";
  "-12";
  "+1";
  "01";
  "-01";
  "00";
  "1.5";
  "1e3";
  "1.";
  "1e";
  "0x10";
  "4611686018427387903";
  "4611686018427387904";
  "-4611686018427387904";
  "-4611686018427387905";
  "99999999999999999999";
  "NaN";
  "Infinity";
  "-Infinity";
  "-";
  "--1";
  "- 1";
  "nul";
  "True";
  "nullx";
  "truex";
  "\"a\\\"b\\\\c\\/d\\b\\f\\n\\r\\t\"";
  "\"\\u00e9\\u20AC\\ud83d\\ude00\"";
  "\"\\ud83d\"";
  "\"\\ude00x\"";
  "\"\\ud83dx\"";
  "\"\\ud83d\\u0041\"";
  "\"\\uDBFF\\uDFFF\"";
  "\"\\u0000\"";
  "\"\\u001f\\u007F\"";
  "\"\\x\"";
  "\"\\u12\"";
  "\"\\uZZZZ\"";
  "\"\\U0041\"";
  "\"a\nb\"";
  "\"a\tb\x01\"";
  "\"hé€\"";
  "\"abc";
  "\"";
  "[1, 2 ,3]";
  "[]";
  "[ ]";
  "[1,]";
  "[,1]";
  "[1 2]";
  "[[[]],[{}]]";
  "[1";
  "[null,]";
  "[true ,false]";
  "[1.0]";
  "{}";
  "{ \"a\" : 1 , \"a\" : [2] }";
  "{\"a\":1,}";
  "{a:1}";
  "{'a':1}";
  "{a_b1:1,_c:2}";
  "{1a:1}";
  "{a-b:1}";
  "{null:true}";
  "{\"a\"}";
  "{\"a\" 1}";
  "{\"a\":}";
  "{\"a\":1 \"b\":2}";
  "{\"\":{\"x\":\"y\"}}";
  "{\"a\":NaN}";
  "// c\n1";
  "/* c */ [1 /* x */,2]";
  "# c\n1";
  "//x\r1";
  "//x\r\n1";
  "1//x";
  "1/*x";
  "1/*x*/";
  "/**/1";
  "/";
  "1 /";
  "{\"a\":1 // c\n}";
  "1 2";
  "1 x";
  "";
  "  ";
  "\x0c1";
  "1\x00";
  "<1>";
  "\"a\" \"b\"";
  "true false"]

let rec all_bytes (acc:string) (i:nat) : string =
  if i >= 128 then acc
  else all_bytes (S.(acc ^ string_of_char (FStar.Char.char_of_int i))) (i + 1)

let pr (s:string) : ML unit = FStar.IO.print_string s; FStar.IO.print_string "\n"

let main () : ML unit =
  List.iter (fun s ->
    match json_of_string s with
    | Some j -> pr (string_of_json j)
    | None -> pr "NONE") inputs;
  pr (string_of_json (JsonStr (all_bytes "" 0)));
  pr (string_of_json (JsonAssoc [("k\n", JsonList [JsonNull; JsonBool true; JsonInt (-42); JsonStr "é"]);
                                 ("", JsonAssoc []); ("l", JsonList [])]))
