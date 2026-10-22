module CherryFStarCString

(* FStarC.String-c.cherry.fst: byte- and code-point-level access, malformed
   UTF-8, the failures, and long strings built in place. *)
open FStarC.Effect
module S = FStarC.String
module I = FStarC.SmallInt

let check (b:bool) (n:int) (acc:int) : int = if b then acc else acc * 100 + n

let fails (#a:Type) (f:unit -> ML a) : ML bool =
  try_with (fun () -> let _ = f () in false)
           (fun e -> match e with Failure _ -> true | _ -> false)

let e_acute : FStar.Char.char = '\u00e9'

let rec build (n:nat) (acc:list string) : list string =
  if n = 0 then acc else build (n - 1) ("ab" :: acc)

let rec count (#a:Type) (l:list a) (n:nat) : Tot nat (decreases l) =
  match l with [] -> n | _ :: t -> count t (n + 1)

let main () : ML FStar.UInt32.t =
  let h = "h\u00e9llo" in
  let e = 0 in
  let e = check (I.to_int (S.byte_length h) = 6 && I.to_int (S.byte_at h (I.of_int 1)) = 0xC3
                 && S.byte_at h (I.of_int 6) = I.minus_one
                 && S.byte_at h I.minus_one = I.minus_one) 1 e in
  let e = check (I.to_int (S.code_point_at h I.one) = 0xE9
                 && I.to_int (S.next_code_point h I.one) = 3
                 && I.to_int (S.next_code_point h (I.of_int 5)) = 6) 2 e in
  let e = check (S.byte_substring h (I.of_int 1) (I.of_int 3) = "\u00e9"
                 && S.byte_substring h (I.of_int (-5)) (I.of_int 99) = h
                 && S.byte_substring h (I.of_int 4) (I.of_int 2) = "") 3 e in
  let e = check (S.split_on_string "a,,b" "," = ["a"; ""; "b"]
                 && S.split_on_string "" "," = [] && S.split_on_string "ab" "" = ["ab"]
                 && S.split_on_string "x::y::" "::" = ["x"; "y"; ""]) 4 e in
  let m1 = S.make 3 'x' in
  let m2 = S.make (-1) 'x' in
  let e = check (m1 = "xxx" && m2 = "" && S.split [','; ';'] "a,b;c" = ["a"; "b"; "c"]) 5 e in
  let e = check (S.strcat "a" "b" = "ab" && S.op_Hat "c" "d" = "cd"
                 && S.concat ", " ["a"; "b"; "c"] = "a, b, c" && S.concat "x" [] = ""
                 && S.concat "-" ["only"] = "only") 6 e in
  let e = check (S.compare "ab" "abc" < 0 && S.compare "b" "abc" > 0 && S.compare "q" "q" = 0) 7 e in
  let e = check (S.strlen h = 5 && S.length "" = 0) 8 e in
  let e = check (S.lowercase "Ab\u00c9Z" = "ab\u00c9z" && S.uppercase "ab\u00e9z" = "AB\u00e9Z") 9 e in
  let one = S.string_of_char (FStar.Char.char_of_u32 1ul) in
  let del = S.string_of_char (FStar.Char.char_of_u32 127ul) in
  let e = check (S.escaped "a\"b\\c\n\t\r" = "a\\\"b\\\\c\\n\\t\\r"
                 && S.escaped "\u00e9~ '" = "\\195\\169~ '"
                 && S.escaped one = "\\001" && S.escaped del = "\\127") 10 e in
  let c200 = S.string_of_char (FStar.Char.char_of_u32 200ul) in
  let e = check (S.string_of_char 'a' = "a" && I.to_int (S.byte_length c200) = 1) 11 e in
  let s1 = S.substring h 1 3 in
  let f1 = fails (fun () -> S.substring h 3 3) in
  let f2 = fails (fun () -> S.substring h (-1) 1) in
  let g1 = S.get h 1 in
  let f3 = fails (fun () -> S.get h 5) in
  let f4 = fails (fun () -> S.index h (-1)) in
  let e = check (s1 = "\u00e9ll" && f1 && f2 && g1 = e_acute && f3 && f4) 12 e in
  let c = S.collect (fun c -> if c = e_acute then "e" else S.string_of_char c) h in
  let i1 = S.index_of h 'l' in
  let i2 = S.index_of h 'z' in
  let e = check (c = "hello" && i1 = 2 && i2 = -1) 13 e in
  let e = check (S.list_of_string h = ['h'; e_acute; 'l'; 'l'; 'o']
                 && S.string_of_list ['h'; e_acute; '\u03b1'] = "h\u00e9\u03b1"
                 && S.string_of_list (S.list_of_string "\u20ac\U0001F600") = "\u20ac\U0001F600") 14 e in
  (* Malformed UTF-8: a lone continuation byte, a truncated sequence. *)
  let bad = S.strcat (S.byte_substring "\u00e9" I.one (I.of_int 2)) "x" in
  let trunc = S.strcat "a" (S.byte_substring "\u00e9" I.zero I.one) in
  let fffd = FStar.Char.char_of_u32 0xFFFDul in
  let e = check (I.to_int (S.code_point_at bad I.zero) = 0xFFFD
                 && S.list_of_string trunc = ['a'; fffd]) 15 e in
  (* Long results are built in place. *)
  let big = S.concat "" (build 200000 []) in
  let big2 = S.string_of_list (S.list_of_string big) in
  let big3 = S.collect (fun c -> S.string_of_char c) big in
  let e = check (I.to_int (S.byte_length big) = 400000 && big2 = big && big3 = big
                 && S.strlen big = 400000 && count (S.split_on_string big "ba") 0 = 200000) 16 e in
  if e = 0 then 0ul else 1ul
