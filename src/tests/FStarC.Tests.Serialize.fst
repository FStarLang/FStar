(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Tests.Serialize
// tests of FStarC.Serialize: every backend must write the same bytes
open FStarC
open FStarC.Effect
open FStarC.Class.Show
open FStarC.Class.Deq
open FStarC.Serialize
module BB = FStarC.ByteBuffer
module I = FStarC.SmallInt

let check (what:string) (b:bool) : ML unit =
  if not b then failwith ("Serialize test failed: " ^ what)

let rec upto (i n:int) (f:int -> ML 'a) : ML (list 'a) =
  if i >= n then [] else let x = f i in x :: upto (i + 1) n f

let bytes_of (s:string) : ML (list int) =
  upto 0 (I.to_int (FStarC.String.byte_length s))
    (fun i -> I.to_int (FStarC.String.byte_at s (I.of_int i)))

let roundtrip (#a:Type) {| serializable a |} {| deq a |} {| showable a |} (x:a) : ML unit =
  let y = deserialize (serialize x) in
  check ("roundtrip of " ^ show x ^ ", got " ^ show y) (x =? y)

let ints : list int = [
  0; 1; -1; 63; 64; -64; -65; 127; 128; 300; -300;
  0xfffffffffffffff; 0x1000000000000000 - 1; 0x1000000000000000;
  -0x1000000000000000; -0x1000000000000000 - 1;
  0x7fffffffffffffff; 0x10000000000000000; -0x10000000000000000;
  100000000000000000000000000000000000000000; -100000000000000000000000000000000000000000;
]

let run_all () : ML unit =
  Format.print_string "serialize tests\n";
  ints |> List.iter (fun i -> roundtrip i);
  roundtrip ints;
  roundtrip [Some "a"; None; Some ""; Some "\u00e9 z"];
  roundtrip (true, false, (), [Inl 1; Inr "x"]);
  roundtrip ([[1;2];[];[3]], ("x", -7));
  let (a, b) : I.t & I.t = deserialize (serialize (I.of_int (-5), I.of_int 1000000)) in
  check "smallint roundtrip" (I.to_int a = -5 && I.to_int b = 1000000);
  let cs = ['a'; '\n'; FStar.Char.char_of_int 0x1F600] in
  let cs' : list FStar.Char.char = deserialize (serialize cs) in
  check "char roundtrip" (cs = cs');

  (* The exact bytes, which must not depend on the backend. *)
  let golden = bytes_of (serialize (["ab"; "ab"], -2, 0x1000000000000000, Some true)) in
  let expect = [
    2; 0; 2; 97; 98; 1;          (* a list of two strings, the second shared *)
    6;                           (* -2: the varint of twice zigzag(-2) = 3 *)
    1; 19; 49; 49; 53; 50; 57; 50; 49; 53; 48; 52; 54; 48; 54; 56; 52; 54; 57; 55; 54;
                                 (* 2^60 is big: tag 1, its decimal digits *)
    1; 1                         (* Some true *)
  ] in
  check ("golden bytes: " ^ show golden) (golden = expect);

  (* Sharing: equal strings are written once, and read back as one value. *)
  let s = "a fairly long string, repeated" in
  let l = upto 0 100 (fun i -> if i % 2 = 0 then s else "x" ^ s) in
  let b = serialize l in
  check "sharing keeps it small" (I.to_int (FStarC.String.byte_length b) < 200);
  let l' : list string = deserialize b in
  check "sharing roundtrip" (l = l');
  (match l' with
   | x :: _ :: y :: _ -> check "shared values are physically equal" (Util.physical_equality x y)
   | _ -> check "sharing roundtrip length" false);

  (* Malformed inputs are rejected. *)
  let rejects (what:string) (f : unit -> ML unit) : ML unit =
    check what (try f (); false with | BB.Malformed _ -> true)
  in
  rejects "truncated" (fun () -> ignore (deserialize #(list int) (FStarC.String.byte_substring b I.zero (I.of_int 5))));
  rejects "trailing" (fun () -> ignore (deserialize #int (serialize (1, 2))));
  rejects "bad tag" (fun () -> ignore (deserialize #(option int) (serialize 7)));
  rejects "bad back-reference" (fun () -> ignore (deserialize #string (serialize (I.of_int 3))));
  Format.print_string "serialize tests ok\n"
