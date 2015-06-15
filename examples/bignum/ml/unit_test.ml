open Multiplication
open Seq
open Eval
open Carry
open Resize

(*
let rnd_bigint max len =
  Random.self_init ();
  let a = Array.make 10 Int64.zero in
  let b = ref (Seq.create 10 Int64.zero) in
  for i = 0 to 9 do
    let r = Random.int64 (Int64.of_int max) in
    a.(i) <- r;
    b := Seq.upd !b i r
  done;
  (a,b)

let print_seq s =
  for i = 0 to length s - 1 do
    print_string ((Int64.to_string (index s i)) ^ " ")
  done;
  print_string "\n"

let print_array a =
  Array.iter (fun x -> print_string ((Int64.to_string x) ^ " ")) a;
  print_string "\n"
  *)

let pow2 n =
  let rec acc n t =
    if n = 0 then t else acc (n-1) (2*t) in
  acc n 1

let rnd_bigint max len =
  Random.self_init ();
  let a = Array.make len 0 in
  let b = ref (Seq.create len 0) in
  for i = 0 to 9 do
    let r = Random.int (max) in
    a.(i) <- r;
    b := Seq.upd !b i r
  done;
  (a,b)

let array_of_seq s =
  let a = Array.make (Seq.length s) 0 in
  for i = 0 to Seq.length s - 1 do
    a.(i) <- Seq.index s i
  done;
  a

let seq_of_array a =
  let s = ref (Seq.create (Array.length a) 0) in
  for i = 0 to Seq.length !s - 1 do
    s := (Seq.upd !s i a.(i))
  done;
  !s

let print_seq s =
  for i = 0 to length s - 1 do
    print_string ((string_of_int (index s i)) ^ " ")
  done;
  print_string "\n"

let print_array a =
  Array.iter (fun x -> print_string ((string_of_int x) ^ " ")) a;
  print_string "\n"

let bigint_of_seq s size =
  Bigint64 (s, (fun x -> size), (fun x -> size), true)

let seq_of_bigint = fun 
    (Bigint64 (s, _, _, _)) -> s

let ocaml_bigint_of_array a size =
  let b = ref (Big_int.big_int_of_int a.(0)) in
  for i = 1 to Array.length a - 1 do
    b := Big_int.add_big_int !b (Big_int.mult_int_big_int a.(i) (Big_int.power_int_positive_int 2 (i*size)))
  done;
  !b

let array_of_ocaml_bigint b size =
  if Big_int.compare_big_int b Big_int.zero_big_int = 0 then [|0|]
  else
    let mask = Big_int.pred_big_int (Big_int.power_int_positive_int 2 size) in
    let v = ref b in
    let l = ref [] in
    while Big_int.compare_big_int !v Big_int.zero_big_int != 0 do
      let x = Big_int.and_big_int !v mask in
      v := Big_int.shift_right_towards_zero_big_int !v size;
      l := (Big_int.int_of_big_int x)::!l
    done;
    Array.of_list (List.rev !l)

let resize s size =
  array_of_ocaml_bigint (ocaml_bigint_of_array (array_of_seq  s) size) size

let test size =
  let a1, s1 = rnd_bigint (pow2 size) 10 in
  let a2, s2 = rnd_bigint (pow2 size) 10 in
  
  let our_res = multiplication (bigint_of_seq !s1 size) (bigint_of_seq !s2 size) in
  let our_res_normalized = carry our_res in
  let our_res_array = array_of_seq (seq_of_bigint our_res_normalized) in

  let our_res_realigned = realign our_res_normalized (fun x -> if x mod 2 = 0 then 25 else 15) in
  let our_res_realigned_array = array_of_seq (seq_of_bigint (our_res_realigned)) in

  let our_res_realigned2 = realign our_res_normalized (fun x -> size) in
  let our_res_realigned_array2 = array_of_seq (seq_of_bigint (our_res_realigned2)) in

  let ocaml_res = Big_int.mult_big_int (ocaml_bigint_of_array a1 size) (ocaml_bigint_of_array a2 size) in
  let ocaml_res_array = array_of_ocaml_bigint ocaml_res size in
  if our_res_array = ocaml_res_array && our_res_realigned_array2 = our_res_array then true else (
    print_string "Multiplied and carried result :\n";
    print_array our_res_array;

    print_string "Realigned twice result :\n";
    print_array our_res_realigned_array2;
  
    print_string "OCaml bigint result :\n";
    print_array ocaml_res_array;
    false)
				 
				 
let _ =
  let b = ref true in
  for i = 0 to 100 do
    b := (!b && (test 22))
  done;
  if !b then 
    print_string "*** TEST SUCCEEDED ***\n"
  else 
    print_string "*** TEST FAILED ***\n"

	       
