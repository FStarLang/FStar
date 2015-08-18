open Multiplication
open Addition
open Seq
open Eval
(* open Carry *)
(* open Resize *)
(* open Z *)

let size = 26


(* 2^n *)
let pow2 n =
  let rec acc n t =
    if n = 0 then t else acc (n-1) (2*t) in
  acc n 1

(* Returns random values *)
let rnd_bigint max len =
  let a = Array.make len 0 in
  let b = ref (Seq.create len 0) in
  for i = 0 to 9 do
    let r = Random.int (max) in
    a.(i) <- r;
    b := Seq.upd !b i r
  done;
  (a,b)

let mk_bigint max len templ =
  let a = Array.make len 0 in
  for i = 0 to len - 1 do
    a.(i) <- Random.int (max)
  done;
  Bigint.Bigint63(a, fun x -> templ)

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

(* Print sequence of integers *)
let print_seq s =
  for i = 0 to length s - 1 do
    print_string ((string_of_int (index s i)) ^ " ")
  done;
  print_string "\n"

(* Prints ocaml int array *)
let print_array a =
  Array.iter (fun x -> print_string ((string_of_int x) ^ " ")) a;
  print_string "\n"

let bigint_of_seq s template =
  Bigint.Bigint63(s, template)

(* Converts from fstar bigint to sequence of ints *)
let seq_of_bigint = fun 
    (Bigint.Bigint63 (s, _)) -> s

(* Converts from seq of int and size to fstar bigint *)
let ocaml_bigint_of_array a size =
  let b = ref (Big_int.big_int_of_int a.(0)) in
  for i = 1 to Array.length a - 1 do
    b := Big_int.add_big_int !b (Big_int.mult_int_big_int a.(i) (Big_int.power_int_positive_int 2 (i*size)))
  done;
  !b

(* Returns an array from the Big_int.t type *)
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

(*
let resize s size =
  array_of_ocaml_bigint (ocaml_bigint_of_array (array_of_seq  s) size) size

let carry_test a size =
  let a = (fun x -> match x with | Bigint.Bigint63(data,_) -> data) a in
  let len = Array.length a in
  let b = Array.make (len+1) 0 in
  Array.blit a 0 b 0 len;
  let mask = 1 lsl size in
  for i = 0 to len-1 do
    b.(i+1) <- b.(i+1) + b.(i) / mask;
    b.(i) <- (b.(i) mod mask)
  done;
  Bigint.Bigint63 (b, (fun x -> 26))

let test size =
  Random.self_init ();
  let a1, s1 = rnd_bigint (pow2 size) 10 in
  let a2, s2 = rnd_bigint (pow2 size) 10 in
  
  let our_res = multiplication (bigint_of_seq !s1 (fun x -> size)) (bigint_of_seq !s2 (fun x -> size)) in
  let our_res_normalized = carry_test our_res (fun x -> size) in
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
				 

(* Initializes values for benchmarking *)
let initialize_values size len nb =
  let fstar_array = Array.make nb (bigint_of_seq (Seq.create len 0) size) in
  let big_int_array = Array.make nb (Big_int.zero_big_int) in
  let zarith_array = Array.make nb (Z.zero) in
  for j = 0 to nb-1 do
    let s = ref (Seq.create len 0) in
    for i = 0 to len-1 do
      let r = Random.int (pow2 size) in
      s := Seq.upd !s i r;
      big_int_array.(j) <- Big_int.add_big_int big_int_array.(j) (Big_int.shift_left_big_int (Big_int.big_int_of_int r) (i*size));
      zarith_array.(j) <- Z.add zarith_array.(j) (Z.shift_left (Z.of_int r) (i*size));
    done;
    fstar_array.(j) <- bigint_of_seq !s size
  done;
  (fstar_array, big_int_array, zarith_array)

let rounds = 5	
			
let benchmark_fstar_mul values len =
  for j = 0 to rounds do
  for i = 0 to len-2 do 
    carry_test (multiplication values.(i) values.(i+1)) size
  done;
  done
    
let benchmark_big_int_mul values len =
  for j = 0 to rounds do
  for i = 0 to len - 2 do 
    Big_int.mult_big_int values.(i) values.(i+1)
  done;
  done

let benchmark_zarith_mul values len =
  for j = 0 to rounds do
  for i = 0 to len - 2 do
    Z.mul values.(i) values.(i+1)
  done;
  done 

let benchmark_fstar_add values len =
  for j = 0 to rounds do
  for i = 0 to len-2 do 
    addition values.(i) values.(i+1)
  done;
  done
    
let benchmark_big_int_add values len =
  for j = 0 to rounds do
  for i = 0 to len - 2 do 
    Big_int.add_big_int values.(i) values.(i+1)
  done;
  done

let benchmark_zarith_add values len =
  for j = 0 to rounds do
  for i = 0 to len - 2 do
    Z.add values.(i) values.(i+1)
  done;
  done 

let run_benchmark () =
  let f_values, b_values, z_values =
    initialize_values size 10 1000 in
  let time f x s =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Execution time for %s : %fs\n" s (Sys.time() -. t) in
  let len = Array.length f_values in
  time (benchmark_fstar_add f_values) len "fstar addition";
  time (benchmark_big_int_add b_values) len "big_int addition";
  time (benchmark_zarith_add z_values) len "zarith addition";
  time (benchmark_fstar_mul f_values) len "fstar multiplication";
  time (benchmark_big_int_mul b_values) len "big_int multiplication";
  time (benchmark_zarith_mul z_values) len "zarith multiplication"
  
let _ =
  let b = ref true in
  for i = 0 to 100 do
    b := (!b && (test 22))
  done;
  if !b then 
    print_string "*** TEST SUCCEEDED ***\n"
  else 
    print_string "*** TEST FAILED ***\n";
  print_string "\nStarting benchmark between F* bigint, OCaml Big_int and Zarith.\n";
  run_benchmark ();
  print_string "\nEnd of benchmark\n"

*)

let print_bigint b =
  match b with
  | Bigint.Bigint63(data,_) ->
     begin
       Array.iter (Printf.printf "%d ") data;
       print_string "\n"
     end 

let _ =
  Random.self_init();
  let a = mk_bigint 67108864 10 26 in
  let b = mk_bigint 67108864 5 26 in
  let c = Division.division a b in
  print_bigint a;
  print_bigint b;
  print_bigint c;
  let d = Bigint.mk_zero_bigint 10 (fun x -> 26) in
  Multiplication.multiplication2 d b c;
  let d = Carry.carry d in
  let d = Bigint.Bigint63(Array.sub ((fun x -> match x with Bigint.Bigint63(data,_) -> data) d) 0 10, fun x -> 26) in
  print_bigint d;
  let r = Bigint.copy a in
  Substraction.substraction_with_lemma r d 10;
  Carry.normalized_carry r;
  print_bigint r;
  
  print_string "\n";
  print_bigint a;
  print_bigint b;
  let r = Division.modulo a b in
  print_bigint r
    
