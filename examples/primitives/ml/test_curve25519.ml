open Bignum_Parameters
open SInt_UInt64
open Big_int
open Stdint
open SBuffer
open Bignum_Core
open Curve_Point
       
let template_donna_64 = fun x -> 51
let template_donna = fun x -> 26 - (x mod 2)
let template_448 = fun x -> 56

let t = template_donna_64
			      
let rec bitweight t i =
  match i with
  | 0 -> 0
  | _ -> t i + bitweight t (i-1)
			      
(* let rnd_bigint_donna_64 () = *)
(*   let a = SBuffer.create 0 one 5 in *)
(*   let b = ref zero_big_int in *)
(*   for i = 0 to 4 do *)
(*     let r = (Random.int64 (Int64.of_int 0x7ffffffffffff)) in *)
(*     upd 64 a i (Uint64.of_int64 r); *)
(*     b := add_big_int !b (mult_int_big_int (Int64.to_int r) (power_int_positive_int 2 (bitweight t i))); *)
(*   done; *)
(*   print_string "\n"; *)
(*   (a, !b) *)
        
let print_bigint_64 b =
  let mask = Uint64.of_string "0x3ffffff" in
  for i = 0 to norm_length-1 do
    print_string (SInt_UInt64.to_string (index 64 b i));
    print_string " ";
  done;
  print_string "\n"
	          
let print_bigint_donna_128 b =
  for i = 0 to Array.length b.content - 1 do
    print_string (Uint128.to_string (index 128 b i));
    print_string " ";
  done;
  print_string "\n"

let print_big_int b =
  for i = 0 to (norm_length-1) do
    print_string (string_of_big_int (mod_big_int (div_big_int b (power_int_positive_int 2 (bitweight t i))) (power_int_positive_int 2 (t i))));
    print_string " ";
  done;
  print_string "\n"
	       
let modulo b =
  let prime = sub_big_int (power_int_positive_int 2 255) (big_int_of_int 19) in
  mod_big_int b prime

let format_secret s =
  upd 8 s 0 (SInt_UInt8.logand (index 8 s 0) (SInt_UInt8.of_int 248));
  upd 8 s 31 (SInt_UInt8.logand (index 8 s 31) (SInt_UInt8.of_int 127));
  upd 8 s 31 (SInt_UInt8.logand (SInt_UInt8.logor (index 8 s 31) (SInt_UInt8.of_int 64)) (SInt_UInt8.of_int 255))

let scalar1 = "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
let scalar2 = "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"

let input1 = "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
let input2 = "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"
		      
let get_input_scalar scalar_string =
  let bytes = Array.init 32 (fun i -> SInt_UInt8.of_string ("0x" ^ (String.sub scalar_string (2*i) 2))) in
  {content = bytes; idx=0; length = 32}
	       
let get_input input_string =
  let bytes = Array.init 32 (fun i -> int_of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let input64 = Array.make 4 Stdint.Uint64.zero in
  let rec fill a b ctr =
    match ctr with
    | 0 -> ()
    | _ ->
       let i = ctr-1 in
       let idx = i / 8 in
       let shift = i mod 8 in
       a.(idx) <- Uint64.add a.(idx) (Uint64.shift_left (Uint64.of_int b.(i)) (shift*8));
       fill a b (i-1) in
  fill input64 bytes 32;
  let input51 = Array.make 5 SInt_UInt64.zero in
  let mask = Uint64.of_string "0x7ffffffffffff" in
  input51.(0) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand input64.(0) mask));
  input51.(1) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.add (Uint64.logand (Uint64.shift_right input64.(0) 51) mask)
			    (Uint64.logand (Uint64.shift_left (input64.(1)) 13) mask)));
  input51.(2) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.add (Uint64.logand (Uint64.shift_right input64.(1) 38) mask)
			    (Uint64.logand (Uint64.shift_left (input64.(2)) 26) mask)));
  input51.(3) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.add (Uint64.logand (Uint64.shift_right input64.(2) 25) mask)
			    (Uint64.logand (Uint64.shift_left (input64.(3)) 39) mask)));
  input51.(4) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand (Uint64.shift_right input64.(3) 12) mask));
  {content = input51; idx = 0; length = 5}

let get_input2 input_string =
  let mask = Uint64.of_string "0x7ffffffffffff" in
  let bytes = Array.init 32 (fun i -> int_of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let rec mk64 b idx i =
    match i with
    | 0 -> Uint64.zero | _ -> Uint64.add (Uint64.shift_left (Uint64.of_int b.(idx+i-1)) (8*(i-1)))
				(mk64 b idx (i-1)) in
  let input51 = Array.make 5 SInt_UInt64.zero in
  input51.(0) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand (mk64 bytes 0 8) mask));
  input51.(1) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand (Uint64.shift_right (mk64 bytes 6 8) 3) mask));
  input51.(2) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand (Uint64.shift_right (mk64 bytes 12 8) 6) mask));
  input51.(3) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand (Uint64.shift_right (mk64 bytes 19 8) 1) mask));
  input51.(4) <- SInt_UInt64.of_string (Uint64.to_string (Uint64.logand (Uint64.shift_right (mk64 bytes 24 8) 12) mask));
  {content = input51; idx = 0; length = 5}
         
let get_output output =
  let input51 = output.content in
  let input64 = Array.make 5 SInt_UInt64.zero in
  input64.(0) <- SInt_UInt64.add input51.(0) (SInt_UInt64.shift_left input51.(1) 51);
  input64.(1) <- SInt_UInt64.add (SInt_UInt64.shift_right input51.(1) 13) (SInt_UInt64.shift_left input51.(2) 48);
  input64.(2) <- SInt_UInt64.add (SInt_UInt64.shift_right input51.(2) 26) (SInt_UInt64.shift_left input51.(3) 25);
  input64.(3) <- SInt_UInt64.add (SInt_UInt64.shift_right input51.(3) 39) (SInt_UInt64.shift_left input51.(4) 12);
  let s = ref "" in
  for i = 0 to 3 do
    for j = 0 to 7 do
      let s' = (Uint8.to_string_hex (Uint8.of_uint64 (Uint64.of_string (SInt_UInt64.to_string (SInt_UInt64.shift_right input64.(i) (j*8)))))) in
      let s' = String.sub s' 2 (String.length s' - 2) in
      let s' = if String.length s' = 2 then s' else ("0" ^ s') in
      s := !s ^ s';
    done;
  done;
  !s

	       
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)
      
let test4 () =
  (* Output data *)
  let output = create 0 zero norm_length in

  (* Get test scalar *)
  let scalar = get_input_scalar scalar1 in
  format_secret scalar;
  print_string "Input scalar:\n";
  Array.iter (fun x -> print_string ((SInt_UInt8.to_string x) ^ " ")) (scalar.content);
  print_string "\n";

  (* Create basepoint *)
  let qx = get_input2 input1 in
  let qy = create 0 zero norm_length in
  let qz = create 0 zero norm_length in
  upd platform_size qz 0 one;
  print_string "Basepoint : \n";
  print_bigint_64 qx;
  print_bigint_64 qz;
  let basepoint = {x = qx; y = qy; z = qz} in

  (* Point to store the result *)
  let resx = create 0 zero norm_length in
  let resy = create 0 zero norm_length in
  let resz = create 0 zero norm_length in
  let res = {x = resx; y = resy; z = resz} in

  (* Ladder *)
  time (fun () ->
      for i = 0 to 99 do
        Curve_Ladder.montgomery_ladder res scalar basepoint;
        let zrecip = create 0 zero norm_length in
        (* Get the affine coordinates back *)
        crecip' zrecip (get_z res);
        fmul output resx zrecip;
      done
    ) () "100 times the montgomery ladder";

  let zrecip = create 0 zero norm_length in
  (* Get the affine coordinates back *)
  crecip' zrecip (get_z res);
  fmul output resx zrecip;

  let output_string = get_output output in
  print_string "\nString output: \n";
  print_string output_string;
  print_string "\n"
	       
		  
let _ =
  test4 ()
  
