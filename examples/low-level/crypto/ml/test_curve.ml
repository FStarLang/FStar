open Curve_Parameters
open Big_int
open Stdint
open Curve_Bignum
open FStar_Buffer
       
let to_limb = FStar_UInt64.uint_to_t
       
let template_curve_25519 = fun x -> 51

let t = template_curve_25519
  
let rec bitweight t i =
  match i with
  | 0 -> 0
  | _ -> t i + bitweight t (i-1)
			      
let rnd_bigint_donna_64 () =
  let a = create (FStar_UInt64.of_string "0") 5 in
  let b = ref zero_big_int in
  for i = 0 to 4 do
    let r = (Random.int64 (Int64.of_int 0x7ffffffffffff)) in
    upd a i (Stdint.Uint64.of_int64 r);
    b := add_big_int !b (mult_int_big_int (Int64.to_int r) (power_int_positive_int 2 (bitweight t i)));
  done;
  print_string "\n";
  (a, !b)
        
let print_bigint_64 b =
  let mask = FStar_UInt64.of_string "0x3ffffff" in
  for i = 0 to nlength-1 do
    print_string (FStar_UInt64.to_string (index b i));
    print_string " ";
  done;
  print_string "\n"
	       
let print_bigint_donna_128 b =
  for i = 0 to Array.length b.content - 1 do
    print_string (FStar_UInt128.to_string (index b i));
    print_string " ";
  done;
  print_string "\n"

let print_big_int b =
  for i = 0 to (nlength-1) do
    print_string (string_of_big_int (mod_big_int (div_big_int b (power_int_positive_int 2 (bitweight t i))) (power_int_positive_int 2 (t i))));
    print_string " ";
  done;
  print_string "\n"
	       
let modulo b =
  let prime = sub_big_int (power_int_positive_int 2 255) (big_int_of_int 19) in
  mod_big_int b prime

let format_secret s =
  FStar_Buffer.upd s 0 ((index s 0) land (248));
  FStar_Buffer.upd s 31 ((index s 31) land (127));
  FStar_Buffer.upd s 31 ((index s 31) lor (64))

let scalar1 = "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
let scalar2 = "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"

let input1 = "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
let input2 = "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"
		      
let get_input_scalar scalar_string =
  let bytes = Array.init 32 (fun i -> FStar_UInt8.of_string ("0x" ^ (String.sub scalar_string (2*i) 2))) in
  {content = bytes; idx = 0; length = 0}
	       
let get_input input_string =
  let bytes = Array.init 32 (fun i -> FStar_UInt8.of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let input64 = Array.make 4 (FStar_UInt64.of_string "0") in
  let rec fill a b ctr =
    match ctr with
    | 0 -> ()
    | _ ->
       let i = ctr-1 in
       let idx = i / 8 in
       let shift = i mod 8 in
       a.(idx) <- FStar_UInt64.add a.(idx) (FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 b.(i)) (shift*8));
       fill a b (i-1) in
  fill input64 bytes (FStar_UInt32.of_string "32");
  let input51 = Array.make (FStar_UInt32.of_string "5") (FStar_UInt64.of_string "0") in
  let mask = FStar_UInt64.of_string "0x7ffffffffffff" in
  input51.(0) <- FStar_UInt64.logand input64.(0) mask;
  input51.(1) <- FStar_UInt64.add (FStar_UInt64.logand (FStar_UInt64.shift_right input64.(0) 51) mask)
			    (FStar_UInt64.logand (FStar_UInt64.shift_left (input64.(1)) 13) mask);
  input51.(2) <- FStar_UInt64.add (FStar_UInt64.logand (FStar_UInt64.shift_right input64.(1) 38) mask)
			    (FStar_UInt64.logand (FStar_UInt64.shift_left (input64.(2)) 26) mask);
  input51.(3) <- FStar_UInt64.add (FStar_UInt64.logand (FStar_UInt64.shift_right input64.(2) 25) mask)
			    (FStar_UInt64.logand (FStar_UInt64.shift_left (input64.(3)) 39) mask);
  input51.(4) <- FStar_UInt64.logand (FStar_UInt64.shift_right input64.(3) 12) mask;
  {content = input51; idx = 0; length = 5}

let get_input2 input_string =
  let mask = FStar_UInt64.of_string "0x7ffffffffffff" in
  let bytes = Array.init 32 (fun i -> FStar_UInt8.of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let rec mk64 b idx i =
    match i with
    | 0 -> FStar_UInt64.of_string "0" | _ -> FStar_UInt64.add (FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 b.(idx+i-1)) (8*(i-1)))
				(mk64 b idx (i-1)) in
  let input51 = Array.make 5 (FStar_UInt64.of_string "0") in
  input51.(0) <- FStar_UInt64.logand (mk64 bytes 0 8) mask;
  input51.(1) <- FStar_UInt64.logand (FStar_UInt64.shift_right (mk64 bytes 6 8) 3) mask;
  input51.(2) <- FStar_UInt64.logand (FStar_UInt64.shift_right (mk64 bytes 12 8) 6) mask;
  input51.(3) <- FStar_UInt64.logand (FStar_UInt64.shift_right (mk64 bytes 19 8) 1) mask;
  input51.(4) <- FStar_UInt64.logand (FStar_UInt64.shift_right (mk64 bytes 24 8) 12) mask;
  {content = input51; idx = 0; length = 5}
  
	       
let get_output output =
  let input51 = output.content in
  let input64 = Array.make 5 (FStar_UInt64.of_string "0") in
  input64.(0) <- FStar_UInt64.add input51.(0) (FStar_UInt64.shift_left input51.(1) 51);
  input64.(1) <- FStar_UInt64.add (FStar_UInt64.shift_right input51.(1) 13) (FStar_UInt64.shift_left input51.(2) 48);
  input64.(2) <- FStar_UInt64.add (FStar_UInt64.shift_right input51.(2) 26) (FStar_UInt64.shift_left input51.(3) 25);
  input64.(3) <- FStar_UInt64.add (FStar_UInt64.shift_right input51.(3) 39) (FStar_UInt64.shift_left input51.(4) 12);
  let s = ref "" in
  for i = 0 to 3 do
    for j = 0 to 7 do
      let s' = Printf.sprintf "%02x" (FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right input64.(i) (j*8))) in
      s := !s ^ s';
    done;
  done;
  !s

let p t =
  let c = t.content in
  for i = 0 to Array.length c - 1 do
    Printf.printf "%x " c.(i)
  done
   
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)
      
let test3 () =
  (* Output data *)
  Random.self_init();
  let (a, a') = rnd_bigint_donna_64 () in
  let (b, b') = rnd_bigint_donna_64 () in
  Curve_Modulo.add_big_zero a;
  Curve_Bignum.fmul a a b;
  print_bigint_64 a;
  let prime = Big_int.add_int_big_int (-19) (Big_int.power_int_positive_int 2 255) in
  let c' = Big_int.mod_big_int (Big_int.mult_big_int a' b') prime in
  print_big_int c'
                
let test4 () =
  (* Output data *)
  let output = create (FStar_UInt64.of_string "0") nlength in

  (* Get test scalar *)
  let scalar = get_input_scalar scalar1 in
  format_secret scalar;
  print_string "Input scalar:\n";
  Array.iter (fun x -> print_string ((FStar_UInt8.to_string x) ^ " ")) (scalar.content);
  print_string "\n";

  (* Create basepoint *)
  let qx = get_input2 input1 in
  let qy = create (FStar_UInt64.of_string "0") nlength in
  let qz = create (FStar_UInt64.of_string "0") nlength in
  upd qz 0 (FStar_UInt64.of_string "1");
  print_string "Basepoint : \n";
  print_bigint_64 qx;
  print_bigint_64 qz;
  let basepoint = Curve_Point.Point(qx, qy, qz) in

  (* Point to store the result *)
  let resx = create (FStar_UInt64.of_string "0") nlength in
  let resy = create (FStar_UInt64.of_string "0") nlength in
  let resz = create (FStar_UInt64.of_string "0") nlength in
  let res = Curve_Point.Point(resx, resy, resz) in
  
  (* Ladder *)
  time (fun () ->
      for i = 0 to 1 do
        Curve_Ladder.montgomery_ladder res scalar basepoint;
      done
    ) () "1 time the montgomery ladder";

  let zrecip = create (FStar_UInt64.of_string "0") nlength in
  (* Get the affine coordinates back *)
  Curve_Crecip.crecip' zrecip (Curve_Point.get_z res);
  Curve_Bignum.fmul output resx zrecip;

  let output_string = get_output output in
  print_string "\nExpected output u-coordinate:\nc3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552\n";
  print_string "Got:\n";
  print_string output_string;
  print_string "\n"
	       
let _ =
  test4 ()
