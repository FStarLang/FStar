open FStar_Buffer

type uint8_p = FStar_UInt8.t FStar_Buffer.buffer

let uint8_p_to_string b len : string =
  let s = ref ""  in
  for i = 0 to len - 1 do
    s := !s ^ Printf.sprintf "%02x" (index b i)
  done;
  !s

let compare_and_print txt (reference:uint8_p) (produced:uint8_p) len =
  let ref_string = uint8_p_to_string reference len in
  let prod_string = uint8_p_to_string produced len in
  Printf.printf "[test] expected output is %s\n" ref_string;
  Printf.printf "[test] computed output is %s\n" prod_string;
  for i = 0 to len - 1 do
    if (String.get ref_string i <> String.get prod_string i) then (
      Printf.printf "[test] reference %s and expected %s differ at byte %d\n" ref_string prod_string i;
      failwith "Bad crypto")
  done

let unsafe_malloc len = create 0 len
