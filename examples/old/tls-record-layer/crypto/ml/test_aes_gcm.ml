open FStar_UInt8
open FStar_Buffer
open Crypto_AEAD_AES256GCM
open Crypto_Symmetric_GF128
open Crypto_Symmetric_GCM

let zero = 0

let rec print_loop str =
  if String.length str <= 32 then print_string str else begin
      print_string (String.sub str 0 32);
      print_string "\n";
      print_loop (String.sub str 32 (String.length str - 32))
  end
                                    
let print str =
  if String.length str = 0 then print_string "(empty string)\n\n" else begin
      print_loop str;
      print_string "\n\n"
  end
       
let print_bytes (b:bytes) =
  if Array.length b.content = 0 then print_string "(empty string)\n\n" else
    begin
      for i = 0 to (Array.length b.content - 1) do
        print_string (to_string_hex (index b i));
        if i mod 16 = 15 then print_string "\n"
      done;
      if (Array.length b.content) mod 16 <> 0 then print_string "\n";
      print_string "\n"
    end

let hex_string_to_bytes buffer str =
  for i = 0 to (String.length str / 2 - 1) do
    let block = String.concat "" ["0x"; String.sub str (i * 2) 2] in
    upd buffer i ((int_of_string block))
  done

(* consider movint that test to ...GF128.fst *)
let test_gf128 a b shift sum prod =
  let fbuf = create zero 16 in
  let sbuf = create zero 16 in
  let pbuf = create zero 16 in
  let bbuf = create zero 16 in
  print_string "a = \n";
  print a;
  print_string "b = \n";
  print b;
  hex_string_to_bytes fbuf a;
  gf128_shift_right fbuf;
  print_string "Expect shift_right a = \n";
  print shift;
  print_string "Result shift_right a = \n";
  print_bytes fbuf;
  hex_string_to_bytes sbuf a;
  hex_string_to_bytes bbuf b;
  gf128_add sbuf bbuf;
  print_string "Expect a + b = \n";
  print sum;
  print_string "Result a + b = \n";
  print_bytes sbuf;
  hex_string_to_bytes pbuf a;
  gf128_mul pbuf bbuf;
  print_string "Expect a * b = \n";
  print prod;
  print_string "Result a * b = \n";
  print_bytes pbuf

let _ =
  print_string "\n\n-------------------------\nTesting Module GF128:\n-------------------------\n\n";
  test_gf128 "7a2c9af0e07bdfbde688a796960066fa" "5a4416e3bdb92f10cb50b62e57a6b76e" "3d164d78703defdef34453cb4b00337d" "20688c135dc2f0ad2dd811b8c1a6d194" "0fb723221f467313aad48b409dbe0b4f"
            
let test_crypt n k p iv a c t =
  let adlen = String.length a / 2 in
  let len = String.length p / 2 in
  let key = create zero 32 in
  let plaintext = create zero len in
  let nonce = create zero 12 in
  let aad = create zero adlen in
  let ciphertext = create zero len in
  let tag = create zero 16 in
  hex_string_to_bytes key k;
  hex_string_to_bytes plaintext p;
  hex_string_to_bytes nonce iv;
  hex_string_to_bytes aad a;
  aead_encrypt ciphertext tag key nonce plaintext len aad adlen;
  Printf.printf "\n  ***     Testcase: %d    ***\n\n" n;
  print_string "Ciphertext Answer:\n";
  print c;
  print_string "Ciphertext Result:\n";
  print_bytes ciphertext;
  print_string "Tag Answer:\n";
  print t;
  print_string "Tag Result:\n";
  print_bytes tag
           
let _ =
  print_string "\n\n-------------------------\nTesting AES256GCM:\n-------------------------\n\n";
  test_crypt 1 "0000000000000000000000000000000000000000000000000000000000000000" "" "000000000000000000000000" "" "" "530f8afbc74536b9a963b4f1c4cb738b";
  test_crypt 2 "0000000000000000000000000000000000000000000000000000000000000000" "00000000000000000000000000000000" "000000000000000000000000" "" "cea7403d4d606b6e074ec5d3baf39d18" "d0d1c8a799996bf0265b98b5d48ab919";
  test_crypt 3 "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308" "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255" "cafebabefacedbaddecaf888" "" "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad" "b094dac5d93471bdec1a502270e3cc6c";
  test_crypt 4 "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308" "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39" "cafebabefacedbaddecaf888" "feedfacedeadbeeffeedfacedeadbeefabaddad2" "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662" "76fc6ece0f4e1768cddf8853bb2d551b"
