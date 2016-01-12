(* The original "Bytes" module from OCaml. *)
module B = Bytes

(* Things brings in [Platform.Bytes] into scope... *)
open CoreCrypto
open Platform

let _ =
  print_endline "Tests started"
;;

let digit_to_int c = match c with
  | '0'..'9' -> Char.code c - Char.code '0'
  | 'a'..'f' -> 10 + Char.code c - Char.code 'a'
  | _ -> failwith "hex_to_char: invalid hex digit"

let hex_to_char a b =
  Char.chr ((digit_to_int a) lsl 4 + digit_to_int b)

let char_to_hex c =
  let n = Char.code c in
  let digits = "0123456789abcdef" in
  digits.[n lsr 4], digits.[n land 0x0f]

let string_to_hex s =
  let n = String.length s in
  let buf = Buffer.create n in
  for i = 0 to n - 1 do
    let d1,d2 = char_to_hex s.[i] in
    Buffer.add_char buf d1;
    Buffer.add_char buf d2;
  done;
  Buffer.contents buf

let hex_to_string s =
  let n = String.length s in
  if n mod 2 <> 0 then
    failwith "hex_to_string: invalid length"
  else
    let res = B.create (n/2) in
    let rec aux i =
      if i >= n then ()
      else (
        B.set res (i/2) (hex_to_char s.[i] s.[i+1]);
        aux (i+2)
      )
    in
    aux 0;
    res

let hex_to_bytes s = bytes_of_string (hex_to_string s)
let bytes_to_hex b = string_to_hex (string_of_bytes b)

module TestAead = struct

  type test_vector = {
    cipher: aead_cipher;
    key: string;
    iv : string;
    aad: string;
    tag: string;
    plaintext: string;
    ciphertext: string;
  }

  let print_test_vector v =
    Printf.printf "key:\t\t%S\niv:\t\t%S\naad:\t\t%S\ntag:\t\t%S\nplaintext:\t%S\nciphertext:\t%S\n"
      v.key v.iv v.aad v.tag v.plaintext v.ciphertext

  let test v =
    let key = hex_to_bytes v.key in
    let iv  = hex_to_bytes v.iv  in
    let aad = hex_to_bytes v.aad in
    let plaintext = hex_to_bytes v.plaintext in
    let c = aead_encrypt v.cipher key iv aad plaintext in
    let c',t = Bytes.split c (Bytes.length c - 16) in
    if not(bytes_to_hex c' = v.ciphertext && bytes_to_hex t = v.tag) then
      false
    else
      let p = aead_decrypt v.cipher key iv aad c in
      p = Some plaintext

  let test_vectors = [
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "58e2fccefa7e3061367f1d57a4e7455a";
    plaintext  = "";
    ciphertext = "";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "ab6e47d42cec13bdf53a67b21257bddf";
    plaintext  = "00000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78";
  };
  {
    cipher = AES_128_GCM;
    key = "feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "";
    tag = "4d5c2af327cd64a62cf35abd2ba6fab4";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985";
  };
  {
    cipher = AES_128_GCM;
    key = "feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "5bc94fbc3221a5db94fae95ae7121a47";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091";
  };
  {
    cipher = AES_128_GCM;
    key = "feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbad";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "3612d2e79e3b0785561be14aaca2fccb";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "61353b4c2806934a777ff51fa22a4755699b2a714fcdc6f83766e5f97b6c742373806900e49f24b22b097544d4896b424989b5e1ebac0f07c23f4598";
  };
  {
    cipher = AES_128_GCM;
    key = "feffe9928665731c6d6a8f9467308308";
    iv  = "9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "619cc5aefffe0bfa462af43c1699d050";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5";
  };
  {
    cipher = AES_256_GCM;
    key = "0000000000000000000000000000000000000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "530f8afbc74536b9a963b4f1c4cb738b";
    plaintext  = "";
    ciphertext = "";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "";
    tag = "b094dac5d93471bdec1a502270e3cc6c";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "";
    tag = "b094dac5d93471bdec1a502270e3cc6c";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbaddecaf888";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "76fc6ece0f4e1768cddf8853bb2d551b";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "cafebabefacedbad";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "3a337dbf46a792c45e454913fe2ea8f2";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "c3762df1ca787d32ae47c13bf19844cbaf1ae14d0b976afac52ff7d79bba9de0feb582d33934a4f0954cc2363bc73f7862ac430e64abe499f47c9b1f";
  };
  {
    cipher = AES_256_GCM;
    key = "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = "9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b";
    aad = "feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = "a44a8266ee1c8eb0c8b5d4cf5ae9f19a";
    plaintext  = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = "5a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
    tag = "5fea793a2d6f974d37e68e0cb8ff9492";
    plaintext  = "";
    ciphertext = "";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "9dd0a376b08e40eb00c35f29f9ea61a4";
    plaintext  = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "98885a3a22bd4742fe7b72172193b163";
    plaintext  = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0c94da219118e297d7b7ebcbcc9c388f28ade7d85a8ee35616f7124a9d5270291";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "000000000000000000000000";
    aad = "";
    tag = "cac45f60e31efd3b5a43b98a22ce1aa1";
    plaintext  = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0c94da219118e297d7b7ebcbcc9c388f28ade7d85a8ee35616f7124a9d527029195b84d1b96c690ff2f2de30bf2ec89e00253786e126504f0dab90c48a30321de3345e6b0461e7c9e6c6b7afedde83f40";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    aad = "";
    tag = "566f8ef683078bfdeeffa869d751a017";
    plaintext  = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "56b3373ca9ef6e4a2b64fe1e9a17b61425f10d47a75a5fce13efc6bc784af24f4141bdd48cf7c770887afd573cca5418a9aeffcd7c5ceddfc6a78397b9a85b499da558257267caab2ad0b23ca476a53cb17fb41c4b8b475cb4f3f7165094c229c9e8c4dc0a2a5ff1903e501511221376a1cdb8364c5061a20cae74bc4acd76ceb0abc9fd3217ef9f8c90be402ddf6d8697f4f880dff15bfb7a6b28241ec8fe183c2d59e3f9dfff653c7126f0acb9e64211f42bae12af462b1070bef1ab5e3606";
  };
  {
    cipher = AES_128_GCM;
    key = "00000000000000000000000000000000";
    iv  = "ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    aad = "";
    tag = "8b307f6b33286d0ab026a9ed3fe1e85f";
    plaintext  = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = "56b3373ca9ef6e4a2b64fe1e9a17b61425f10d47a75a5fce13efc6bc784af24f4141bdd48cf7c770887afd573cca5418a9aeffcd7c5ceddfc6a78397b9a85b499da558257267caab2ad0b23ca476a53cb17fb41c4b8b475cb4f3f7165094c229c9e8c4dc0a2a5ff1903e501511221376a1cdb8364c5061a20cae74bc4acd76ceb0abc9fd3217ef9f8c90be402ddf6d8697f4f880dff15bfb7a6b28241ec8fe183c2d59e3f9dfff653c7126f0acb9e64211f42bae12af462b1070bef1ab5e3606872ca10dee15b3249b1a1b958f23134c4bccb7d03200bce420a2f8eb66dcf3644d1423c1b5699003c13ecef4bf38a3b60eedc34033bac1902783dc6d89e2e774188a439c7ebcc0672dbda4ddcfb2794613b0be41315ef778708a70ee7d75165c";
  };
  {
    cipher = AES_128_GCM;
    key = "843ffcf5d2b72694d19ed01d01249412";
    iv  = "dbcca32ebf9b804617c3aa9e";
    aad = "00000000000000000000000000000000101112131415161718191a1b1c1d1e1f";
    tag = "3b629ccfbc1119b7319e1dce2cd6fd6d";
    plaintext  = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f";
    ciphertext = "6268c6fa2a80b2d137467f092f657ac04d89be2beaa623d61b5a868c8f03ff95d3dcee23ad2f1ab3a6c80eaf4b140eb05de3457f0fbc111a6b43d0763aa422a3013cf1dc37fe417d1fbfc449b75d4cc5";
  };
  ]
end

let bytes_of_hex = hex_to_bytes
let hex_of_bytes = bytes_to_hex
let string_of_hex = hex_to_string
let hex_of_string = string_to_hex

module TestHmac = struct

  type test_case = {
    key: Bytes.bytes;
    data: Bytes.bytes;
    digests: (Bytes.bytes * hash_alg) list;
    truncation: int option
  }

  let test_cases = [{
      key =           bytes_of_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
      data =          bytes_of_string "Hi There";
      digests =       [ bytes_of_hex "9294727a3638bb1c13f48ef8158bfc9d", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_string "Jefe";
      data =          bytes_of_string "what do ya want for nothing?";
      digests =       [ bytes_of_hex "750c783e6ab0b503eaa86e310a5db738", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_hex "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
      digests =       [ bytes_of_hex "56be34521d144c88dbb8c733f0e8b3f6", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_hex "0102030405060708090a0b0c0d0e0f10111213141516171819";
      data =          bytes_of_hex "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
      digests =       [ bytes_of_hex "697eaf0aca3a3aea3a75164746ffaa79", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_hex "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c";
      data =          bytes_of_string "Test With Truncation";
      digests =       [ bytes_of_hex "56461ef2342edc00f9bab995690efd4c", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key - Hash Key First";
      digests =       [ bytes_of_hex "6b1ab7fe4bd7bf8f0b62e6ce61b9d0cd", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
      digests =       [ bytes_of_hex "6f630fad67cda0ee1fb1f562db3aa53e", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
      data =          bytes_of_string "Hi There";
      digests =       [ bytes_of_hex "b617318655057264e28bc0b6fb378c8ef146be00", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_string "Jefe";
      data =          bytes_of_string "what do ya want for nothing?";
      digests =       [ bytes_of_hex "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_hex "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
      digests =       [ bytes_of_hex "125d7342b9ac11cd91a39af48aa17b4f63f175d3", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "0102030405060708090a0b0c0d0e0f10111213141516171819";
      data =          bytes_of_hex "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
      digests =       [ bytes_of_hex "4c9007f4026250c6bc8414f9bf50c86c2d7235da", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c";
      data =          bytes_of_string "Test With Truncation";
      digests =       [ bytes_of_hex "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key - Hash Key First";
      digests =       [ bytes_of_hex "aa4ae5e15272d00e95705637ce8a3b55ed402112", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
      digests =       [ bytes_of_hex "e8e99d0f45237d786d6bbaa7965c7808bbff1a91", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key - Hash Key First";
      digests =       [ bytes_of_hex "aa4ae5e15272d00e95705637ce8a3b55ed402112", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
      digests =       [ bytes_of_hex "e8e99d0f45237d786d6bbaa7965c7808bbff1a91", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
      data =          bytes_of_hex "4869205468657265";
      digests =       [
        bytes_of_hex "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7", SHA256;
        bytes_of_hex "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6", SHA384;
        bytes_of_hex "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854", SHA512
      ];
      truncation = None
    }; {
      key =           bytes_of_hex "4a656665";
      data =          bytes_of_hex "7768617420646f2079612077616e7420666f72206e6f7468696e673f";
      digests =       [
        bytes_of_hex "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843", SHA256;
        bytes_of_hex "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e8e2240ca5e69e2c78b3239ecfab21649", SHA384;
        bytes_of_hex "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737", SHA512
      ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_hex "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
      digests =       [
        bytes_of_hex "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe", SHA256;
        bytes_of_hex "88062608d3e6ad8a0aa2ace014c8a86f0aa635d947ac9febe83ef4e55966144b2a5ab39dc13814b94e3ab6e101a34f27", SHA384;
        bytes_of_hex "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb", SHA512
      ];
      truncation = None
    }; {
      key =           bytes_of_hex "0102030405060708090a0b0c0d0e0f10111213141516171819";
      data =          bytes_of_hex "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
      digests =       [
        bytes_of_hex "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b", SHA256;
        bytes_of_hex "3e8a69b7783c25851933ab6290af6ca77a9981480850009cc5577c6e1f573b4e6801dd23c4a7d679ccf8a386c674cffb", SHA384;
        bytes_of_hex "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd", SHA512
      ];
      truncation = None
    }; {
      key =           bytes_of_hex "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c";
      data =          bytes_of_hex "546573742057697468205472756e636174696f6e";
      digests =       [
        bytes_of_hex "a3b6167473100ee06e0c796c2955552b", SHA256;
        bytes_of_hex "3abf34c3503b2a23a46efc619baef897", SHA384;
        bytes_of_hex "415fad6271580a531d4179bc891d87a6", SHA512
      ];
      truncation = Some 16
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_hex "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374";
      digests =       [
        bytes_of_hex "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54", SHA256;
        bytes_of_hex "4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c60c2ef6ab4030fe8296248df163f44952", SHA384;
        bytes_of_hex "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598", SHA512
      ];
      truncation = None
    }; {
      key =           bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_hex "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e";
      digests =       [
        bytes_of_hex "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2", SHA256;
        bytes_of_hex "6617178e941f020d351e2f254e8fd32c602420feb0b8fb9adccebb82461e99c5a678cc31e799176d3860e6110c46523e", SHA384;
        bytes_of_hex "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58", SHA512
      ];
      truncation = None
    }]

  let print_test_case v =
    List.iter (fun (digests, hash_alg) ->
      Printf.printf "key: %s\ndata: %s\ndigests: %s (%s)\n"
        (hex_of_bytes v.key) (hex_of_bytes v.data)
        (hex_of_bytes digests) (string_of_hash_alg hash_alg)
    ) v.digests

  let test v =
    List.for_all (fun (digest, hash_alg) ->
      let digest' = hmac hash_alg v.key v.data in
      match v.truncation with
      | None ->
          Bytes.equalBytes digest digest'
      | Some i ->
          Bytes.equalBytes digest (fst (Bytes.split digest' i))
    ) v.digests

end

module TestHash = struct
  type test = {
    (* The input is [input] repeated [repeat] times. *)
    input: string;
    output: string;
    hash_alg: hash_alg;
    repeat: int;
  }

  let tests = [{
      hash_alg = MD5;
      input = "";
      output = "d41d8cd98f00b204e9800998ecf8427e";
      repeat = 1
    }; {
      hash_alg = MD5;
      input = "a";
      output = "0cc175b9c0f1b6a831c399e269772661";
      repeat = 1
    }; {
      hash_alg = MD5;
      input = "abc";
      output = "900150983cd24fb0d6963f7d28e17f72";
      repeat = 1
    }; {
      hash_alg = MD5;
      input = "message digest";
      output = "f96b697d7cb7938d525a2f31aaf161d0";
      repeat = 1
    }; {
      hash_alg = MD5;
      input = "abcdefghijklmnopqrstuvwxyz";
      output = "c3fcd3d76192e4007dfb496cca67e13b";
      repeat = 1
    }; {
      hash_alg = MD5;
      input = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
      output = "d174ab98d277d9f5a5611c2c9f419d9f";
      repeat = 1
    }; {
      hash_alg = MD5;
      input = "12345678901234567890123456789012345678901234567890123456789012345678901234567890";
      output = "57edf4a22be3c955ac49da2e2107b67a";
      repeat = 1
    }; {
      hash_alg = SHA1;
      input = "abc";
      output = "a9993e364706816aba3e25717850c26c9cd0d89d";
      repeat = 1
    }; {
      hash_alg = SHA1;
      input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
      output = "84983e441c3bd26ebaae4aa1f95129e5e54670f1";
      repeat = 1
    }; {
      hash_alg = SHA1;
      input = "a";
      output = "34aa973cd4c4daa4f61eeb2bdbad27316534016f";
      repeat = 1000000
    }; {
      hash_alg = SHA1;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "dea356a2cddd90c7a7ecedc5ebb563934f460452";
      repeat = 10
    }; {
      hash_alg = SHA256;
      input = "abc";
      output = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
      repeat = 1
    }; {
      hash_alg = SHA256;
      input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
      output = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
      repeat = 1
    }; {
      hash_alg = SHA256;
      input = "a";
      output = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0";
      repeat = 1000000
    }; {
      hash_alg = SHA256;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "594847328451bdfa85056225462cc1d867d877fb388df0ce35f25ab5562bfbb5";
      repeat = 10
    }; {
      hash_alg = SHA256;
      input = "\x19";
      output = "68aa2e2ee5dff96e3355e6c7ee373e3d6a4e17f75f9518d843709c0c9bc3e3d4";
      repeat = 1
    }; {
      hash_alg = SHA256;
      input = "\xe3\xd7\x25\x70\xdc\xdd\x78\x7c\xe3\x88\x7a\xb2\xcd\x68\x46\x52";
      output = "175ee69b02ba9b58e2b0a5fd13819cea573f3940a94f825128cf4209beabb4e8";
      repeat = 1
    }; {
      hash_alg = SHA256;
      input = "\x83\x26\x75\x4e\x22\x77\x37\x2f\x4f\xc1\x2b\x20\x52\x7a\xfe\xf0\x4d\x8a\x05\x69\x71\xb1\x1a\xd5\x71\x23\xa7\xc1\x37\x76\x00\x00\xd7\xbe\xf6\xf3\xc1\xf7\xa9\x08\x3a\xa3\x9d\x81\x0d\xb3\x10\x77\x7d\xab\x8b\x1e\x7f\x02\xb8\x4a\x26\xc7\x73\x32\x5f\x8b\x23\x74\xde\x7a\x4b\x5a\x58\xcb\x5c\x5c\xf3\x5b\xce\xe6\xfb\x94\x6e\x5b\xd6\x94\xfa\x59\x3a\x8b\xeb\x3f\x9d\x65\x92\xec\xed\xaa\x66\xca\x82\xa2\x9d\x0c\x51\xbc\xf9\x33\x62\x30\xe5\xd7\x84\xe4\xc0\xa4\x3f\x8d\x79\xa3\x0a\x16\x5c\xba\xbe\x45\x2b\x77\x4b\x9c\x71\x09\xa9\x7d\x13\x8f\x12\x92\x28\x96\x6f\x6c\x0a\xdc\x10\x6a\xad\x5a\x9f\xdd\x30\x82\x57\x69\xb2\xc6\x71\xaf\x67\x59\xdf\x28\xeb\x39\x3d\x54\xd6";
      output = "97dbca7df46d62c8a422c941dd7e835b8ad3361763f7e9b2d95f4f0da6e1ccbc";
      repeat = 1
    }; {
      hash_alg = SHA384;
      input = "abc";
      output = "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7";
      repeat = 1
    }; {
      hash_alg = SHA384;
      input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
      output = "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039";
      repeat = 1
    }; {
      hash_alg = SHA384;
      input = "a";
      output = "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985";
      repeat = 1000000
    }; {
      hash_alg = SHA384;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "2fc64a4f500ddb6828f6a3430b8dd72a368eb7f3a8322a70bc84275b9c0b3ab00d27a5cc3c2d224aa6b61a0d79fb4596";
      repeat = 10
    }; {
      hash_alg = SHA512;
      input = "abc";
      output = "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";
      repeat = 1
    }; {
      hash_alg = SHA512;
      input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
      output = "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909";
      repeat = 1
    }; {
      hash_alg = SHA512;
      input = "a";
      output = "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b";
      repeat = 1000000
    }; {
      hash_alg = SHA512;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "89d05ba632c699c31231ded4ffc127d5a894dad412c0e024db872d1abd2ba8141a0f85072a9be1e2aa04cf33c765cb510813a39cd5a84c4acaa64d3f3fb7bae9";
      repeat = 10
    }]

  let print_test t =
    Printf.printf "%s(%s) = %s (got: %s)\n"
      (string_of_hash_alg t.hash_alg) (hex_of_string t.input) t.output
      (hex_of_bytes (hash t.hash_alg (bytes_of_string t.input)))

  let test t =
    let input =
      if t.repeat = 1 then
        bytes_of_string t.input
      else
        let l = String.length t.input in
        let s = String.make (l * t.repeat) ' ' in
        for i = 0 to t.repeat - 1 do
          String.blit t.input 0 s (i * l) l
        done;
        bytes_of_string s
    in
    let output = hash t.hash_alg input in
    Bytes.equalBytes output (bytes_of_hex t.output)
end

module TestEcc = struct
  type test = {
    params: ec_params;
    point: ec_point;
  }

  let x = bytes_of_hex

  let tests = [{
    params = {
      curve = ECC_P256;
      point_compression = false
    };
    point = {
      ecx = x"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
      ecy = x"4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"
    }
  }; {
    params = {
      curve = ECC_P384;
      point_compression = false
    };
    point = {
      ecx = x"aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7";
      ecy = x"3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f"
    }
  }; {
    params = {
      curve = ECC_P521;
      point_compression = false
    };
    point = {
      ecx = x"00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66";
      ecy = x"011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650"
    }
  }]

  let test { params; point } =
    ec_is_on_curve params point

  let print_test { point = { ecx; ecy }; _ } =
    Printf.printf "Point at coordinates %s,%s should be on curve but isn't\n"
      (hex_of_bytes ecx) (hex_of_bytes ecy)

end

let bytes1, bytes2, bytes3 =
  let chunk1 = bytes_of_string "Lorem ipsum dolor sit amet, consectetur adipiscing elit.  Integer vitae tincidunt enim. Pellentesque luctus, turpis sed lobortis ullamcorper, orci nisi commodo sem, ut sagittis augue elit vel ipsum. Aenean aliquam eros est, sed molestie ex aliquet sed. Vest" in
  let chunk2 = bytes_of_string "bulum in massa mauris. Phasellus non arcu pulvinar, elementum sapien eu, congue dolor. Fusce malesuada nisl enim, non accumsan mi gravida aliquam. Sed ornare augue eget quam pretium, vitae sodales urna hendrerit.  Curabitur mi ante, fermentum eget lacus ut," in
  let chunk = Platform.Bytes.(chunk1 @| chunk2) in
  let _, chunk = Platform.Bytes.split chunk 128 in
  let chunk, _ = Platform.Bytes.split chunk (256 - 11) in
  chunk, bytes_of_string "012345678901234567890123456789012345", bytes_of_string "coucou"

module TestRsa = struct

  let tests = [bytes1; bytes2; bytes3]

  let roundtrip original_bytes =
    let k = rsa_gen_key 2048 in
    let cipher_bytes = rsa_encrypt k Pad_PKCS1 original_bytes in
    let plain_bytes = rsa_decrypt k Pad_PKCS1 cipher_bytes in
    try match plain_bytes with
      | Some bytes when string_of_bytes bytes = string_of_bytes original_bytes ->
          ()
      | Some bytes ->
          Printf.printf "rsa_encrypt/decrypt: got %s\n" (string_of_bytes bytes);
          raise Exit
      | None ->
          Printf.printf "rsa_encrypt/decrypt: got no bytes\n";
          raise Exit; ;
      let sig_bytes = rsa_sign (Some SHA512) k original_bytes in
      if not (rsa_verify (Some SHA512) k original_bytes sig_bytes) then begin
        Printf.printf "rsa_sign/rsa_verify: check failed\n";
        raise Exit
      end;
      true
    with Exit ->
      false

  let print_test x = print_string (hex_of_bytes x)

end

module TestDsa = struct

  let tests = TestRsa.tests

  let check original_bytes =
    let private_key = dsa_gen_key 2048 in
    let public_key = { private_key with dsa_private = None } in
    let sig_bytes = dsa_sign private_key original_bytes in
    if not (dsa_verify public_key original_bytes sig_bytes) then begin
      Printf.printf "dsa_sign/dsa_verify: check failed\n";
      false
    end else
      true

  let print_test = TestRsa.print_test
end

module TestEcdsa = struct

  let tests = TestRsa.tests

  let check original_bytes =
    let params = { curve = ECC_P521; point_compression = false } in
    let private_key = ec_gen_key params in
    let public_key = { private_key with ec_priv = None } in
    let sig_bytes = ecdsa_sign None private_key original_bytes in
    if not (ecdsa_verify None public_key original_bytes sig_bytes) then begin
      Printf.printf "ecdsa_sign/ecdsa_verify: check failed\n";
      false
    end else
      true

  let print_test = TestRsa.print_test
end


module TestDhke = struct
  let test () =
    let params = dh_gen_params 2048 in
    let alice = dh_gen_key params in
    let bob = dh_gen_key params in
    let shared1 = dh_agreement alice bob.dh_public in
    let shared2 = dh_agreement bob alice.dh_public in
    string_of_bytes shared1 = string_of_bytes shared2
end

module TestEcdhke = struct
  let test () =
    let params = { curve = ECC_P521; point_compression = false } in
    let alice = ec_gen_key params in
    let bob = ec_gen_key params in
    let shared1 = ecdh_agreement alice bob.ec_point in
    let shared2 = ecdh_agreement bob alice.ec_point in
    string_of_bytes shared1 = string_of_bytes shared2
end


let run_test section test_vectors print_test_vector test_vector =
  let passed = ref 0 in
  let total  = ref 0 in
  let doit v =
    total := !total + 1;
    if test_vector v then
      passed := !passed + 1
    else (
      Printf.printf "Test failed:\n";
      print_test_vector v
    )
  in
  List.iter doit test_vectors;
  Printf.printf "%s: %d/%d tests passed\n%!" section !passed !total

let simple_test name f =
  if f () then
    Printf.printf "%s: OK\n%!" name
  else
    Printf.printf "%s: FAIL\n%!" name

let _ =
  TestAead.(run_test "AEAD" test_vectors print_test_vector test);
  TestHmac.(run_test "HMAC" test_cases print_test_case test);
  TestHash.(run_test "HASH" tests print_test test);
  TestEcc.(run_test "ECC" tests print_test test);
  TestRsa.(run_test "RSA" tests print_test roundtrip);
  TestDsa.(run_test "DSA" tests print_test check);
  TestEcdsa.(run_test "ECDSA" tests print_test check);
  simple_test "DH key exchange" TestDhke.test;
  simple_test "ECDH key exchange" TestEcdhke.test
