(* The original "Bytes" module from OCaml. *)
module B = Bytes

(* This brings [Platform.Bytes] into scope. *)
open CoreCrypto
open Platform

let _ =
  print_endline "Tests started"
;;


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
    let key = Bytes.bytes_of_hex v.key in
    let iv  = Bytes.bytes_of_hex v.iv  in
    let aad = Bytes.bytes_of_hex v.aad in
    let plaintext = Bytes.bytes_of_hex v.plaintext in
    let c = aead_encrypt v.cipher key iv aad plaintext in
    let c',t = Bytes.split c (Z.sub (Bytes.length c) (Z.of_int 16)) in
    if not(Bytes.hex_of_bytes c' = v.ciphertext && Bytes.hex_of_bytes t = v.tag) then
      let () = Printf.printf "Expected cipher: %s\nExpected tag: %s\n" (Bytes.hex_of_bytes c) (Bytes.hex_of_bytes t) in
      false
    else
      let p = aead_decrypt v.cipher key iv aad c in
      p = Some plaintext

  let test_vectors = [
  { (* rfc7539#page-22 *)
    cipher = CHACHA20_POLY1305;
    key = "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f";
    iv  = "070000004041424344454647";
    aad = "50515253c0c1c2c3c4c5c6c7";
    tag = "1ae10b594f09e26a7e902ecbd0600691";
    plaintext  = "4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e";
    ciphertext = "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116";
  };
  {
    cipher = CHACHA20_POLY1305;
    key = "1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0";
    iv  = "000000000102030405060708";
    aad = "f33388860000000000004e91";
    tag = "eead9d67890cbb22392336fea1851f38";
    plaintext  = "496e7465726e65742d4472616674732061726520647261667420646f63756d656e74732076616c696420666f722061206d6178696d756d206f6620736978206d6f6e74687320616e64206d617920626520757064617465642c207265706c616365642c206f72206f62736f6c65746564206279206f7468657220646f63756d656e747320617420616e792074696d652e20497420697320696e617070726f70726961746520746f2075736520496e7465726e65742d447261667473206173207265666572656e6365206d6174657269616c206f7220746f2063697465207468656d206f74686572207468616e206173202fe2809c776f726b20696e2070726f67726573732e2fe2809d";
    ciphertext = "64a0861575861af460f062c79be643bd5e805cfd345cf389f108670ac76c8cb24c6cfc18755d43eea09ee94e382d26b0bdb7b73c321b0100d4f03b7f355894cf332f830e710b97ce98c8a84abd0b948114ad176e008d33bd60f982b1ff37c8559797a06ef4f0ef61c186324e2b3506383606907b6a7c02b0f9f6157b53c867e4b9166c767b804d46a59b5216cde7a4e99040c5a40433225ee282a1b0a06c523eaf4534d7f83fa1155b0047718cbc546a0d072b04b3564eea1b422273f548271a0bb2316053fa76991955ebd63159434ecebb4e466dae5a1073a6727627097a1049e617d91d361094fa68f0ff77987130305beaba2eda04df997b714d6c6f2c29a6ad5cb4022b02709b";
  };
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


module TestBlock = struct

  type test_vector = {
    cipher: block_cipher;
    key: string;
    iv : string;
    plaintext: string;
    ciphertext: string;
  }

  let print_test_vector v =
    Printf.printf "key:\t\t%S\niv:\t\t%S\nplaintext:\t%S\nciphertext:\t%S\n"
      v.key v.iv v.plaintext v.ciphertext

  let test v =
    let key = Bytes.bytes_of_hex v.key in
    let iv  = Bytes.bytes_of_hex v.iv  in
    let plaintext = Bytes.bytes_of_hex v.plaintext in
    let c = block_encrypt v.cipher key iv plaintext in
    if not(Bytes.hex_of_bytes c = v.ciphertext) then
      false
    else
      let p = block_decrypt v.cipher key iv c in
      p = plaintext

  let test_vectors = [
  {
    cipher = AES_128_CBC;
    key  = "00000000000000000000000000000000";
    iv   = "00000000000000000000000000000000";
    plaintext  = "00000000000000000000000000000000";
    ciphertext = "66e94bd4ef8a2c3b884cfa59ca342b2e";
  };

  {
    cipher = AES_128_CBC;
    key = "e77f6871e1697b2286416f973aee9ff6";
    iv  = "00000000000000000000000000000000";
    plaintext = "474554202f20485454502f312e310d0a486f73743a20756e646566696e65640d0a0d0a431ad4d620ea0c63bf9afc8124afcae6729593f1080808080808080808";
    ciphertext = "28cf3b38da8358b78aae63e5fcc334c1eac5278a283fa709cb274df85a2a7fa2885704eda72f1bc65a50c45164b1ccbbfff18032a540f39f20400a2fe1e68cd9";
  };

  (*
   * These are AES-CBC vectors from NIST document SP800-38A, Appendix F.2
   * http://csrc.nist.gov/publications/nistpubs/800-38a/sp800-38a.pdf
   * Skipping AES-192-CBC vectors, not used with TLS
   * The individual block vectors appear also in OpenSSL's evptests.txt
   *)
  {
    cipher = AES_128_CBC;
    key = "2b7e151628aed2a6abf7158809cf4f3c";
    iv  = "000102030405060708090a0b0c0d0e0f";
    plaintext  = "6bc1bee22e409f96e93d7e117393172a";
    ciphertext = "7649abac8119b246cee98e9b12e9197d";
  };
  {
    cipher = AES_128_CBC;
    key = "2b7e151628aed2a6abf7158809cf4f3c";
    iv  = "7649abac8119b246cee98e9b12e9197d";
    plaintext  = "ae2d8a571e03ac9c9eb76fac45af8e51";
    ciphertext = "5086cb9b507219ee95db113a917678b2";
  };
  {
    cipher = AES_128_CBC;
    key = "2b7e151628aed2a6abf7158809cf4f3c";
    iv  = "5086cb9b507219ee95db113a917678b2";
    plaintext  = "30c81c46a35ce411e5fbc1191a0a52ef";
    ciphertext = "73bed6b8e3c1743b7116e69e22229516";
  };
  {
    cipher = AES_128_CBC;
    key = "2b7e151628aed2a6abf7158809cf4f3c";
    iv  = "73bed6b8e3c1743b7116e69e22229516";
    plaintext  = "f69f2445df4f9b17ad2b417be66c3710";
    ciphertext = "3ff1caa1681fac09120eca307586e1a7";
  };
  {
    cipher = AES_128_CBC;
    key = "2b7e151628aed2a6abf7158809cf4f3c";
    iv  = "000102030405060708090a0b0c0d0e0f";
    plaintext = "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710";
   ciphertext = "7649abac8119b246cee98e9b12e9197d5086cb9b507219ee95db113a917678b273bed6b8e3c1743b7116e69e222295163ff1caa1681fac09120eca307586e1a7";
  };
  {
    cipher = AES_256_CBC;
    key = "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    iv  = "000102030405060708090a0b0c0d0e0f";
    plaintext  = "6bc1bee22e409f96e93d7e117393172a";
    ciphertext = "f58c4c04d6e5f1ba779eabfb5f7bfbd6";
  };
  {
    cipher = AES_256_CBC;
    key = "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    iv  = "f58c4c04d6e5f1ba779eabfb5f7bfbd6";
    plaintext  = "ae2d8a571e03ac9c9eb76fac45af8e51";
    ciphertext = "9cfc4e967edb808d679f777bc6702c7d";
  };
  {
    cipher = AES_256_CBC;
    key = "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    iv  = "9cfc4e967edb808d679f777bc6702c7d";
    plaintext  = "30c81c46a35ce411e5fbc1191a0a52ef";
    ciphertext = "39f23369a9d9bacfa530e26304231461";
  };
  {
    cipher = AES_256_CBC;
    key = "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    iv  = "39f23369a9d9bacfa530e26304231461";
    plaintext  = "f69f2445df4f9b17ad2b417be66c3710";
    ciphertext = "b2eb05e2c39be9fcda6c19078c6a9d1b";
  };
  {
    cipher = AES_256_CBC;
    key = "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    iv  = "000102030405060708090a0b0c0d0e0f";
    plaintext = "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710";
    ciphertext = "f58c4c04d6e5f1ba779eabfb5f7bfbd69cfc4e967edb808d679f777bc6702c7d39f23369a9d9bacfa530e26304231461b2eb05e2c39be9fcda6c19078c6a9d1b";
  }
  ]
end


module TestHmac = struct

  type test_case = {
    key: Bytes.bytes;
    data: Bytes.bytes;
    digests: (Bytes.bytes * hash_alg) list;
    truncation: int option
  }

  let test_cases = [{
      key =           Bytes.bytes_of_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
      data =          bytes_of_string "Hi There";
      digests =       [ Bytes.bytes_of_hex "9294727a3638bb1c13f48ef8158bfc9d", MD5 ];
      truncation = None
    }; {
      key =           bytes_of_string "Jefe";
      data =          bytes_of_string "what do ya want for nothing?";
      digests =       [ Bytes.bytes_of_hex "750c783e6ab0b503eaa86e310a5db738", MD5 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          Bytes.bytes_of_hex "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
      digests =       [ Bytes.bytes_of_hex "56be34521d144c88dbb8c733f0e8b3f6", MD5 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0102030405060708090a0b0c0d0e0f10111213141516171819";
      data =          Bytes.bytes_of_hex "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
      digests =       [ Bytes.bytes_of_hex "697eaf0aca3a3aea3a75164746ffaa79", MD5 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c";
      data =          bytes_of_string "Test With Truncation";
      digests =       [ Bytes.bytes_of_hex "56461ef2342edc00f9bab995690efd4c", MD5 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key - Hash Key First";
      digests =       [ Bytes.bytes_of_hex "6b1ab7fe4bd7bf8f0b62e6ce61b9d0cd", MD5 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
      digests =       [ Bytes.bytes_of_hex "6f630fad67cda0ee1fb1f562db3aa53e", MD5 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
      data =          bytes_of_string "Hi There";
      digests =       [ Bytes.bytes_of_hex "b617318655057264e28bc0b6fb378c8ef146be00", SHA1 ];
      truncation = None
    }; {
      key =           bytes_of_string "Jefe";
      data =          bytes_of_string "what do ya want for nothing?";
      digests =       [ Bytes.bytes_of_hex "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          Bytes.bytes_of_hex "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
      digests =       [ Bytes.bytes_of_hex "125d7342b9ac11cd91a39af48aa17b4f63f175d3", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0102030405060708090a0b0c0d0e0f10111213141516171819";
      data =          Bytes.bytes_of_hex "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
      digests =       [ Bytes.bytes_of_hex "4c9007f4026250c6bc8414f9bf50c86c2d7235da", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c";
      data =          bytes_of_string "Test With Truncation";
      digests =       [ Bytes.bytes_of_hex "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key - Hash Key First";
      digests =       [ Bytes.bytes_of_hex "aa4ae5e15272d00e95705637ce8a3b55ed402112", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
      digests =       [ Bytes.bytes_of_hex "e8e99d0f45237d786d6bbaa7965c7808bbff1a91", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key - Hash Key First";
      digests =       [ Bytes.bytes_of_hex "aa4ae5e15272d00e95705637ce8a3b55ed402112", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          bytes_of_string "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data";
      digests =       [ Bytes.bytes_of_hex "e8e99d0f45237d786d6bbaa7965c7808bbff1a91", SHA1 ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
      data =          Bytes.bytes_of_hex "4869205468657265";
      digests =       [
        Bytes.bytes_of_hex "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7", SHA256;
        Bytes.bytes_of_hex "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6", SHA384;
        Bytes.bytes_of_hex "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854", SHA512
      ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "4a656665";
      data =          Bytes.bytes_of_hex "7768617420646f2079612077616e7420666f72206e6f7468696e673f";
      digests =       [
        Bytes.bytes_of_hex "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843", SHA256;
        Bytes.bytes_of_hex "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e8e2240ca5e69e2c78b3239ecfab21649", SHA384;
        Bytes.bytes_of_hex "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737", SHA512
      ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          Bytes.bytes_of_hex "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
      digests =       [
        Bytes.bytes_of_hex "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe", SHA256;
        Bytes.bytes_of_hex "88062608d3e6ad8a0aa2ace014c8a86f0aa635d947ac9febe83ef4e55966144b2a5ab39dc13814b94e3ab6e101a34f27", SHA384;
        Bytes.bytes_of_hex "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb", SHA512
      ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0102030405060708090a0b0c0d0e0f10111213141516171819";
      data =          Bytes.bytes_of_hex "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
      digests =       [
        Bytes.bytes_of_hex "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b", SHA256;
        Bytes.bytes_of_hex "3e8a69b7783c25851933ab6290af6ca77a9981480850009cc5577c6e1f573b4e6801dd23c4a7d679ccf8a386c674cffb", SHA384;
        Bytes.bytes_of_hex "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd", SHA512
      ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c";
      data =          Bytes.bytes_of_hex "546573742057697468205472756e636174696f6e";
      digests =       [
        Bytes.bytes_of_hex "a3b6167473100ee06e0c796c2955552b", SHA256;
        Bytes.bytes_of_hex "3abf34c3503b2a23a46efc619baef897", SHA384;
        Bytes.bytes_of_hex "415fad6271580a531d4179bc891d87a6", SHA512
      ];
      truncation = Some 16
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          Bytes.bytes_of_hex "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374";
      digests =       [
        Bytes.bytes_of_hex "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54", SHA256;
        Bytes.bytes_of_hex "4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c60c2ef6ab4030fe8296248df163f44952", SHA384;
        Bytes.bytes_of_hex "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598", SHA512
      ];
      truncation = None
    }; {
      key =           Bytes.bytes_of_hex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
      data =          Bytes.bytes_of_hex "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e";
      digests =       [
        Bytes.bytes_of_hex "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2", SHA256;
        Bytes.bytes_of_hex "6617178e941f020d351e2f254e8fd32c602420feb0b8fb9adccebb82461e99c5a678cc31e799176d3860e6110c46523e", SHA384;
        Bytes.bytes_of_hex "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58", SHA512
      ];
      truncation = None
    }]

  let print_test_case v =
    List.iter (fun (digests, hash_alg) ->
      Printf.printf "key: %s\ndata: %s\ndigests: %s (%s)\n"
        (Bytes.hex_of_bytes v.key) (Bytes.hex_of_bytes v.data)
        (Bytes.hex_of_bytes digests) (string_of_hash_alg hash_alg)
    ) v.digests

  let test v =
    List.for_all (fun (digest, hash_alg) ->
      let digest' = hmac hash_alg v.key v.data in
      match v.truncation with
      | None ->
          Bytes.equalBytes digest digest'
      | Some i ->
          Bytes.equalBytes digest (fst (Bytes.split digest' (Z.of_int i)))
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
      (string_of_hash_alg t.hash_alg) (Bytes.hex_of_string t.input) t.output
      (Bytes.hex_of_bytes (hash t.hash_alg (bytes_of_string t.input)))

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
    Bytes.equalBytes output (Bytes.bytes_of_hex t.output)
end

module TestHashUpdate = struct
  type test = {
    input: string; (* copied from TestHash but we don't repeat *)
    output: string;
    hash_alg: hash_alg;
  }

  let tests = [{
      hash_alg = MD5;
      input = "";
      output = "d41d8cd98f00b204e9800998ecf8427e";
    }; {
      hash_alg = MD5;
      input = "a";
      output = "0cc175b9c0f1b6a831c399e269772661";
    }; {
      hash_alg = MD5;
      input = "abc";
      output = "900150983cd24fb0d6963f7d28e17f72";
    }; {
      hash_alg = MD5;
      input = "message digest";
      output = "f96b697d7cb7938d525a2f31aaf161d0";
    }; {
      hash_alg = MD5;
      input = "abcdefghijklmnopqrstuvwxyz";
      output = "c3fcd3d76192e4007dfb496cca67e13b";
    }; {
      hash_alg = MD5;
      input = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
      output = "d174ab98d277d9f5a5611c2c9f419d9f";
    }; {
      hash_alg = MD5;
      input = "12345678901234567890123456789012345678901234567890123456789012345678901234567890";
      output = "57edf4a22be3c955ac49da2e2107b67a";
    }; {
      hash_alg = SHA1;
      input = "abc";
      output = "a9993e364706816aba3e25717850c26c9cd0d89d";
    }; {
      hash_alg = SHA1;
      input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
      output = "84983e441c3bd26ebaae4aa1f95129e5e54670f1";
    };{
      hash_alg = SHA1;
      input = "a";
      output = "86f7e437faa5a7fce15d1ddcb9eaeaea377667b8"; 
    }; {
      hash_alg = SHA1;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "e0c094e867ef46c350ef54a7f59dd60bed92ae83";
    }; {
      hash_alg = SHA256;
      input = "abc";
      output = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
    }; {
      hash_alg = SHA256;
      input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
      output = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
    }; {
      hash_alg = SHA256;
      input = "a";
      output = "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb";
    }; {
      hash_alg = SHA256;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "8182cadb21af0e37c06414ece08e19c65bdb22c396d48ba7341012eea9ffdfdd";
    };{
      hash_alg = SHA256;
      input = "\x19";
      output = "68aa2e2ee5dff96e3355e6c7ee373e3d6a4e17f75f9518d843709c0c9bc3e3d4";
    }; {
      hash_alg = SHA256;
      input = "\xe3\xd7\x25\x70\xdc\xdd\x78\x7c\xe3\x88\x7a\xb2\xcd\x68\x46\x52";
      output = "175ee69b02ba9b58e2b0a5fd13819cea573f3940a94f825128cf4209beabb4e8";
    }; {
      hash_alg = SHA256;
      input = "\x83\x26\x75\x4e\x22\x77\x37\x2f\x4f\xc1\x2b\x20\x52\x7a\xfe\xf0\x4d\x8a\x05\x69\x71\xb1\x1a\xd5\x71\x23\xa7\xc1\x37\x76\x00\x00\xd7\xbe\xf6\xf3\xc1\xf7\xa9\x08\x3a\xa3\x9d\x81\x0d\xb3\x10\x77\x7d\xab\x8b\x1e\x7f\x02\xb8\x4a\x26\xc7\x73\x32\x5f\x8b\x23\x74\xde\x7a\x4b\x5a\x58\xcb\x5c\x5c\xf3\x5b\xce\xe6\xfb\x94\x6e\x5b\xd6\x94\xfa\x59\x3a\x8b\xeb\x3f\x9d\x65\x92\xec\xed\xaa\x66\xca\x82\xa2\x9d\x0c\x51\xbc\xf9\x33\x62\x30\xe5\xd7\x84\xe4\xc0\xa4\x3f\x8d\x79\xa3\x0a\x16\x5c\xba\xbe\x45\x2b\x77\x4b\x9c\x71\x09\xa9\x7d\x13\x8f\x12\x92\x28\x96\x6f\x6c\x0a\xdc\x10\x6a\xad\x5a\x9f\xdd\x30\x82\x57\x69\xb2\xc6\x71\xaf\x67\x59\xdf\x28\xeb\x39\x3d\x54\xd6";
      output = "97dbca7df46d62c8a422c941dd7e835b8ad3361763f7e9b2d95f4f0da6e1ccbc";
    }; {
      hash_alg = SHA384;
      input = "abc";
      output = "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7";
    }; {
      hash_alg = SHA384;
      input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
      output = "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039";
    }; {
      hash_alg = SHA384;
      input = "a";
      output = "54a59b9f22b0b80880d8427e548b7c23abd873486e1f035dce9cd697e85175033caa88e6d57bc35efae0b5afd3145f31";
    }; {
      hash_alg = SHA384;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "72f5893331c249312d3c2b7a9709a7b96908b7769179dd9824ed578669fcc1f1c2de02c03b3d35a467aa0b472c1bb3d1";
    }; {
      hash_alg = SHA512;
      input = "abc";
      output = "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";
    }; {
      hash_alg = SHA512;
      input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
      output = "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909";
    }; {
      hash_alg = SHA512;
      input = "a";
      output = "1f40fc92da241694750979ee6cf582f2d5d7d28e18335de05abc54d0560e0f5302860c652bf08d560252aa5e74210546f369fbbbce8c12cfc7957b2652fe9a75";
    }; {
      hash_alg = SHA512;
      input = "0123456701234567012345670123456701234567012345670123456701234567";
      output = "846e0ef73436438a4acb0ba7078cfe381f10a0f5edebcb985b3790086ef5e7ac5992ac9c23c77761c764bb3b1c25702d06b99955eb197d45b82fb3d124699d78";
    }]

  (* SI: uses hash, rather than hash's components. *)
  let print_test t =
    Printf.printf "%s(%s) = %s (got: %s)\n"
      (string_of_hash_alg t.hash_alg) (Bytes.hex_of_string t.input) t.output
      (Bytes.hex_of_bytes (hash t.hash_alg (bytes_of_string t.input)))

  let test t =
    let input = bytes_of_string t.input in
    let ctx = digest_create t.hash_alg in
    (* Add input incrementally *)
    for i = input.Bytes.index to (input.Bytes.length - 1) do
       digest_update ctx (Bytes.abyte (Bytes.index input (Z.of_int i)))
    done; 
    let output = digest_final ctx in  
    Bytes.equalBytes output (Bytes.bytes_of_hex t.output)
end

module TestEcc = struct
  type test = {
    params: ec_params;
    point: ec_point;
  }

  let x = Bytes.bytes_of_hex

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
      (Bytes.hex_of_bytes ecx) (Bytes.hex_of_bytes ecy)

end


module TestRsa = struct

  let keysize_small, keysize_large = 1024, 2048
  (* ci/corecryptotest_reduce_keysize.sh alters next line: *)
  let keysize = keysize_large

  (* Test vectors for RSA/DSA/ECDSA below *)
  let tests =
    let large = CoreCrypto.random (Z.of_int (keysize/8 - 11)) in (* bytes_in_keysize - padding *)
    let small = CoreCrypto.random (Z.of_int ((min keysize 512)/8 - 11)) in
    [large; small; bytes_of_string "0"]

  let roundtrip original_bytes =
    let k = rsa_gen_key (Z.of_int keysize) in
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

  let print_test x = print_string (Bytes.hex_of_bytes x)

end


module TestDsa = struct

  let keysize_small, keysize_large = 1024, 2048
  (* ci/corecryptotest_reduce_keysize.sh alters next line: *)
  let keysize = keysize_large

  let tests = TestRsa.tests

  let check original_bytes =
    let private_key = dsa_gen_key (Z.of_int keysize) in
    let public_key = { private_key with dsa_private = None } in
    let sig_bytes = dsa_sign None private_key original_bytes in
    if not (dsa_verify None public_key original_bytes sig_bytes) then begin
      Printf.printf "dsa_sign/dsa_verify: check failed\n";
      false
    end else
      true

  let print_test = TestRsa.print_test
end


module TestEcdsa = struct

  let tests = TestRsa.tests

  let check original_bytes =
    let params = { curve = ECC_P256; point_compression = false } in
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

  type test_vector = {
    params: dh_params;
    dh_x: string;
    dh_X: string;
    dh_y: string;
    dh_Y: string;
    secret: string
    }

  let print_dh_params dhp =
    Printf.printf "p:\t%S\ng:\t%S\nq:\t%S\nsafe?\t%b\n"
      (Bytes.hex_of_bytes dhp.dh_p) (Bytes.hex_of_bytes dhp.dh_g)
      (match dhp.dh_q with | None -> "-" | Some q -> Bytes.hex_of_bytes q)
      dhp.safe_prime

  let print_test_vector v =
    print_dh_params v.params;
    Printf.printf "x:\t%S\nX:\t%S\ny:\t%S\nY:\t%S\nsecret:\t%S\n" v.dh_x v.dh_X v.dh_y v.dh_Y v.secret

  (* Note that only dh_p is currently used *)
  let apache =
    {
      dh_p = Bytes.bytes_of_hex "d67de440cbbbdc1936d693d34afd0ad50c84d239a45f520bb88174cb98bce951849f912e639c72fb13b4b4d7177e16d55ac179ba420b2a29fe324a467a635e81ff5901377beddcfd33168a461aad3b72dae8860078045b07a7dbca7874087d1510ea9fcc9ddd330507dd62db88aeaa747de0f4d6e2bd68b0e7393e0f24218eb3";
      dh_g = Bytes.bytes_of_hex "02";
      dh_q = Some (Bytes.bytes_of_hex "d67de440cbbbdc1936d693d34afd0ad50c84d239a45f520bb88174cb98bce951849f912e639c72fb13b4b4d7177e16d55ac179ba420b2a29fe324a467a635e81ff5901377beddcfd33168a461aad3b72dae8860078045b07a7dbca7874087d1510ea9fcc9ddd330507dd62db88aeaa747de0f4d6e2bd68b0e7393e0f24218eb2");
      safe_prime = true;
    }

  let ikegroup14 =
    {
      dh_p = Bytes.bytes_of_hex "ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca18217c32905e462e36ce3be39e772c180e86039b2783a2ec07a28fb5c55df06f4c52c9de2bcbf6955817183995497cea956ae515d2261898fa051015728e5a8aacaa68ffffffffffffffff";
      dh_g = Bytes.bytes_of_hex "02";
      dh_q = Some (Bytes.bytes_of_hex "7fffffffffffffffe487ed5110b4611a62633145c06e0e68948127044533e63a0105df531d89cd9128a5043cc71a026ef7ca8cd9e69d218d98158536f92f8a1ba7f09ab6b6a8e122f242dabb312f3f637a262174d31bf6b585ffae5b7a035bf6f71c35fdad44cfd2d74f9208be258ff324943328f6722d9ee1003e5c50b1df82cc6d241b0e2ae9cd348b1fd47e9267afc1b2ae91ee51d6cb0e3179ab1042a95dcf6a9483b84b4b36b3861aa7255e4c0278ba3604650c10be19482f23171b671df1cf3b960c074301cd93c1d17603d147dae2aef837a62964ef15e5fb4aac0b8c1ccaa4be754ab5728ae9130c4c7d02880ab9472d455655347fffffffffffffff");
      safe_prime = true;
    }

  let amazon =
    {
      dh_p = Bytes.bytes_of_hex "d6c094ad57f5374f68d58c7b096872d945cee1f82664e0594421e1d5e3c8e98bc3f0a6af8f92f19e3fef9337b99b9c93a055d55a96e425734005a68ed47040fdf00a55936eba4b93f64cba1a004e4513611c9b217438a703a2060c2038d0cfaaffbba48fb9dac4b2450dc58cb0320a0317e2a31b44a02787c657fb0c0cbec11d";
      dh_g = Bytes.bytes_of_hex "27e1ab131b6c22d259d199e9df8acbb1fe2fd4461afb7cb321d6946b02c66a9a45c062d5ffd01e47075cf7b082845e87e49529a66a8405354d1148184933078341c9fa627fde3c2a9a195e2cae33145c47bd86bbcd49b012f235bbc58486ce1d75522175fc7c9efd3aeaac06855b003e65a2208d16e7d89d9359dfd5e7002de1";
      dh_q = Some (Bytes.bytes_of_hex "9414a18a7b575e8f42f6cb2dbc22eb1fc21d4929");
      safe_prime = false;
    }

  let test_vectors = [
    (* Amazon 1024-bit DSA group, 160-bit exponents *)
    {
      params = amazon;
      dh_x = "f1c27c1bb6db3b52924fc731f5b0364d7e8bb357";
      dh_X = "0e3bfc5827ae3962f7e07323382805a0e9bf6f65276a63fddbd083eb00183812d83a1ff11f570e91b4589e4a3372cb5dd439cb3cf1252a947184e5ebadacd1b3e60b58832cd10138029b73e07e93a8ad152fbcfa2dc139d6c780e3a8f3db210791e6b95b37e2036c0478875007b44b9f86680368610fd0d491ddce39942a4a90";
      dh_y = "f59f06875d0bff7c42ce658a8b0d19b714ccd00b";
      dh_Y = "b11b1669e09067b92931fc2246513fdcdb4a4bb81127f611fed23071896f5ff3ed8a9b6be3344b129872c82b56e0329a9f8d36c28e34b6e522013f4553ec09a67bf81198d8c852427faaf0d33bf03b1a28c2bdea6aab5daf94abdd2365b9fc7803f79f3cb69d0cecc88e283760870ffd2a78a1622d371bd11adb1b7d517140b3";
      secret = "29d79c06e9bd43f0a2cccb69d68ca170633979d8985a28f34268b6f5e5264ad44a6ea6fa49b298054d7b90944d4f4ff113e88ee416070b05f05de9c67511b5cb70f78211b12744e77718cec12468cfc60cf91e582bb96b46e5f0670f0a8262382fca9834b5be0d5a737bbe8c8a57073facf64af818532309cbd1435065113fab";
    };
    (* Apache 2.2 group, 160-bit exponents *)
    {
      params = apache;
      dh_x = "d4fc3dbe6d0ef9324fd002ebbd5b898d11352cbc";
      dh_X = "c496c19df7632a44a817105c7c5bef97251fcb18f8a4cd28fd937738e6cad20a9fbe009bfe2757f54844b56b4ef098c6712fd501844771b29b9c68494ca8b6e226e961795a4d65e08ec7673da6a113718ac84f67f2cd7f37880e9bcfa53f6301c4cda6212129454831a762755f44755ed0246087345a25a9a770dbfe29799577";
      dh_y = "5adba88d5e3147c8a901fcee5e6118ec13137daf";
      dh_Y = "4e507a03aada862f3367d274a6e02462b56c02a7a68785ef7cfcc2d3b3a3d3ccfa2a40a26dc7916a78fea1293bd8dd8b2018e4969dba84cef6903468a337288cd9f63d3332d2c1e24f15eef075a128d8ed2be7a1b53723ef7f3f2d7b260c2bf9d9991f786c13b6b6d8df474bbeb51df40cb912e10dd8af789fb92340f02004b4";
      secret = "64ef68c9cb77279b3f8de6f4417cb61846e74c01e8d2409c53a92982886dc20bf34838a89d78be34aca8998423d41c6b7bc1104408fb751dbe17390221b032b249858574f1669e49c3394f2b5cfec2292776ceb2849fafd5689c436005ed47405ca578ef4e6c8cab2d6f542f912de887bbe258370c3108b3894f0d467415ec43";
    };
    (* Apache 2.2 group, 1024-bit exponents *)
    {
      params = apache;
      dh_x = "31d970551b056f8fc067e478e60b314d0fb2f278fc8b627a14a97bf5a7b8af1cc15e3d8c659064010a3f383153d2c4f3e65ba3b00c54ffdfe74ce3361312d5b5a21e2ca67745658fb89355acad604834649d2c38f2895f9e9115be913e302ebc56780e2d24fa227fc22de1586c81bc0f53ae6050662be1343a8ab74244e815cd";
      dh_X = "afa384f7c10bc06d6db2c503fa133a416aa9d546b46016392475f4785f2ece4b26d0d8a90892662f0066d11841bc88c434f24769fb4e1094fe1e7505b63ac9b1ad7f8dca9cc28be8d1eb32bd93b3111f144207f5ebe2894f8846aae2af26af7c2e6c9e774afc390222efbee8f250eb69672d983c86c943301b2bdddcf4ed7ed8";
      dh_y = "c989f2e956327f7c3e69ee43164e6d2853182704847cde14370fadad5cfe66924f613fdfb08613f2200646a375cf88e183bb6eacfc6d45e561ba9f33a95259a3fa53487a02765abb2b7ed4749d1482912d50ce4951249fc40c333c4caf05248a5ad30de61ff116523b3163c9c584e9d0b86fc7e96403543b66d1c2a593262199";
      dh_Y = "46707a6c3d14bc5dc72c9151cfcaddcfcb86a58feb5917e72f64fd009324660a55debf5840478db15973df82227f4648ed1fcb13d69444401f4c85ab7d832cbbae51bb15bed4aa0ddb7e26d5470291fd1b8c8894fa5afc536bc7772a67288fe55850a20c0c41fd594757732a0be6c71f30828598e6a1d507facfca1c2efe7eb2";
      secret = "159c55d697d1cc982638914d6659500b3dd1969ec065e41fc56a7ffe22d84520bfcb08b4fa195dfe53722c659438857c8931fe22af0072de85a79c656a52a385016380e0c01085db9eaf62cf5047b57ec5344f59355f799641c2550071256fe9644bbe628e169ee1d0fd451942c7c18f2f994188281b505213d8bd7b838794c8";
    };
    (* IKE Group 14, 224-bit exponents *)
    {
      params = ikegroup14;
      dh_x = "5fe7e6fb40ed9ab5c7d30b062ffe63bd454159330393f287bfa8a0d4";
      dh_X = "e4d042e2a7b1d7a411aa3fc29affb6c3c5d7f049fdc6cdd8755dbdd83ba91f33de90b40e9ab9ab820bf054a8224d9b5382801e852818aefe645ff31c93f6e1a1fd82d95070d075477b6fdfc6a18d8a87988e9eaefc54b6b3c625dfe1cbcd278499c4b47e3b23dadd85824c768b170a1a7789c2f29f5ab2090105cfbd5c7f3e8b353442dc4cb3214a1126aec1428a85aab9a743be96920712c604261236df0a09d7ff6baac5517da38c05d7f2e7cf787dbdc08d5e5b07f32fe41aab1f644b177d6726f7a478943d7308f72d317f24dd0979849d9789172584ca29aad64d61dc94e31f2ce09765a7bac8406f9ff8c961762931c5093fa0ef28fcf3ccb59176c512";
      dh_y = "e540441ab02b7ac8059f97fc5a725972bb5ca391b2b879c9f05470cf";
      dh_Y = "5f554d0be1b92abd6b815222ae3af87baad66481653f504a2492227fdb2900c266312d9caf8dbb2fceebfda9080ea17306e813e44d24389e8576f23ef39611e865cdd064ee0eb815fac38051fdfc0ac17efffd661eaefef24626a6a8a00c61d32c028ee183b55dd677edac677f0fed73e9be37aa7d4fd0ef5bd4a6843b1639c05416651b4ad23f4fb6b77fea949e2fba6f6e9aa320297a33872a6f3e8d9f89e7b6b34b439474e25470a58b3b2abf390b862fcf2fda79a7191277ce0981772c0d669ff60515de0ea57d22c72703b825eedd61c5fda26fc0260f320c0c93a2a3e91109128b19d98de996015d67ce5b12dce1c859ae33564e11534e96559b8f52c1";
      secret = "10ca7728af50fd03baad3307b9245f5d51813ca8aadc8a15b25eb2a17a4f3593a9778fd5ffffb5736fcbfcc508de4a8f190d8534db92d1c124c28f9dc91705e26306194d349daa455f638497715b2112174cb24e4f5904b2c56c51081d17eb9e86f83cc0f66b0c07195962766066e13e94c1c5a6339872d04fb231a19117d10380ec99ef2a14ba9151d70635b26fac5d0339b577bb63db2ae259ca27001abd1108a67d7d85353a2fa0f93e74a08db71923e62bf490f04746529f92d181cc7ee654ee99f143190909db89af7d8089fdc6c39fe7b4e18fc584fe59967957f9c5bc24d802ad3a8911bfee074311319ce2f00b2f34326a3be17b8a69c7131d2b1b4f";
    };
    (* IKE Group 14, 2048-bit exponents *)
    {
      params = ikegroup14;
      dh_x = "e18ee9f415a28cb36670181d4dc37ecb1ee3769aa3b38134c3bf291c83a21a3a411f471f90663281924301972cb6de6bf05efc048c14077e990546ae32605eb9b349ef68c835b9829e1058b7bd187cf4a99ba373c6ab70319e1b05e7a26ab232e9ef7213c7079629c66af15c5021a296ee19bb6f38b08a7c6913c7315241fd32d0e8e84f8dc5c6b445ecdd66a94131c472ebc93dbdea7114741b822482178c9cae5af3cdd2a544ce9d89f7c6feacae0b3f428488bfb62a8c5563e40cda461a9f56850a98ce1d573f406d6c3ca5e2010132502466eb67f0f743d65b60bfbb5d8a6a1373c4006c18451282febc9aea069f80e9f60798ba7e39c0155eb83b1036f1";
      dh_X = "c20dddd6ca7868bf616b1110c914cbccd73bbdbdd135e8eb7b9ffc520540f9c9f53ffc25da96ccb07ca507d42eb9541eb2058bab594ae0baaed3167c138bfe9c7c3ab6fc5a9d38255dd1fc1c586975943e51f62d8c9f57a6ac9a714a949ff022ad8ca2d1ebfbaa1f9a9420bcd1ad09c9dc9bc4a9457fd6c353c97edfc0bd7dc36f52f5c9027144ecc2a8bced9006ffa0407b663511dd00536cb17c510694487d6483e125e4b6259129aa874aa2fcda4b39a92028bb70605a6f35473740ee340756168d81a1a0f91cfdecd5a36d04b772271c96d71ab9e89a8d66bc1042425da3ef221554d4b13b2b017fe894f05c7c8bb86e423f1af8c61d834a9c87f00fe206";
      dh_y = "3e71a6830efe80d9e81147f8d9637685d9d0ddbf6ff164eaffd4d249ccc0dea4f26e5952a6e148075d51a2979c86ce1bafc7087864cb2639d2af2c89ac4d7c11ab996e10bc88097075a7bb07160e539d8020bc2c2126697bfb8c07e813520e5a917b9541854a976cb93294c65bd3a851438c50a642235eefefb884507e28f1139b427f6e7ecb054113c73003acbaad258a6674b321617061eb74d79e0d5603d9d82ef5ecba243b42a817c4ba6938c4ab50f860d89351fa2ebb17e09f26132a05c0fc54efe8cbaf96fe614901ca9c0722bee655fb614621fc3823a2548102a425f9c4f7a54b6987ac7c18788c37638e8b7add36d8638a9a4b544faf35c39a7b3f";
      dh_Y = "4dbd94438cf2ae324532fe4df45a10bad7197ac54d3295bd4a9f8b0d9b8022a93ab8d078662e71b77aaeac29194af196ea0add0359e80500f6c048367f6439c5db16bcfb7f6997fd80f16aa95a31dc85d2350ce6b7e3d10d679bf69e6310ce6df40b3ca312ad39c61f7f26b6b452dd8984750dc1907931469715597cfcd04a1847e61af80cb592a9d1e44aab7719c94e7307305b306fc6110c35b72fc28d49f8a785c04944c8c0b35bf35427ee3759223646b2ba3f86edd53e68eaf2a0d273f858212d69a5933729863045bb5cb5848f7098e8d528d164c49be44486f91e1bce5c572680dfe5addaef58608783b629f42fa6aeaa7f9104efb74d296882685bbb";
      secret = "e71d601d89865ea0e4bdc24f02a515807f66979329447ef36a7884b595aba78206d320c08cf56232c7e5b95813c5e24fc2d82087ef261f1d1eb3fdb5936746adf0dc744aca258a7294929a3441ce63842d4a4d7c43e93407413b6b736adaea7f61da476ee5cd961957844705792966966e9b7b8f77414b868264d33c1d1ceb47a62bd1382143c075a23319bf50718017fb7fd624c048ae0eb4a4487c3de8d0fd56fb3343fef41952f1904c11c5227e764297e0766f9479d28230720bde572daabe9f63fd432071a22ee826388977f7214eb00ee3eef42c04c983c7c80a6e7d91377941241c6eb1eba24f968a634c283553fdd5c8eff684976e50de92a37c6f08";
}
  ]

  let test v =
    let alice =
      {
        dh_params  = v.params;
        dh_public  = Bytes.bytes_of_hex v.dh_X;
        dh_private = Some (Bytes.bytes_of_hex v.dh_x)
      } in
    let bob =
      {
        dh_params  = v.params;
        dh_public  = Bytes.bytes_of_hex v.dh_Y;
        dh_private = Some (Bytes.bytes_of_hex v.dh_y)
      } in
    let secret1 = dh_agreement alice bob.dh_public in
    let secret2 = dh_agreement bob alice.dh_public in
    Bytes.hex_of_bytes secret1 = v.secret &&
    string_of_bytes secret1 = string_of_bytes secret2

  let dh_param_size_small, dh_param_size_large = 512, 1024
  (* ci/corecryptotest_reduce_keysize.sh alters next line: *)
  let dh_param_size = dh_param_size_large

  let simple_test () =
    let params = dh_gen_params (Z.of_int dh_param_size) in
    let alice = dh_gen_key params in
    let bob = dh_gen_key params in
    let shared1 = dh_agreement alice bob.dh_public in
    let shared2 = dh_agreement bob alice.dh_public in
    string_of_bytes shared1 = string_of_bytes shared2
end


module TestEcdhke = struct

  type test_vector = {
    params: ec_params;
    ecdh_d1: string;
    ecdh_x1: string;
    ecdh_y1: string;
    ecdh_d2: string;
    ecdh_x2: string;
    ecdh_y2: string;
    secret: string;
    }

  let print_curve = function
    | ECC_P256 -> "P256"
    | ECC_P384 -> "P384"
    | ECC_P521 -> "P521"

  let print_dh_params ecp =
    Printf.printf "curve:\t%S\npoint compression?:\t%b\n"
      (print_curve ecp.curve) ecp.point_compression

  let print_test_vector v =
    print_dh_params v.params;
    Printf.printf "d1:\t%S\nx1:\t%S\ny1:\t%S\nd2:\t%S\nx2:\t%S\ny2:\t%S\nsecret:\t%S\n"
      v.ecdh_d1 v.ecdh_x1 v.ecdh_y1 v.ecdh_d2 v.ecdh_x2 v.ecdh_y2 v.secret

  let test_vectors = [
    (* From OpenSSL evptests.txt *)
    {
      params = { curve = ECC_P256; point_compression = false };
      ecdh_d1 = "8a872fb62893c4d1ffc5b9f0f91758069f8352e08fa05a49f8db926cb5728725";
      ecdh_x1 = "2c150f429ce70f216c252cf5e062ce1f639cd5d165c7f89424072c27197d78b3";
      ecdh_y1 = "3b920e95cdb664e990dcf0cfea0d94e2a8e6af9d0e58056e653104925b9fe6c9";
      ecdh_d2 = "fd4473bb54c3370505599de274b212019a44634bdf276a4b07b7fe5e78f29763";
      ecdh_x2 = "2006e5e14a078aa73fb8a625e561254bbf2d0d4fec0ab995942372ea514095d3";
      ecdh_y2 = "bc20f912cb318f3234af648ea720643b3f701f9b7adeb89d0abe74d9efb69c46";
      secret  = "e3cc07dfbdde76a1139811db9ff5faf9d17ef39944f1e77d1f6a208524bf7b1b"
    };
    (* Random test vectors *)
    {
      params = { curve = ECC_P256; point_compression = false };
      ecdh_d1 = "c945c799c65d06b604be3dd8e3994efc733877014aa407e5edf336650429b9ca";
      ecdh_x1 = "7fa7034cf81e6e6224509b7e61466e3d0724a6caceadf8e5273acf2bf743608c";
      ecdh_y1 = "f9edc8b1d743c96440f57212f082dcdfccd422d2d4b67620bd6770f1a002c7e2";
      ecdh_d2 = "8c198d42a0a2f3a2455ad5f690c87cc2aedc00967d3f973f19e0aba73198ee36";
      ecdh_x2 = "b3100291722534d0057f768359795cb6e140012789996df4382a8a301a5e0da0";
      ecdh_y2 = "7babe994735fd16985c1771a2aa5ba7875a949a3730181eb33ad15104a9e2e48";
      secret  = "7ab2cac9a74da380b5dd32359e5abea8ba9b055faf91213fbc4ae687444b6c4c";
    };
    {
      params = { curve = ECC_P256; point_compression = false };
      ecdh_d1 = "0f242a058a337714c17b94bafb24fcc2c0a376b479105140df5df3b09b954eaa";
      ecdh_x1 = "4dba00dfb4b0d6b9f902c0a6e8e360362a5a0d05e81e43197b6b5fdcaae33f4f";
      ecdh_y1 = "4d835d7df671d184056745dc57bc0d5719a22db4ad2970ce07ba87b8435e79c1";
      ecdh_d2 = "7c08811670bee64dc66a0fcfd5b8531353acb11aea83d8b857bf05dd3e7b5443";
      ecdh_x2 = "dc6826c4fe5bc7aea47956c595d82dfd16f3fa890b53eb98756b135f81bb20f8";
      ecdh_y2 = "0e43d8a7746bdbe42d01704e52beedb9fed12cf018dab48bb0476a97788a5600";
      secret  = "cb1dd9c96a266a93e94b3e2dbc1c3e772263c49c35c735316c1b573aef344013";
    };
    {
      params = { curve = ECC_P384; point_compression = false };
      ecdh_d1 = "afebb080940b45951bfa5751f9e0ff76ef5634d7ea0b15b2376539f4cc02d2ebe4891f6e36d6a56c8e5f784fdcb35b81";
      ecdh_x1 = "28b314bfe8651ad2a9cd76922b43373923811fb12a74a32bc59ac8c4f4d5a1ca593de410dfa148b3ea70247e6be8c33f";
      ecdh_y1 = "616eebdc4a848782627d73b64a5c35072bf77c1324c11c36434e8362e8306a5ba70b5d1717658d331a1870024649e50b";
      ecdh_d2 = "5a8421fa5ce0e383cbfe0f5299749a2ffb59c40f31d618c80ce6e5f988833fe4d12ba45781d7918057c4391d25ef7d34";
      ecdh_x2 = "790603650350d39904619866d6a1a50709cab24eda82719dd24ea49caf13e06f5b7583639f5e640577f74025feaa0770";
      ecdh_y2 = "126b1f347ab4eb8cd2dbf0119932c1cd981825c45c5a9c8d62a50c51042d743ee242cfeabd973a0170a9309e1a88c4c6";
      secret  = "7b0ee48cdd81c0e6165b35535c6c3e20058cce001e074020b3ca92a8279a9c0d1879a2f7221f04a1860f3c3ab4305253";
    };
    {
      params = { curve = ECC_P384; point_compression = false };
      ecdh_d1 = "afebb080940b45951bfa5751f9e0ff76ef5634d7ea0b15b2376539f4cc02d2ebe4891f6e36d6a56c8e5f784fdcb35b81";
      ecdh_x1 = "28b314bfe8651ad2a9cd76922b43373923811fb12a74a32bc59ac8c4f4d5a1ca593de410dfa148b3ea70247e6be8c33f";
      ecdh_y1 = "616eebdc4a848782627d73b64a5c35072bf77c1324c11c36434e8362e8306a5ba70b5d1717658d331a1870024649e50b";
      ecdh_d2 = "5a8421fa5ce0e383cbfe0f5299749a2ffb59c40f31d618c80ce6e5f988833fe4d12ba45781d7918057c4391d25ef7d34";
      ecdh_x2 = "790603650350d39904619866d6a1a50709cab24eda82719dd24ea49caf13e06f5b7583639f5e640577f74025feaa0770";
      ecdh_y2 = "126b1f347ab4eb8cd2dbf0119932c1cd981825c45c5a9c8d62a50c51042d743ee242cfeabd973a0170a9309e1a88c4c6";
      secret  = "7b0ee48cdd81c0e6165b35535c6c3e20058cce001e074020b3ca92a8279a9c0d1879a2f7221f04a1860f3c3ab4305253";
    };
    {
      params = { curve = ECC_P384; point_compression = false };
      ecdh_d1 = "01f6";
      ecdh_x1 = "bbb2aa7033419e9de067ad3a14dcb555517a82e850e732b67ec45812e37e8a5a268d5f959f690fc387e008ba3f085615";
      ecdh_y1 = "6d926f4477bd7c488c48815f5bf6fc21fe1f4b23c9ec191c59765e36c36f168d617fb0f9417a9d3d2df9348917126076";
      ecdh_d2 = "119424f7ec6eb41524fd67a0f9c7ea9a73a473e04907e1eff84fc62d661e6f467d7d5daa861bfdd9a1e35283fbfd0c8b";
      ecdh_x2 = "fe3acf39944e2b387c24a35e9e8dcf2268e1a1c6d334a34d288cecf7c0bbc7c9c9f25832465737a7b277c7370112752d";
      ecdh_y2 = "e6fbc9eb1beb4cb96b5114f81bc1083540fbf398aa96dc74b21fa7e9f9884f5ed6680a7c1eb900663b92683b4a4e2769";
      secret  = "792084929baaa4e82701797d98bb388aeddefb377f6641ddfeb8b1bec3594997b5da246e99249e0f200402060fa328b1";
    };
    {
      params = { curve = ECC_P521; point_compression = false };
      ecdh_d1 = "01fac6086741d6458290707921a025b6b9676a0d593b3c5ef2f9552b077bcfd563770de2599c9d417fdabde737a71685ba6235801a1c6841fe107a7d275238552262";
      ecdh_x1 = "015353d2772fa47a519f69f5ec9c0b01e05279bec3c85233158e3e197585327b56dcb01da40b8542a0aca3e4d1dd4aebd6d0598a092356366942358da86d753f14b7";
      ecdh_y1 = "595391d4d4aeeefbffa8de76fac2a8ee3cf8b72984572c3e543807775a2fb1f769fdd582cc9769ee2a419694e4d3518cf0f67e936835d2099c527d33c4ec4b100b";
      ecdh_d2 = "b9ea0c80398809305e5719665c9c126a6085ac7728abbb709e74578dd2ba87b0fbd8a42fce004c0ba6399fd9cb675703a20bb2f8765ef0111ff9c596f5b96f49ba";
      ecdh_x2 = "67dc5b1088b4dad61bc92a89f8f6a791b9be04e48da41813de31da7f260b7084094665622462eae5ea60be63e02574d1a7b42ae4ad02cd68627cbfde3d44748f65";
      ecdh_y2 = "fec3d94be661eff265d082fb30f20d95ac06cf28e41f39dcbb3c6f19732de5b4cadafd77af4c7308e0bfe3c1d1878f2bf80e2ba0b9ff3b72a1306c6025fd32c3d1";
      secret  = "01a22359ced3a7eb4f54d16605228ef1911773bc28bb1f4c86f0c2aa0b34ba7f040b010b1ca0a67938f24d135d10d451d1782f2a4997973da3c4ef38100a861878b9";
    };
    {
      params = { curve = ECC_P521; point_compression = false };
      ecdh_d1 = "02";
      ecdh_x1 = "433c219024277e7e682fcb288148c282747403279b1ccc06352c6e5505d769be97b3b204da6ef55507aa104a3a35c5af41cf2fa364d60fd967f43e3933ba6d783d";
      ecdh_y1 = "f4bb8cc7f86db26700a7f3eceeeed3f0b5c6b5107c4da97740ab21a29906c42dbbb3e377de9f251f6b93937fa99a3248f4eafcbe95edc0f4f71be356d661f41b02";
      ecdh_d2 = "0d";
      ecdh_x2 = "7e3e98f984c396ad9cd7865d2b4924861a93f736cde1b4c2384eedd2beaf5b866132c45908e03c996a3550a5e79ab88ee94bec3b00ab38eff81887848d32fbcda7";
      ecdh_y2 = "0108ee58eb6d781feda91a1926daa3ed5a08ced50a386d5421c69c7a67ae5c1e212ac1bd5d5838bc763f26dfdd351cbfbbc36199eaaf9117e9f7291a01fb022a71c9";
      secret  = "017b61bd55cc8b533222d9857bb0c04dcd1331a02407e9a8576609bc2cbefa11d6aef686bfc27593b717007102d5dd038ed768dd29c10c73e41060d9e9a7e8c685c6";
    };
    {
      params = { curve = ECC_P521; point_compression = false };
      ecdh_d1 = "01e0309972ba5bfcef9359bd57b9f81fdc42b68f542840b6ba86777cc88a5f0212ebbe9dbd127b6d002dc04693a08244c19a70731684c8ae2f69d55aa31e0f033694";
      ecdh_x1 = "7bc64851ef5f5479ec693d013bc4dd49eed41f83e1c541bab31b36d2a718936d2679911f12fd0ad791aefed4fe90ace3c701064c3b13a8fe549481bf6bbcd50f34";
      ecdh_y1 = "74ae39f8a6365647bb60a0fc6d604e03b3f825c628e7bd2b1624b65f7c1efb5475856f25db987d5050dfa3e3add57219e4dbc313d5ddd31a0bebc2329b5dcdbe13";
      ecdh_d2 = "0129aaa6e62ffeb1607fac1a89d89e30c6cea1cd5950713e61fdea5a020dbb378eb237ed4deba74db459a14bd30c1a59ff6f34ae81a2c9d267b6eae28e5250790298";
      ecdh_x2 = "a5bf1a56bd4ba362f4c993d0be3e730279fe6adcf9b1eec0d80bd90c42d704fb682ddec394e5da9282d065c5b2c765d1db3dd059d4c786d1c0af39cb0fd81885c2";
      ecdh_y2 = "01203e82a4ca77298dcd49830413b4b415736ab4db03a61d23b711cda53193b1066704242c0c8061bf2444c3ed400476b831c8d298f2ac171b807a863953635f3c1b";
      secret  = "011b919b14eaeea1b8881cede6bd16ff04e4ec45a943f1b5e3852fce2e83e997398af3b233b796cff023a0430d69bb2eda1d475c806e9b7f716cf08e8daefb31a6b2";
    }
  ]

  let test v =
    let alice =
      {
        ec_params = v.params;
        ec_point  =
          {
            ecx = Bytes.bytes_of_hex v.ecdh_x1;
            ecy = Bytes.bytes_of_hex v.ecdh_y1
          };
        ec_priv   = Some (Bytes.bytes_of_hex v.ecdh_d1)
      } in
    let bob =
     {
        ec_params = v.params;
        ec_point  =
          {
            ecx = Bytes.bytes_of_hex v.ecdh_x2;
            ecy = Bytes.bytes_of_hex v.ecdh_y2
          };
        ec_priv   = Some (Bytes.bytes_of_hex v.ecdh_d2)
      } in
    let secret1 = ecdh_agreement alice bob.ec_point in
    let secret2 = ecdh_agreement bob alice.ec_point in
    ec_is_on_curve alice.ec_params alice.ec_point &&
    ec_is_on_curve bob.ec_params bob.ec_point &&  
    Bytes.hex_of_bytes secret1 = v.secret &&
    string_of_bytes secret1 = string_of_bytes secret2

  let simple_test () =
    let params = { curve = ECC_P256; point_compression = false } in
    let alice = ec_gen_key params in
    let bob = ec_gen_key params in
    let shared1 = ecdh_agreement alice bob.ec_point in
    let shared2 = ecdh_agreement bob alice.ec_point in
    string_of_bytes shared1 = string_of_bytes shared2
end

module TestCertAndSign = struct
  let test mode () =
    match load_chain ("pki/" ^ mode ^ "/certificates/" ^ mode ^ ".cert.mitls.org.crt") with
    | None -> false
    | Some chain ->
       if validate_chain chain true (Some (mode ^ ".cert.mitls.org"))
         ("pki/" ^ mode ^ "/certificates/ca.crt") then
        begin
        match load_key ("pki/" ^ mode ^ "/certificates/" ^ mode ^ ".cert.mitls.org.key") with
        | None -> (Printf.printf "Coudln't load key\n"; false)
        | Some k ->
          let tbs = bytes_of_string "hello world" in
          let sigv = maybe_hash_and_sign k (Some SHA256) tbs in
          match get_key_from_cert (List.hd chain) with
          | Some k -> verify_signature k (Some SHA256) tbs sigv
          | None -> false
        end
      else (Printf.printf "Invalid chain\n"; false)
end

module TestCert = struct
   let test () =
      let c1 = "MIIEvzCCA6egAwIBAgISESGKFzM2mw6wNuApCakhJ3f2MA0GCSqGSIb3DQEBCwUAMEwxCzAJBgNVBAYTAkJFMRkwFwYDVQQKExBHbG9iYWxTaWduIG52LXNhMSIwIAYDVQQDExlBbHBoYVNTTCBDQSAtIFNIQTI1NiAtIEcyMB4XDTE1MDIxMTE1MzUxOFoXDTE3MDYwMjE3Mjc1NVowNTEhMB8GA1UECxMYRG9tYWluIENvbnRyb2wgVmFsaWRhdGVkMRAwDgYDVQQDFAcqLmh0LnZjMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAqN7uyVXDSmnwpRIL7c5MKjFUbcRdQ4w4EA90vPRHAusmFmlrpY2pNrxzgXaTYaxrx7Rs3BUHBfr84hc4yrmpXsFd2+BuznR1l0KLM5tkY7gS5H5L53r0tPSrh+qrZrHq9S6zm4oEOFJ6zaslYUCdfW0mpIlG3YBROEkllE924fW+jdnk9G76nPSL/1/WPiQ67m4cZ+fwQt5FeFs/mu1016DqokZL24ymtan+bfSQx++wtSIdulSAPNeq7NL3l9sXgOvjcoRJVq8WsePjrS5D8A9iD3gKn1SWZgAg76RTpzbq40B2m2tXyxKFnCkW1UddIFBuxyjcOm8NTbZ9i/HBgwIDAQABo4IBsDCCAawwDgYDVR0PAQH/BAQDAgWgMEkGA1UdIARCMEAwPgYGZ4EMAQIBMDQwMgYIKwYBBQUHAgEWJmh0dHBzOi8vd3d3Lmdsb2JhbHNpZ24uY29tL3JlcG9zaXRvcnkvMBkGA1UdEQQSMBCCByouaHQudmOCBWh0LnZjMAkGA1UdEwQCMAAwHQYDVR0lBBYwFAYIKwYBBQUHAwEGCCsGAQUFBwMCMD4GA1UdHwQ3MDUwM6AxoC+GLWh0dHA6Ly9jcmwyLmFscGhhc3NsLmNvbS9ncy9nc2FscGhhc2hhMmcyLmNybDCBiQYIKwYBBQUHAQEEfTB7MEIGCCsGAQUFBzAChjZodHRwOi8vc2VjdXJlMi5hbHBoYXNzbC5jb20vY2FjZXJ0L2dzYWxwaGFzaGEyZzJyMS5jcnQwNQYIKwYBBQUHMAGGKWh0dHA6Ly9vY3NwMi5nbG9iYWxzaWduLmNvbS9nc2FscGhhc2hhMmcyMB0GA1UdDgQWBBRqqrlNqjRoJa7dF/eY/jOsXrWjTjAfBgNVHSMEGDAWgBT1zdU8CFD5ak86t5faVoPmadJo9zANBgkqhkiG9w0BAQsFAAOCAQEAwt6NjuZuIykka+jiK+t4mXar7yO3SwcM6bFIyBOVIJ7rdTIMtbPUrg8PJK3Xzs+iF8vQvmWRLCmSCvcR2OZpjBQXMFMt0UpIQUa+q02YUCasX4viFsD+GlWf+TuC3kJo9Gu+ZWfrMI21WrLjFGYVeTHyQ0TTJj6fHEirfMkG8Kl3+CRz3d13tfkWYein4OUmRxfPq0YB/pDmxKPaGc7dD6NAss4u3o0XkCpXUlMa3XCNMNVRPMsww7Vmlavupc3GEjs/zNi8Vls+CkgD7ADEvRPNgepDLY0LQZCmEFmF/7VSLldWncb6rSVlFxlksE/MF9X2aX97z8WJOqmWLnqESQ" in
     let c2 = "MIIETTCCAzWgAwIBAgILBAAAAAABRE7wNjEwDQYJKoZIhvcNAQELBQAwVzELMAkGA1UEBhMCQkUxGTAXBgNVBAoTEEdsb2JhbFNpZ24gbnYtc2ExEDAOBgNVBAsTB1Jvb3QgQ0ExGzAZBgNVBAMTEkdsb2JhbFNpZ24gUm9vdCBDQTAeFw0xNDAyMjAxMDAwMDBaFw0yNDAyMjAxMDAwMDBaMEwxCzAJBgNVBAYTAkJFMRkwFwYDVQQKExBHbG9iYWxTaWduIG52LXNhMSIwIAYDVQQDExlBbHBoYVNTTCBDQSAtIFNIQTI1NiAtIEcyMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA2gHs5OxzYPt+j2q3xhfjkmQy1KwA2aIPue3ua4qGypJn2XTXXUcCPI9A1p5tFM3D2ik5pw8FCmiiZhoexLKLdljlq10dj0CzOYvvHoN9ItDjqQAu7FPPYhmFRChMwCfLew7sEGQAEKQFzKByvkFsMVtI5LHsuSPrVU3QfWJKpbSlpFmFxSWRpv6mCZ8GEG2PgQxkQF5zAJrgLmWYVBAAcJjI4e00X9icxw3A1iNZRfz+VXqG7pRgIvGu0eZVRvaZxRsIdF+ssGSEj4k4HKGnkCFPAm694GFn1PhChw8K98kEbSqpL+9Cpd/do1PbmB6B+Zpye1reTz5/olig4hetZwIDAQABo4IBIzCCAR8wDgYDVR0PAQH/BAQDAgEGMBIGA1UdEwEB/wQIMAYBAf8CAQAwHQYDVR0OBBYEFPXN1TwIUPlqTzq3l9pWg+Zp0mj3MEUGA1UdIAQ+MDwwOgYEVR0gADAyMDAGCCsGAQUFBwIBFiRodHRwczovL3d3dy5hbHBoYXNzbC5jb20vcmVwb3NpdG9yeS8wMwYDVR0fBCwwKjAooCagJIYiaHR0cDovL2NybC5nbG9iYWxzaWduLm5ldC9yb290LmNybDA9BggrBgEFBQcBAQQxMC8wLQYIKwYBBQUHMAGGIWh0dHA6Ly9vY3NwLmdsb2JhbHNpZ24uY29tL3Jvb3RyMTAfBgNVHSMEGDAWgBRge2YaRQ2XyolQL30EzTSo//z9SzANBgkqhkiG9w0BAQsFAAOCAQEAYEBoFkfnFo3bXKFWKsv0XJuwHqJL9csCP/gLofKnQtS3TOvjZoDzJUN4LhsXVgdSGMvRqOzm+3M+pGKMgLTSxRJzo9P6Aji+Yz2EuJnB8br3n8NA0VgYU8Fi3a8YQn80TsVD1XGwMADH45CuP1eGl87qDBKOInDjZqdUfy4oy9RU0LMeYmcI+Sfhy+NmuCQbiWqJRGXy2UzSWByMTsCVodTvZy84IOgu/5ZR8LrYPZJwR2UcnnNytGAMXOLRc3bgr07i5TelRS+KIz6HxzDmMTh89N1SyvNTBCVXVmaU6Avu5gMUTu79bZRknl7OedSyps9AsUSoPocZXun4IRZZUw" in
     let tob x = bytes_of_string (BatBase64.str_decode x) in
     let chain = List.map tob [c1; c2] in
     validate_chain chain true (Some "test.ht.vc") "pki/CAFile.pem"
end                 

module TestECDSACert = struct
  let test () =
    let c1 = "MIIB0jCCAXmgAwIBAgIJAOJIzXwrhyTmMAoGCCqGSM49BAMCMEYxCzAJBgNVBAYTAlVLMRMwEQYDVQQIDApTb21lLVN0YXRlMQ4wDAYDVQQKDAVtaVRMUzESMBAGA1UEAwwJbWl0bHMub3JnMB4XDTE2MDUxMzE1MjMxOVoXDTI2MDUxMTE1MjMxOVowRjELMAkGA1UEBhMCVUsxEzARBgNVBAgMClNvbWUtU3RhdGUxDjAMBgNVBAoMBW1pVExTMRIwEAYDVQQDDAltaXRscy5vcmcwWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAAQSir7rBJZ/wpSd+cbUawAi5mp/aKl8O7t52tgD/N+qC29BfXvTGLycOJKb3KH4RUbuQ/PtFm297Vl45CB4Zrzao1AwTjAdBgNVHQ4EFgQUZUVvmKM0O9/eXV+PxjWUeAit5z4wHwYDVR0jBBgwFoAUZUVvmKM0O9/eXV+PxjWUeAit5z4wDAYDVR0TBAUwAwEB/zAKBggqhkjOPQQDAgNHADBEAiAtElNiXA+iEw9Y01MKRBCVsIXeSqLlOrQTN7n4DSehnQIgdohQ8vTeqmUegyft7IPS2mL3QKqqXYMUkOFC+RTGJwQ" in
    let sigv = "MEYCIQD6yaMocDqSb5xnzDa8J+ZYQqS98DIERubsToyn48GYEwIhAOphlNSOvshuV/gjPC6fWuQj8gJuW3859lpSnFLH16tE" in
    let c1b = bytes_of_string (BatBase64.str_decode c1) in
    let sigvb = bytes_of_string (BatBase64.str_decode sigv) in
    let tbs = bytes_of_string "Hello World\n" in
    match get_key_from_cert c1b with
    | Some k -> verify_signature k (Some SHA256) tbs sigvb
    | None -> false
end

module TestDSACert = struct
  let test () =
    let c1 = "MIIFIjCCBOKgAwIBAgIJAOIxk5jud+Z/MAkGByqGSM44BAMwVTELMAkGA1UEBhMCVUsxDjAMBgNVBAgTBUNhbWJzMRIwEAYDVQQHEwlDYW1icmlkZ2UxDjAMBgNVBAoTBW1pVExTMRIwEAYDVQQDEwltaXRscy5vcmcwHhcNMTYwNTExMTY1ODI5WhcNMTYwNjEwMTY1ODI5WjBVMQswCQYDVQQGEwJVSzEOMAwGA1UECBMFQ2FtYnMxEjAQBgNVBAcTCUNhbWJyaWRnZTEOMAwGA1UEChMFbWlUTFMxEjAQBgNVBAMTCW1pdGxzLm9yZzCCAzowggItBgcqhkjOOAQBMIICIAKCAQEAl1tfhKIN2z96xAwWvQVBZVa/QL0vtp44FmqyS0VFyeNQSViYzkT4IprmdVtWb+8kB1zs27O5fA5+Js/s5/0lkoXCp4WQF9CwOv9Bw2GvGZutssx3VbMj4qfYgEIyjwU9ETdRW3yB890wlM/usTDSoNBbn6MRtduYKFGeOrHgBptKerSHwN94rSUO80Ech5qpdUNiZbRgZVBSO2h+KVjw6ZdCpw8XwQfnyI7YooWOrY/RmYA9DtzRtEYuwuHIJUB+sswsNdws/LcZ1rZZCpO+Y+oW50BfQVBrg/nbi78SAtplrLns5HrYyqiQARX4ub6f6zAdHQrvFI0xlPDo+ujXNwIVAK1v2Jw93EA9Hjb7nnaNb528y8itAoIBAFQ3xrCZAD1BkeNzSN0ehZiaakUH5YPpo5zMTfqhWs5jtbf6xe0sn20NVkcEuWYFvgiW91iDA0KOS11l093CstdoVOHaGpUnogSZ1OneOY/CwHWKcNM5JlQbom62G85nL9qWu7WqWSNMwQSRV/BKimmFfbWI3i+65dG7DUtVZMIV8lJ4jJWW9blZUrChuTl6miOdih14+NmFgxom/XNYbhmZz8i68oQCc/PfcPGbt6ayx4MCYMtxWS/FrsvaAVVYT0CLqtdz7rOt+WN+UWOd5B7GFu6nmOaz52qVSYtow+LI9TosAnij60osYoAd1Hrd5kOogjmChfQsFXlX4HOK7joDggEFAAKCAQAh2EQMmXVwgiBaGiuDkMAJFPvYaqqd/d86wYaqJTKknUqoEoOkKtpn9msfWwINF0sXTElTL1bD+pm9Ql6lATqHmO1pYcoSWMR1L7JI7zcMc2gU3jpd0lbUDUx5SboAeEih83k4lSnNEftFdNMQ973YmL3ReFmk3GZzNkzHHeHzo9HnDXFLxCeFM9S7F8gv1Vx9CSgAebQNKv1SHfhuSGp9srknKyZBcGncjtDQAy00fvGpWeCdrlgNoBFVz4EigH5Z15F+4AFkuUJ8fIPAifYWInjOWk0d0PG9IIXN/n7snXtGId+szZdCUnhSUGmC6o/wTJWvZMG9BGtQpPZJ9BCdo4G4MIG1MB0GA1UdDgQWBBSxG0nDZJobYSuj4kj+McWPALyOBzCBhQYDVR0jBH4wfIAUsRtJw2SaG2Ero+JI/jHFjwC8jgehWaRXMFUxCzAJBgNVBAYTAlVLMQ4wDAYDVQQIEwVDYW1iczESMBAGA1UEBxMJQ2FtYnJpZGdlMQ4wDAYDVQQKEwVtaVRMUzESMBAGA1UEAxMJbWl0bHMub3JnggkA4jGTmO535n8wDAYDVR0TBAUwAwEB/zAJBgcqhkjOOAQDAy8AMCwCFASsPMokAXZSGO3ZiYCMic7HC62EAhRVamZaepsT3rAkZSpxMfAE0qN98w" in
    let sigv = "MC4CFQCWRmyYmzTe9CN4SSgIEpWUPY/6JwIVAJ1STjc12/9L8K341SKw1r6Cai3g" in
    let c1b = bytes_of_string (BatBase64.str_decode c1) in
    let sigvb = bytes_of_string (BatBase64.str_decode sigv) in
    let tbs = bytes_of_string "Hello World\n" in
    match get_key_from_cert c1b with
    | Some k -> verify_signature k (Some SHA256) tbs sigvb
    | None -> false
end

module TestRSACert = struct
  let test () =
    let c1 = "MIIEvzCCA6egAwIBAgISESGKFzM2mw6wNuApCakhJ3f2MA0GCSqGSIb3DQEBCwUAMEwxCzAJBgNVBAYTAkJFMRkwFwYDVQQKExBHbG9iYWxTaWduIG52LXNhMSIwIAYDVQQDExlBbHBoYVNTTCBDQSAtIFNIQTI1NiAtIEcyMB4XDTE1MDIxMTE1MzUxOFoXDTE3MDYwMjE3Mjc1NVowNTEhMB8GA1UECxMYRG9tYWluIENvbnRyb2wgVmFsaWRhdGVkMRAwDgYDVQQDFAcqLmh0LnZjMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAqN7uyVXDSmnwpRIL7c5MKjFUbcRdQ4w4EA90vPRHAusmFmlrpY2pNrxzgXaTYaxrx7Rs3BUHBfr84hc4yrmpXsFd2+BuznR1l0KLM5tkY7gS5H5L53r0tPSrh+qrZrHq9S6zm4oEOFJ6zaslYUCdfW0mpIlG3YBROEkllE924fW+jdnk9G76nPSL/1/WPiQ67m4cZ+fwQt5FeFs/mu1016DqokZL24ymtan+bfSQx++wtSIdulSAPNeq7NL3l9sXgOvjcoRJVq8WsePjrS5D8A9iD3gKn1SWZgAg76RTpzbq40B2m2tXyxKFnCkW1UddIFBuxyjcOm8NTbZ9i/HBgwIDAQABo4IBsDCCAawwDgYDVR0PAQH/BAQDAgWgMEkGA1UdIARCMEAwPgYGZ4EMAQIBMDQwMgYIKwYBBQUHAgEWJmh0dHBzOi8vd3d3Lmdsb2JhbHNpZ24uY29tL3JlcG9zaXRvcnkvMBkGA1UdEQQSMBCCByouaHQudmOCBWh0LnZjMAkGA1UdEwQCMAAwHQYDVR0lBBYwFAYIKwYBBQUHAwEGCCsGAQUFBwMCMD4GA1UdHwQ3MDUwM6AxoC+GLWh0dHA6Ly9jcmwyLmFscGhhc3NsLmNvbS9ncy9nc2FscGhhc2hhMmcyLmNybDCBiQYIKwYBBQUHAQEEfTB7MEIGCCsGAQUFBzAChjZodHRwOi8vc2VjdXJlMi5hbHBoYXNzbC5jb20vY2FjZXJ0L2dzYWxwaGFzaGEyZzJyMS5jcnQwNQYIKwYBBQUHMAGGKWh0dHA6Ly9vY3NwMi5nbG9iYWxzaWduLmNvbS9nc2FscGhhc2hhMmcyMB0GA1UdDgQWBBRqqrlNqjRoJa7dF/eY/jOsXrWjTjAfBgNVHSMEGDAWgBT1zdU8CFD5ak86t5faVoPmadJo9zANBgkqhkiG9w0BAQsFAAOCAQEAwt6NjuZuIykka+jiK+t4mXar7yO3SwcM6bFIyBOVIJ7rdTIMtbPUrg8PJK3Xzs+iF8vQvmWRLCmSCvcR2OZpjBQXMFMt0UpIQUa+q02YUCasX4viFsD+GlWf+TuC3kJo9Gu+ZWfrMI21WrLjFGYVeTHyQ0TTJj6fHEirfMkG8Kl3+CRz3d13tfkWYein4OUmRxfPq0YB/pDmxKPaGc7dD6NAss4u3o0XkCpXUlMa3XCNMNVRPMsww7Vmlavupc3GEjs/zNi8Vls+CkgD7ADEvRPNgepDLY0LQZCmEFmF/7VSLldWncb6rSVlFxlksE/MF9X2aX97z8WJOqmWLnqESQ" in
    let sigv = "LBjksyC2OtMz5BafvCpwgTK5EVU7ICFpVqovKyg7K4hlpVEOkq7+gZNzhfgrdj2G59eV3N9pk7gGmElayFf7g9P6CwnMa4KUOae0dSLmRmPwjwNnfmrFa/CjrEiNTq/rINxJYZMACDJaadFcFj+mbIGd2/34fogPYdzqgfpolhJC1W6yMjkqfEvCesl+q1An+DrJjPurRgdB4oJXq0sJ+ykDCxiUHxaghvrVFjySSP/3YfDYVRD2nShyEUULMm+6DUdHL8safSSo4yj7zu3qdCM2ri/ypjeGOIWDVD9VLNTOPwOKW7Y2PAz3ZSjfUaa5rGDDZPmn3vLEeAnz+yhLCg" in
    let c1b = bytes_of_string (BatBase64.str_decode c1) in
    let sigvb = bytes_of_string (BatBase64.str_decode sigv) in
    let tbs = bytes_of_string "Hello World\n" in
    match get_key_from_cert c1b with
    | Some k -> verify_signature k (Some SHA256) tbs sigvb
    | None -> false
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
  TestBlock.(run_test "Block ciphers" test_vectors print_test_vector test);
  TestAead.(run_test "AEAD" test_vectors print_test_vector test);
  TestHmac.(run_test "HMAC" test_cases print_test_case test);
  TestHash.(run_test "HASH" tests print_test test);
  TestHashUpdate.(run_test "HASHUPDATE" tests print_test test);
  TestEcc.(run_test "ECC" tests print_test test);
  TestRsa.(run_test "RSA" tests print_test roundtrip);
  TestDsa.(run_test "DSA" tests print_test check);
  TestEcdsa.(run_test "ECDSA" tests print_test check);
  TestDhke.(run_test "DHE" test_vectors print_test_vector test);
  simple_test "DHE key exchange" TestDhke.simple_test;
  TestEcdhke.(run_test "ECDHE" test_vectors print_test_vector test);
  simple_test "ECDH key exchange" TestEcdhke.simple_test;
  simple_test "Certificate chain verify" TestCert.test;
  simple_test "Certificate ECDSA certs and signatures" (TestCertAndSign.test "ecdsa");
  simple_test "Certificate DSA   certs and signatures" (TestCertAndSign.test "dsa");
  simple_test "Certificate RSA   certs and signatures" (TestCertAndSign.test "rsa");
  simple_test "Certificate signature verify (ECDSA)  " TestECDSACert.test;
  simple_test "Certificate signature verify (DSA)    " TestDSACert.test;
  simple_test "Certificate signature verify (RSA)    " TestRSACert.test;
  ()
