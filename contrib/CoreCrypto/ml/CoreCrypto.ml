module Option = Platform.Option

(** Bytes, as modeled on the F* side, are a record with various fields in it
 * (see [Platform]). *)
type bytes = Platform.Bytes.bytes

(** C bindings, however, will want most of the time to have a chunk of memory
 * containing data, that is, actual bytes. For this, we use the type [string],
 * also called [cbytes] in [Platform.Bytes]. *)
let string_of_bytes b = Platform.Bytes.get_cbytes b
let bytes_of_string s = Platform.Bytes.abytes s


(* -------------------------------------------------------------------- *)

(** Hashing *)

(** We support a subset of the algorithms from OpenSSL. Note: when changing
 * these types, please only append new constructors *at the end* (otherwise, C
 * functions such as [RSADigest_val] will most likely break). *)
type hash_alg = MD5 | SHA1 | SHA224 | SHA256 | SHA384 | SHA512
type sig_alg = RSASIG | DSA | ECDSA | RSAPSS
type block_cipher = AES_128_CBC | AES_256_CBC | TDES_EDE_CBC
type aead_cipher = AES_128_GCM | AES_256_GCM
type stream_cipher = RC4_128
type rsa_padding = Pad_none | Pad_PKCS1

let string_of_hash_alg = function
  | MD5 -> "MD5"
  | SHA1 -> "SHA1"
  | SHA224 -> "SHA224"
  | SHA256 -> "SHA256"
  | SHA384 -> "SHA384"
  | SHA512 -> "SHA512"

let blockSize = function
  | TDES_EDE_CBC -> 8
  | AES_128_CBC  -> 16
  | AES_256_CBC  -> 16

let aeadKeySize = function
  | AES_128_GCM -> 16
  | AES_256_GCM -> 32

let aeadRealIVSize = function
  | AES_128_GCM -> 12
  | AES_256_GCM -> 12

let aeadTagSize = function
  | AES_128_GCM -> 16
  | AES_256_GCM -> 16

let hashSize = function
  | MD5    -> 16
  | SHA1   -> 20
  | SHA224 -> 28
  | SHA256 -> 32
  | SHA384 -> 48
  | SHA512 -> 64

type md
type md_ctx
external ocaml_EVP_MD_md5 : unit -> md = "ocaml_EVP_MD_md5"
external ocaml_EVP_MD_sha1  : unit -> md = "ocaml_EVP_MD_sha1"
external ocaml_EVP_MD_sha224 : unit -> md = "ocaml_EVP_MD_sha224"
external ocaml_EVP_MD_sha256 : unit -> md = "ocaml_EVP_MD_sha256"
external ocaml_EVP_MD_sha384 : unit -> md = "ocaml_EVP_MD_sha384"
external ocaml_EVP_MD_sha512 : unit -> md = "ocaml_EVP_MD_sha512"
external ocaml_EVP_MD_block_size : md -> int = "ocaml_EVP_MD_block_size"
external ocaml_EVP_MD_size : md -> int = "ocaml_EVP_MD_size"
external ocaml_EVP_MD_CTX_create : md -> md_ctx = "ocaml_EVP_MD_CTX_create"
external ocaml_EVP_MD_CTX_fini   : md_ctx -> unit = "ocaml_EVP_MD_CTX_fini"
external ocaml_EVP_MD_CTX_update : md_ctx -> string -> unit = "ocaml_EVP_MD_CTX_update"
external ocaml_EVP_MD_CTX_final  : md_ctx -> string = "ocaml_EVP_MD_CTX_final"

let md_of_hash_alg h = match h with
  | MD5 -> ocaml_EVP_MD_md5()
  | SHA1 -> ocaml_EVP_MD_sha1()
  | SHA224 -> ocaml_EVP_MD_sha224()
  | SHA256 -> ocaml_EVP_MD_sha256()
  | SHA384 -> ocaml_EVP_MD_sha384()
  | SHA512 -> ocaml_EVP_MD_sha512()

let hash (h:hash_alg) (b:bytes) =
  let md = md_of_hash_alg h in
  let ctx = ocaml_EVP_MD_CTX_create(md) in
  ocaml_EVP_MD_CTX_update ctx (string_of_bytes b);
  let h = ocaml_EVP_MD_CTX_final(ctx) in
  ocaml_EVP_MD_CTX_fini(ctx);
  bytes_of_string h

(* -------------------------------------------------------------------- *)
(* HMAC *)
external ocaml_EVP_HMAC : md -> key:string -> data:string -> string = "ocaml_EVP_HMAC"

let hmac (h:hash_alg) (k:bytes) (d:bytes) =
  let md = md_of_hash_alg h in
  let h = ocaml_EVP_HMAC md (string_of_bytes k) (string_of_bytes d) in
  bytes_of_string h

(* -------------------------------------------------------------------- *)
type cipher
type cipher_ctx
type cipher_stream = cipher_ctx

external ocaml_EVP_CIPHER_des_ede3   : unit -> cipher = "ocaml_EVP_CIPHER_des_ede3"
external ocaml_EVP_CIPHER_des_ede3_cbc : unit -> cipher = "ocaml_EVP_CIPHER_des_ede3_cbc"
external ocaml_EVP_CIPHER_aes_128_ecb  : unit -> cipher = "ocaml_EVP_CIPHER_aes_128_ecb"
external ocaml_EVP_CIPHER_aes_128_cbc  : unit -> cipher = "ocaml_EVP_CIPHER_aes_128_cbc"
external ocaml_EVP_CIPHER_aes_256_ecb  : unit -> cipher = "ocaml_EVP_CIPHER_aes_256_ecb"
external ocaml_EVP_CIPHER_aes_256_cbc  : unit -> cipher = "ocaml_EVP_CIPHER_aes_256_cbc"

external ocaml_EVP_CIPHER_aes_128_gcm  : unit -> cipher = "ocaml_EVP_CIPHER_aes_128_gcm"
external ocaml_EVP_CIPHER_aes_256_gcm  : unit -> cipher = "ocaml_EVP_CIPHER_aes_256_gcm"

external ocaml_EVP_CIPHER_rc4 : unit -> cipher = "ocaml_EVP_CIPHER_rc4"

external ocaml_EVP_CIPHER_CTX_create : cipher -> bool -> cipher_ctx = "ocaml_EVP_CIPHER_CTX_create"
external ocaml_EVP_CIPHER_CTX_fini   : cipher_ctx -> unit = "ocaml_EVP_CIPHER_CTX_fini"

external ocaml_EVP_CIPHER_CTX_block_size : cipher_ctx -> int = "ocaml_EVP_CIPHER_CTX_block_size"

external ocaml_EVP_CIPHER_CTX_key_length : cipher_ctx -> int = "ocaml_EVP_CIPHER_CTX_key_length"
external ocaml_EVP_CIPHER_CTX_iv_length  : cipher_ctx -> int = "ocaml_EVP_CIPHER_CTX_iv_length"

external ocaml_EVP_CIPHER_CTX_set_key : cipher_ctx -> string -> unit = "ocaml_EVP_CIPHER_CTX_set_key"
external ocaml_EVP_CIPHER_CTX_set_iv  : cipher_ctx -> string -> unit = "ocaml_EVP_CIPHER_CTX_set_iv"
external ocaml_EVP_CIPHER_CTX_set_additional_data : cipher_ctx -> string -> unit = "ocaml_EVP_CIPHER_CTX_set_additional_data"
external ocaml_EVP_CIPHER_CTX_process : cipher_ctx -> string -> string = "ocaml_EVP_CIPHER_CTX_process"

external ocaml_EVP_CIPHER_CTX_set_tag : cipher_ctx -> string -> unit = "ocaml_EVP_CIPHER_CTX_set_tag"
external ocaml_EVP_CIPHER_CTX_get_tag : cipher_ctx -> string = "ocaml_EVP_CIPHER_CTX_get_tag"

let cipher_of_block_cipher (c:block_cipher) = match c with
  | AES_128_CBC -> ocaml_EVP_CIPHER_aes_128_cbc()
  | AES_256_CBC -> ocaml_EVP_CIPHER_aes_256_cbc()
  | TDES_EDE_CBC -> ocaml_EVP_CIPHER_des_ede3_cbc()

let cipher_of_stream_cipher (c:stream_cipher) = match c with
  | RC4_128 -> ocaml_EVP_CIPHER_rc4()

let cipher_of_aead_cipher (c:aead_cipher) = match c with
  | AES_128_GCM ->
      ocaml_EVP_CIPHER_aes_128_gcm()
  | AES_256_GCM ->
      ocaml_EVP_CIPHER_aes_256_gcm()

let block_encrypt (c:block_cipher) (k:bytes) (iv:bytes) (d:bytes) =
  let c = cipher_of_block_cipher c in
  let ctx = ocaml_EVP_CIPHER_CTX_create c true in
  ocaml_EVP_CIPHER_CTX_set_key ctx (string_of_bytes k);
  ocaml_EVP_CIPHER_CTX_set_iv ctx (string_of_bytes iv);
  let e = ocaml_EVP_CIPHER_CTX_process ctx (string_of_bytes d) in
  ocaml_EVP_CIPHER_CTX_fini ctx;
  bytes_of_string e

let block_decrypt (c:block_cipher) (k:bytes) (iv:bytes) (d:bytes) =
  let c = cipher_of_block_cipher c in
  let ctx = ocaml_EVP_CIPHER_CTX_create c false in
  ocaml_EVP_CIPHER_CTX_set_key ctx (string_of_bytes k);
  ocaml_EVP_CIPHER_CTX_set_iv ctx (string_of_bytes iv);
  let e = ocaml_EVP_CIPHER_CTX_process ctx (string_of_bytes d) in
  ocaml_EVP_CIPHER_CTX_fini ctx;
  bytes_of_string e

let aead_encrypt (c:aead_cipher) (k:bytes) (iv:bytes) (ad:bytes) (d:bytes) =
  let c = cipher_of_aead_cipher c in
  let ctx = ocaml_EVP_CIPHER_CTX_create c true in
  ocaml_EVP_CIPHER_CTX_set_key ctx (string_of_bytes k);
  ocaml_EVP_CIPHER_CTX_set_iv ctx (string_of_bytes iv);
  ocaml_EVP_CIPHER_CTX_set_additional_data ctx (string_of_bytes ad);
  let e = ocaml_EVP_CIPHER_CTX_process ctx (string_of_bytes d) in
  let t = ocaml_EVP_CIPHER_CTX_get_tag ctx in
  ocaml_EVP_CIPHER_CTX_fini ctx;
  Platform.Bytes.op_At_Bar (bytes_of_string e) (bytes_of_string t)

let aead_decrypt (c:aead_cipher) (k:bytes) (iv:bytes) (ad:bytes) (d:bytes) =
  let c = cipher_of_aead_cipher c in
  let ctx = ocaml_EVP_CIPHER_CTX_create c false in
  let d,t = Platform.Bytes.split d ((Platform.Bytes.length d) - 16) in
  ocaml_EVP_CIPHER_CTX_set_key ctx (string_of_bytes k);
  ocaml_EVP_CIPHER_CTX_set_iv ctx (string_of_bytes iv);
  ocaml_EVP_CIPHER_CTX_set_additional_data ctx (string_of_bytes ad);
  let e = ocaml_EVP_CIPHER_CTX_process ctx (string_of_bytes d) in
  ocaml_EVP_CIPHER_CTX_set_tag ctx (string_of_bytes t);
  ocaml_EVP_CIPHER_CTX_fini ctx;
  Some (bytes_of_string e)

let stream_encryptor (c:stream_cipher) (k:bytes) =
  let c = cipher_of_stream_cipher c in
  let ctx = ocaml_EVP_CIPHER_CTX_create c true in
  ocaml_EVP_CIPHER_CTX_set_key ctx (string_of_bytes k);
  ctx

let stream_decryptor (c:stream_cipher) (k:bytes) =
  let c = cipher_of_stream_cipher c in
  let ctx = ocaml_EVP_CIPHER_CTX_create c false in
  ocaml_EVP_CIPHER_CTX_set_key ctx (string_of_bytes k);
  ctx

let stream_process (ctx:cipher_ctx) (d:bytes) =
  let e = ocaml_EVP_CIPHER_CTX_process ctx (string_of_bytes d) in
  bytes_of_string e

let stream_fini (ctx:cipher_ctx) =
  ocaml_EVP_CIPHER_CTX_fini ctx

(* -------------------------------------------------------------------- *)
external ocaml_rand_status : unit -> bool = "ocaml_rand_status"
external ocaml_rand_bytes  : int -> string = "ocaml_rand_bytes"

let random i =
    if (i < 0) then invalid_arg "input to random must be non-negative"
    else if (not (ocaml_rand_status())) then failwith "random number generator not ready"
    else bytes_of_string (ocaml_rand_bytes i)

(* -------------------------------------------------------------------- *)
type rsa

type rsa_key = {
  rsa_mod     : bytes;
  rsa_pub_exp : bytes;
  rsa_prv_exp : bytes option;
}

external ocaml_rsa_new : unit -> rsa = "ocaml_rsa_new"
external ocaml_rsa_fini   : rsa -> unit = "ocaml_rsa_fini"

external ocaml_rsa_gen_key : size:int -> exp:int -> string * string * string = "ocaml_rsa_gen_key"
external ocaml_rsa_set_key : rsa -> rsa_key -> unit = "ocaml_rsa_set_key"

external ocaml_rsa_encrypt : rsa -> prv:bool -> rsa_padding -> string -> string = "ocaml_rsa_encrypt"
external ocaml_rsa_decrypt : rsa -> prv:bool -> rsa_padding -> string -> string = "ocaml_rsa_decrypt"

external ocaml_rsa_sign : rsa -> hash_alg option -> string -> string = "ocaml_rsa_sign"
external ocaml_rsa_verify : rsa -> hash_alg option -> data:string -> sig_:string -> bool = "ocaml_rsa_verify"

let rsa_gen_key (i:int) =
  let rsa_mod, rsa_pub_exp, rsa_prv_exp = ocaml_rsa_gen_key i 65537 in {
    rsa_mod = bytes_of_string rsa_mod;
    rsa_pub_exp = bytes_of_string rsa_pub_exp;
    rsa_prv_exp = Some (bytes_of_string rsa_prv_exp)
  }

let rsa_encrypt (pk:rsa_key) (p:rsa_padding) (d:bytes) =
  let r = ocaml_rsa_new() in
  ocaml_rsa_set_key r pk;
  let e = ocaml_rsa_encrypt r false p (string_of_bytes d) in
  ocaml_rsa_fini r;
  bytes_of_string e

let rsa_decrypt (sk:rsa_key) (p:rsa_padding) (e:bytes) =
  let r = ocaml_rsa_new() in
  ocaml_rsa_set_key r sk;
  let d = ocaml_rsa_decrypt r true p (string_of_bytes e) in
  ocaml_rsa_fini r;
  Some (bytes_of_string d)

(* Note: if [h = None], then [t] is understood to be an SHA1+MD5 "SSL
 * signature", meaning its length must be 36 bytes exactly. *)
let rsa_sign (h:hash_alg option) (sk:rsa_key) (t:bytes) =
  let r = ocaml_rsa_new() in
  ocaml_rsa_set_key r sk;
  let d = match h with None -> t | Some a -> hash a t in
  let s = ocaml_rsa_sign r h (string_of_bytes d) in
  ocaml_rsa_fini r;
  bytes_of_string s

let rsa_verify (h:hash_alg option) (sk:rsa_key) (data:bytes) (sign:bytes) =
  let rsa = ocaml_rsa_new() in
  ocaml_rsa_set_key rsa sk;
  let data = match h with None -> data | Some h -> hash h data in
  let ret = ocaml_rsa_verify rsa h (string_of_bytes data) (string_of_bytes sign) in
  ocaml_rsa_fini rsa;
  ret

(* -------------------------------------------------------------------- *)
type dsa

type dsa_params = {
  dsa_p : bytes;
  dsa_q : bytes;
  dsa_g : bytes;
}
type dsa_key = {
  dsa_params  : dsa_params;
  dsa_public  : bytes;
  dsa_private : bytes option;
}

external ocaml_dsa_new : unit -> dsa = "ocaml_dsa_new"
external ocaml_dsa_fini   : dsa -> unit = "ocaml_dsa_fini"

external ocaml_dsa_gen_params : int -> string * string * string = "ocaml_dsa_gen_params"
external ocaml_dsa_gen_key : dsa_params -> string * string = "ocaml_dsa_gen_key"

external ocaml_dsa_set_key : dsa -> dsa_key -> unit = "ocaml_dsa_set_key"

external ocaml_dsa_sign : dsa -> string -> string = "ocaml_dsa_sign"
external ocaml_dsa_verify : dsa -> data:string -> sig_:string -> bool = "ocaml_dsa_verify"

let dsa_gen_key (n:int) =
  let p, q, g = ocaml_dsa_gen_params n in
  let dp = {
    dsa_p = bytes_of_string p;
    dsa_q = bytes_of_string q;
    dsa_g = bytes_of_string g
  } in
  let dsa_public, dsa_private = ocaml_dsa_gen_key dp in
  {
    dsa_params = dp;
    dsa_public = bytes_of_string dsa_public;
    dsa_private = Some (bytes_of_string dsa_private)
  }

let dsa_sign (k:dsa_key) (d:bytes) =
  let dsa = ocaml_dsa_new() in
  ocaml_dsa_set_key dsa k;
  let s = ocaml_dsa_sign dsa (string_of_bytes d) in
  ocaml_dsa_fini dsa;
  bytes_of_string s

let dsa_verify (k:dsa_key) (d:bytes) (s:bytes) =
  let dsa = ocaml_dsa_new() in
  ocaml_dsa_set_key dsa k;
  let b = ocaml_dsa_verify dsa (string_of_bytes d) (string_of_bytes s) in
  ocaml_dsa_fini dsa;
  b

(* -------------------------------------------------------------------- *)
type dh

type dh_params = {
  dh_p : bytes;
  dh_g : bytes;
  dh_q : bytes option;
  safe_prime : bool;
}

type dh_key = {
  dh_params  : dh_params;
  dh_public  : bytes;
  dh_private : bytes option;
}

external ocaml_dh_new : unit -> dh = "ocaml_dh_new"
external ocaml_dh_fini   : dh -> unit = "ocaml_dh_fini"

external ocaml_dh_gen_params : size:int -> gen:int -> string * string = "ocaml_dh_gen_params"
external ocaml_dh_params_of_string : string -> string * string = "ocaml_dh_params_of_string"

external ocaml_dh_gen_key : dh_params -> string * string = "ocaml_dh_gen_key"
external ocaml_dh_set_key : dh -> dh_key -> unit = "ocaml_dh_set_key"

external ocaml_dh_compute : dh -> string -> string = "ocaml_dh_compute"

let dh_gen_params (size:int) =
  let p, g = ocaml_dh_gen_params size 2 in
  {
    dh_p = bytes_of_string p;
    dh_g = bytes_of_string g;
    dh_q = None;
    safe_prime = true
  }

let dh_gen_key (dh:dh_params)=
  let pub, priv = ocaml_dh_gen_key dh in
  {
    dh_params = dh;
    dh_public = bytes_of_string pub;
    dh_private = Some (bytes_of_string priv)
  }

let dh_agreement (mypriv:dh_key) (opub:bytes) =
  let dh = ocaml_dh_new() in
  ocaml_dh_set_key dh mypriv;
  let a = ocaml_dh_compute dh (string_of_bytes opub) in
  ocaml_dh_fini dh;
  bytes_of_string a

(* -------------------------------------------------------------------- *)

type ec_curve =
     | ECC_P256
     | ECC_P384
     | ECC_P521
type ec_params = { curve: ec_curve; point_compression: bool; }
type ec_point = { ecx : bytes; ecy : bytes; }

type ec_key = {
     ec_params : ec_params;
     ec_point : ec_point; (* a.k.a. the public key *)
     ec_priv : bytes option;
}

(* Types prefixed with [ssl_] are wrappers around raw C pointers and are not
 * intended for outside use. The bindings for the various EC_* functions adopt a
 * style where the OCaml side does as much as possible, and the C side does as
 * little as possible. This means that constructing structures such as EC_KEY
 * and EC_GROUP is done by binding various EC_KEY_set* functions.
 *
 * Note: these bindings seem very inefficient, because we're re-creating the
 * EC_*$ data structures every time. We would be better off having them stashed
 * somewhere inside the record (and export the record as private in the
 * interface so that clients can't misuse it). *)

type ssl_ec_method

external ocaml_gfp_simple_method: unit -> ssl_ec_method = "ocaml_GFp_simple_method"
external ocaml_gfp_nist_method: unit -> ssl_ec_method = "ocaml_GFp_nist_method"
external ocaml_gfp_mont_method: unit -> ssl_ec_method = "ocaml_GFp_mont_method"


type ssl_ec_group

external ocaml_ec_group_new_by_curve_name: string -> ssl_ec_group =
  "ocaml_ec_group_new_by_curve_name"
external ocaml_ec_group_set_point_conversion_form: ssl_ec_group -> bool -> unit =
  "ocaml_ec_group_set_point_conversion_form"

let ssl_name_of_curve = function
  | ECC_P256 -> "prime256v1"
  | ECC_P384 -> "secp384r1"
  | ECC_P521 -> "secp521r1"

let ec_group_new curve =
  ocaml_ec_group_new_by_curve_name (ssl_name_of_curve curve)

let ssl_group_of_params params =
  let g = ec_group_new params.curve in
  ocaml_ec_group_set_point_conversion_form g params.point_compression;
  g


type ssl_ec_point

external ocaml_ec_point_new: ssl_ec_group -> ssl_ec_point = "ocaml_ec_point_new"
external ocaml_ec_point_set_affine_coordinates_GFp:
  ssl_ec_group -> ssl_ec_point -> string -> string -> unit =
  "ocaml_ec_point_set_affine_coordinates_GFp"
external ocaml_ec_point_get_affine_coordinates_GFp:
  ssl_ec_group -> ssl_ec_point -> string * string =
  "ocaml_ec_point_get_affine_coordinates_GFp"
external ocaml_ec_point_is_on_curve: ssl_ec_group -> ssl_ec_point -> bool =
  "ocaml_ec_point_is_on_curve"

let ssl_point_of_point params { ecx; ecy } =
  let g = ssl_group_of_params params in
  let p = ocaml_ec_point_new g in
  ocaml_ec_point_set_affine_coordinates_GFp g p (string_of_bytes ecx) (string_of_bytes ecy);
  p

let ec_is_on_curve params point =
  let g = ssl_group_of_params params in
  let p = ssl_point_of_point params point in
  ocaml_ec_point_is_on_curve g p

let ec_point_serialize ecp =
  failwith "Not implemented"


type ssl_ec_key

external ocaml_ec_key_new_by_curve_name: string -> ssl_ec_key =
  "ocaml_ec_key_new_by_curve_name"
external ocaml_ec_key_generate: ssl_ec_key -> unit =
  "ocaml_ec_key_generate"
external ocaml_ec_key_get0_public_key: ssl_ec_key -> ssl_ec_point =
  "ocaml_ec_key_get0_public_key"
external ocaml_ec_key_get0_private_key: ssl_ec_key -> string =
  "ocaml_ec_key_get0_private_key"
external ocaml_ec_key_set_public_key: ssl_ec_key -> ssl_ec_point -> unit =
  "ocaml_ec_key_set_public_key"
external ocaml_ec_key_set_private_key: ssl_ec_key -> string -> unit =
  "ocaml_ec_key_set_private_key"
external ocaml_ecdh_agreement: ssl_ec_key -> ssl_ec_group -> ssl_ec_point -> string =
  "ocaml_ecdh_agreement"
external ocaml_ecdsa_sign: ssl_ec_key -> string -> string =
  "ocaml_ecdsa_sign"
external ocaml_ecdsa_verify: ssl_ec_key -> string -> string -> bool =
  "ocaml_ecdsa_verify"

let ec_key_new curve =
  ocaml_ec_key_new_by_curve_name (ssl_name_of_curve curve)

let ssl_key_of_key key =
  let ssl_key = ec_key_new key.ec_params.curve in
  ocaml_ec_key_set_public_key ssl_key (ssl_point_of_point key.ec_params key.ec_point);
  if key.ec_priv <> None then
    ocaml_ec_key_set_private_key ssl_key (string_of_bytes (Option.must key.ec_priv));
  ssl_key

let ec_gen_key (params: ec_params): ec_key =
  let k = ec_key_new params.curve in
  let g = ssl_group_of_params params in
  ocaml_ec_key_generate k;
  let pub_point = ocaml_ec_key_get0_public_key k in
  let ecx, ecy = ocaml_ec_point_get_affine_coordinates_GFp g pub_point in
  let priv = ocaml_ec_key_get0_private_key k in {
    ec_params = params;
    ec_point = { ecx = bytes_of_string ecx; ecy = bytes_of_string ecy };
    ec_priv = Some (bytes_of_string priv)
  }

let ecdh_agreement (key: ec_key) (point: ec_point) =
  let ssl_key = ssl_key_of_key key in
  let ssl_point = ssl_point_of_point key.ec_params point in
  let ssl_group = ssl_group_of_params key.ec_params in
  bytes_of_string (ocaml_ecdh_agreement ssl_key ssl_group ssl_point)

let ecdsa_sign hash_alg key input =
  let input = match hash_alg with
    | Some hash_alg -> hash hash_alg input
    | None -> input
  in
  let key = ssl_key_of_key key in
  let output = ocaml_ecdsa_sign key (string_of_bytes input) in
  bytes_of_string output

let ecdsa_verify hash_alg key input signature =
  let input = match hash_alg with
    | Some hash_alg -> hash hash_alg input
    | None -> input
  in
  let key = ssl_key_of_key key in
  ocaml_ecdsa_verify key (string_of_bytes input) (string_of_bytes signature)


(* -------------------------------------------------------------------------- *)

external ocaml_err_load_crypto_strings: unit -> unit = "ocaml_err_load_crypto_strings"
external ocaml_rand_poll: unit -> unit = "ocaml_rand_poll"

let _ =
  ocaml_rand_poll ();
  ocaml_err_load_crypto_strings ()
