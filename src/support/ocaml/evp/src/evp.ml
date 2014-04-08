(* -------------------------------------------------------------------- *)
module MD = struct
  type md
  type md_ctx

  external md5    : unit -> md = "ocaml_EVP_MD_md5"
  external sha1   : unit -> md = "ocaml_EVP_MD_sha1"
  external sha256 : unit -> md = "ocaml_EVP_MD_sha256"
  external sha384 : unit -> md = "ocaml_EVP_MD_sha384"
  external sha512 : unit -> md = "ocaml_EVP_MD_sha512"

  external block_size : md -> int = "ocaml_EVP_MD_block_size"
  external size : md -> int = "ocaml_EVP_MD_size"

  external create : md -> md_ctx = "ocaml_EVP_MD_CTX_create"
  external fini   : md_ctx -> unit = "ocaml_EVP_MD_CTX_fini"

  external update : md_ctx -> string -> unit = "ocaml_EVP_MD_CTX_update"
  external final  : md_ctx -> string = "ocaml_EVP_MD_CTX_final"
end

(* -------------------------------------------------------------------- *)
module CIPHER = struct
  type cipher
  type cipher_ctx

  external des_ede3     : unit -> cipher = "ocaml_EVP_CIPHER_des_ede3"
  external des_ede3_cbc : unit -> cipher = "ocaml_EVP_CIPHER_des_ede3_cbc"
  external aes_128_ecb  : unit -> cipher = "ocaml_EVP_CIPHER_aes_128_ecb"
  external aes_128_cbc  : unit -> cipher = "ocaml_EVP_CIPHER_aes_128_cbc"
  external aes_256_ecb  : unit -> cipher = "ocaml_EVP_CIPHER_aes_256_ecb"
  external aes_256_cbc  : unit -> cipher = "ocaml_EVP_CIPHER_aes_256_cbc"

  external rc4 : unit -> cipher = "ocaml_EVP_CIPHER_rc4"

  external create : cipher -> bool -> cipher_ctx = "ocaml_EVP_CIPHER_CTX_create"
  external fini   : cipher_ctx -> unit = "ocaml_EVP_CIPHER_CTX_fini"

  external block_size : cipher_ctx -> int = "ocaml_EVP_CIPHER_CTX_block_size"

  external key_length : cipher_ctx -> int = "ocaml_EVP_CIPHER_CTX_key_length"
  external iv_length  : cipher_ctx -> int = "ocaml_EVP_CIPHER_CTX_iv_length"

  external set_key : cipher_ctx -> string -> unit = "ocaml_EVP_CIPHER_CTX_set_key"
  external set_iv  : cipher_ctx -> string -> unit = "ocaml_EVP_CIPHER_CTX_set_iv"

  external process : cipher_ctx -> string -> string = "ocaml_EVP_CIPHER_CTX_process"
end

(* -------------------------------------------------------------------- *)
module HMAC = struct
  external hmac : MD.md -> key:string -> data:string -> string = "ocaml_EVP_HMAC"
end

(* -------------------------------------------------------------------- *)
module RANDOM = struct
  external status : unit -> bool = "ocaml_rand_status"
  external bytes  : int -> string = "ocaml_rand_bytes"
end

(* -------------------------------------------------------------------- *)
module RSA = struct
  type rsa

  type padding = PD_None | PD_PKCS1

  type key = {
    k_mod     : string;
    k_pub_exp : string;
    k_prv_exp : string option;
  }

  type digest = MD5 | SHA1 | SHA256 | SHA384

  external create : unit -> rsa = "ocaml_rsa_new"
  external fini   : rsa -> unit = "ocaml_rsa_fini"

  external genkey : size:int -> exp:int -> key = "ocaml_rsa_gen_key"
  external setkey : rsa -> key -> unit = "ocaml_rsa_set_key"

  external encrypt : rsa -> prv:bool -> padding -> string -> string = "ocaml_rsa_encrypt"
  external decrypt : rsa -> prv:bool -> padding -> string -> string = "ocaml_rsa_decrypt"

  external sign : rsa -> digest -> string -> string = "ocaml_rsa_sign"
  external verify : rsa -> digest -> data:string -> sig_:string -> bool = "ocaml_rsa_verify"
end

(* -------------------------------------------------------------------- *)
module DSA = struct
  type params = {
    p : string;
    q : string;
    g : string;
  }

  type key = {
    k_params  : params;
    k_public  : string;
    k_private : string option;
  }

  type dsa

  external create : unit -> dsa = "ocaml_dsa_new"
  external fini   : dsa -> unit = "ocaml_dsa_fini"

  external genparams : int -> params = "ocaml_dsa_gen_params"
  external genkey : params -> key = "ocaml_dsa_gen_key"

  external setkey : dsa -> key -> unit = "ocaml_dsa_set_key"

  external sign : dsa -> string -> string = "ocaml_dsa_sign"
  external verify : dsa -> data:string -> sig_:string -> bool = "ocaml_dsa_verify"
end

(* -------------------------------------------------------------------- *)
module DH = struct
  type params = {
    p : string;
    g : string;
  }

  type key = {
    k_params  : params;
    k_public  : string;
    k_private : string option;
  }

  type dh

  external create : unit -> dh = "ocaml_dh_new"
  external fini   : dh -> unit = "ocaml_dh_fini"

  external genparams : size:int -> gen:int -> params = "ocaml_dh_gen_params"
  external genkey : params -> key = "ocaml_dh_gen_key"

  external params_of_string : string -> params = "ocaml_dh_params_of_string"

  external setkey : dh -> key -> unit = "ocaml_dh_set_key"

  external compute : dh -> string -> string = "ocaml_dh_compute"
end
