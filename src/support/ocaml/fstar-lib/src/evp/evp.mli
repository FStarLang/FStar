(* -------------------------------------------------------------------- *)
module MD : sig
  type md
  type md_ctx

  val md5    : unit -> md
  val sha1   : unit -> md
  val sha256 : unit -> md
  val sha384 : unit -> md
  val sha512 : unit -> md

  val block_size : md -> int
  val size       : md -> int
  val create     : md -> md_ctx

  val fini   : md_ctx -> unit
  val update : md_ctx -> string -> unit
  val final  : md_ctx -> string
end

(* -------------------------------------------------------------------- *)
module CIPHER : sig
  type cipher
  type cipher_ctx

  val des_ede3     : unit -> cipher
  val des_ede3_cbc : unit -> cipher
  val aes_128_ecb  : unit -> cipher
  val aes_128_cbc  : unit -> cipher
  val aes_256_ecb  : unit -> cipher
  val aes_256_cbc  : unit -> cipher
  val rc4          : unit -> cipher

  val create : cipher -> bool -> cipher_ctx
  val fini   : cipher_ctx -> unit

  val block_size : cipher_ctx -> int
  val key_length : cipher_ctx -> int
  val iv_length  : cipher_ctx -> int
  val set_key    : cipher_ctx -> string -> unit
  val set_iv     : cipher_ctx -> string -> unit

  val process : cipher_ctx -> string -> string
end

(* -------------------------------------------------------------------- *)
module HMAC : sig
  val hmac : MD.md -> key:string -> data:string -> string
end

(* -------------------------------------------------------------------- *)
module RANDOM : sig
  val status : unit -> bool
  val bytes  : int -> string
end

(* -------------------------------------------------------------------- *)
module RSA : sig
  type rsa
  type padding = PD_None | PD_PKCS1

  type key = {
    k_mod : string;
    k_pub_exp : string;
    k_prv_exp : string option;
  }

  type digest = MD5 | SHA1 | SHA256 | SHA384

  val create : unit -> rsa
  val fini   : rsa -> unit
  val genkey : size:int -> exp:int -> key
  val setkey : rsa -> key -> unit

  val encrypt : rsa -> prv:bool -> padding -> string -> string
  val decrypt : rsa -> prv:bool -> padding -> string -> string

  val sign   : rsa -> digest -> string -> string
  val verify : rsa -> digest -> data:string -> sig_:string -> bool
end

(* -------------------------------------------------------------------- *)
module DSA : sig
  type params = { p : string; q : string; g : string; }
  type key = {
    k_params : params;
    k_public : string;
    k_private : string option;
  }

  type dsa

  val create : unit -> dsa
  val fini   : dsa -> unit

  val genparams : int -> params
  val genkey    : params -> key

  val setkey : dsa -> key -> unit
  val sign   : dsa -> string -> string
  val verify : dsa -> data:string -> sig_:string -> bool
end

(* -------------------------------------------------------------------- *)
module DH : sig
  type params = { p : string; g : string; }
  type key = {
    k_params : params;
    k_public : string;
    k_private : string option;
  }

  type dh

  val create : unit -> dh
  val fini   : dh -> unit

  val genparams : size:int -> gen:int -> params
  val genkey    : params -> key

  val params_of_string : string -> params

  val setkey  : dh -> key -> unit
  val compute : dh -> string -> string
end
