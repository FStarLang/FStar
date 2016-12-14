module Crypto.Config

type aesImpl =
  | SpartanAES
  | HaclAES

inline_for_extraction let aes_implementation = HaclAES
