(* NOTE: This example MUST HAVE an .fsti because of --use_extracted_interfaces *)
module MiniParseExample
open MiniParse.Impl.Base

type test = | TA | TB | TC | TD

noextract
val p : parser test

val q : parser32 p

// this is necessary to typecheck the projectors of somme, which generate SMT queries
val bidon: unit

noeq
type somme = | U of FStar.UInt8.t | V | W | X

noextract
val somme_p : parser somme

// val somme_p32: parser32 somme_p
