(* NOTE: This example MUST HAVE an .fsti because of --use_extracted_interfaces *)
module MiniParseExample
open MiniParse.Impl.Base

type test = | TA | TB | TC | TD

noextract
val p : parser test

val q : parser32 p
