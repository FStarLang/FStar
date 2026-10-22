module CustardEmbTest
open FStar.Tactics.V2

(* Both definitions are irreducible, so only the native steps the two loaded
   plugins registered can reduce them; [paint]'s embeds and unembeds
   [color] with the embedding CustardEmbA generated. *)
let _ = assert (CustardEmbB.paint (CustardEmbA.next CustardEmbA.Green) == CustardEmbA.Blue 10)
          by (norm [primops]; trefl ())
