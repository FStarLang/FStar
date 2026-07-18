module Bug3991

open FStar.Tactics
open FStar.Tactics.Typeclasses

class mytc (#a:Type0) (s:a) = {  e : unit; }

#set-options "--warn_error -328" // imprecise inner let rec

instance mytc_let_rec () : mytc (let rec f x = x in ()) = { e = () }
