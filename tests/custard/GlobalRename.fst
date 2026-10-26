module GlobalRename

open FStar.Attributes
module U32 = FStar.UInt32

[@@rename_let "ApiPair"]
noeq type pair = { lo: U32.t; hi: U32.t }

[@@rename_let "ApiMake"]
let make (lo:U32.t) (hi:U32.t) : pair = { lo = lo; hi = hi }

[@@rename_let "api_global"]
let stored : U32.t = GlobalRenameIface.step 4ul

[@@rename_let "mixedCaseLimit"; CMacro]
let limit : U32.t = 7ul

[@@rename_let "privateWorker"]
private let helper (x:U32.t) : U32.t = U32.add_mod x 1ul

[@@rename_let "ExternalStep"]
assume val external_step : U32.t -> Tot U32.t

[@@rename_let "AgreedStep"; custard_extern "AgreedStep"]
assume val agreed_step : U32.t -> Tot U32.t

[@@rename_let "CheckAPI"]
assume val check_api : unit -> Tot U32.t

[@@rename_let "ApiAdd"]
let add (p:pair) : U32.t =
  U32.add_mod (helper p.lo) (U32.add_mod p.hi (U32.add_mod stored limit))

[@@rename_let "CountDown"]
let rec countdown (#a:Type) (x:a) (n:U32.t) : Tot a (decreases (U32.v n)) =
  if U32.gt n 0ul then countdown x (U32.sub n 1ul) else x

let twice (f:U32.t -> U32.t) (x:U32.t) : U32.t = f (f x)

let shadow (privateWorker:U32.t) : U32.t =
  U32.add_mod (helper privateWorker) privateWorker

[@@rename_let "run_test"]
let main () : FStar.All.ML FStar.Int32.t =
  if U32.eq (check_api ()) 0ul &&
     U32.eq (external_step 40ul) 41ul &&
     U32.eq (agreed_step 41ul) 42ul &&
     U32.eq (twice helper 40ul) 42ul &&
     U32.eq (shadow 20ul) 41ul &&
     U32.eq (countdown 42ul 3ul) 42ul
  then 0l else 1l
