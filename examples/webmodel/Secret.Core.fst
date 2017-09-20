module Secret.Core

open FStar.String
open Web.Origin
open ML.ExternalFunctions
open AuxiliaryFunctions
open Secret.SecString

module List = FStar.List.Tot

(* Secret Types *)
type secretVal =
| Secret : s:secLevel -> v:secString s -> secretVal

type secType = 
| SecString : s:secretVal -> secType
| SecToken : s:secretVal -> w:list torigin -> msg:pubString -> secType

val genSecret : l:secLevel -> Tot (s:secretVal{Secret?.s s = l})
let genSecret l = Secret l (classify #PublicVal (randomVal 32) l) (* Generate random-string of length 32 *)

val getSecret : #l:secLevel -> s:secretVal{Secret?.s s = l} -> Tot (secString l)
let getSecret #l s = (Secret?.v s)

assume val authMsg : secretVal -> w:list torigin -> msg:pubString -> Tot (st:secType{SecToken? st})

assume val verifyMsg : st:secType{SecToken? st} -> secretVal -> Tot bool

