module Secret.Core

open Web.Origin 
open AuxiliaryFunctions
open FStar.List.Tot


type origins = list origin

val trustedOrigins : origins 

val mem : origin -> origins -> GTot bool

val allOrigins : origins

val noOrigin : origins

val someOrigins : list origin -> origins


type globalState

val stateInv : globalState -> Tot bool

type state = g:globalState{stateInv g} (* global log containing all requests sent and event-occurrences *)

val dishonest : state -> origin -> Tot bool


type secret

val create : origins -> string -> Tot secret (* creates a new secret using the value and the origins *)

val retrieve : secret -> Tot string (* retrieve a string from the secret - only at origins that have the secret *)

val readers : secret -> Tot origins (* returns the list of origins *)

val createdFor : secret -> origin -> Tot bool (* returns true if the secret has been created for the origin *)

val eq_secret : s:secret -> s':secret -> Tot (b:bool{b = true ==> readers s = readers s'})

val isReader : st:state -> s:secret -> o:origin -> Tot (b:bool{b = true ==> createdFor s o \/ (exists a. createdFor s a /\ dishonest st a)})


type field

type httpRequest 

val isUserRequest : state -> httpRequest -> Tot bool

val isOriginRequest : state -> httpRequest -> origin -> Tot bool

type validRequest (st:state) (b:origin) (s:origin) = h:httpRequest{dishonest st b \/ isUserRequest st h \/ (exists o. isOriginRequest st h o)}

val getSecret : #st:state -> #b:origin -> #s:origin -> r:validRequest st b s -> f:field -> 
		Tot (v:(option secret){match v with | None -> true | Some x -> isReader st x b /\ isReader st x s /\ (forall s'. isOriginRequest st r s' ==> isReader st x s')})


val createReader : s:secret -> o:origins -> t:string -> Lemma (requires (eq_secret (create o t) s)) (ensures (readers s = o))

val readerCreator : s:secret -> o:origin -> Lemma (requires (createdFor s o)) (ensures (List.mem o (readers s)))

val readerLemma : st:state -> s:secret -> o:origin -> Lemma (requires (isReader st s o)) (ensures (List.mem o (readers s))) 

val readerAttacker : st:state -> s:secret -> o:origin -> a:origin -> Lemma (requires (isReader st s o /\ dishonest st o)) (ensures (isReader st s a)) 

(* noeq type request = *)
(* | URequest : b:oorigin -> s:torigin -> c:secret{isReader c b /\ isReader c s} -> request *)
(* | JSRequest : b:oorigin -> s:torigin -> s':torigin -> c:secret{isReader c b /\ isReader c s /\ isReader c s'} -> request *)
(* | RedirectRequest : b:oorigin -> s:torigin -> s':torigin -> c:secret{isReader c b /\ isReader c s /\ isReader c s'} -> request  *)

noeq type response =
| Resp : resptype:string -> red:(option origin) -> s:(option (list secret)) -> response


