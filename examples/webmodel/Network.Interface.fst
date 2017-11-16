(*
  Defines secret and trusted origins to be used by the OAuth protocol and exposes a set of APIs from Browser.Model.Interface
*)
module Network.Interface

open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.StringFunctions
open Browser.Model.Interface
open ML.ExternalFunctions

module List = FStar.List.Tot

(* the secrets are indexed by a list of origins --- state, authcode, accesstoken, client_secret, password *)
type secretVal =
| Secret : s:secLevel -> v:secString s -> secretVal

(* default responses *)
let defResponse o d = ActResponse PublicVal ({respori=o;respdest=d;resptype="default";respcode=200;respurl=[];resphead=[];respbody=(emptyString PublicVal);resptrail=[];respHTTPS="none";respCSP=[];respCORS=[];resploc=None;respRedSec=PublicVal})
let defErrResponse o d = ActResponse PublicVal ({respori=o;respdest=d;resptype="default";respcode=404;respurl=[];resphead=[];respbody=(emptyString PublicVal);resptrail=[];respHTTPS="none";respCSP=[];respCORS=[];resploc=None;respRedSec=PublicVal})

val mk_secretval : #l:secLevel -> secString l -> Tot secretVal
let mk_secretval #l s = (Secret l s)

val mk_svheaderval : secretVal -> Tot headervalue
let mk_svheaderval s = Headervalue (Secret?.s s) (Secret?.v s)

val genSecret : l:secLevel -> Tot (s:secretVal{Secret?.s s = l})
let genSecret l = Secret l (classify #PublicVal (randomVal 32) l) (* Generate random-string of length 32 *)

val getSecret : #l:secLevel -> s:secretVal{Secret?.s s = l} -> Tot (secString l)
let getSecret #l s = (Secret?.v s)

(* Server-side checks for equality of two strings *)
val s_equal: #l:secLevel -> #l':secLevel -> s:secString l -> t:secString l' -> Tot (b:bool{b = true ==> content s = content t})
let s_equal #l #l' s t = 
  match l, l' with
  | PublicVal, PublicVal -> s = t
  | SecretVal ol, PublicVal -> let (AString #ol v1) = s in v1 = t
  | PublicVal, SecretVal ol -> let (AString #ol v2) = t in s = v2
  | SecretVal ol, SecretVal ol' ->
      let (AString #ol v1) = s in
      let (AString #ol' v2) = t in
      v1 = v2

val compareSecret : s:secretVal -> t:secretVal -> Tot (b:bool)
let compareSecret s t = s_equal (Secret?.v s) (Secret?.v t)

val checkEP : browserRequest -> string -> Tot bool
let checkEP r s = 
  let ruri = (firstElement (BRequest?.rf r).requrl) in
  match getPathVal #(URI?.usl ruri) (ruri) with
  | [] -> false
  | h::_ -> eqString h s


(* SERVER REQUESTS *)
type srequest (s:secLevel) = {
  sreqm:reqMethod;
  srequrl:list uri;
  sreqhead:header;
  sreqo:torigin;
  sreqtype:requesttype;
  sreqnonce:pubString;
  sreqmode:mode;
  sreqbody:secString s;
}

(* construct a valid request to be sent on the network *)
val isValidServerRequest : #s:secLevel -> rf:srequest s -> Tot bool
let isValidServerRequest #s rf = 
  if (emptyList rf.srequrl) then false
  else 
    let u = (firstElement rf.srequrl) in 
    match s with
    | PublicVal -> (URI?.usl u = s)
    | SecretVal ol -> (URI?.usl u = s) && (isHeaderVisible rf.sreqhead ol)
    
val validRequestLemma : #s:secLevel -> rf:(srequest s){isValidServerRequest #s rf /\ checkHeaderSecLevel rf.sreqhead} -> 
			Lemma (requires (True)) (ensures (s = URI?.usl (firstElement rf.srequrl))) [SMTPat (isValidServerRequest #s rf)]
let validRequestLemma #s rf = ()

type serverRequest = 
| SRequest : (srsl:secLevel) -> srf:(srequest srsl){isValidServerRequest srf /\ checkHeaderSecLevel srf.sreqhead} -> serverRequest


(* any request - browser or server *)
type anyRequest =
| BrowserRequest : browserRequest -> anyRequest
| ServerRequest : serverRequest -> anyRequest 


(* Server functions *)
val checkSEP : serverRequest -> string -> Tot bool
let checkSEP r s = 
  let ruri = (firstElement (SRequest?.srf r).srequrl) in
  match getPathVal #(URI?.usl ruri) (ruri) with
  | [] -> false
  | h::_ -> eqString h s

private val parseReqHeader : h:header -> hf:headerfield -> Tot (option headervalue)
let rec parseReqHeader h hf = 
  match h with
  | [] -> None
  | (f,v)::tl -> if (f=hf) then (Some v)
	       else (parseReqHeader tl hf)

val s_getReqHeaderValue : serverRequest -> headerfield -> Tot (list string)
let s_getReqHeaderValue req h =
  match (parseReqHeader (SRequest?.srf req).sreqhead h) with
  | None -> []
  | Some v -> let s = (if (h = "Cookie") then parseCookieHeaderVal #(Headervalue?.hvs v) v else parseHeaderVal #(Headervalue?.hvs v) v) in
	     declassify_list s
  
val s_getRequestURI : #s:secLevel -> req:serverRequest{(URI?.usl (firstElement (SRequest?.srf req).srequrl)) = s} -> Tot (c_uri s)
let s_getRequestURI #s req = u_curi (firstElement (SRequest?.srf req).srequrl)

val s_getRequestOrigin : serverRequest -> Tot origin
let s_getRequestOrigin req = (SRequest?.srf req).sreqo

val s_getReqURISecLevel : serverRequest  -> Tot (l:secLevel)
let s_getReqURISecLevel req = (URI?.usl (firstElement (SRequest?.srf req).srequrl))

val s_getRequestBody : #s:secLevel -> req:serverRequest{SRequest?.srsl req = s} -> Tot (secString s)
let s_getRequestBody #s req = (SRequest?.srf req).sreqbody

(* returns whether the redirect response (307/308) is valid or not -- 
   assume that all redirect responses with code 307/308 should have public requests *)
private val isValidRedirectResp : req:serverRequest -> resp:actResponse -> GTot bool
let isValidRedirectResp req resp = 
  if isRedirectResponse (ActResponse?.ar resp) then 
    (checkLocationURISecLevel resp) &&
    (canReclHeader (redirectHeaders (SRequest?.srf req).sreqhead) (ActResponse?.ar resp).respRedSec) &&
    (if isRedResponse (ActResponse?.ar resp) then canReclassify (SRequest?.srf req).sreqbody (ActResponse?.ar resp).respRedSec else true)
  else (ActResponse?.ar resp).resploc = None (* if it is not a redirect response, the resploc field should not be populated *)

private val isValidLocResp : req:serverRequest -> resp:actResponse -> GTot bool
let isValidLocResp req resp = 
  match (ActResponse?.ar resp).resploc with 
  | None -> true
  | Some Failure -> true
  | Some (URL u) -> (* (uriSecLevel (URL u)) && *) (checkRespSecLevel resp) && (getLocationURI resp = Some (URL u))
		   
(* A response to request is valid ---
   Check if the redirect response is valid and can be reclassified appropriately and
   Check if the resploc of response is valid (populated by browser using the location header)
*)
val sRequestResponseValid : serverRequest -> actResponse -> GTot bool
let sRequestResponseValid req resp = (isValidRedirectResp req resp) && (isValidLocResp req resp)

private val isValidRedReclURI : req:serverRequest -> resp:actResponse -> GTot bool
let isValidRedReclURI req resp = (canReclHeader (redirectHeaders (SRequest?.srf req).sreqhead) (ActResponse?.ar resp).respRedSec)

(* If a response to request is valid then headers can be reclassified *)
val validSRedLemma : req:serverRequest -> resp:actResponse -> 
		    Lemma (requires (sRequestResponseValid req resp /\ isRedirectResponse (ActResponse?.ar resp)))
			  (ensures (isValidRedReclURI req resp))
		    [SMTPat (sRequestResponseValid req resp)]
let validSRedLemma req resp = ()

val reqRespSLocLemma : req:serverRequest -> resp:actResponse -> 
		      Lemma (requires (sRequestResponseValid req resp /\ isRedirectResponse (ActResponse?.ar resp))) 
			    (ensures (match (ActResponse?.ar resp).resploc with | None -> true | Some Failure -> true 
				     | Some (URL u) -> (canReclHeader (redirectHeaders (SRequest?.srf req).sreqhead) (URI?.usl u))))
		      [SMTPat (sRequestResponseValid req resp)]
let reqRespSLocLemma req resp = ()

(* write a proper processing of the server request's response *)
val processSResponse : anyRequest -> actResponse -> Tot result
let processSResponse s r = Success ("Did nothing")


(* TRUSTED ORIGINS *)
val trustedOrigins : list torigin

let ipori = TOrigin "https" ["login";"ip";"com"] (Some 443) None
let rpori = TOrigin "https" ["rp";"com"] (Some 443) None
let badipori = TOrigin "https" ["login";"badip";"com"] (Some 443) None

let trustedOrigins = [ipori;rpori]

(* Is the uri from a list of origins specified *)
private val isTrusted : list torigin -> uri -> Tot bool
let rec isTrusted t u = 
  match t with
  | [] -> false
  | h::tl -> (isSameOriginUO u h) || (isTrusted tl u)

(* Is the window from a trustedOrigin? *)
val isTrustedOriginWindow : cowindow -> Tot bool
let isTrustedOriginWindow cw =
  let wurl = getWinURI cw in
  isTrusted trustedOrigins wurl 


(* retrieve the value from the querystring (also cookie name value) that corresponds to the given string str *)
val getVal : #l:secLevel -> list (secString l * secString l) -> secString l -> Tot (secString l)
let rec getVal #l qs str = 
  match qs with
  | [] -> emptyString l
  | (f,s)::tl -> if (f=str) then (s) else getVal tl str

(* retrieve the value from the querystring (also cookie name value) that corresponds to the given string str *)
val getQSVal : #l:secLevel -> querystring l -> string -> Tot (secString l)
let getQSVal #l qs str = getVal #l qs (classify #PublicVal str l)


(* Leak values which the adversary can access - declassify the value to the attacker *)
val leakValue : headervalue -> Tot string
let leakValue hv = 
  match (Headervalue?.hvs hv) with 
  | PublicVal -> s_getHeaderValueString #PublicVal hv
  | SecretVal lo -> 
      if (List.for_all (fun x -> List.mem x trustedOrigins) lo) then "" 
      else declassify (s_getHeaderValueString #(SecretVal lo) hv)

(* Coerce values to an attacker defined index *)
val coerceValue : string -> l:(list torigin){not (emptyList l)} -> Tot headervalue
let coerceValue s l = Headervalue (SecretVal l) (classify #PublicVal s (SecretVal l))

private val getWinList : list cowindow -> Tot (list cowindow)
let rec getWinList l = 
  match l with
  | [] -> []
  | hd::tl -> List.append (getWinList (getFrames hd)) (getWinList tl)

private val getWindows : browser -> Tot (list cowindow)
let getWindows b = getWinList b.windows
  



(* ***** Browser Exposed Functions ***** *)
val getAllWindows : b:browser -> Tot (list cowindow)
let getAllWindows b = getWindows b

type execWindow = sw:window{List.find (fun w -> w = SB_Script) sw.wsbox = None}

val getWin : cowindow -> Tot (option execWindow)
let getWin cw =
  if (isTrustedOriginWindow cw) then None
  else if (List.find (fun w -> w = SB_Script) (CWindow?.cwsbox cw) <> None) then None
  else Some (cowin_to_win cw) (* Need to expose the function here *)

val getDocumentDomain : browser -> execWindow -> Tot (hdomain)
let getDocumentDomain b sw = (get_document_domain b sw)

val setDocumentDomain : browser -> execWindow -> hdomain -> Tot (browser * cowindow)
let setDocumentDomain b sw hd =
    let (r, w, nb) = (set_document_domain b sw hd) in
    (nb, win_to_cowin w)

val getWinLocation : #s:secLevel -> browser -> execWindow -> cowindow -> Tot (option (c_uri s))
let getWinLocation #s b sw cw =
  let (r, u) = get_win_location b (win_to_cowin sw) cw in
  u

val setWinLocation : browser -> execWindow -> cowindow -> u:uri{match (URI?.usl u) with | SecretVal [o] -> true | _ -> false} -> Tot browser
let setWinLocation b sw cw u =
  let (r, req, w, nb) = set_win_location b (win_to_cowin sw) cw u in
  nb

val getLocalStorageItem : browser -> execWindow -> string -> Tot string
let getLocalStorageItem b sw key =
  let (r, v) = (get_item_localStorage b sw None key) in
  v

val setLocalStorageItem : browser -> execWindow -> string -> string -> Tot browser
let setLocalStorageItem b sw key value =
  let (r, nb) = (set_item_localStorage b sw None key value) in
  nb

val postMessage : browser -> execWindow -> cowindow -> string -> string -> Tot result
let postMessage b sw cw msg ori = post_message b (win_to_cowin sw) cw msg ori

val getWinByName : browser -> execWindow -> string -> Tot (browser * cowindow)
let getWinByName b sw n =
  let (r, cw, nb) = get_window_from_name b (win_to_cowin sw) n in
  (nb, cw)

val winOpen : browser -> execWindow -> string -> string -> Tot (browser * cowindow)
let winOpen b sw u n =
  let (r, req, cw, nb) = open_window b (win_to_cowin sw) u n in
  (nb, cw)

val winClose : browser -> execWindow -> cowindow -> Tot browser
let winClose b sw cw = close_window b (sw) cw

(* val processNextResponse : browser -> cowindow -> actResponse -> bool -> result *)
(* let processNextResponse b cw resp f = *)
(*   if (not (isTrustedOriginWindow cw) && Some? (getWin cw)) then  *)
(*     let win = (Some?.v (getWin cw)) in *)
(*     let conn = (mk_connection ({cori=win.wloc.c_origin;ccred=f})) in *)
(*     let (r, nb) = processResponse b conn resp in *)
(*     b := nb; r *)
(*   else  *)
(*     ( *)
(*     let win = cowin_to_win cw in  *)
(*     let conn = (mk_connection ({cori=win.wloc.c_origin;ccred=f})) in *)
(*     let respconn = getResponseConn (b).conn conn in *)
(*     match respconn with *)
(*     | None -> Success "" *)
(*     | Some ((req,sw,tw,ty), f, ncl) ->  *)
(* 	let f = getProcResponse win.wloc.c_origin in  *)
(* 	let (r, nb) = processResponse b conn (f req) in *)
(* 	Success "" *)
(*     )  *)   

