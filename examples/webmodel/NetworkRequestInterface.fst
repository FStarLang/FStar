(*
  Defines secret and trusted origins to be used by the OAuth protocol and exposes a set of APIs from Browser.Model.Interface
*)
module NetworkRequestInterface

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
let defResponse = ActResponse PublicVal ({resptype="default";respcode=200;respurl=[];resphead=[];respbody=(emptyString PublicVal);resptrail=[];respHTTPS="none";respCSP=[];respCORS=[];resploc=None;respRedSec=PublicVal})
let defErrResponse = ActResponse PublicVal ({resptype="default";respcode=404;respurl=[];resphead=[];respbody=(emptyString PublicVal);resptrail=[];respHTTPS="none";respCSP=[];respCORS=[];resploc=None;respRedSec=PublicVal})

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

val checkEP : request -> string -> Tot bool
let checkEP r s = 
  let ruri = (firstElement (Request?.rf r).requrl) in
  match getPathVal #(URI?.usl ruri) (ruri) with
  | [] -> false
  | h::_ -> eqString h s
  



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

