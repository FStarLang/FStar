(*
  Defines some data types used by the browser's data structures like 
  sandbox, referer, cookies, headers, csp and some functions related to them.
  Additionally, defines some refinement types on strings for some fields in request, response etc. 
*)

module Browser.AuxiliaryDatatypes

open AuxiliaryFunctions
open Secret.SecString
open Web.Origin
open Web.URI

module List = FStar.List.Tot

type result =
| Success of string
| Error of string

(* When a sandbox is created, all are set to true. Based on the options -- "allow-<>", some of them can be false*)
type sandbox = {
  sb_forms : bool;
  sb_modals : bool;
  sb_orientation : bool;
  sb_pointerlock : bool;
  sb_popups : bool;
  sb_popupsEscape : bool;
  sb_presentation : bool;
  sb_sameorigin : bool;
  sb_scripts : bool;
  sb_topnavigation : bool;
}

(* Default options with sandbox attribute on iframes *)
let sbox = {sb_forms=true; sb_modals=true; sb_orientation=true; sb_pointerlock=true; sb_popups=true; sb_popupsEscape=true; sb_presentation=true; sb_sameorigin=true; sb_scripts=true; sb_topnavigation=true}

(* Section 6.5 of HTML5.1 spec defines these flags; used when navigating *)
type sandboxFlags =
| SB_Navigation      (*Prevents from navigating contexts other than the sandboxed context itself*)
| SB_NewWindow       (*Prevents creating new auxiliary contexts (using window.open) *)
| SB_TopWindow       (*Prevents navigating or closing the top-level browsing context *)
| SB_Plugins         (*prevents instantiating plugins *)
| SB_Origin          (*Forces content into a unique-origin. Prevents same-origin access, read and write to document.cookie/localStorage *)
| SB_Forms           (*Blocks form submission *)
| SB_PointerLock     (*Disables pointer lock API *)
| SB_Script          (*Blocks script execution *)
| SB_Automatic       (*Blocks features from automatically triggering like video *)
| SB_StorageURL      (*prevents URL schemes that use storage areas from being able to access the origin's data*)
| SB_Domain          (*Prevents document.domain setter*)
| SB_Propagate       (*Propagates all the flags to child/auxiliary contexts*)
| SB_Modals          (*Prevents alert(), confirm(), print(), prompt(), beforeunload *)
| SB_Orientation     (*disables ability to lock screen orientation*)
| SB_Presentation    (*disables presentation API*)

(* fetch is not in the fetchspec (guess its "") but used in CSP spec *)
type initiator = i:string{i="" || i="download" || i="imageset" || i="manifest" || i="xslt" || i="fetch"} 

type requesttype = r:string{r="" || r="audio" || r="font" || r="image" || r="script" || r="style" || r="track" || r="video"}

type destination = d:string{d="" || d="document"  || d="embed" || d="font" || d="image" || d="manifest" || d="media" || d="object" || d="report" || d="script" || d="serviceworker" || d="sharedworker" || d="style" || d="worker" || d="xslt" || d="subresource"}

type parserVal = p:string{p="" || p="parser-inserted" || p="not-parser-inserted"}

type taintVal = t:string{t="basic" || t="cors" || t="opaque"}

type redirectVal = r:string{r="follow" || r="error" || r="manual"}

type credmode = r:string{r="omit" || r="same-origin" || r="include"}

type httpstate = r:string{r="none" || r="deprecated" || r="modern"}

type navType = n:string{n="form-submission" || n="other"}

type responseType = n:string{n="basic" || n="cors" || n="default" || n="error" || n="opaque" || n="opaqueredirect"}

type time = nat (* time is represented as a natural number for indicating when the history entries were added *)

val get_time : time 
let get_time = 1234

type reqMethod = m:string{m="GET" \/ m="POST" \/ m="HEAD" \/ m="OPTIONS" \/ m="DELETE" \/ m="PUT"}

type headerfield = f:string(* {f="Accept" \/ f="Origin" \/ f="Host" \/ f="Referer" \/ f="Location" \/ f="Allow-origin"} *)

type mode =
| SameOrigin
| CORS
| NoCORS
| Navigate
| WebSocket

(* Referrer policy *)
type refPolicy = 
| RP_EmptyPolicy     (*defaults to Norefwhendowngrade*)     
| RP_NoReferrer      (*No referer header to be sent with request*) 
| RP_NoRefWhenDowngrade (*Referer header will be sent from https -> https and http -> any but not from https -> http*)
| RP_SameOrigin      (*Referer header is set for same-origin requests*)
| RP_Origin          (*Referer header set with "origin" of the request even for https -> http requests*)
| RP_StrictOrigin    (*Referer header set with "origin" of the request for https -> https and http -> any requests*)
| RP_OriginWhenCO    (*For same origin set complete url and for cross origins set with "origin"*)
| RP_StrictWhenCO    (*For same origin set complete url and for cross origins set with "origin" for https -> https and http -> any, else nothing*)
| RP_UnsafeURL       (*Set complete url for same and cross origin requests*)

(*Includes all CSP directives - fetch, document and navigation directives*)
type csp_dir_name =
| CSP_child_src
| CSP_connect_src
| CSP_default_src 
| CSP_font_src
| CSP_frame_src
| CSP_img_src
| CSP_manifest_src
| CSP_media_src
| CSP_object_src
| CSP_script_src
| CSP_style_src
| CSP_worker_src
| CSP_base_uri
| CSP_plugin_types
| CSP_sandbox
| CSP_disown_opener
| CSP_form_action
| CSP_frame_ancestors
| CSP_navigate_to

type origpath = {
  op_prot:scheme;
  op_host:hdomain;
  op_port:option port;
  op_dom:option hdomain;
  op_path:list pubString;
  op_em:bool; (* em indicates whether it is an exact match, i.e., last char is not / *)
} 

(* directive value*)
type dirValue = 
| DV_None
| DV_Self
| DV_Any
| DV_U_Inline
| DV_U_Eval
| DV_St_Dynamic
| DV_U_Hashed
| DV_Scheme of scheme
| DV_Domain of hdomain
| DV_Origin of origpath
| DV_Nonce of pubString
| DV_Hash of pubString
| DV_SBox of pubString

type csp_directive = {
  dir_name:csp_dir_name; 
  dir_value:list dirValue;
}

type csp_policy = list csp_directive

(* Cookie attributes from header *)
type cookieAttribute = 
| SecureOnly : cookieAttribute
| HttpOnly : cookieAttribute
| Expires : pubString -> cookieAttribute (*string is a time representative here and below*)
| Max_age : pubString -> cookieAttribute
| Cdomain : hdomain -> cookieAttribute 
| Cpath : list pubString -> cookieAttribute

type c_cookie (s:secLevel) = {
  cname:secString s; 
  cval:secString s; 
  cexp:pubString; (* expiry-time (max-age) *)
  cdom:hdomain; (* domain *)
  cpath:path s; (* path *)
  ccreate:pubString; (* create-time *)
  cla:pubString; (* last-access time *)
  cpersist:bool; (* persistent-flag /  !(session-only) *)
  chost:bool; (* host-only *)
  csec:bool; (* secure-only *)
  chttp:bool; (* http-only *)
}

val isCookieOriginMatch : #s:secLevel -> torigin -> c_cookie s -> Tot bool
let isCookieOriginMatch #s o c = if c.chost then (TOrigin?.host o) = c.cdom else (domainMatch (TOrigin?.host o) c.cdom)

(* type a_cookie (s:secLevel) = c:(c_cookie s){s <> PublicVal /\ (List.for_all (fun x -> isCookieOriginMatch x c) (SecretVal?.seco s))} *)
type a_cookie (s:secLevel) = c:(c_cookie s){s <> PublicVal}

type cookie =
| Cookie : csl:secLevel{csl <> PublicVal} -> c:a_cookie csl -> cookie

(* type cookie_send' (s:secLevel) = { *)
(*   rcn : secString s; *)
(*   rcv : secString s; *)
(* } *)

(* type cookie_send = *)
(* | CookieSend : csl:secLevel -> cs:cookie_send' csl -> cookie_send *)

type cookie_send = (pubString * pubString)

type cookieHeader' (s:secLevel) = {
  cookie_name : secString s;
  cookie_value : secString s;
  cookie_attr : list cookieAttribute;
}

type cookieHeader (s:secLevel) = cookieHeader' s

type headervalue' (s:secLevel) = secString s
type headervalue =
| Headervalue : hvs:secLevel -> hv:headervalue' hvs -> headervalue

(* Header for requests and responses *)
type header = list (f:headerfield * v:headervalue)

(* val append_l_nil: l:list 'a -> *)
(*   Lemma (requires True) *)
(*         (ensures (l@[] == l)) [SMTPat (l@[])] *)
(* let rec append_l_nil = function *)
(*   | [] -> () *)
(*   | hd::tl -> append_l_nil tl *)
  
(* val origin_append_lemma : l:list torigin -> l':list torigin -> o:torigin -> Lemma (requires (containsOrigin [o] l)) (ensures (containsOrigin [o] (l'@l))) *)
(* let rec origin_append_lemma l l' o = match l' with *)
(*   | [] -> () *)
(*   | hd::tl -> origin_append_lemma l tl o *)

(* Allowing some public headers - should we keep such a feature? *)
val isHeaderFieldPublic : headerfield -> GTot bool
let isHeaderFieldPublic hf = (hf = "Origin" || hf = "Referer")

(* If at least one of the origin in the index list is the current origin, then the origin must have access to the header? *)
val isHeaderValVisible : headervalue -> list torigin -> GTot bool
let isHeaderValVisible h s =
  match (Headervalue?.hvs h) with
  | PublicVal -> true
  | SecretVal sec -> (if (isSublist s sec) then true else false)

(* If the headerfield can be publicly available, allow it *)
val isHeaderVisible : header -> list torigin -> GTot bool
let rec isHeaderVisible h s =
  match h with 
  | [] -> true
  | (f,v)::tl -> (isHeaderValVisible v s) && (isHeaderVisible tl s)

val headerLemma : h:header -> t:list torigin -> Lemma (requires (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) h))
		  (ensures (isHeaderVisible h t)) [SMTPat (isHeaderVisible h t)]
let rec headerLemma h t = match h with
  | [] -> ()
  | hd::tl -> headerLemma tl t

val emptyHeaderLemma : h:header -> t:list torigin -> Lemma (requires (h = [])) (ensures (isHeaderVisible h t)) [SMTPat (isHeaderVisible h t)]
let emptyHeaderLemma h t = ()

val canReclHeader : header -> secLevel -> secretOriginList -> GTot bool
let rec canReclHeader h l ls = 
  match h with 
  | [] -> true
  | (f,v)::tl -> (canReclassify #(Headervalue?.hvs v) (Headervalue?.hv v) l ls) && (canReclHeader tl l ls)

val reclassifyHeader : h:header -> l:secLevel -> ls:secretOriginList{canReclHeader h l ls} -> Tot header
let rec reclassifyHeader h l ls =
  match h with 
  | [] -> []
  | (f,v)::tl -> (f, Headervalue l (reclassify #(Headervalue?.hvs v) (Headervalue?.hv v) l ls))::(reclassifyHeader tl l ls)

val reclassifyHeaderLemma : h:header -> l:secLevel -> ls:secretOriginList{canReclHeader h l ls} -> Lemma (requires (True))
	(ensures (match l with | SecretVal [o] -> isHeaderVisible (reclassifyHeader h l ls) [o] | _ -> true))
	[SMTPat (reclassifyHeader h l ls)]
let rec reclassifyHeaderLemma h l ls = 
  match h with
  | [] -> ()
  | hd::tl -> (reclassifyHeaderLemma tl l ls)

(* *** Some functions for printing and logging *** *)
val getOriginList : list torigin -> Tot string
let rec getOriginList l =
  match l with 
  | [] -> ""
  | hd::tl -> (origin_to_string hd) ^ " and " ^ (getOriginList tl)

val getValOrigin : headervalue -> Tot string
let getValOrigin hv =
  match (Headervalue?.hvs hv) with
  | PublicVal -> "publicvalue"
  | SecretVal ol -> getOriginList ol

val getHeaderOrigins : header -> Tot string 
let rec getHeaderOrigins h =
  match h with 
  | [] -> ""
  | (h,v)::tl -> (h ^ " : " ^ (getValOrigin v)) ^ "\n" ^ (getHeaderOrigins tl)

