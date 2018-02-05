(*
  Defines some data types used by the browser's data structures like 
  sandbox, referer, headers, csp and some functions related to them.
  Additionally, defines some refinement types on strings for some fields in request, response etc. 
*)

module Browser.AuxiliaryDatatypes

open AuxiliaryFunctions
open Secret.SecString
open Web.Origin
open Web.URI

module List = FStar.List.Tot

type result =
| Success of public_string
| Error of public_string

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
type sandbox_flags =
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

type reqMethod = m:public_string{m="GET" \/ m="POST" \/ m="HEAD" \/ m="OPTIONS" \/ m="DELETE" \/ m="PUT"}

type header_field = f:public_string(* {f="Accept" \/ f="Origin" \/ f="Host" \/ f="Referer" \/ f="Location" \/ f="Allow-origin"} *)

type header_value' (s:secrecy_level) = secret_string s
type header_value =
| Headervalue : hvs:secrecy_level -> hv:header_value' hvs -> header_value

(* Header for requests and responses *)
type header = list (f:header_field * v:header_value)

type mode =
| SameOrigin
| CORS
| NoCORS
| Navigate
| WebSocket

(* Referrer policy *)
type referrer_policy = 
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
type csp_directive_name =
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

type csp_origin_path = {
  op_protocol : origin_protocol;
  op_host : origin_domain;
  op_port : option origin_port;
  op_domain : option origin_domain;
  op_path : list public_string;
  op_exact_match_flag : bool; (* em indicates whether it is an exact match, i.e., last char is not / *)
} 

(* directive value*)
type csp_directive_value = 
| DV_None
| DV_Self
| DV_Any
| DV_U_Inline
| DV_U_Eval
| DV_St_Dynamic
| DV_U_Hashed
| DV_Scheme of origin_protocol
| DV_Domain of origin_domain
| DV_Origin of csp_origin_path
| DV_Nonce of public_string
| DV_Hash of public_string
| DV_SBox of public_string

type csp_directive = {
  directive_name:csp_directive_name; 
  directive_value:list csp_directive_value;
}

type csp_policy = list csp_directive
 


(* COOKIES *)
(* Cookie attributes from header *)
type cookie_header_attributes = 
| SecureOnly : cookie_header_attributes 
| HttpOnly : cookie_header_attributes 
| Expires : public_string -> cookie_header_attributes (*string is a time representative here and below*)
| Max_age : public_string -> cookie_header_attributes
| CookieDomain : origin_domain -> cookie_header_attributes
| CookiePath : list public_string -> cookie_header_attributes

type c_cookie (s:secrecy_level) = {
  cookie_name : secret_string s; 
  cookie_value : secret_string s; 
  cookie_expiry : public_string; (* expiry-time (max-age) *)
  cookie_domain : origin_domain; (* domain *)
  cookie_path : path s; (* path *)
  cookie_create_time : public_string; (* create-time *)
  cookie_last_access : public_string; (* last-access time *)
  cookie_persistent : bool; (* persistent-flag /  !(session-only) *)
  cookie_host_only : bool; (* host-only *)
  cookie_secure : bool; (* secure-only *)
  cookie_http_only : bool; (* http-only *)
}

(* opaque origins cannot access cookies? *)
val can_origin_access_cookie : #s:secrecy_level -> origin -> c_cookie s -> GTot bool
let can_origin_access_cookie #s o c = 
  match o with 
  | Origin sc h p d -> if c.cookie_host_only then h = c.cookie_domain else (origin_domain_match h c.cookie_domain)
  | OpaqueOrigin op -> is_origin_in_secrecy_level o s

(* opaque origins cannot access cookies? *)
val can_secrecy_origin_access_cookie : #s:secrecy_level -> secrecy_origin -> c_cookie s -> GTot bool
let can_secrecy_origin_access_cookie #s o c = 
  match o with 
  | SecOrigin so -> can_origin_access_cookie so c
  | OriginStar h -> if c.cookie_host_only then h = c.cookie_domain else (origin_domain_match h c.cookie_domain)

val can_list_secrecy_origin_access_cookie : #s:secrecy_level -> list secrecy_origin -> c_cookie s -> GTot bool
let rec can_list_secrecy_origin_access_cookie #s lo c = 
  match lo with 
  | [] -> true
  | hd::tl -> can_secrecy_origin_access_cookie hd c && can_list_secrecy_origin_access_cookie tl c

type a_cookie (s:secrecy_level) = c:(c_cookie s){s <> PublicVal /\ (can_list_secrecy_origin_access_cookie (SecretVal?.sec_origin_list s) c)}
(* type a_cookie (s:secrecy_level) = c:(c_cookie s){s <> PublicVal} *)

type cookie =
| Cookie : cookie_secrecy_level:secrecy_level{cookie_secrecy_level <> PublicVal} -> c:a_cookie cookie_secrecy_level -> cookie

type cookie_send' (s:secrecy_level) = {
  cookie_send_name : secret_string s;
  cookie_send_value : secret_string s;
}

type cookie_send =
| CookieSend : cs_secrecy_level:secrecy_level -> cs:cookie_send' cs_secrecy_level -> cookie_send

(* type cookie_send = (public_string * public_string) *)

type cookie_header (l:secrecy_origin_list) = {
  cookie_header_name : secret_string (SecretVal l);
  cookie_header_value : secret_string (SecretVal l);
  cookie_header_attributes_list : list cookie_header_attributes;
}

val mk_acookie : #s:secrecy_level{s <> PublicVal} -> c:c_cookie s{can_list_secrecy_origin_access_cookie (SecretVal?.sec_origin_list s) c} -> Tot (a_cookie s)
let mk_acookie #s c = c 




(* Allowing some public headers - should we keep such a feature? *)
val is_public_header_field : header_field -> GTot bool
let is_public_header_field hf = (hf = "Origin" || hf = "Referer")

(* CORS safelisted request header *)
val is_cors_safelisted_request_header_field : header_field -> Tot bool
let is_cors_safelisted_request_header_field h =
  (h="Accept" || h="Accept-Language" || h="Content-Language" || h="Content-Type" || h="DPR" || h="Downlink" || h="Save-Data" || h="Viewport-Width" || h="Width")

(* is header name a forbidden header name - request *)
val is_forbidden_request_header_field : header_field -> Tot bool
let is_forbidden_request_header_field h =
  (h="Accept-Charset" || h="Accept-Encoding" || h="Access-Control-Request-Headers" || h="Access-Control-Request-Method" || h="Connection" || h="Content-Length" || h="Cookie" || h="Cookie2" || h="Date" || h="DNT" || h="Expect" || h="Host" || h="Keep-Alive" || h="Origin" || h="Referer" || h="TE" || h="Trailer" || h="Transfer-Encoding" || h="Upgrade" || h="Via")

(* Is a forbidden response header name *)
val is_forbidden_response_header_field : header_field -> Tot bool
let is_forbidden_response_header_field n = (n="Set-Cookie" || n="Set-Cookie2")

val notForbiddenHeaderfieldInReqHeader : header -> Tot bool
let rec notForbiddenHeaderfieldInReqHeader h =
  match h with 
  | [] -> true
  | (f,v)::tl -> (not (is_forbidden_request_header_field f)) && (not (is_forbidden_response_header_field f)) && notForbiddenHeaderfieldInReqHeader tl

(* Are all headers CORS safelisted request headers? *)
val isCORSSafelistedHeaders : header -> Tot bool
let isCORSSafelistedHeaders h = List.for_all (fun (hf, v) -> is_cors_safelisted_request_header_field hf) h

val checkHeaderFieldValueSecLevel : header_field -> header_value -> GTot bool
let checkHeaderFieldValueSecLevel hf hv = 
  if (not (is_forbidden_request_header_field hf)) && (not (is_forbidden_response_header_field hf)) && (Headervalue?.hvs hv <> PublicVal) then 
     false
  else true

(* Allow only forbidden request headers to be secret --- Is it too strict? *)
(* The headers in the initial request object are all considered *)
val checkHeaderSecLevel : h:header -> GTot bool
let rec checkHeaderSecLevel h =
  match h with 
  | [] -> true
  | (f,v)::tl -> checkHeaderFieldValueSecLevel f v && checkHeaderSecLevel tl

(* remove all the forbidden headers as per the initial request constructed by the browser, just before getFetchHeader *)
val removeForbiddenHeaderfieldInHeader : h:header{checkHeaderSecLevel h} -> Tot (nh:header{notForbiddenHeaderfieldInReqHeader nh /\ checkHeaderSecLevel nh})
let rec removeForbiddenHeaderfieldInHeader h = 
  match h with 
  | [] -> []
  | (f,v)::tl -> if (not (is_forbidden_request_header_field f)) && (not (is_forbidden_response_header_field f)) then (f,v)::(removeForbiddenHeaderfieldInHeader tl)
	       else removeForbiddenHeaderfieldInHeader tl

(* Return the headers that shall be used with redirect *)
val redirectHeaders : h:header{checkHeaderSecLevel h} -> Tot (nh:header{notForbiddenHeaderfieldInReqHeader nh /\ checkHeaderSecLevel nh})
let rec redirectHeaders h = 
  match h with 
  | [] -> []
  | (f,v)::tl -> if (not (is_forbidden_request_header_field f)) && (not (is_forbidden_response_header_field f)) then (f,v)::(redirectHeaders tl) else (redirectHeaders tl)

(* If at least one of the origin in the index list is the current origin, then the origin must have access to the header? *)
(* val isHeaderValVisible : header_value -> secrecy_level -> GTot bool *)
(* let isHeaderValVisible h s = can_restrict_secrecy_level (Headervalue?.hvs h) s *)
(*   (\* match (Headervalue?.hvs h) with *\) *)
(*   (\* | PublicVal -> true *\) *)
(*   (\* | SecretVal sec -> (if (Some? (List.tryFind (fun o -> List.mem o s) sec)) then true else false) *\) *)

(* If the header_field can be publicly available, allow it *)
val isHeaderVisible : header -> secrecy_level -> GTot bool
let rec isHeaderVisible h s =
  match h with 
  | [] -> true
  | (f,v)::tl -> (can_restrict_secrecy_level (Headervalue?.hvs v) s) && (isHeaderVisible tl s)

val headerLemma : h:header -> s:secrecy_level -> Lemma (requires (List.for_all (fun (f,v) -> (Headervalue?.hvs v) = PublicVal) h))
		  (ensures (isHeaderVisible h s)) [SMTPat (isHeaderVisible h s)]
let rec headerLemma h t = match h with
  | [] -> ()
  | hd::tl -> headerLemma tl t

(* val emptyHeaderLemma : h:header -> t:secrecy_level -> Lemma (requires (h = [])) (ensures (isHeaderVisible h t)) [SMTPat (isHeaderVisible h t)] *)
(* let emptyHeaderLemma h t = () *)

val canReclHeader : h:header{checkHeaderSecLevel h} -> secrecy_level -> GTot bool
let rec canReclHeader h l = 
  match h with 
  | [] -> true
  | (f,v)::tl -> if (is_forbidden_request_header_field f) || (is_forbidden_response_header_field f) then 
		  (can_reclassify_secret_string #(Headervalue?.hvs v) (Headervalue?.hv v) l) && (canReclHeader tl l)
	       else (canReclHeader tl l)

val reclassifyHeader : h:header{checkHeaderSecLevel h} -> l:secrecy_level{canReclHeader h l} -> Tot (nh:header{checkHeaderSecLevel nh /\ isHeaderVisible nh l})
let rec reclassifyHeader h l =
  match h with 
  | [] -> []
  | (f,v)::tl -> if (is_forbidden_request_header_field f) || (is_forbidden_response_header_field f) then 
		  (f, Headervalue l (reclassify_secret_string #(Headervalue?.hvs v) (Headervalue?.hv v) l))::(reclassifyHeader tl l)
	       else 
		  (f, v)::(reclassifyHeader tl l)
		  
val reclassifyHeaderLemma : h:header{checkHeaderSecLevel h} -> l:secrecy_level{canReclHeader h l} -> Lemma (requires (True))
	(ensures (isHeaderVisible (reclassifyHeader h l) l))
	[SMTPat (reclassifyHeader h l)]
let rec reclassifyHeaderLemma h l = 
  match h with
  | [] -> ()
  | (f,v)::tl -> (reclassifyHeaderLemma tl l)

val reclForbiddenLemma : h:header{checkHeaderSecLevel h} -> l:secrecy_level{canReclHeader h l} -> Lemma (requires (notForbiddenHeaderfieldInReqHeader h)) 
			       (ensures (notForbiddenHeaderfieldInReqHeader (reclassifyHeader h l))) [SMTPat (reclassifyHeader h l)]
let rec reclForbiddenLemma h l = 
  match h with 
  | [] -> ()
  | (f,v)::tl -> reclForbiddenLemma tl l

val reclHeaderRedLemma : h:header{checkHeaderSecLevel h} -> l:secrecy_level -> Lemma (requires (notForbiddenHeaderfieldInReqHeader h))
			 (ensures (canReclHeader h l)) [SMTPat (canReclHeader h l)]
let rec reclHeaderRedLemma h l = 
  match h with
  | [] -> ()
  | hd::tl -> reclHeaderRedLemma tl l

val redirectHeadersLemma : h:header{checkHeaderSecLevel h} -> l:secrecy_level ->
			   Lemma (requires (True)) (ensures (canReclHeader (redirectHeaders h) l)) [SMTPat (canReclHeader (redirectHeaders h) l)]
let rec redirectHeadersLemma h l = 
  match h with 
  | [] -> ()
  | hd::tl -> (redirectHeadersLemma tl l)

val reclassifyHeaderVisibleLemma : h:header{checkHeaderSecLevel h} -> o:secrecy_origin{canReclHeader h (SecretVal [o])} -> 
	Lemma (requires (True)) (ensures (isHeaderVisible (reclassifyHeader h (SecretVal [o])) (SecretVal [o]))) [SMTPat (reclassifyHeader h (SecretVal [o]))]
let reclassifyHeaderVisibleLemma h o = ()

val reclassifyHeaderVisibleListLemma : h:header{checkHeaderSecLevel h} -> o:list secrecy_origin{(not (list_is_empty o)) /\ canReclHeader h (SecretVal o)} -> 
	Lemma (requires (True)) (ensures (isHeaderVisible (reclassifyHeader h (SecretVal o)) (SecretVal o))) [SMTPat (reclassifyHeader h (SecretVal o))]
let rec reclassifyHeaderVisibleListLemma h o = 
  match h with 
  | [] -> ()
  | (f,v)::tl -> reclassifyHeaderVisibleListLemma tl o

 
(* *** Some functions for printing and logging *** *)
(* val getOriginList : list origin -> Tot public_string *)
(* let rec getOriginList l = *)
(*   match l with  *)
(*   | [] -> "" *)
(*   | hd::tl -> (origin_to_string hd) ^ " and " ^ (getOriginList tl) *)

(* val getValOrigin : header_value -> Tot public_string *)
(* let getValOrigin hv = *)
(*   match (Headervalue?.hvs hv) with *)
(*   | PublicVal -> "publicvalue" *)
(*   | SecretVal ol -> getOriginList ol *)

(* val getHeaderOrigins : header -> Tot public_string  *)
(* let rec getHeaderOrigins h = *)
(*   match h with  *)
(*   | [] -> "" *)
(*   | (h,v)::tl -> (h ^ " : " ^ (getValOrigin v)) ^ "\n" ^ (getHeaderOrigins tl) *)



