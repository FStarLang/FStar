(*
  Defines the functionality related to request and response headers (from fetch.spec.whatwg.org)
*)
module Browser.RequestResponseHeader

open AuxiliaryFunctions
open Web.Origin
open Web.URI
open Browser.AuxiliaryDatatypes
open Secret.SecString
open Browser.Datatypes

module List = FStar.List.Tot

(* append a name/value to header list *)
val appendName : header -> header_field -> header_value -> Tot header 
let appendName h hf v = List.append [(hf,v)] h

val appendLemma : #s:secrecy_level -> r:requestFormat s -> hf:header_field -> hv:header_value{Headervalue?.hvs hv = s /\ checkHeaderFieldValueSecLevel hf hv} ->  
		  Lemma (requires (isValidBrowserRequest r)) 
		  (ensures (isValidBrowserRequest ({r with reqhead = (appendName r.reqhead hf hv)}))) [SMTPat (appendName r.reqhead hf hv)]
let appendLemma #s r hf hv = ()

val appendSecLevelLemma : h:header -> hf:header_field -> hv:header_value -> Lemma (requires (checkHeaderSecLevel h /\ 
			  ((not (is_forbidden_request_header_field hf)) && (not (is_forbidden_response_header_field hf)) ==> Headervalue?.hvs hv = PublicVal) )) 
			  (ensures (checkHeaderSecLevel (appendName h hf hv))) [SMTPat (appendName h hf hv)]
let appendSecLevelLemma h hf hv = ()

(* delete all headers with name/value from header list *)
val removeName : header -> header_field -> Tot header
let rec removeName h hf = 
  match h with
  | [] -> []
  | (f,v)::tl -> if f = hf then (removeName tl hf)
	       else (f,v)::(removeName tl hf)

(* set a name/value in header list *)
val setHeader : header -> header_field -> header_value -> Tot header
let setHeader h hf v = 
  let nh = removeName h hf in 
  appendName h hf v

val combineHeaderValues : h:header_value{Headervalue?.hvs h = PublicVal} -> h':header_value{Headervalue?.hvs h' = PublicVal} -> Tot header_value
let combineHeaderValues h h' = Headervalue PublicVal (secret_string_strcat #PublicVal (secret_string_strcat #PublicVal (Headervalue?.hv h) ",") (Headervalue?.hv h'))

(* combine a name/value in header list *)
val combineHeader : header -> header_field -> header_value -> Tot header
let rec combineHeader h hf v =
  match h with 
  | [] -> [(hf,v)]
  | (f,ov)::tl -> if f = hf && (Headervalue?.hvs ov = PublicVal) && (Headervalue?.hvs v = PublicVal) then (f, combineHeaderValues ov v)::tl
		else (f,ov)::(combineHeader tl hf v)

(* determine header names as a string *)
val getHeaderNamesList : header -> Tot (list header_field)
let rec getHeaderNamesList h = match h with
  | [] -> []
  | (f,_)::tl -> if (is_cors_safelisted_request_header_field f) then getHeaderNamesList tl
	       else f::(getHeaderNamesList tl)

val getHeaderNamesString : list header_field -> Tot string
let rec getHeaderNamesString h = match h with
  | [] -> ""
  | hd::tl -> hd ^ "," ^ (getHeaderNamesString tl)

val getHeaderNames : header -> Tot string
let getHeaderNames h = getHeaderNamesString (list_remove_duplicates (getHeaderNamesList h))

(* Only unique header names in the header *)
(* Do we need all header names with no repeatations or the ones which.are not repeated *)
(* The commented text gives the latter *)
(* val getUniqueRespHeader : header -> list header_field -> list header_field -> Tot (list header_field) *)
(* let rec getUniqueRespHeader h hf rep = *)
(*   match h with *)
(*   | [] -> hf *)
(*   | (f,v)::tl -> if (List.find (fun x -> x = f) rep <> None) then (getUniqueRespHeader tl hf rep) *)
(* 	       else  *)
(* 		 match (List.find (fun x -> x = f) hf) with *)
(* 		 | None -> getUniqueRespHeader tl (f::hf) rep *)
(* 		 | Some fl -> getUniqueRespHeader tl (list_remove_element hf fl) (fl::rep) *)

val getUniqueRespHeaderList : header -> list header_field -> Tot (list header_field)
let rec getUniqueRespHeaderList h hfl =
  match h with
  | [] -> hfl
  | (f,v)::tl -> match (List.find (fun x -> x = f) hfl) with
	       | None -> (getUniqueRespHeaderList tl (f::hfl))
	       | Some _ -> (getUniqueRespHeaderList tl hfl)

val getUniqueRespHeader : header -> Tot (list header_field)
let getUniqueRespHeader h = getUniqueRespHeaderList h []

val getDirName : string -> Tot (option csp_directive_name)
let getDirName s = match s with
  | "child-src" -> Some CSP_child_src
  | "connect-src" -> Some CSP_connect_src
  | "default-src" -> Some CSP_default_src 
  | "font-src" -> Some CSP_font_src
  | "frame-src" -> Some CSP_frame_src
  | "img-src" -> Some CSP_img_src
  | "manifest-src" -> Some CSP_manifest_src
  | "media-src" -> Some CSP_media_src
  | "object-src" -> Some CSP_object_src
  | "script-src" -> Some CSP_script_src
  | "style-src" -> Some CSP_style_src
  | "worker-src" -> Some CSP_worker_src
  | "base-uri" -> Some CSP_base_uri
  | "plugin-types" -> Some CSP_plugin_types
  | "sandbox" -> Some CSP_sandbox
  | "disown-opener" -> Some CSP_disown_opener
  | "form-action" -> Some CSP_form_action
  | "frame-ancestors" -> Some CSP_frame_ancestors
  | "navigate-to" -> Some CSP_navigate_to
  | _ -> None 
  
(* CSP Level 3 - 4.1.1. Set response’s CSP list *)
val setRespCSPList : browserResponse -> Tot browserResponse
let setRespCSPList resp = 
  let csp = getCSPDirectives resp in
  BrowserResponse (resp.bresp_secrecy_level) ({resp.b_response with respCSP=csp})

(* set the response's https state *)
val setRespHTTPS : browserResponse -> Tot browserResponse
let setRespHTTPS resp = 
  let httpsString = (if (not (list_is_empty resp.b_response.respurl)) && (getScheme (List.hd resp.b_response.respurl) = "https") then "modern" 
		    else resp.b_response.respHTTPS) in
  BrowserResponse (resp.bresp_secrecy_level) ({resp.b_response with respHTTPS=httpsString})


