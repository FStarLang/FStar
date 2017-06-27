(*
  *** Content Security Policy Level 3 ***
  This module defines the various functions and checks related to CSP level 3 as per the spec at 
  https://www.w3.org/TR/CSP3/
*)

module Browser.ContentSecurityPolicy

open AuxiliaryFunctions
open Browser.AuxiliaryDatatypes
open Web.URI
open Browser.Datatypes

module List = FStar.List.Tot

(* Section 6.6.1.7. - effective-directive-for-a-request *)
(* Returns the effective CSP directive for the request type based on the algorithm*)
private val getDirectiveForRequest: request -> Tot (option csp_dir_name)
let getDirectiveForRequest req = 
  let r = (Request?.rf req) in 
  if r.reqtype = "" then (
     if r.reqinit="fetch" then Some CSP_connect_src
     else if r.reqinit="manifest" then Some CSP_manifest_src
     else if r.reqdest="subresource" then Some CSP_connect_src
     else if r.reqdest="unknown" then Some CSP_object_src
     else if (r.reqdest="document" && (match r.reqtarget with | Some f -> if (CWindow?.cwparent f) <> None then true else false | None -> false))
	 then Some CSP_frame_src
     else None
     )
  else if r.reqtype = "audio" then Some CSP_media_src 
  else if r.reqtype = "track" then Some CSP_media_src 
  else if r.reqtype = "video" then Some CSP_media_src
  else if r.reqtype = "font" then Some CSP_font_src
  else if r.reqtype = "image" then Some CSP_img_src
  else if r.reqtype = "style" then Some CSP_style_src
  else if r.reqtype = "script" then (
      if r.reqdest = "script" then Some CSP_script_src
      else if r.reqdest = "subresource" then Some CSP_script_src
      else if r.reqdest = "serviceworker" then Some CSP_worker_src
      else if r.reqdest = "sharedworker" then Some CSP_worker_src
      else if r.reqdest = "worker" then Some CSP_worker_src
      else None)
  else None

(* the nonce string n is of the form "nonce-<>" *)
private val get_nonce_list : list dirValue -> Tot (list string)
let rec get_nonce_list l =
  match l with
  | [] -> []
  | h::t -> match h with
	  | DV_Nonce n -> n::(get_nonce_list t)
	  | _ -> (get_nonce_list t)

(* Section 6.6.1.2. - match-nonce-to-source-list *)
(* Does nonce match source list - uses the auxiliary function get_nonce_list above *)
private val nonce_match_source : string -> list dirValue -> Tot bool
let nonce_match_source n l =
  if n = "" then false
  else if (let nl=(get_nonce_list l) in List.find (fun s -> s = n) nl <> None) then true (* nonce is matched with one of the values in the list *)
  else false

(* CSP spec uses "subresource" while the HTML5 spec uses these strings *)
(* val isSubresource : destinationstring -> Tot bool *)
(* let isSubresource d = (d="" || d="font" || d="image" || d="manifest" || d="media" || d="script" || d="style" || d="xslt") *)

(* val isPotNavSub : destinationstring -> Tot bool *)
(* let isPotNavSub d = (d="object" || d="embed") *)

(* val isNonSubresource : destinationstring -> Tot bool *)
(* let isNonSubresource d = (d="document" || d="report" || d="serviceworker" || d="sharedworker" || d="worker") *)

(* val isNavigationDest : destinationstring -> Tot bool *)
(* let isNavigationDest d = (d="document") *)

(* Section 6.1.2.1. -- CSP's prerequest check for connect-src *)
(* true indicates that the prerequest check succeeds. otherwise, false *)
private val connect_src_prerequest : request -> csp_directive -> Tot bool
let connect_src_prerequest req d =
  let r = (Request?.rf req) in
  if r.reqinit="fetch" || (r.reqtype="" && r.reqdest="subresource") then 
    uri_match_source r.requrl d.dir_value r.reqo r.reqredirect
  else true  
  (* if t="default" then ( *)
  (*   match (List.find (fun s -> s.dir_name = CSP_default_src) p) with  *)
  (*   | None -> true *)
  (*   | Some d ->  ) *)
  (* else ( *)
  (*   match (List.find (fun s -> s.dir_name = CSP_connect_src) p) with  *)
  (*   | None -> true *)
  (*   | Some d -> if r.reqinit="fetch" || (r.reqtype="" && r.reqdest="subresource") then  *)
  (* 		  uri_match_source r.requrl d.dir_value r.reqo r.reqredirect *)
  (* 	       else true ) *)

(* Section 6.1.4.1. -- CSP's prerequest check for font-src *)
private val font_src_prerequest : request -> csp_directive -> Tot bool
let font_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "font") then
      uri_match_source r.requrl d.dir_value r.reqo r.reqredirect
  else true

(* Section 6.1.5.1. -- CSP's prerequest check for frame-src *)
private val frame_src_prerequest : request -> csp_directive -> Tot bool
let frame_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "document" && (match r.reqtarget with |None -> false |Some win -> ((CWindow?.cwparent win) <> None))) then (
     uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.6.1. -- CSP's prerequest check for img-src *)
private val img_src_prerequest : request -> csp_directive -> Tot bool
let img_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "img") then (
     uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.7.1. -- CSP's prerequest check for manifest-src *)
private val manifest_src_prerequest : request -> csp_directive -> Tot bool
let manifest_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "" && r.reqinit = "manifest") then (
     uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.8.1. -- CSP's prerequest check for media-src *)
private val media_src_prerequest : request -> csp_directive -> Tot bool
let media_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "audio" || r.reqtype = "video" || r.reqtype = "track") then (
     uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.9.1. -- CSP's prerequest check for object-src *)
private val object_src_prerequest : request -> csp_directive -> Tot bool
let object_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "" && r.reqdest = "unknown") then (
     uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.10.1. -- CSP's prerequest check for script-src *)
private val script_src_prerequest : request -> csp_directive -> Tot bool
let script_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "script" && r.reqdest = "subresource") then ( 
    if (nonce_match_source r.reqnonce d.dir_value) then true (*check for cryptographic nonces*)
    else if (List.find (fun v -> v = DV_St_Dynamic) d.dir_value <> None) then 
      (if r.reqparser = "parser-inserted" then false else true)
    else uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.11.1. -- CSP's prerequest check for style-src *)
private val style_src_prerequest : request -> csp_directive -> Tot bool
let style_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqtype = "style") then ( 
    if (nonce_match_source r.reqnonce d.dir_value) then true (*check for cryptographic nonces*)
    else uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.12.1. -- CSP's prerequest check for worker-src *)
private val worker_src_prerequest : request -> csp_directive -> Tot bool
let worker_src_prerequest req d =
  let r = (Request?.rf req) in
  if (r.reqdest = "worker" || r.reqdest = "serviceworker" || r.reqdest = "sharedworker") then (
    uri_match_source r.requrl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.1.1. -- CSP's prerequest check for child-src *)
private val child_src_prerequest : request -> csp_directive -> csp_policy -> Tot bool
let child_src_prerequest r d p =
  let n=getDirectiveForRequest r in
    match n with
    | Some dir -> if dir<>CSP_frame_src && dir<>CSP_worker_src then true
		 else if (List.find (fun f -> f.dir_name = dir) p <> None) then true
		 else (
		   match dir with
		   | CSP_frame_src -> frame_src_prerequest r d
		   | CSP_worker_src -> worker_src_prerequest r d
		 )
    | None -> true  (* Not specified - doing as per default-src *)

(* Section 6.1.3.1. -- CSP's prerequest check for default-src *)
private val default_src_prerequest : request -> csp_directive -> csp_policy -> Tot bool
let default_src_prerequest r d p =
  let n=getDirectiveForRequest r in
    match n with
    | Some dir -> if (List.find (fun f -> f.dir_name = dir) p <> None) then true
		 else if (dir=CSP_frame_src || dir=CSP_worker_src) && (List.find (fun f -> f.dir_name = CSP_child_src) p <> None) then true
		 else (
		   match dir with
		   | CSP_connect_src -> connect_src_prerequest r d 
		   | CSP_font_src -> font_src_prerequest r d  
		   | CSP_frame_src -> frame_src_prerequest r d
		   | CSP_img_src -> img_src_prerequest r d
		   | CSP_manifest_src -> manifest_src_prerequest r d
		   | CSP_media_src -> media_src_prerequest r d
		   | CSP_object_src -> object_src_prerequest r d
		   | CSP_script_src -> script_src_prerequest r d
		   | CSP_style_src -> style_src_prerequest r d
		   | CSP_worker_src -> worker_src_prerequest r d
		 )
    | None -> true  

(* Section 6.1.2.2. -- CSP's postrequest check for connect-src *)
(* true indicates that the postrequest check succeeds. otherwise, false *)
private val connect_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let connect_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if r.reqinit="fetch" || (r.reqtype="" && r.reqdest="subresource") then 
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect
  else true 
  
(* Section 6.1.4.2. -- CSP's postrequest check for font-src *)
private val font_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let font_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "font") then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect) 
  else true

(* Section 6.1.5.2. -- CSP's postrequest check for frame-src *)
private val frame_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let frame_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "document" && (match r.reqtarget with |None -> false |Some win -> (CWindow?.cwparent win) <> None)) then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.6.2. -- CSP's postrequest check for img-src *)
private val img_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let img_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "img") then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.7.2. -- CSP's postrequest check for manifest-src *)
private val manifest_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let manifest_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "" && r.reqinit = "manifest") then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.8.2. -- CSP's postrequest check for media-src *)
private val media_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let media_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "audio" || r.reqtype = "video" || r.reqtype = "track") then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.9.2. -- CSP's postrequest check for object-src *)
private val object_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let object_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "" && r.reqdest = "unknown") then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.10.2. -- CSP's postrequest check for script-src *)
private val script_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let script_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "script" && r.reqdest = "subresource") then ( 
    if (nonce_match_source r.reqnonce d.dir_value) then true
    else uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.11.2. -- CSP's postrequest check for style-src *)
private val style_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let style_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqtype = "style") then ( 
    if (nonce_match_source r.reqnonce d.dir_value) then true (*check for cryptographic nonces*)
    else uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.12.2. -- CSP's postrequest check for worker-src *)
private val worker_src_postrequest : request -> actResponse -> csp_directive -> Tot bool
let worker_src_postrequest req resp d =
  let r = (Request?.rf req) in
  if (r.reqdest = "worker" || r.reqdest = "serviceworker" || r.reqdest = "sharedworker") then (
    uri_match_resp_source (ActResponse?.ar resp).respurl d.dir_value r.reqo r.reqredirect)
  else true

(* Section 6.1.1.2. -- CSP's postrequest check for child-src *)
private val child_src_postrequest : request -> actResponse -> csp_directive -> csp_policy -> Tot bool
let child_src_postrequest r resp d p =
  let n=getDirectiveForRequest r in
    match n with
    | Some dir -> if dir<>CSP_frame_src && dir<>CSP_worker_src then true
		 else if (List.find (fun f -> f.dir_name = dir) p <> None) then true
		 else (
		   match dir with
		   | CSP_frame_src -> frame_src_postrequest r resp d  (*Define the postrequest for frame and worker*)
		   | CSP_worker_src -> worker_src_postrequest r resp d
		 )
    | None -> false  

(* Section 6.1.3.2. -- CSP's postrequest check for default-src *)
private val default_src_postrequest : request -> actResponse -> csp_directive -> csp_policy -> Tot bool
let default_src_postrequest r resp d p =
  let n=getDirectiveForRequest r in
    match n with
    | Some dir -> if (List.find (fun f -> f.dir_name = dir) p <> None) then true
		 else if (dir=CSP_frame_src || dir=CSP_worker_src) && (List.find (fun f -> f.dir_name = CSP_child_src) p <> None) then true
		 else (
		   match dir with
		   | CSP_connect_src -> connect_src_postrequest r resp d
		   | CSP_font_src -> font_src_postrequest r resp d
		   | CSP_frame_src -> frame_src_postrequest r resp d
		   | CSP_img_src -> img_src_postrequest r resp d
		   | CSP_manifest_src -> manifest_src_postrequest r resp d 
		   | CSP_media_src -> media_src_postrequest r resp d
		   | CSP_object_src -> object_src_postrequest r resp d
		   | CSP_script_src -> script_src_postrequest r resp d
		   | CSP_style_src -> style_src_postrequest r resp d
		   | CSP_worker_src -> worker_src_postrequest r resp d
		 )
    | None -> true  
    
(* 6.6.1.1. CSP Level 3 - Does request violate CSP policy *)
private val reqViolatePolicy: request -> csp_policy -> Tot (option csp_directive)
let rec reqViolatePolicy r p =
  match p with
  | [] -> None 
  | ph::pt -> ( match ph.dir_name with
	      | CSP_child_src -> if child_src_prerequest r ph p then reqViolatePolicy r pt else Some ph
	      | CSP_default_src -> if default_src_prerequest r ph p then reqViolatePolicy r pt else Some ph
	      | CSP_connect_src -> if connect_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_font_src -> if font_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_frame_src -> if frame_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_img_src -> if img_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_manifest_src -> if manifest_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_media_src -> if media_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_object_src -> if object_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_script_src -> if script_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_style_src -> if style_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | CSP_worker_src -> if worker_src_prerequest r ph then reqViolatePolicy r pt else Some ph
	      | _ -> reqViolatePolicy r pt
	      )

(* CSP Level 3 - 4.1.3. Should request be blocked by Content Security Policy? *)
(* true -> blocked; false -> allowed *)
val reqBlockedCSP : request -> Tot bool
let reqBlockedCSP r =
  match (Request?.rf r).reqw with 
  | None -> false (* Not specified in the spec? may be the policy list is treated to be [] *)
  | Some w -> match reqViolatePolicy r (getCSPList w) with
	     | None -> false
	     | Some v -> true (*report all violations*)
 
private val respViolatePolicy: actResponse -> request -> csp_policy -> Tot (option csp_directive)
let rec respViolatePolicy resp req p =
  match p with
  | [] -> None 
  | ph::pt -> ( match ph.dir_name with
	      | CSP_child_src -> if child_src_postrequest req resp ph p then respViolatePolicy resp req pt else Some ph
	      | CSP_default_src -> if default_src_postrequest req resp ph p then respViolatePolicy resp req pt else Some ph
	      | CSP_connect_src -> if connect_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_font_src -> if font_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_frame_src -> if frame_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_img_src -> if img_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_manifest_src -> if manifest_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_media_src -> if media_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_object_src -> if object_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_script_src -> if script_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_style_src -> if style_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | CSP_worker_src -> if worker_src_postrequest req resp ph then respViolatePolicy resp req pt else Some ph
	      | _ -> respViolatePolicy resp req pt
	      )
	      
(* CSP Level 3 - 4.1.4. Should response to request be blocked by Content Security Policy? *)
(* true -> blocked; false -> allowed *)
val respReqBlockedCSP : actResponse -> request -> Tot bool
let respReqBlockedCSP resp req =
  match (Request?.rf req).reqw with 
  | None -> false 
  | Some w -> match respViolatePolicy resp req (getCSPList w) with
	     | None -> false
	     | Some v -> true (*report all violations*)

(* 6.3.1.1 form-action pre-navigation check *)
private val form_action_prenavigate : request -> string -> csp_directive -> Tot bool
let form_action_prenavigate req t d =
  let r = (Request?.rf req) in
  if (t = "form-submission") then 
    uri_match_source r.requrl d.dir_value r.reqo r.reqredirect
    (* match (List.find (fun s -> s.dir_name = CSP_form_action) p) with  *)
    (* | None -> true *)
    (* | Some d -> uri_match_source r.requrl d.dir_value r.reqo r.reqredirect *)
  else true 

(* 6.3.3.1 navigate-to pre-navigation check *)
private val navigate_to_prenavigate : request -> csp_directive -> Tot bool
let navigate_to_prenavigate req d =   
  let r = (Request?.rf req) in 
  uri_match_source r.requrl d.dir_value r.reqo r.reqredirect

private val navViolatePolicy: request -> string -> csp_policy -> Tot (option csp_directive)
let rec navViolatePolicy r t p =
  match p with
  | [] -> None
  | ph::pt -> match ph.dir_name with
	      | CSP_form_action -> if form_action_prenavigate r t ph then navViolatePolicy r t pt else Some ph
	      | CSP_navigate_to -> if navigate_to_prenavigate r ph then navViolatePolicy r t pt else Some ph
	      | _ -> navViolatePolicy r t pt
  
(* CSP Level 3 - 4.2.4. Should navigation request of type from source to target be blocked by Content Security Policy? *)
val navReqBlockedCSP : request -> string -> cowindow -> cowindow -> Tot bool
let navReqBlockedCSP r t sw tw =
  match navViolatePolicy r t (getCSPList sw) with
    | None -> false
    | Some v -> true

private val checkAncestor : cowindow -> list dirValue -> uri -> nat -> Tot bool 
let rec checkAncestor w v u n = 
  match (CWindow?.cwparent w) with 
  | None -> true
  | Some p -> (origin_match_expr_source_list (getWinURI p) v u n) && (checkAncestor p v u n)
  
(* 6.3.2.1. frame-ancestors Navigation Response Check *)
(* request is not used by the algorithm currently *)
private val frame_ancestors_navresponse : request -> resp:actResponse{not (emptyList (ActResponse?.ar resp).respurl)} ->
					cowindow -> cowindow -> csp_directive -> Tot bool
let frame_ancestors_navresponse req resp sw tw d = 
  match (ActResponse?.ar resp).respurl with 
  | rurl::_ -> checkAncestor tw d.dir_value rurl 0

(* request is not used by the algorithm currently *)
private val navRespViolatePolicy: request -> actResponse -> cowindow -> cowindow -> csp_policy -> Tot (option csp_directive)
let rec navRespViolatePolicy req resp sw tw p =
  match p with
  | [] -> None
  | ph::pt -> match ph.dir_name with
	      | CSP_frame_ancestors -> if (not (emptyList (ActResponse?.ar resp).respurl) && frame_ancestors_navresponse req resp sw tw ph) then 
					 navRespViolatePolicy req resp sw tw pt 
				      else Some ph
	      | _ -> navRespViolatePolicy req resp sw tw pt

(* 4.2.5. Should navigation response to navigation request of type from source in target be blocked by Content Security Policy? *)
(* Use of type? Not used by underlying algorithm *)
(* request is not used by the algorithm currently *)
val navRespBlockedCSP : request -> string -> actResponse -> cowindow -> cowindow -> Tot bool
let navRespBlockedCSP r t resp sw tw =
  match navRespViolatePolicy r resp sw tw (ActResponse?.ar resp).respCSP with
    | None -> false
    | Some v -> true

