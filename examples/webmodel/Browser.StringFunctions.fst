(*
  This module contains a few string operations and a few functions to create a uri, CSP directive, headers etc. from a string 
*)
module Browser.StringFunctions

open Web.Origin
open Secret.SecString
open Browser.AuxiliaryDatatypes
open ML.ExternalFunctions
open Web.URI
open FStar.IO

private val substring : s:string -> i:nat -> l:nat{i + l <= String.length s} -> Tot (ns:string{String.length ns = l})
let substring s i l = substringImpl s i l
  (* String.make l (String.sub s i l) *)

private val splitStr : #l:secrecy_level -> #l':secrecy_level -> s:string -> p:(option (secret_string l * secret_string l')) -> Tot bool
let splitStr #l #l' s p =
  match p with 
  | Some (fst, snd) -> (String.length s) > (secret_string_length snd) 
  | None -> true

private val getStringScheme : s:string -> n:nat -> Tot (p:(option (sc:string * string)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
let rec getStringScheme s n =
  if (String.length s <= (n+3)) then None
  else if (substring s n 3 =  "://") then 
    let origin_protocol = substring s 0 n in Some (origin_protocol , substring s (n+3) ((String.length s) - (n+3)))
  else getStringScheme s (n+1)

private val getStringDom : s:string -> n:nat -> Tot (p:(option (string * string)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
let rec getStringDom s n =
  if (String.length s <= n) then None
  else if (substring s n 1 = ".") then Some (substring s 0 n, substring s (n+1) ((String.length s) - (n+1)))
  else getStringDom s (n+1)

(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
private val splitDom : s:string -> Tot (list string) (decreases (String.length s))
let rec splitDom s =
    match getStringDom s 0 with
    | None -> [s]
    | Some (f,r) -> f::(splitDom r)

private val stringContains : s1:string -> s2:string -> n:nat -> Tot (p:(option nat){match p with | None -> true | Some po -> (po >= n && po < String.length s1)}) 
					       (decreases (String.length s1 - n))
let rec stringContains s1 s2 n =
  let l1 = String.length s1 in
  let l2 = String.length s2 in
  if (l1 <= n || (l1 - n) < l2) then None
  else if (substring s1 n l2 = s2) then Some n
  else stringContains s1 s2 (n+1)

private val splitHDom : string -> Tot (list string * option origin_port)
let rec splitHDom ts =
  let s = trim ts in 
  match (stringContains s ":" 0) with
  | None -> (splitDom s, None)
  | Some p -> (splitDom (substring s 0 p), Some (int_of_string (substring s (p+1) ((String.length s) - (p+1)))))

private val getStringPath : l:secrecy_level -> s:string -> n:nat -> Tot (p:(option (secret_string l * public_string)){splitStr #l #PublicVal s p}) (decreases (String.length s - n))
let rec getStringPath l s n =
  if (String.length s <= n) then None
  else if (substring s n 1 = "/") then (
    if n = 0 then 
      getStringPath l (substring s (n+1) ((String.length s) - (n+1))) 0 (* avoid spurious / *)
    else 
      Some (classify_secret_string #PublicVal (substring s 0 n) l, substring s (n+1) ((String.length s) - (n+1))))
  else getStringPath l s (n+1)

(* Takes a string and returns a list of strings with delimiter being "/" in the string *)
val splitPath : l:secrecy_level -> s:string -> Tot (path l) (decreases (String.length s))
let rec splitPath l s =
  match getStringPath l s 0 with
    | None -> [classify_secret_string #PublicVal s l]
    | Some (f,r) -> f::(splitPath l r)

private val getStringQuery : l:secrecy_level -> s:string -> n:nat -> Tot (p:(option (secret_string l * secret_string l)){splitStr #l #l s p}) (decreases (String.length s - n))
let rec getStringQuery l s n =
  if (String.length s <= n) then None
  else if (substring s n 1 = "=") then Some (classify_secret_string #PublicVal (substring s 0 n) l, classify_secret_string #PublicVal (substring s (n+1) ((String.length s) - (n+1))) l)
  else getStringQuery l s (n+1)

private val getStringQS : s:string -> n:nat -> Tot (p:(option (public_string * public_string)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
let rec getStringQS s n =
  if (String.length s <= n) then None
  else if (substring s n 1) = "&" then Some ((substring s 0 n), substring s (n+1) ((String.length s) - (n+1)))
  else getStringQS s (n+1)

private val splitQueryString : l:secrecy_level -> s:string -> Tot (querystring l) (decreases (String.length s))
let rec splitQueryString l s =
  match getStringQS s 0 with
  | None -> (match (getStringQuery l s 0) with
		  | None -> []
		  | Some (q,v) -> [(q,v)])
  | Some (f,r) -> (match (getStringQuery l f 0) with 
			| None -> (splitQueryString l r)
			| Some (q,v) -> (q,v)::(splitQueryString l r))

private val splitOrigPath : l:secrecy_level -> s:string -> n:nat{n < String.length s} -> slash:nat{slash >= (n+3) && slash < String.length s} -> Tot (origin_tuple * path l)
let splitOrigPath l s n slash =
  if (n = 0) then (Origin "" [] None None, [])
  else 
    let origin_protocol = (substring s 0 n) in 
    if is_origin_protocol origin_protocol then 
      let (hdom,pv) = splitHDom (substring s (n+3) (slash - (n+3))) in
      let p = splitPath l (substring s (slash+1) ((String.length s)-(slash+1))) in
      (Origin origin_protocol hdom pv None, p)
    else (Origin "" [] None None, [])

private val splitOrigin : s:string -> n:nat{n < String.length s} -> Tot (origin_tuple)
let splitOrigin s n =
  if (n = 0) then (Origin "" [] None None)
  else 
    match getStringScheme s n with
    | None -> (Origin "" [] None None)
    | Some (scheme,dom) -> if (is_origin_protocol scheme) then
			     let (hdom,pv) = splitHDom dom (* (substring s (n+3) ((String.length s) - (n+3))) *) in
			     (Origin scheme hdom pv None)
			  else (Origin "" [] None None)

private val getStringPathPub : s:string -> n:nat -> Tot (p:(option (public_string * public_string)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
let rec getStringPathPub s n =
  if (String.length s <= n) then None
  else if (substring s n 1 = "/") then Some (substring s 0 n, substring s (n+1) ((String.length s) - (n+1)))
  else getStringPathPub s (n+1)

(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
private val splitPathPub : s:string -> Tot (list string) (decreases (String.length s))
let rec splitPathPub s =
  match getStringPathPub s 0 with
    | None -> [s]
    | Some (f,r) -> f::(splitPathPub r)
    
private val splitOriginPath : s:string -> n:nat{n < String.length s} -> slash:nat{slash >= (n+3) && slash < String.length s} -> Tot csp_origin_path
let splitOriginPath s n slash =
  if (n = 0) then {op_protocol=""; op_host=[]; op_port=None; op_domain=None; op_path=[];op_exact_match_flag=false}
  else
    let scheme = (substring s 0 n) in
    if is_origin_protocol scheme then 
      let (hdom,pv) = splitHDom (substring s (n+3) (slash - (n+3))) in
      let p = splitPathPub (substring s (slash+1) ((String.length s) - (slash + 1))) in
      let em = ((substring s ((String.length s) - 1) 1) = "/") in (* check for last c.aracter *)
      ({op_protocol=scheme;op_host=hdom;op_port=pv;op_domain=None;op_path=p;op_exact_match_flag=em})
    else 
      ({op_protocol=""; op_host=[]; op_port=None; op_domain=None; op_path=[];op_exact_match_flag=false})
            
private val getDirValue : string -> Tot (csp_directive_value)
let getDirValue s = 
  let ts = (trim s) in 
  let ns = String.length ts in 
  if (ns <= 0) then DV_None
  else if (ts = "'self'") then DV_Self
  else if (ts = "'none'") then DV_None
  else if (ts = "*") then DV_Any
  else if (ts = "'unsafe-inline'") then DV_U_Inline
  else if (ts = "'unsafe-eval'") then DV_U_Eval
  else if (ts = "'strict-dynamic'") then DV_St_Dynamic
  else if (ts = "'unsafe-hashed-attributes'") then DV_U_Hashed  
  else if (substring ts (ns - 1) 1 = ":") then let origin_protocol = (substring ts 0 (ns - 1)) in if is_origin_protocol origin_protocol then DV_Scheme origin_protocol else DV_None
  else if (ns > 6 && (substring ts 0 6) = "nonce-") then DV_Nonce (substring ts 6 (ns - 6))
  else if (ns > 7 && (substring ts 0 7) = "sha256-")  then DV_Hash (substring ts 7 (ns - 7))
  else if (ns > 7 && (substring ts 0 7) = "sha384-") then DV_Hash (substring ts 7 (ns - 7))
  else if (ns > 7 && (substring ts 0 7) = "sha512-") then DV_Hash (substring ts 7 (ns - 7))
  else match stringContains ts "://" 0 with 
       | None -> (match stringContains ts "." 0 with
		       | None -> DV_None
		       | Some dot -> (match stringContains ts "/" dot with
					   | None -> DV_Domain (splitDom ts)
					   | Some slash -> DV_None))
       | Some num -> (match stringContains ts "/" (num+3) with
			   | None -> DV_None (*should we also .arse normal origins?*)
			   | Some slash -> DV_Origin (splitOriginPath ts num slash))

private val getDirValList : s:string -> n:nat -> Tot (list csp_directive_value) (decreases (String.length s - n))
let rec getDirValList s n =
  if (String.length s <= n) then []
  else if (substring s n 1) = " " then 
      (getDirValue (substring s 0 n))::(getDirValList (substring s (n+1) ((String.length s)-(n+1))) 0) 
  else getDirValList s (n+1)

private val getSubStringVal : string -> Tot (list csp_directive_value)
let getSubStringVal s = getDirValList (s) 0

private val getDirName : string -> Tot (option csp_directive_name)
let getDirName s = 
  if s = "child-src" then Some CSP_child_src
  else if s = "connect-src" then Some CSP_connect_src
  else if s = "default-src" then Some CSP_default_src 
  else if s = "font-src" then Some CSP_font_src
  else if s = "frame-src" then Some CSP_frame_src
  else if s = "img-src" then Some CSP_img_src
  else if s = "manifest-src" then Some CSP_manifest_src
  else if s = "media-src" then Some CSP_media_src
  else if s = "object-src" then Some CSP_object_src
  else if s = "script-src" then Some CSP_script_src
  else if s = "style-src" then Some CSP_style_src
  else if s = "worker-src" then Some CSP_worker_src
  else if s = "base-uri" then Some CSP_base_uri
  else if s = "plugin-types" then Some CSP_plugin_types
  else if s = "sandbox" then Some CSP_sandbox
  else if s = "disown-opener" then Some CSP_disown_opener
  else if s = "form-action" then Some CSP_form_action
  else if s = "frame-ancestors" then Some CSP_frame_ancestors
  else if s = "navigate-to" then Some CSP_navigate_to
  else None 
  
private val getSubStringCSP : s:string -> n:nat -> Tot (p:(option (csp_directive_name * list csp_directive_value))) (decreases (String.length s - n))
let rec getSubStringCSP s n =
  if (String.length s <= n) then None
  else if (substring s n 1) = " " then 
      (match getDirName (trim (substring s 0 n)) with
	     | None -> None
	     | Some dirName -> (Some (dirName, getSubStringVal (substring s n ((String.length s) - n)))))
  else getSubStringCSP s (n+1)

val getDirectiveFromStringAll : string -> Tot (option csp_directive)
let getDirectiveFromStringAll s = 
  let ns = trim s in 
  if (String.length ns = 0) then None
  else let f = getSubStringCSP ns 0 in
      match f with
      | None -> None
      | Some (n,v) -> Some ({directive_name=n;directive_value=v})
      
(* Rather than checking for isOriginSec, do it statically *)
val hstring_to_curi_ml : l:secrecy_level -> string -> Tot (option (origin_tuple * a_uri l))
let hstring_to_curi_ml l s = 
  match stringContains s "://" 0 with 
  | None -> None 
  | Some num -> (
      match stringContains s "/" (num+3) with
      | None -> let orig = (splitOrigin s num) in 
	       if (is_origin_in_secrecy_level orig l) then (* check if the origin is .art of the secrecy_level - either PublicVal or SecretVal list containing origin *)
		 Some (orig, ({uri_origin=orig;uri_username=(empty_secret_string l);uri_password=(empty_secret_string l);uri_path=[];uri_querystring=[];uri_fragment=(empty_secret_string l)}))
	       else None
      | Some slash -> (
	  match stringContains s "?" (slash+1) with
	  | None -> (
	      match stringContains s "#" (slash+1) with
	      | None -> let (orig,p) = (splitOrigPath l s num slash) in 
		       if (is_origin_in_secrecy_level orig l) then
			 Some (orig, ({uri_origin=orig;uri_username=(empty_secret_string l);uri_password=(empty_secret_string l);uri_path=p;uri_querystring=[];uri_fragment=(empty_secret_string l)}))
		       else None
   	      | Some fragp -> let ns = (substring s 0 fragp) in
			    let (orig, p) = (splitOrigPath l ns num slash) in 
			    let frag = classify_secret_string #PublicVal (substring s (fragp+1) ((String.length s) - (fragp+1))) l in
			    if (is_origin_in_secrecy_level orig l) then
			      Some (orig, ({uri_origin=orig;uri_username=(empty_secret_string l);uri_password=(empty_secret_string l);uri_path=p;uri_querystring=[];uri_fragment=frag}))
			    else None
	      )
	  | Some ques -> (
	      let ns = (substring s 0 ques) in
	      match stringContains s "#" (ques+1) with
	      | None -> let (orig,p) = (splitOrigPath l ns num slash) in 
		       let qs = splitQueryString l (substring s (ques+1) ((String.length s)-(ques+1))) in
		       if (is_origin_in_secrecy_level orig l) then
			 Some (orig, ({uri_origin=orig;uri_username=(empty_secret_string l);uri_password=(empty_secret_string l);uri_path=p;uri_querystring=qs;uri_fragment=(empty_secret_string l)}))
		       else None
  	      | Some fragp -> let (orig,p) = (splitOrigPath l ns num slash) in 
			    let qs = splitQueryString l (substring s (ques+1) (fragp-(ques+1))) in
			    let frag = classify_secret_string #PublicVal (substring s (fragp+1) ((String.length s)-(fragp+1))) l in
			    if (is_origin_in_secrecy_level orig l) then
			      Some (orig, ({uri_origin=orig;uri_username=(empty_secret_string l);uri_password=(empty_secret_string l);uri_path=p;uri_querystring=qs;uri_fragment=frag}))
			    else None)
	))

val stringLemma : l:secrecy_level -> s:string -> Lemma (requires (True)) 
		  (ensures (match hstring_to_curi_ml l s with | None -> true | Some (o, u) -> o = u.uri_origin)) [SMTPat (hstring_to_curi_ml l s)]
let stringLemma l s = ()

private val getSubStrHead : #l:secrecy_level -> s:(secret_string l) -> c:string -> n:nat -> Tot (p:(option (secret_string l * secret_string l)){splitStr (declassify_secret_string s) p}) 
					(decreases (secret_string_length s - n))
let rec getSubStrHead #l s c n =
  if (secret_string_length s <= n) then None
  else if (substring (declassify_secret_string s) n 1) = c then Some (secret_string_substring s 0 (n) , secret_string_substring s (n+1) ((secret_string_length s) - (n+1)))
  else getSubStrHead s c (n+1)

(* Determine commands for substring operations *)
private val getSubStringHead : s:(string) -> n:nat -> Tot (p:(option (public_string * public_string)){splitStr #PublicVal #PublicVal s p}) 
					(decreases (String.length s - n))
let rec getSubStringHead s n =
  if (String.length s <= n) then None
  else if (substring s n 1) = ";" then Some (substring s 0 (n) , substring s (n+1) ((String.length s) - (n+1)))
  else getSubStringHead s (n+1)
    
(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
private val parseAttributesList : s:string -> Tot (list string) (decreases (String.length s))
let rec parseAttributesList s =
  match getSubStringHead s 0 with
    | None -> [s]
    | Some (f,r) -> f::(parseAttributesList r)

(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
private val getDomain : s:string -> Tot (list string) (decreases (String.length s))
let rec getDomain s =
    match getStringDom s 0 with
    | None -> [s]
    | Some (f,r) -> f::(getDomain r)
    
private val getAttribute : s:string -> n:nat -> Tot (option cookie_header_attributes) (decreases (String.length s - n))
let rec getAttribute s n =
  if (String.length s <= n) then (
      if s = "secure" then Some SecureOnly
      else if s = "httponly" then Some HttpOnly
      else None )
  else if (substring s n 1) = "=" then (
      let (name,value) = (substring s 0 n, substring s (n+1) ((String.length s) - (n+1))) in 
      if name = "path" then Some (CookiePath (splitPathPub value))
      else if name = "domain" then Some (CookieDomain (getDomain value))
      else if name = "expires" then Some (Expires value)
      else if name = "max-age" then Some (Max_age value)
      else None )
  else getAttribute s (n+1)

private val parseAttributes : list string -> Tot (list cookie_header_attributes)
let rec parseAttributes ls = 
  match ls with
  | [] -> []
  | hd::tl -> match (getAttribute hd 0) with
	    | None -> (parseAttributes tl)
	    | Some a -> a::(parseAttributes tl)

private val getCookieNameVal : s:string -> n:nat -> Tot (p:(option (string * string))) (decreases (String.length s - n))
let rec getCookieNameVal s n =
  if (String.length s <= n) then None
  else if (substring s n 1) = "=" then Some (substring s 0 n, substring s (n+1) ((String.length s) - (n+1)))
  else getCookieNameVal s (n+1)

private val getCookieData : s:string -> Tot (string * string)
let getCookieData s = 
  match getCookieNameVal s 0 with
  | None -> (s, "")
  | Some (n, v) -> (n, v)

(* FORMAT -- "mt_mop=4:1481209291; domain=.mathtag.com; path=/; expires=Wed, 11-Jan-2017 15:01:05 GMT" *)
val getCookieFromStringAll : l:secrecy_origin_list -> string -> Tot (option (cookie_header l))
let getCookieFromStringAll l s = 
  let ns = trim s in 
  let sec = SecretVal l in 
  if (String.length ns = 0) then None
  else 
    match (getSubStringHead ns 0) with
    | None -> let (n,v) = (getCookieData ns) in     
	     Some ({cookie_header_name=(classify_secret_string #PublicVal n sec);
		  cookie_header_value=(classify_secret_string #PublicVal v sec);
		  cookie_header_attributes_list=[]})
    | Some (f,a) -> 
	let (n,v) = (getCookieData f) in     
	let attr = (parseAttributes (parseAttributesList a)) in
	Some ({cookie_header_name=(classify_secret_string #PublicVal n sec);
	     cookie_header_value=(classify_secret_string #PublicVal v sec);
	     cookie_header_attributes_list=attr})

(* Get cookies' name value *)
val getReqCookie : s:list string -> Tot (list (public_string * public_string))
let rec getReqCookie s =
  match s with
  | [] -> []
  | hd::tl -> (match (getCookieNameVal hd 0) with | None -> (hd,"") | Some (q,v) -> (q,v))::(getReqCookie tl)

(* Multiple cookies *)
(* private val getSubCookie : #l:secrecy_level -> s:(secret_string l) -> n:nat -> Tot (p:(option (secret_string l * secret_string l)){splitStr (declassify_secret_string s) p})  *)
(* 					(decreases (secret_string_length s - n)) *)
(* let rec getSubCookie #l s n = *)
(*   if (secret_string_length s <= n) then None *)
(*   else if substring (declassify_secret_string s) n 1 = "," then Some (secret_string_substring s 0 (n) , secret_string_substring s (n+1) ((secret_string_length s) - (n+1))) *)
(*   else getSubCookie s (n+1) *)

val parseSerialCookie : #l:secrecy_level -> s:secret_string l -> Tot (list (secret_string l)) (decreases (secret_string_length s))
let rec parseSerialCookie #l s =
  match getSubStrHead s "," 0 with
    | None -> [s]
    | Some (f,r) -> [f] (* ::(parseSerialCookie r) *) (* browsers only parse 1st cookie and ignore others -- add others if required *)

(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
val parseSerialAll : #l:secrecy_level -> s:secret_string l -> Tot (list (secret_string l)) (decreases (secret_string_length s))
let rec parseSerialAll #l s =
  match getSubStrHead s ";" 0 with
    | None -> [s]
    | Some (f,r) -> f::(parseSerialAll r)

(* Return the form data from the body *)
val getFormData : #l:secrecy_level -> (secret_string l) -> Tot (querystring l)
let getFormData #l s = splitQueryString l (declassify_secret_string s)

