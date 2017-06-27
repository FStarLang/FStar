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

private val splitStr : #l:secLevel -> #l':secLevel -> s:string -> p:(option (secString l * secString l')) -> Tot bool
let splitStr #l #l' s p =
  match p with 
  | Some (fst, snd) -> (String.length s) > (length snd) 
  | None -> true

private val getStringScheme : s:string -> n:nat -> Tot (p:(option (sc:string * string)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
let rec getStringScheme s n =
  if (String.length s <= (n+3)) then None
  else if (substring s n 3 =  "://") then 
    let scheme = substring s 0 n in Some (scheme , substring s (n+3) ((String.length s) - (n+3)))
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

private val stringContains : s:string -> string -> n:nat -> Tot (p:(option nat){match p with | None -> true | Some po -> (po >= n && po < String.length s)}) 
					       (decreases (String.length s - n))
let rec stringContains s1 s2 n =
  let l1 = String.length s1 in
  let l2 = String.length s2 in
  if (l1 <= n || (l1 - n) < l2) then None
  else if (substring s1 n l2 = s2) then Some n
  else stringContains s1 s2 (n+1)

private val splitHDom : string -> Tot (list string * option port)
let rec splitHDom ts =
  let s = trim ts in 
  match (stringContains s ":" 0) with
  | None -> (splitDom s, None)
  | Some p -> (splitDom (substring s 0 p), Some (int_of_string (substring s (p+1) ((String.length s) - (p+1)))))

private val getStringPath : l:secLevel -> s:string -> n:nat -> Tot (p:(option (secString l * pubString)){splitStr #l #PublicVal s p}) (decreases (String.length s - n))
let rec getStringPath l s n =
  if (String.length s <= n) then None
  else if (substring s n 1 = "/") then (
    if n = 0 then 
      getStringPath l (substring s (n+1) ((String.length s) - (n+1))) 0 (* avoid spurious / *)
    else 
      Some (classify #PublicVal (substring s 0 n) l, substring s (n+1) ((String.length s) - (n+1))))
  else getStringPath l s (n+1)

(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
val splitPath : l:secLevel -> s:string -> Tot (path l) (decreases (String.length s))
let rec splitPath l s =
  match getStringPath l s 0 with
    | None -> [classify #PublicVal s l]
    | Some (f,r) -> f::(splitPath l r)

private val getStringQuery : l:secLevel -> s:string -> n:nat -> Tot (p:(option (secString l * secString l)){splitStr #l #l s p}) (decreases (String.length s - n))
let rec getStringQuery l s n =
  if (String.length s <= n) then None
  else if (substring s n 1 = "=") then Some (classify #PublicVal (substring s 0 n) l, classify #PublicVal (substring s (n+1) ((String.length s) - (n+1))) l)
  else getStringQuery l s (n+1)

private val getStringQS : s:string -> n:nat -> Tot (p:(option (pubString * pubString)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
let rec getStringQS s n =
  if (String.length s <= n) then None
  else if (substring s n 1) = "&" then Some ((substring s 0 n), substring s (n+1) ((String.length s) - (n+1)))
  else getStringQS s (n+1)

private val splitQueryString : l:secLevel -> s:string -> Tot (querystring l) (decreases (String.length s))
let rec splitQueryString l s =
  match getStringQS s 0 with
  | None -> (match (getStringQuery l s 0) with
		  | None -> []
		  | Some (q,v) -> [(q,v)])
  | Some (f,r) -> (match (getStringQuery l f 0) with 
			| None -> (splitQueryString l r)
			| Some (q,v) -> (q,v)::(splitQueryString l r))

private val splitOrigPath : l:secLevel -> s:string -> n:nat{n < String.length s} -> slash:nat{slash >= (n+3) && slash < String.length s} -> Tot (torigin * path l)
let splitOrigPath l s n slash =
  if (n = 0) then (TOrigin "" [] None None, [])
  else 
    let scheme = (substring s 0 n) in 
    if isProtocol scheme then 
      let (hdom,pv) = splitHDom (substring s (n+3) (slash - (n+3))) in
      let p = splitPath l (substring s (slash+1) ((String.length s)-(slash+1))) in
      (TOrigin scheme hdom pv None, p)
    else (TOrigin "" [] None None, [])

private val splitOrigin : s:string -> n:nat{n < String.length s} -> Tot (torigin)
let splitOrigin s n =
  if (n = 0) then (TOrigin "" [] None None)
  else 
    match getStringScheme s n with
    | None -> (TOrigin "" [] None None)
    | Some (scheme,dom) -> if (isProtocol scheme) then
			     let (hdom,pv) = splitHDom dom (* (substring s (n+3) ((String.length s) - (n+3))) *) in
			     (TOrigin scheme hdom pv None)
			  else (TOrigin "" [] None None)

private val getStringPathPub : s:string -> n:nat -> Tot (p:(option (pubString * pubString)){splitStr #PublicVal #PublicVal s p}) (decreases (String.length s - n))
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
    
private val splitOriginPath : s:string -> n:nat{n < String.length s} -> slash:nat{slash >= (n+3) && slash < String.length s} -> Tot origpath
let splitOriginPath s n slash =
  if (n = 0) then {op_prot=""; op_host=[]; op_port=None; op_dom=None; op_path=[];op_em=false}
  else
    let scheme = (substring s 0 n) in
    if isProtocol scheme then 
      let (hdom,pv) = splitHDom (substring s (n+3) (slash - (n+3))) in
      let p = splitPathPub (substring s (slash+1) ((String.length s) - (slash + 1))) in
      let em = ((substring s ((String.length s) - 1) 1) = "/") in (* check for last character *)
      ({op_prot=scheme;op_host=hdom;op_port=pv;op_dom=None;op_path=p;op_em=em})
    else 
      ({op_prot=""; op_host=[]; op_port=None; op_dom=None; op_path=[];op_em=false})
            
private val getDirValue : string -> Tot (dirValue)
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
  else if (substring ts (ns - 1) 1 = ":") then let scheme = (substring ts 0 (ns - 1)) in if isProtocol scheme then DV_Scheme scheme else DV_None
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
			   | None -> DV_None (*should we also parse normal origins?*)
			   | Some slash -> DV_Origin (splitOriginPath ts num slash))

private val getDirValList : s:string -> n:nat -> Tot (list dirValue) (decreases (String.length s - n))
let rec getDirValList s n =
  if (String.length s <= n) then []
  else if (substring s n 1) = " " then 
      (getDirValue (substring s 0 n))::(getDirValList (substring s (n+1) ((String.length s)-(n+1))) 0) 
  else getDirValList s (n+1)

private val getSubStringVal : string -> Tot (list dirValue)
let getSubStringVal s = getDirValList (s) 0

private val getDirName : string -> Tot (option csp_dir_name)
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
  
private val getSubStringCSP : s:string -> n:nat -> Tot (p:(option (csp_dir_name * list dirValue))) (decreases (String.length s - n))
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
      | Some (n,v) -> Some ({dir_name=n;dir_value=v})

(* Rather than checking for isOriginSec, do it statically *)
val hstring_to_curi_ml : l:secLevel -> string -> Tot (option (origin * a_uri l))
let hstring_to_curi_ml l s = 
  match stringContains s "://" 0 with 
  | None -> None 
  | Some num -> (
      match stringContains s "/" (num+3) with
      | None -> let orig = (splitOrigin s num) in 
	       if (isOriginSec orig l) then
		 Some (orig, ({c_origin=orig;c_uname=(emptyString l);c_pwd=(emptyString l);c_path=[];c_querystring=[];c_fragment=(emptyString l)}))
	       else None
      | Some slash -> (
	  match stringContains s "?" (slash+1) with
	  | None -> (
	      match stringContains s "#" (slash+1) with
	      | None -> let (orig,p) = (splitOrigPath l s num slash) in 
		       if (isOriginSec orig l) then
			 Some (orig, ({c_origin=orig;c_uname=(emptyString l);c_pwd=(emptyString l);c_path=p;c_querystring=[];c_fragment=(emptyString l)}))
		       else None
   	      | Some fragp -> let ns = (substring s 0 fragp) in
			    let (orig, p) = (splitOrigPath l ns num slash) in 
			    let frag = classify #PublicVal (substring s (fragp+1) ((String.length s) - (fragp+1))) l in
			    if (isOriginSec orig l) then
			      Some (orig, ({c_origin=orig;c_uname=(emptyString l);c_pwd=(emptyString l);c_path=p;c_querystring=[];c_fragment=frag}))
			    else None
	      )
	  | Some ques -> (
	      let ns = (substring s 0 ques) in
	      match stringContains s "#" (ques+1) with
	      | None -> let (orig,p) = (splitOrigPath l ns num slash) in 
		       let qs = splitQueryString l (substring s (ques+1) ((String.length s)-(ques+1))) in
		       if (isOriginSec orig l) then
			 Some (orig, ({c_origin=orig;c_uname=(emptyString l);c_pwd=(emptyString l);c_path=p;c_querystring=qs;c_fragment=(emptyString l)}))
		       else None
  	      | Some fragp -> let (orig,p) = (splitOrigPath l ns num slash) in 
			    let qs = splitQueryString l (substring s (ques+1) (fragp-(ques+1))) in
			    let frag = classify #PublicVal (substring s (fragp+1) ((String.length s)-(fragp+1))) l in
			    if (isOriginSec orig l) then
			      Some (orig, ({c_origin=orig;c_uname=(emptyString l);c_pwd=(emptyString l);c_path=p;c_querystring=qs;c_fragment=frag}))
			    else None)
	))

private val getSubStrHead : #l:secLevel -> s:(secString l) -> c:string -> n:nat -> Tot (p:(option (secString l * secString l)){splitStr (declassify s) p}) 
					(decreases (length s - n))
let rec getSubStrHead #l s c n =
  if (length s <= n) then None
  else if (substring (declassify s) n 1) = c then Some (substr s 0 (n) , substr s (n+1) ((length s) - (n+1)))
  else getSubStrHead s c (n+1)

(* Determine commands for substring operations *)
private val getSubStringHead : s:(string) -> n:nat -> Tot (p:(option (pubString * pubString)){splitStr #PublicVal #PublicVal s p}) 
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
    
private val getAttribute : s:string -> n:nat -> Tot (p:(option cookieAttribute)) (decreases (String.length s - n))
let rec getAttribute s n =
  if (String.length s <= n) then (
      if s = "secure" then Some SecureOnly
      else if s = "httponly" then Some HttpOnly
      else None )
  else if (substring s n 1) = "=" then (
      let (name,value) = (substring s 0 n, substring s (n+1) ((String.length s) - (n+1))) in 
      if name = "path" then Some (Cpath (splitPathPub value))
      else if name = "domain" then Some (Cdomain (getDomain value))
      else if name = "expires" then Some (Expires value)
      else if name = "max-age" then Some (Max_age value)
      else None )
  else getAttribute s (n+1)

private val parseAttributes : list string -> Tot (p:(list cookieAttribute))
let rec parseAttributes l = 
  match l with
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
val getCookieFromStringAll : l:secLevel -> string -> Tot (option (cookieHeader' l))
let getCookieFromStringAll l s = 
  let ns = trim s in 
  if (String.length ns = 0) then None
  else 
    match (getSubStringHead ns 0) with
    | None -> let (n,v) = (getCookieData ns) in     
	     Some ({cookie_name=(classify #PublicVal n l);cookie_value=(classify #PublicVal v l);cookie_attr=[]})
    | Some (f,a) -> 
	let (n,v) = (getCookieData f) in     
	let attr = (parseAttributes (parseAttributesList a)) in
	Some ({cookie_name=(classify #PublicVal n l);cookie_value=(classify #PublicVal v l);cookie_attr=attr})

(* Get cookies' name value *)
val getReqCookie : s:list string -> Tot (list (pubString * pubString))
let rec getReqCookie s =
  match s with
  | [] -> []
  | hd::tl -> (match (getCookieNameVal hd 0) with | None -> (hd,"") | Some (q,v) -> (q,v))::(getReqCookie tl)

(* Multiple cookies *)
(* private val getSubCookie : #l:secLevel -> s:(secString l) -> n:nat -> Tot (p:(option (secString l * secString l)){splitStr (declassify s) p})  *)
(* 					(decreases (length s - n)) *)
(* let rec getSubCookie #l s n = *)
(*   if (length s <= n) then None *)
(*   else if substring (declassify s) n 1 = "," then Some (substr s 0 (n) , substr s (n+1) ((length s) - (n+1))) *)
(*   else getSubCookie s (n+1) *)

val parseSerialCookie : #l:secLevel -> s:secString l -> Tot (list (secString l)) (decreases (length s))
let rec parseSerialCookie #l s =
  match getSubStrHead s "," 0 with
    | None -> [s]
    | Some (f,r) -> [f] (* ::(parseSerialCookie r) *) (* browsers only parse 1st cookie and ignore others -- add others if required *)

(* Takes a string and returns a list of strings with delimiter being ";" in the string *)
val parseSerialAll : #l:secLevel -> s:secString l -> Tot (list (secString l)) (decreases (length s))
let rec parseSerialAll #l s =
  match getSubStrHead s ";" 0 with
    | None -> [s]
    | Some (f,r) -> f::(parseSerialAll r)

(* Return the form data from the body *)
val getFormData : #l:secLevel -> (secString l) -> Tot (querystring l)
let getFormData #l s = splitQueryString l (declassify s)
