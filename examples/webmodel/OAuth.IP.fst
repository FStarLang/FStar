(*
  Defines the functionality of the IP in the OAuth protocol
*)
module OAuth.IP

open FStar.All
open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.StringFunctions
open Browser.Model.Interface
open Network.Interface
open OAuth.Datatypes

#reset-options "--z3rlimit 100"

(* ***** IP.COM ***** *)
let ipurl = ({c_origin=ipori;c_uname=emptyString (SecretVal [ipori]);c_pwd=emptyString (SecretVal [ipori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [ipori])})
let ipuri = mk_uri ipurl

(* This should be the same for the RP and the IP - pre-registered *)
val ipCD : ref (clientData) (* for ipori *)
let ipCD = ST.alloc [(rpori, clientIDRPIP,  clientSecretRPIP)]

(* The access token to be sent to the RP *)
val ipTL : ref (tokenList) (* for ipori *)
let ipTL = ST.alloc []

(* create a code list for the IP *)
val ipCL : ref (codeList) (* for ipori *)
let ipCL = ST.alloc []

(* get the client_id for the origin *)
val getIPClientID : torigin -> ML (option (s:secretVal{Secret?.s s = PublicVal}))
let getIPClientID t = getClientID (!ipCD) t  

(* get the RP's origin using the client_id *)
val getRPOrigin : secretVal -> ML torigin
let getRPOrigin s = getCDOrigin (!ipCD) s

type uList = (list (secString (SecretVal [ipori]) * secString (SecretVal [ipori]) * list (secString (SecretVal [ipori]))))
let userList:uList = [((classify #PublicVal "usernameU" (SecretVal [ipori])), (classify #PublicVal "passwordP" (SecretVal [ipori])), [])]

val addCookieList : #s:secLevel -> list (secString s * secString s * (list (secString s))) -> secString s -> secString s -> secString s -> 
		    Tot (list (secString s * secString s * (list (secString s))))
let rec addCookieList #s ul u p c =
  match ul with
    | [] -> []
    | (su,sp,sc)::tl -> if (u = su) && (p = sp) then (su,sp,c::sc)::tl
		      else (su,sp,sc)::(addCookieList #s tl u p c)

(* check the validity of the session id *)
val isValid : #l:secLevel -> list (secString l) -> string -> Tot bool
let rec isValid #l ls s = 
  match ls with
    | [] -> false
    | hd::tl -> eqString (hd) s || isValid tl s
  
val isValidSessionId : uList -> string -> Tot bool
let rec isValidSessionId sl s = 
  match sl with
    | [] -> false
    | (_,_,c)::tl -> isValid c s || isValidSessionId tl s 

(* check the validity of the password *)
val isValidPwd : #l:secLevel -> #l':secLevel -> uList -> (secString l) -> (secString l') -> Tot bool
let rec isValidPwd #l #l' sl su sp = 
  match sl with
    | [] -> false
    | (u,p,_)::tl -> if (s_equal u su) then (s_equal p sp) else isValidPwd tl su sp 
    
val isAlreadyLoggedIn : uList -> list (string * string) -> Tot bool
let isAlreadyLoggedIn ul l = isValidSessionId ul (getVal #PublicVal l "_ipsid")

val authenticateUser : uList -> req:browserRequest -> Tot bool
let authenticateUser ul req =
  let s = (BRequest?.rf req).reqbody in
  let qs = getFormData s in
  isValidPwd ul (getQSVal qs "user") (getQSVal qs "pwd")


val ipAuthResp : #rsl:secLevel -> ruri:c_uri rsl -> r:browserRequest{BRequest?.rsl r = rsl} -> ML (resp:actResponse{requestResponseValid r resp})
let ipAuthResp #rsl ruri r =
  let cid = declassify (getQSVal ruri.c_querystring "client_id") in
  let reduri = s_secstring_uri #PublicVal (declassify (getQSVal ruri.c_querystring "redirect_uri")) in 
  match reduri with 
  | None -> (print_string ("Error:getIPAuthResp - getRPOrigin \n");defErrResponse ipori (BRequest?.rf r).reqb)
  | Some (o,red) -> (* && (getRPOrigin cid = (s_getURI (Some?.v reduri)).c_origin) ) then ( check for origins to be the same? *)
	 let urisl = SecretVal [o] in
	 (* let rori = declassify (getQSVal #rsl ruri.c_querystring "origin") in *)
	 let token = classify #PublicVal (declassify (getQSVal #rsl ruri.c_querystring "csrftoken")) urisl in
	 let authcode = genSecret urisl in
	 let ipREP = curi_to_hstring ({c_origin=red.c_origin;c_uname=classify red.c_uname urisl;c_pwd=classify red.c_pwd urisl;c_path=classifyPath red.c_path urisl;c_querystring=[(classify #PublicVal "authcode" urisl, getSecret (authcode));(classify #PublicVal "csrftoken" urisl, token);(classify #PublicVal "Issuer" urisl,classify #PublicVal (origin_to_string ipori) urisl)];c_fragment=emptyString urisl}) in
	 let stateToken = Secret urisl token in 
	 let rduri = mk_uri red in 
	 ipCL := (o, stateToken, authcode, rduri)::(!ipCL);
	 (
	 (* ******* For redirect-attack, change the respcode here to 307 or 308 ******* *)
	 let ck = genSecret (SecretVal [ipori]) in
	 let chead = (if (emptyList (getReqCookie (s_getBReqHeaderValue r "Cookie"))) then [("Set-Cookie", (mk_svheaderval ck))] else []) in
	 let nhead = ("Location", (mk_headerval #urisl ipREP))::chead in
	 ActResponse (SecretVal [o;ipori]) ({respori=ipori;respdest=(BRequest?.rf r).reqb;resptype="default";respcode=303;respurl=[];resphead=nhead;respbody=(emptyString (SecretVal [o;ipori]));resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=urisl})
	 )
	 
(* authentication of the user - return the authcode along with the state to the RP *)
val getIPAuthResp : r:browserRequest -> ML (resp:actResponse{requestResponseValid r resp})
let getIPAuthResp r =
    let rsl = (BRequest?.rsl r) in
    let ruri = s_getURI (firstElement (BRequest?.rf r).requrl) in
    let ul = userList in
    if ((isAlreadyLoggedIn ul (getReqCookie (s_getBReqHeaderValue r "Cookie"))) ||
       ((BRequest?.rf r).reqm = "POST" && (authenticateUser ul r))) then
       ipAuthResp #rsl ruri r
    else if ((BRequest?.rf r).reqm = "GET") then (* send login form for authentication *)
    (
       let cid = declassify (getQSVal ruri.c_querystring "client_id") in
       if (getRPOrigin (Secret PublicVal cid) = s_getBRequestOrigin r) then
	 ActResponse (SecretVal [ipori]) ({respori=ipori;respdest=(BRequest?.rf r).reqb;resptype="default";respcode=200;respurl=[];resphead=[];respbody=(emptyString (SecretVal [ipori]));resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=PublicVal})
       else
	 defErrResponse ipori (BRequest?.rf r).reqb
    )
    else
	(print_string ("Error:getIPAuthResp \n"); defErrResponse ipori (BRequest?.rf r).reqb) (* Authenticate user - send a redirect response to authentication page *)


(* check the authcode from the RP and then send the access_token *)
val getIPTokenResp : r:serverRequest -> ML (resp:actResponse{sRequestResponseValid r resp})
let getIPTokenResp r =
    let urisl = s_getReqURISecLevel r in
    let ruri = s_getRequestURI r in
    let cid = declassify (getQSVal ruri.c_querystring "client_id") in
    let reduri = secstring_to_uri #urisl (getQSVal ruri.c_querystring "redirect_uri") in
    let rorig = getRPOrigin (Secret PublicVal cid) in
    let olist = (SecretVal [ipori;rorig]) in
    let cs = (getQSVal ruri.c_querystring "client_secret") in
    let code = (getQSVal ruri.c_querystring "authcode") in
    let clcode = (getCLCode !ipCL rorig) in
    let cdsec = (getCDSecret !ipCD rorig) in
    let red_uri = (getCLRedURI !ipCL rorig) in
    match clcode, cdsec with
    | None, _ -> defErrResponse ipori rorig
    | _, None -> defErrResponse ipori rorig
    | Some ccode, Some csec -> (
	   if ((rorig = s_getRequestOrigin r) && (compareSecret (mk_secretval code) ccode) && (compareSecret (mk_secretval cs) csec) &&
	      (Some? reduri) && (Some? red_uri) && (Some?.v red_uri = Some?.v reduri)) then (
	      let tokenS = genSecret olist in
	      ipCL := (getNewCodeList !ipCL rorig ccode (Some?.v red_uri));
	      ipTL := (rorig, tokenS)::(!ipTL);
	      let atoken = getSecret tokenS in
	      let rbody = strcat (classify #PublicVal "access_token:" olist) atoken in
	      let ipResp = ActResponse olist ({respori=ipori;respdest=rorig;resptype="default";respcode=200;respurl=[];resphead=[];respbody=rbody;resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=PublicVal}) in
	      ipResp)
	   else
	      defErrResponse ipori rorig)


val ipReqResp : req:anyRequest -> ML (ret:retReqResp{isValidRetResp req ret})
let ipReqResp req =
  match req with 
  | BrowserRequest r ->
      let urisl = (BRequest?.rsl r) in
      let ruri = (firstElement (BRequest?.rf r).requrl) in (* get the request url *)
      if (getPort (ruri)) = (Some 443) then (* Only accept secure connections (HTTPS) *)
      (
	if (checkEP r "authEP") then (* check for cookies and then either get user-data or send redirection url *)
	  (RetResponse (getIPAuthResp r))
	else (RetResponse (defErrResponse ipori (BRequest?.rf r).reqb))
      )
      else
	(RetResponse (defErrResponse ipori (BRequest?.rf r).reqb))
  | ServerRequest sr ->
      let urisl = s_getReqURISecLevel sr in
      let ruri = s_getRequestURI #urisl sr in (* get the request url *)
      if (getPort (mk_uri ruri)) = (Some 443) then (* Only accept secure connections (HTTPS) *)
      (
	if (checkSEP sr "tokenEP") then (RetResponse (getIPTokenResp sr))
	else (RetResponse (defErrResponse ipori (SRequest?.srf sr).sreqo))
      )
      else
	(RetResponse (defErrResponse ipori (SRequest?.srf sr).sreqo))
