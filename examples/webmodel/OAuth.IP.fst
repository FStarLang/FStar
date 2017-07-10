module OAuth.IP

open FStar.All
open FStar.Heap
open FStar.IO
open Web.Origin
open Web.URI
open Secret.SecString
open Browser.AuxiliaryDatatypes
open Browser.Datatypes
open AuxiliaryFunctions
open Browser.StringFunctions
open Browser.Model.Interface
open NetworkRequestInterface
open OAuth.Datatypes

(* ***** IP.COM ***** *)
let ipurl = ({c_origin=ipori;c_uname=emptyString (SecretVal [ipori]);c_pwd=emptyString (SecretVal [ipori]);c_path=[];c_querystring=[];c_fragment=emptyString (SecretVal [ipori])})
let ipuri = mk_uri ipurl

val checkIPReq : req:request -> Tot (b:bool)
let checkIPReq req =
  match (Request?.rsl req) with
  | PublicVal -> true
  | SecretVal ol -> List.mem ipori ol

val ipReqLemma : req:request -> Lemma (requires (checkIPReq req)) (ensures (restricts (Request?.rsl req) (SecretVal [ipori]))) [SMTPat (checkIPReq req)]
let ipReqLemma req = ()

(* check the validity of the session id *)
val isValid : #l:secLevel -> list (secString l) -> string -> Tot bool
let rec isValid #l ls s = 
  match ls with
    | [] -> false
    | hd::tl -> eqString (hd) s || isValid tl s
  
val isValidSessionId : #l:secLevel -> uList l -> string -> Tot bool
let rec isValidSessionId #l sl s = 
  match sl with
    | [] -> false
    | (_,_,c)::tl -> isValid c s || isValidSessionId tl s 

(* check the validity of the password *)
val isValidPwd : #l:secLevel -> #l':secLevel -> uList (SecretVal [ipori]) -> (secString l) -> (secString l') -> Tot bool
let rec isValidPwd #l #l' sl su sp = 
  match sl with
    | [] -> false
    | (u,p,_)::tl -> if (s_equal u su) then (s_equal p sp) else isValidPwd tl su sp 
    
val isAlreadyLoggedIn : uList (SecretVal [ipori]) -> list (string * string) -> Tot bool
let isAlreadyLoggedIn ul l = isValidSessionId ul (getVal #PublicVal l "_ipsid")

val authenticateUser : uList (SecretVal [ipori]) -> req:request -> Tot bool
let authenticateUser ul req =
  let s = (s_getRequestBody #(Request?.rsl req) req) in
  let qs = getFormData s in
  isValidPwd ul (getQSVal qs "user") (getQSVal qs "pwd")
		    
(* authentication of the user - return the authcode along with the state to the RP *)
val getIPAuthResp : r:request -> ML (resp:actResponse{requestResponseValid r resp})
let getIPAuthResp r =
    let rsl = s_getReqURISecLevel r in
    let ruri = s_getRequestURI r in
    let ul = !userList in 
    if ((isAlreadyLoggedIn ul (getReqCookie (s_getReqHeaderValue r "Cookie"))) ||
       ((Request?.rf r).reqm = "POST" && (authenticateUser ul r))) then
       let cid = declassify (getQSVal ruri.c_querystring "client_id") in
       let reduri = s_secstring_uri #PublicVal (declassify (getQSVal ruri.c_querystring "redirect_uri")) in 
       match reduri with 
       | None -> (print_string ("Error:getIPAuthResp - getRPOrigin \n");defErrResponse)
       | Some (o,red) -> (* && (getRPOrigin cid = (s_getURI (Some?.v reduri)).c_origin) ) then ( check for origins to be the same? *)
	 let urisl = SecretVal [o] in
	 let rori = declassify (getQSVal #rsl ruri.c_querystring "origin") in
	 let token = classify #PublicVal (declassify (getQSVal #rsl ruri.c_querystring "csrftoken")) urisl in
	 let authcode = genSecret urisl in
	 let ipREP = curi_to_hstring ({c_origin=red.c_origin;c_uname=classify red.c_uname urisl;c_pwd=classify red.c_pwd urisl;c_path=classifyPath red.c_path urisl;c_querystring=[(classify #PublicVal "authcode" urisl, getSecret (authcode));(classify #PublicVal "csrftoken" urisl, token);(classify #PublicVal "IP" urisl,classify #PublicVal (origin_to_string ipori) urisl)];c_fragment=emptyString urisl}) in
	 let stateToken = Secret urisl token in 
	 let rduri = mk_uri red in
	 ipCL := (o, stateToken, authcode, rduri)::(!ipCL);
	 (
	 (* ******* For redirect-attack, change the respcode here to 307 or 308 ******* *)
	 let ck = genSecret (SecretVal [ipori]) in
	 let chead = (if (emptyList (getReqCookie (s_getReqHeaderValue r "Cookie"))) then [("Set-Cookie", (mk_svheaderval ck))] else []) in
	 let nhead = ("Location", (mk_headerval #urisl ipREP))::chead in
	 ActResponse (SecretVal [o;ipori]) ({resptype="default";respcode=303;respurl=[];resphead=nhead;respbody=(emptyString (SecretVal [o;ipori]));resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=urisl})
	 )	 
    else if ((Request?.rf r).reqm = "GET") then (* send login form for authentication *)
    (
       let cid = declassify (getQSVal ruri.c_querystring "client_id") in
       if (getRPOrigin cid = s_getRequestOrigin r) then 
	 ActResponse (SecretVal [ipori]) ({resptype="default";respcode=200;respurl=[];resphead=[];respbody=(emptyString (SecretVal [ipori]));resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=PublicVal})
       else
	 defErrResponse
    )
    else
	(print_string ("Error:getIPAuthResp \n"); defErrResponse) (* Authenticate user - send a redirect response to authentication page *)
	
(* check the authcode from the RP and then send the access_token *)
val getIPTokenResp : r:request -> ML (resp:actResponse{requestResponseValid r resp})
let getIPTokenResp r =
    let urisl = s_getReqURISecLevel r in
    let ruri = s_getRequestURI r in
    let cid = declassify (getQSVal ruri.c_querystring "client_id") in
    let reduri = secstring_to_uri #urisl (getQSVal ruri.c_querystring "redirect_uri") in
    let rorig = getRPOrigin cid in
    let olist = (SecretVal [ipori;rorig]) in
    let cs = (getQSVal ruri.c_querystring "client_secret") in
    let code = (getQSVal ruri.c_querystring "authcode") in
    let clcode = (getCLCode !ipCL rorig) in
    let cdsec = (getCDSecret !ipCD rorig) in
    let red_uri = (getCLRedURI !ipCL rorig) in
    match clcode, cdsec with
    | None, _ -> defErrResponse
    | _, None -> defErrResponse
    | Some ccode, Some csec -> (
	   if ((rorig = s_getRequestOrigin r) && (compareSecret (mk_secretval code) ccode) && (compareSecret (mk_secretval cs) csec) &&
	      (Some? reduri) && (Some? red_uri) && (Some?.v red_uri = Some?.v reduri)) then (
	      let tokenS = genSecret olist in
	      ipCL := (getNewCodeList !ipCL rorig ccode (Some?.v red_uri));
	      ipTL := (rorig, tokenS)::(!ipTL);
	      let atoken = getSecret tokenS in 
	      let rbody = strcat (classify #PublicVal "access_token:" olist) atoken in
	      let ipResp = ActResponse olist ({resptype="default";respcode=200;respurl=[];resphead=[];respbody=rbody;resptrail=[];respHTTPS="modern";respCSP=cspPol;respCORS=[];resploc=None;respRedSec=PublicVal}) in
	      ipResp)
	   else
	      defErrResponse)

val ipReqResp : req:request -> ML (ret:retReqResp{isValidRetResp req ret})
let ipReqResp r =
    let urisl = s_getReqURISecLevel r in
    let ruri = s_getRequestURI #urisl r in (* get the request url *)
    if checkIPReq r && (getPort (mk_uri ruri)) = (Some 443) then (* Only accept secure connections (HTTPS) *)
    (
      if (checkEP r "authEP") then (* check for cookies and then either get user-data or send redirection url *)
	(RetResponse (getIPAuthResp r))
      else if (checkEP r "tokenEP") then (RetResponse (getIPTokenResp r))
      else (RetResponse defErrResponse)
      )
    else
      (RetResponse defErrResponse)
