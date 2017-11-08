module OAuth.Min

open Web.Origin
open Secret.Core

assume val csrfToken : field
assume val code : field
assume val ipid : field
assume val orig:field

assume val loggedIn : state -> origin -> origin -> Tot bool

assume val getOrigin : string -> Tot origin
assume val toString : o:origin -> Tot (s:string{getOrigin s = o})

(* Honest user does not send the code or csrftoken to the RP by entering the value in url/navigating window *)
assume val userRequestOAuth : st:state -> b:oorigin -> s:torigin -> h:(validRequest st b s) -> 
		       Lemma (requires (isUserRequest st h)) (ensures (None? (getSecret #st #b #s h code) /\ None? (getSecret h csrfToken)))

(* Honest IP does not send the code directly to the RP? *)
assume val originRequestOAuthN : st:state -> b:oorigin -> s:torigin -> o:torigin -> h:(validRequest st b s) ->
			 Lemma (requires (isOriginRequest st h o /\ Some? (getSecret #st #b #s h orig) /\
					 eq_secret (create [b;s;o] (toString o)) (Some?.v (getSecret #st #b #s h orig))))
			       (ensures (None? (getSecret h code)))

(* Honest IP sends the code and ipid to the RP *)
assume val originRequestOAuthP : st:state -> b:oorigin -> s:torigin -> o:torigin -> h:(validRequest st b s) ->
			 Lemma (requires (isOriginRequest st h o /\ Some? (getSecret #st #b #s h orig) /\ Some? (getSecret #st #b #s h ipid) /\ 
					 not (eq_secret (create [b;s;o] (toString o)) (Some?.v (getSecret #st #b #s h orig)))))
			       (ensures ((eq_secret (create [b;s;o] (toString o)) (Some?.v (getSecret #st #b #s h ipid))) /\ (loggedIn st b o)))

(* val csrfTokenLemma : st:state -> b:oorigin -> rp:torigin -> ip:torigin -> s':torigin -> 
			r: validRequest st b rp{isOriginRequest st r s' /\ (Some? (getSecret r csrfToken))} -> *)
(* 		     csrf:secret{eq_secret csrf (Some?.v (getSecret r csrfToken))} -> *)
(* 		     Lemma (requires (isReader st csrf s')) (ensures ((s' = ip) \/ (dishonest st b) \/ (dishonest st rp) \/ (dishonest st ip))) *)

assume val csrfTokenLemma : st:state -> b:oorigin -> rp:torigin -> ip:torigin -> s':torigin -> csrf:secret ->
		     Lemma (requires (isReader st csrf s')) (ensures ((s' = ip) \/ (dishonest st b) \/ (dishonest st rp) \/ (dishonest st ip)))

assume val authCodeLemma : st:state -> b:oorigin -> rp:torigin -> ip:torigin -> s':torigin -> csrf:secret -> acode:secret ->
		    Lemma (requires (isReader st acode s' /\ isReader st acode ip)) (ensures (s' = ip))

assume val oauthLemma : st:state -> b:oorigin -> rp:torigin -> ip:torigin -> csrf:secret -> acode:secret -> r: validRequest st b rp ->
		 Lemma (requires (True)) (ensures ((isOriginRequest st r ip /\ (Some? (getSecret r code)) /\ eq_secret acode (Some?.v (getSecret r code)) /\ loggedIn st b ip)
				      \/ dishonest st b \/ dishonest st rp \/ (dishonest st ip /\ isReader st acode ip)))

(* send the initial login redirect to the IP from the RP *)
val rpLoginIPAuth : #st:state -> #b:oorigin -> #s:torigin -> r:validRequest st b s -> token:secret -> Tot (option secret * response) 
let rpLoginIPAuth #st #b #s r token =
  match (getSecret r ipid) with
  | None -> (None, Resp "ok" None None)
  | Some ipS -> 
      let ipori = getOrigin (retrieve ipS) in 
      (Some token, Resp "redirect" (Some ipori) (Some [token]))

(* Compact authcode resend method for the RP *)
val rpReqCodeEP : #st:state -> #b:oorigin -> #s:torigin -> r:validRequest st b s -> secret -> Tot ((s:(option secret)) * response) 
let rpReqCodeEP #st #b #s r sec =
  match (getSecret r code) with
  | None -> (None, Resp "ok" None None) 
  | Some acode -> (
      match (getSecret r csrfToken) with
      | None -> (Some acode, Resp "error" None None)
      | Some ct -> if eq_secret ct sec then 
		     (Some acode, Resp "ok" None None)
		  else (Some acode, Resp "error" None None))

(* ip send authcode and csrftoken for a logged in browser at s *)
val ipAuthResp : #st:state -> #b:oorigin -> #s:torigin -> r:validRequest st b s{loggedIn st b s} -> ac:secret -> Tot (option secret * response)
let ipAuthResp #st #b #s r ac =
  match (getSecret r csrfToken) with
  | None -> (None, Resp "error" None None)
  | Some ct -> (
      match (getSecret r orig) with
      | None -> (None, Resp "error" None None)
      | Some rpS -> 
	  let rpori = getOrigin (retrieve rpS) in 
	  (Some ac, Resp "redirect" (Some rpori) (Some [ac;ct])))

(* check the authcode from the RP and then send the access_token *)
val getIPTokenResp : #st:state -> #rp:torigin -> #ip:torigin -> r:validRequest st rp ip -> secret -> secret -> Tot (option secret * response) 
let getIPTokenResp #st #b #s r sec at =
  match (getSecret r code) with
  | None -> (None, Resp "ok" None None) 
  | Some acode -> (
      match (getSecret r orig) with
      | None -> (None, Resp "error" None None)
      | Some rpS -> 
	  let rpori = getOrigin (retrieve rpS) in 
	  if eq_secret acode sec then 	  
	    (Some at, Resp "ok" None (Some [at]))
	  else (None, Resp "error" None None))






assume val oauthState : state
assume val rp : torigin
assume val ip : torigin 
assume val browser : oorigin

val ipSec : secret
let ipSec = create [browser;rp;ip] (toString ip)

assume val authcode : (s:secret{readers s = [browser;rp;ip]})
assume val csrfT : (s:secret{readers s = [browser;rp;ip]})
assume val atoken : (s:secret{readers s = [rp;ip]})

assume val browserRPInit : r:(validRequest oauthState browser rp){(Some? (getSecret r ipid)) /\ (eq_secret ipSec (Some?.v (getSecret r ipid)))}
assume val browserIPLogin : t:secret -> r:(validRequest oauthState browser ip){loggedIn oauthState browser ip /\ (Some? (getSecret r csrfToken)) /\ 
				       (eq_secret t (Some?.v (getSecret r csrfToken)))}
assume val browserRPCode : r:(validRequest oauthState browser rp){(Some? (getSecret r ipid)) /\ (eq_secret ipSec (Some?.v (getSecret r ipid)))}
assume val rpIPCode : c:secret -> r:(validRequest oauthState rp ip){(Some? (getSecret r code)) /\ (eq_secret c (Some?.v (getSecret r code)))}

assume val csrfIPToken : s:secret{(Some? (getSecret browserRPCode csrfToken)) /\ (eq_secret s (Some?.v (getSecret browserRPCode csrfToken)))}

let main =
  let (s, r) = rpLoginIPAuth browserRPInit csrfT in 
  match s with
  | None -> ()
  | Some ct -> 
      if (Resp?.resptype r) = "redirect" then 
	(let (c, rip) = ipAuthResp (browserIPLogin ct) authcode in
	 if (Resp?.resptype rip) = "redirect" then 
	   (let (_, rrp) = rpReqCodeEP browserRPCode csrfT in 
	   let (_, _) = getIPTokenResp (rpIPCode authcode) authcode atoken in
	   ()
	   )
	 else () (* nothing to do here *)
	)
      else () (* nothing to do here *)
