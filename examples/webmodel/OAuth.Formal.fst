module OAuth.Formal.Test

type http_request
type http_response
type param
type header
type body
type uri
type origin = string
type uid = string
type nonce

assume val eq_uri: uri -> uri -> bool // Make sure URIs are public

// We will check by typing that a nonce of type "nonce idx"
// can never be sent to principals other than idx.uid, idx.rp, idx.ip

// HTTP Fetch
type index 
assume val public_index: index
assume val can_send: i:index -> i':index -> GTot Type
assume val includes: i:index -> o:origin -> GTot Type
assume val index_add: idx:index -> rp:origin -> i:index{includes i rp /\ can_send i idx}
assume val index2 : o1:origin -> o2:origin -> i:index{includes i o1 /\ includes i o2}

assume val nonce_index: nonce -> Tot index
assume val eq_nonce: x:nonce -> y:nonce -> b:bool{b ==> nonce_index x == nonce_index y}

assume val param_index: param -> GTot index
type pub_param = p:param{param_index p == public_index}

assume val header_index: header -> GTot index
type pub_header = h:header{header_index h == public_index}

assume val body_index: body -> GTot index
type pub_body = b:body{body_index b == public_index}

assume val can_send_public: i:index ->  Lemma 
	   (requires True)
	   (ensures (can_send public_index i))
	   [SMTPat (can_send public_index i)]

assume val can_send_self: i:index ->  Lemma 
	   (requires True)
	   (ensures (can_send i i))
	   [SMTPat (can_send i i)]

assume val can_send_origin: i:index -> i':index -> o:origin -> Lemma 
	   (requires (can_send i i' /\ i `includes` o))
	   (ensures (can_send i (index_add i' o)))
	   [SMTPat (can_send i i');
	    SMTPat (i `includes` o)]

type indexed_parameters (idx:index) = list (p:param{can_send (param_index p) idx})

assume val uri_index: uri -> GTot index
type pub_uri = u:uri{uri_index u == public_index}
assume val mk_uri: #idx:index -> origin -> path:string -> indexed_parameters idx  -> u:uri{uri_index u == idx}
assume val uri_origin: uri -> origin
assume val add_parameters: #idx:index -> u:uri{can_send (uri_index u) idx}  -> indexed_parameters idx -> u':uri{uri_origin u == uri_origin u' /\ uri_index u' == idx}

assume val request_uri: http_request -> uri
assume val request_path: http_request -> string
assume val request_parameters: #req_idx:index -> http_request ->  indexed_parameters req_idx	      

assume val request_method: http_request -> string
			      
assume val request_origin_header: http_request -> string
assume val request_cookie_header: http_request -> nonce
assume val request_body: http_request -> body
assume val request_authorization_header: http_request -> option (string * nonce)


assume val mk_referrer_policy_header: string -> pub_header
assume val mk_set_cookie_header: n:nonce -> h:header{header_index h == nonce_index n}
assume val mk_authorization_header: uid:string -> p:nonce -> h:header{header_index h == nonce_index p}


assume val mk_request: #req_idx:index -> 
		       method:string -> 
		       request_uri:uri{includes req_idx (uri_origin request_uri) /\
				       can_send (uri_index request_uri) req_idx }  -> 
		       list (h:header{can_send (header_index h) req_idx}) -> 
		       b:body{body_index b == req_idx} -> 
		       http_request
assume val mk_response: #resp_idx:index -> 
		       list (h:header{can_send (header_index h) resp_idx}) -> 
		       b:body{body_index b == resp_idx} -> 
		       http_response
		       
assume val mk_redirect_response: #red_idx:index ->
		       u:uri {includes red_idx (uri_origin u) 
		              /\ can_send (uri_index u) red_idx } -> 
		       list header -> // Aha, bug: (h:header{can_send (header_index h) red_idx}) -> 
		       http_response

assume val response_body: http_response -> body


assume val mk_body: #idx:index -> indexed_parameters idx -> b:body{body_index b == idx}
assume val get_body: #idx:index -> body -> indexed_parameters idx

assume val mk_origin: string -> origin
assume val get_origin: origin -> string

// Servers (ad hoc)

type server_state 
unfold type server 'a = server_state -> ('a * server_state)
unfold let bind (f:server 'a) (g: 'a -> server 'b) = 
  (fun s0 -> let (r,s1) = (f s0) in g r s1)
unfold let return (x:'a) : server 'a =
  fun s0 -> x,s0

type session
assume val create_session: server nonce
assume val mk_nonce: #idx:index -> server (n:nonce{nonce_index n == idx})

// OAuth Specific
type idp_record
assume val get_idp_origin: idp_record -> origin
assume val get_rp_origin: idp_record -> origin
assume val read_idp_record: rp:origin -> ip:origin -> server (option (ir:idp_record{get_rp_origin ir == rp /\ get_idp_origin ir == ip}))

assume val get_idp_auth_endpoint_uri: ir:idp_record -> u:pub_uri{uri_origin u == get_idp_origin ir}
assume val get_idp_token_endpoint_uri: ir:idp_record -> u:pub_uri{uri_origin u == get_idp_origin ir}
assume val get_idp_introspection_endpoint_uri: ir:idp_record -> u:pub_uri{uri_origin u == get_idp_origin ir}
assume val get_client_id: idp_record -> string
assume val get_client_secret: ir:idp_record -> option (n:nonce{nonce_index n `includes` get_rp_origin ir /\ 
							      nonce_index n `includes` get_idp_origin ir /\
							      can_send (nonce_index n) 
								(index2 (get_idp_origin ir) (get_rp_origin ir))})




assume val response_type_param: string -> pub_param
assume val client_id_param: string -> pub_param
assume val idp_param: origin -> pub_param
assume val redirect_uri_param: uri -> pub_param
assume val script_param: string -> pub_param

assume val script_data_param: #idx:index -> 
			      script_name:string -> 
			      data:indexed_parameters idx ->
			      p:param{param_index p == idx}


assume val grant_type_param: string -> pub_param
assume val state_param: n:nonce -> p:param{param_index p == nonce_index n}
assume val authorization_code_param: n:nonce -> p:param{param_index p == nonce_index n}
assume val access_token_param: n:nonce -> p:param{param_index p == nonce_index n}

// Any IP/RP/User is only allowed to create a "code" parameter in a URI or message body using this function
assume val idp_code_params: user:uid -> ip:origin -> rp:origin -> code:nonce -> Pure param
			    (requires (nonce_index code == public_index \/
				       (nonce_index code `includes` ip /\
					nonce_index code `includes` rp /\
				        nonce_index code `includes` user /\
				        can_send (nonce_index code) (index2 ip rp))))
			    (ensures (fun _ -> True))

assume val get_idp_param: #idx:index -> indexed_parameters idx -> option origin
assume val get_client_id_param: #idx:index -> indexed_parameters idx -> option string
assume val get_redirect_uri_param: #idx:index -> indexed_parameters idx -> option uri
assume val get_state_param: #idx:index -> indexed_parameters idx -> option nonce 
assume val get_mode_param: #idx:index -> indexed_parameters idx -> option string // echoes back response_type
assume val get_code_param: #idx:index -> indexed_parameters idx -> option nonce 
assume val get_access_token_param: #idx:index -> indexed_parameters idx -> option (n:nonce{nonce_index n == idx})

assume val get_username_param: #idx:index -> indexed_parameters idx -> option string
assume val get_password_param: #idx:index -> indexed_parameters idx -> option nonce
assume val get_response_type_param: #idx:index -> indexed_parameters idx -> option string


assume val client_id_origin: client_id:string -> o:origin



// Postcondition can be proved using an invariant on the "code" parameter, relying on the precondition on idp_code_params
assume val get_idp_code_params: #idx:index -> (rp:origin) -> 
				indexed_parameters idx -> Pure (option (origin * nonce))
				   (requires True)
				   (ensures (fun result -> match result with 
						   | None -> True
						   | Some (idp,code) -> 
						     nonce_index code == public_index \/
						     (nonce_index code `includes` idp /\
						      nonce_index code `includes` rp /\
						      can_send (nonce_index code) (index2 idp rp))))

assume val get_client_id_state_params: #idx:index -> indexed_parameters idx -> Pure (option (string * nonce))
  				   (requires True)
				   (ensures (fun x -> match x with 
						   | None -> True
						   | Some (id,st) -> 
						     nonce_index st == public_index \/
						     (can_send (nonce_index st) idx /\
						      nonce_index st `includes` (client_id_origin id))))

assume val set_rp_session: loginSessionId:nonce -> idp:origin -> s:nonce -> m:string -> redir:uri -> server unit
assume val get_rp_session: loginSessionId:nonce -> server (option (idp:origin * s:nonce * m:string * redir:uri))

assume val check_password: username:string -> password:nonce -> server bool

noeq type req_id = 
  | Id : src:origin -> n:nonce -> req_id


assume val set_rp_request_state: request_id:nonce -> mode:string -> idp:origin -> req:req_id -> server unit
assume val get_rp_request_state: request_id:nonce -> server (o:option (mode:string * idp:origin * req:req_id){ match o with 
			| Some (m,i,r) -> (nonce_index request_id) `includes` i
			| None -> True})


noeq type http_message = 
  | Req : id:req_id -> req:http_request -> http_message 
  | Resp: id:req_id -> resp:http_response -> http_message

#reset-options "--z3rlimit 100"
//val rp_http_server: rp_origin:origin -> msg:http_message -> server (option (msg':http_message{
//						match (msg,msg') with 
//						| Req i _, Resp i' _ -> i == i'
//						| _, _ -> True}))


let rp_http_server (rp_origin:origin) (msg:http_message) : server (option http_message) = 
 match msg with
 | Req id req -> 
  let path = request_path req in
  if path = "/" then
    let headers = [mk_referrer_policy_header "origin"] in 
    let script_ = script_param "script_rp_index" in
    can_send_public (nonce_index id.n);
    assert (can_send (param_index script_) (nonce_index id.n));
    let resp = Resp id (mk_response #(nonce_index id.n) headers (mk_body #(nonce_index id.n) [script_])) in
    return (Some resp)
  else if path = "/startInteractiveLogin" then
    if (request_method req = "POST" &&
        request_origin_header req = get_origin rp_origin)
	 //may need extra checks for HTTPS 
    then (
       match get_idp_param (get_body #(nonce_index id.n) (request_body req)) with
       | None -> return None 
       | Some idp -> 
	 iro <-- read_idp_record rp_origin idp;
	 match iro with
	 | None -> return None
	 | Some ir -> 
	     let redir_index = index_add (nonce_index id.n) idp in
  	     (state <-- mk_nonce #redir_index;
	     let auth_uri = get_idp_auth_endpoint_uri ir in
	     let client_id = get_client_id ir in
	     let redirect_uri = mk_uri #redir_index rp_origin "/redirectionEndpoint" [idp_param idp] in
   	     let auth_uri = add_parameters #redir_index 
	                                  auth_uri [response_type_param "code"; 
						    client_id_param client_id; 
						    state_param state; 
						    redirect_uri_param redirect_uri] in
	     session_id <-- create_session ;
	     set_rp_session session_id idp state "code" redirect_uri ;;
	     let resp = mk_redirect_response #redir_index  auth_uri 
		 [mk_set_cookie_header session_id; 
		  mk_referrer_policy_header "origin"] in
	     let resp = Resp id resp in 
	     return (Some resp)))
	     else return None
    else if path = "/redirectionEndpoint" then
      let session_id = request_cookie_header req in
      session_or_none <-- get_rp_session session_id ;
      match session_or_none with
      | None -> return None
      | Some (idp, state, mode, redir) -> 
	iro <-- read_idp_record rp_origin idp;
	match iro with
	| None -> return None
	| Some ir -> 
	       let client_id = get_client_id ir in
	       let req_params = request_parameters #(nonce_index id.n) req in
	       match (get_client_id_param req_params, 
		      get_state_param req_params, 
		      get_mode_param req_params) with
               | Some cid, Some st, Some mode ->
	           if (cid = client_id && eq_nonce st state && mode = "code") then  
			      // be careful of side-channel leaks in state = state'
	              match (get_idp_code_params rp_origin req_params) with
		      | None -> return None
		      | Some (idp', code) -> 
			  if (idp' <> idp) then 
			    return None 
			  else
                             match (get_client_secret ir) with
			     | None -> return None
			     | Some sec -> 
				    let token_index = index2 idp rp_origin in
				    let auth_header = mk_authorization_header client_id sec in
				    let grant_param = grant_type_param "authorization_code" in
				    can_send_public token_index;
				    //assert(can_send (param_index grant_param) token_index);

				    let code_param = authorization_code_param code in
				    //assert(can_send (param_index code_param) token_index);
				    
				    let token_request = mk_request #token_index "POST" 
				    
							(get_idp_token_endpoint_uri ir)
							[auth_header] 
							(mk_body #token_index 
								 [grant_param;
							          authorization_code_param code;
								  redirect_uri_param redir]) in
				    request_id <-- mk_nonce #(nonce_index id.n);
				    let req_id = Id rp_origin request_id in
				    set_rp_request_state request_id "code" idp id ;;
			            return (Some (Req req_id token_request))
    
		      else return None   
	       | _,_,_ -> return None
    else return None
 | Resp id resp -> // process IP's response and process API response
     session_or_none <-- get_rp_request_state id.n ;
     match session_or_none with
     | None -> return None
     | Some (mode,idp,prev) -> 
        if mode = "code" then 
        let resp_params = get_body (response_body resp) in
	match get_access_token_param #(nonce_index id.n) resp_params with
	| None -> return None
	| Some token -> 
	  iro <-- read_idp_record rp_origin idp;
	  match iro with
	  | None -> return None
	  | Some ir -> 
		 request_id <-- mk_nonce #(nonce_index id.n);
		 let req_id = Id rp_origin request_id in
		 let request_idx = (nonce_index id.n) in
		 let intros_uri = get_idp_introspection_endpoint_uri ir in
		 let token_param = access_token_param token in
		 let intros_uri = add_parameters #(request_idx) intros_uri [token_param] in
   		 set_rp_request_state request_id "introspect" idp prev ;;
		 assert (includes request_idx idp);
		 assert (includes request_idx (uri_origin intros_uri));
		 let request = mk_request #request_idx "GET" intros_uri [] (mk_body #request_idx []) in
		 return (Some (Req req_id request))
        else if mode = "introspect" then
	     /// We may get back the userid and/or a protected resource and/or client_id here
	     /// For authentication, we need to check these values, but not for authorization
	     let headers = [mk_referrer_policy_header "origin"] in 
	     let script_ = script_param "script_rp_index" in
	     can_send_public (nonce_index id.n);
	     assert (can_send (param_index script_) (nonce_index id.n));
	     return (Some (Resp prev (mk_response #(nonce_index prev.n) headers 
			  (mk_body #(nonce_index prev.n) [script_]))))
	else return None 

assume val get_path: u:uri -> path:string

type rp_record
assume val get_rp_record_client_id: rp_record -> string
assume val get_rp_record_rp_origin: rp_record -> string
assume val get_rp_record_ip_origin: rp_record -> origin
assume val read_rp_record: rp_id:string -> ip:origin -> 
  server (option (rpr:rp_record{get_rp_record_client_id rpr == rp_id /\
				get_rp_record_rp_origin rpr == client_id_origin rp_id /\ 
				get_rp_record_ip_origin rpr == ip}))
assume val check_redirect_uri: rp_record -> o:origin -> u:uri -> b:bool{b ==> 
						      (uri_origin u == o /\
						       uri_index u == public_index)}


assume val store_code: code:nonce -> client_id:string -> ruri:uri -> username:string -> server unit
assume val get_code: code:nonce -> server (option (client_id:string * ruri:uri * username:string))
assume val remove_code: code:nonce -> server unit

assume val token: idx:index -> Type
assume val mk_token: #idx:index -> server (token idx)
assume val compromised: origin -> Type
assume val get_token_value: #idx:index -> token idx -> 
			    o:origin{compromised o /\ idx `includes` o} -> string



val ip_http_server: ip:origin -> msg:http_message -> server (option http_message)
let ip_http_server ip msg = 
  match msg with
| Req id req ->
      let path = request_path req in
      if path = "/auth" && request_method req = "GET" then
	 let params = request_parameters #(nonce_index id.n) req in
	 let headers = [mk_referrer_policy_header "origin"] in 
	 let script_ = script_data_param #(nonce_index id.n) "script_idp_form" params in
//	 assert (param_index script_ == nonce_index id.n);
//	 assert (can_send (param_index script_) (nonce_index id.n));
	 let resp = Resp id 
		      (mk_response #(nonce_index id.n) 
			 headers 
			 (mk_body #(nonce_index id.n) [script_])) in
	 return (Some resp)
      else if (path = "/auth" && request_method req = "POST" &&
   	       request_origin_header req = get_origin ip) then
	 let params   = get_body #(nonce_index id.n) (request_body req) in
	 let username = get_username_param params in
	 let password = get_password_param params in
	 let clientid_state = get_client_id_state_params params in
	 let redirect_uri = get_redirect_uri_param params in
	 let response_type = get_response_type_param params in
	(match (username, password, clientid_state, redirect_uri, response_type) with
	 | Some u, Some pw, Some (cid,st), Some ruri, Some "code" -> 
		check <-- check_password u pw;
		if check then (
		   rpr <-- read_rp_record cid ip ;
		   match rpr with 
		   | None -> return None
		   | Some rpr -> 
		   let rp_origin = get_rp_record_rp_origin rpr in
		   if check_redirect_uri rpr rp_origin ruri then
   		     let code_index = index_add (nonce_index id.n) rp_origin in
		     new_code <-- mk_nonce #code_index ;
		     store_code new_code cid ruri u ;;  
		     assert (nonce_index st == public_index \/
			     nonce_index st `includes` rp_origin);
		     assert (can_send (nonce_index st) code_index);
   		     let ruri = add_parameters #code_index 
			                       ruri [authorization_code_param new_code; 
 						     state_param st] in
	   	     let resp = mk_redirect_response #code_index ruri [] in
		     let resp = Resp id resp in 
		     return (Some resp)
		   else return None
		   )
		else return None
	 | _ -> return None)
      else if (path = "/token" && request_method req = "POST") then
	   match request_authorization_header req with
	  | None -> return None
	  | Some (u,p) -> 
	   check <-- check_password u p ;
	   if check then
	     let params   = get_body #(nonce_index id.n) (request_body req) in
	     let code = get_code_param params in
	     let red_uri = get_redirect_uri_param params in
	     match code,red_uri with
	     | None, _  -> return None
	     | _ , None  -> return None
	     | Some code, Some red_uri -> 
	     opt <-- get_code code ;
	     match opt with
	     | Some (client_id, ruri, username) -> 
	           if client_id = u && 
		      eq_uri red_uri ruri then
		    (remove_code code ;;
  		     let token_index = nonce_index id.n in
		     token <-- mk_nonce #token_index ;
		     let b = mk_body #token_index [access_token_param token] in
  	             let resp = Resp id (mk_response #token_index [] b) in
		     return (Some resp))
		   else return None
	     | None -> return None
	   else return None
      else return None
| _ -> return None      



type browser_state
type browser 'a = browser_state -> ('a * browser_state)
assume val new_browser: unit -> browser_state 
assume val new_servers: unit -> server_state
assume val user_navigates: u:origin -> browser (option (m:http_message{Req? m}))
assume val process_response: m:http_message{Resp? m} -> browser (option (m:http_message{Req? m}))


(***********)

type system
type id = origin
assume val is_browser : id -> bool

type window
noeq type event = 
  | HTTP_Msg : http_message -> event
  | Load_Script : id -> window -> event
  
assume val event_target: event -> id
type log = l:list event
assume val get_log: system -> log

type browser_process = option event -> browser_state -> (list event * browser_state)
type server_process = option event -> server_state -> (list event * server_state)
type script_process = option event -> browser_state -> (list event * browser_state)


assume val get_browser_ids: system -> list id 
assume val get_browser: id -> system -> browser_state * browser_process
assume val get_server: id -> system -> server_state * server_process
assume val get_script: id -> system -> script_process
assume val set_browser_state: id -> browser_state -> i:system -> o:system{get_log o == get_log i}
assume val set_server_state: id -> server_state -> i:system -> o:system{get_log o == get_log i}

val valid_event: list event -> event -> Type0
let valid_event l e = True

assume val valid_monotonic: l:list event -> e:event -> e':event -> Lemma
				  (requires (valid_event l e))
				  (ensures (valid_event (e'::l) e))
				  [SMTPat (valid_event (e'::l) e)]
				  
val valid_log: list event -> Type0
let rec valid_log l : Type0 = 
  match l with
  | [] -> True
  | h::t -> valid_log t /\ valid_event t h

val valid_log_lemma: l:list event -> Lemma 
		    (requires (True))
		    (ensures (valid_log l))
		    [SMTPat (valid_log l)]
let rec valid_log_lemma l = 
    match l with 
    | [] -> ()
    | h::t -> valid_log_lemma t
			
			    
val first_n: n:nat -> l:list event{List.Tot.length l >= n}  -> list event
let rec first_n n l = 
  if List.Tot.length l = n then l 
  else 
  match l with
  | h::t -> first_n n t 
  
val extends: l1:list event -> l2:list event -> Type0
let rec extends l1 l2 = 
  if List.Tot.length l1 < List.Tot.length l2 then False
  else first_n (List.Tot.length l2) l1 == l2


assume val mk_browser: stateful id (* creates a new browser and returns an identifier for it *)


val init: browsers: list (id * browser_state * browser_process) -> 
	  servers: list (id * server_state * server_process) -> 
	  scripts: list (id * script_process) ->
	  trusted: list id ->
	  s:system{get_log s == []}
	  
type stateful 'a = s:system -> Pure ('a * system)
			   (requires (valid_log (get_log s)))
			   (ensures (fun (r,f) -> valid_log (get_log f) /\
					       get_log f `extends` get_log s))

type stateful_spec 'a (pre:system -> Type) (post:system -> 'a -> system -> Type) = 
		     i:system -> Pure (r:'a * o:system)
			    (requires (valid_log (get_log i) /\ pre i))
			    (ensures (fun (r,o) -> valid_log (get_log o) /\ 
						get_log o `extends` get_log i /\
						post i r o))

assume val add_event: e:event -> stateful_spec unit (fun i -> valid_log (e::(get_log i)))  (fun i r o -> get_log o == e::get_log i)
assume val add_events: es:list event -> stateful_spec unit (fun i -> valid_log (es@(get_log i)))  (fun i r o -> get_log o == es @ get_log i)

assume val get_pending_event: stateful_spec (option event)
					    (fun _ -> True)
					    (fun i e o -> get_log i == get_log o /\ 
						       (match e with
						       | Some e -> valid_event (get_log i) e
						       | None -> True))

let scheduler_step : stateful unit =  fun st -> 
  let (ev,st) = get_pending_event st in
  match ev with
  | Some (HTTP_Msg (Req id r)) -> 
         let o = uri_origin (request_uri r) in
	 let (s_st,s_fun) = get_server o st in
	 let (evs,s_st) = s_fun ev s_st in
	 let _,st' = add_events evs st in
	 let st' = set_server_state o s_st st' in
	 (),st'

  | Some (HTTP_Msg (Resp id r)) -> 
         if is_browser id.src then 
	   let (b_st,b_fun) = get_browser id.src st in
	   let (evs,b_st) = b_fun ev b_st  in
	   let _,st' = add_events evs st in
	   let st' = set_browser_state id.src b_st st' in
	   (),st'
	 else 
	   let o = id.src in 
	   let (s_st,s_fun) = get_server o st in
	   let (evs,s_st) = s_fun ev s_st in
	   let _,st' = add_events evs st in
	   let st' = set_server_state o s_st st' in
	   (),st'
  | Some (Load_Script id w) ->
	   let (b_st,b_fun) = get_browser id st in
	   let (evs,b_st) = b_fun ev b_st  in
	   let _,st' = add_events evs st in
	   let st' = set_browser_state id b_st st' in
	   (),st'
  | None -> 
	  match (get_browser_ids st) with
	  | [] -> (),st
	  | id::t -> 
		 let (b_st,b_fun) = get_browser id st in
		 let (evs,b_st) = b_fun None b_st  in
		 let _,st' = add_events evs st in
		 let st' = set_browser_state id b_st st' in
		 (),st' 
   

let rec scheduler (n:nat) (st:system{valid_log (get_log st)}) =
  if n > 0 then
    let _,st' = scheduler_step st in
    scheduler (n-1) st'
  else ()	   
	     
	 
	 
  







				      


let main ip rp =
    let browser = new_browser() in
    let servers = new_servers() in
    let (Some req,browser) = user_navigates rp browser in
    let (Some resp,servers) = rp_http_server rp req servers in
    let (Some req, browser) = process_response resp browser in
    let (Some resp,servers) = ip_http_server ip req servers in
    let (Some req, browser) = process_response resp browser in
    let (Some req,servers) = rp_http_server rp req servers in
    let (Some resp,servers) = ip_http_server ip req servers in
    let (Some resp,servers) = rp_http_server rp resp servers in
    let (Some req, browser) = process_response resp browser in
    ()
  




