module OAuth.Formal

module List = FStar.List.Tot

type http_request = Browser.Datatypes.browserRequest
type http_response = Browser.Datatypes.response
type param = Network.Interface.secretVal
type header = Browser.AuxiliaryDatatypes.header
type body = list (Network.Interface.secretVal)
type uri = Web.URI.uri
type origin = Web.Origin.origin
type nonce = Network.Interface.secretVal
type uid = origin
// We will check by typing that a nonce of type "nonce idx"
// can never be sent to principals other than idx.uid, idx.rp, idx.ip
type index = Secret.SecString.secLevel

val public_index: index
val can_send: i:index -> i':index -> GTot Type0
val includes: i:index -> o:origin -> GTot Type0

val index_origins : o:list origin -> i:index{forall x. List.mem x o ==> includes i x}

val nonce_index: nonce -> GTot index
val eq_nonce: x:nonce -> y:nonce -> b:bool{b ==> nonce_index x == nonce_index y}

val param_index: param -> GTot index
type pub_param = p:param{param_index p == public_index}

(* val header_index: header -> GTot index *)
(* type pub_header = h:header{header_index h == public_index} *)

(* val body_index: body -> GTot index *)
(* type pub_body = b:body{body_index b == public_index} *)

(* val can_send_public: i:index ->  Lemma  *)
(* 	   (requires True) *)
(* 	   (ensures (can_send public_index i)) *)
(* 	   [SMTPat (can_send public_index i)] *)
	   
(* val mk_uri: origin -> path:string -> list param  -> uri *)
(* val uri_origin: uri -> origin *)
(* val add_parameters: u:uri -> list param -> u':uri{uri_origin u == uri_origin u'} *)

(* val request_path: http_request -> string *)
(* val request_method: http_request -> string *)
(* val request_parameters: http_request -> (list param) *)
(* val request_origin_header: http_request -> string *)
(* val request_cookie_header: http_request -> nonce *)
(* val request_body: http_request -> body *)


(* val mk_referrer_policy_header: string -> header *)
(* val mk_set_cookie_header: n:nonce -> h:header{header_index h == nonce_index n} *)
(* val mk_authorization_header: string -> n:nonce -> h:header{header_index h == nonce_index n} *)

(* val mk_request: #req_idx:index ->  *)
(* 		       method:string ->  *)
(* 		       request_uri:uri{includes req_idx (uri_origin request_uri)}  ->  *)
(* 		       list (h:header{can_send (header_index h) req_idx}) ->  *)
(* 		       b:body{body_index b == req_idx} ->  *)
(* 		       http_request *)
(* val mk_response: list header -> body -> http_response *)
(* val mk_redirect_response: uri -> list header -> http_response *)

(* val response_body: http_response -> body *)


(* val mk_body: #req_idx:index -> list (p:param{can_send (param_index p) req_idx}) -> b:body{body_index b == req_idx} *)
(* val get_body: body -> list param *)

(* val mk_origin: string -> origin *)
(* val get_origin: origin -> string *)

 
(* type server_state  *)
(* unfold type server 'a = server_state -> ('a * server_state) *)
(* unfold let bind (f:server 'a) (g: 'a -> server 'b) =  *)
(*   (fun s0 -> let (r,s1) = (f s0) in g r s1) *)
(* unfold let return (x:'a) : server 'a = *)
(*   fun s0 -> x,s0 *)

(* type session *)
(* val create_session: server nonce *)
(* val mk_nonce: server nonce *)

(* // OAuth Specific *)
(* type idp_record *)
(* val get_idp_origin: idp_record -> origin *)
(* val get_rp_origin: idp_record -> origin *)
(* //val read_idps: o:origin -> server (list (ir:idp_record{get_rp_origin ir == o}))  *)
(* //val get_idp_record: o:origin -> list idp_record -> option (ir:idp_record{get_idp_origin ir == o}) *)
(* val read_idp_record: rp:origin -> ip:origin -> server (option (ir:idp_record{get_rp_origin ir == rp /\ get_idp_origin ir == ip})) *)

(* val get_idp_auth_endpoint_uri: ir:idp_record -> u:uri{uri_origin u == get_idp_origin ir} *)
(* val get_idp_token_endpoint_uri: ir:idp_record -> u:uri{uri_origin u == get_idp_origin ir} *)
(* val get_idp_introspection_endpoint_uri: ir:idp_record -> u:uri{uri_origin u == get_idp_origin ir} *)
(* val get_client_id: idp_record -> string *)
(* val get_client_secret: ir:idp_record -> option (n:nonce{nonce_index n `includes` get_rp_origin ir /\  *)
(* 							      nonce_index n `includes` get_idp_origin ir /\ *)
(* 							      can_send (nonce_index n)  *)
(* 								(index2 (get_idp_origin ir) (get_rp_origin ir))}) *)


(* val response_type_param: string -> pub_param *)
(* val client_id_param: string -> pub_param *)
(* val idp_param: origin -> pub_param *)
(* val redirect_uri_param: uri -> pub_param *)
(* val script_param: string -> pub_param *)
(* val grant_type_param: string -> pub_param *)
(* val state_param: n:nonce -> p:param{param_index p == nonce_index n} *)
(* val authorization_code_param: n:nonce -> p:param{param_index p == nonce_index n} *)
(* val access_token_param: n:nonce -> p:param{param_index p == nonce_index n} *)

(* // Any IP/RP/User is only allowed to create a "code" parameter in a URI or message body using this function *)
(* val idp_code_params: user:uid -> ip:origin -> rp:origin -> code:nonce -> Pure param *)
(* 			    (requires (nonce_index code == public_index \/ *)
(* 				       (nonce_index code `includes` ip /\ *)
(* 					nonce_index code `includes` rp /\ *)
(* 				        nonce_index code `includes` user /\ *)
(* 				        can_send (nonce_index code) (index2 ip rp)))) *)
(* 			    (ensures (fun _ -> True)) *)

(* val get_idp_param: (list param) -> option origin *)
(* val get_client_id_param: (list param) -> option string *)
(* val get_state_param: (list param) -> option nonce  *)
(* val get_mode_param: (list param) -> option string // echoes back response_type *)
(* val get_code_param: (list param) -> option nonce  *)
(* val get_access_token_param: (list param) -> option nonce *)

(* // Postcondition can be proved using an invariant on the "code" parameter, relying on the precondition on idp_code_params *)
(* val get_idp_code_params: (rp:origin) -> (list param) -> Pure (option (origin * nonce)) *)
(* 				   (requires True) *)
(* 				   (ensures (fun x -> match x with  *)
(* 						   | None -> True *)
(* 						   | Some (idp,code) ->  *)
(* 						     nonce_index code == public_index \/ *)
(* 						     (nonce_index code `includes` idp /\ *)
(* 						      nonce_index code `includes` rp /\ *)
(* 						      can_send (nonce_index code) (index2 idp rp)))) *)

(* val set_rp_session: loginSessionId:nonce -> idp:origin -> s:nonce -> m:string -> redir:uri -> server unit *)
(* val get_rp_session: loginSessionId:nonce -> server (option (idp:origin * s:nonce * m:string * redir:uri)) *)

(* val set_rp_request_state: request_id:nonce -> mode:string -> idp:origin -> req:nonce -> server unit *)
(* val get_rp_request_state: request_id:nonce -> server (option (mode:string * idp:origin * req:nonce)) *)

(* noeq type http_message =  *)
(*   | Req : id:nonce -> http_request -> http_message  *)
(*   | Resp: id:nonce -> http_response -> http_message *)

(* #reset-options "--z3rlimit 100" *)
(* //val rp_http_server: rp_origin:origin -> msg:http_message -> server (option (msg':http_message{ *)
(* //						match (msg,msg') with  *)
(* //						| Req i _, Resp i' _ -> i == i' *)
(* //						| _, _ -> True})) *)

