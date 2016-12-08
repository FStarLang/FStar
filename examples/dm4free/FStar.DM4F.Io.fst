module FStar.DM4F.Io

let product a b = a * b

(* List of types, not of any use since we don't have universe cumulativity and polymorphism *)
let n_ary_product (typs : list Type) : Type =
  List.Tot.fold_right product typs unit

(* *)
assume val precede_app (#a #b : Type) (f : a -> Tot b) (x:a) : Lemma (requires True) (ensures (f x << f))
let apply (#a #b : Type) (f : a -> Tot b) (x:a) : Pure b (requires True) (ensures (fun r -> r == f x /\ r << f)) =
  precede_app f x ; f x


(********************************************************************************)
(*                                                                              *)
(*                    Definition of the IO monad in DM                          *)
(*                                                                              *)
(********************************************************************************)

assume type input
assume type output
assume val bidule : output

let cps (datatype : Type0 -> Type0 -> Tot Type0) (ans a:Type0) : Type = (datatype ans a -> M ans) -> M ans


noeq type io (ans a:Type0) : Type0 =
    | Return : (unit -> M a) -> io ans a
    | Read : (input -> cps io ans a) -> io ans a
    | Write : cps io ans a -> output -> io ans a


let ioM (ans a : Type0) = cps io ans a



let return (#ans #a:Type0) (x:a) : ioM ans a = fun cont -> cont (Return (fun _ -> x))


let rec bind (ans a b:Type0) (x:ioM ans a) (f:a -> ioM ans b) : ioM ans b =
  fun cont -> admit () ; (* There does not seem to be any simple way to prove that calls to cont' *inside* x will be smaller than x *)
           x (cont' ans a b cont f)

and cont' (ans a b:Type0) (cont: io ans b -> M ans) (f:a -> ioM ans b) (x : io ans a)  : M ans =
  match x with
  | Return x0 -> let xa = x0 () in f xa cont   (* bind_M (x0 ()) (f xa cont) *)
  | Read input_cont -> cont (Read (fun (ci:input) -> bind ans a b (apply input_cont ci) f))
  | Write xio co -> cont (Write (bind ans a b xio f) co)

(* The following kind of object should never be constructible... *)
(* let rec x_bad () : ioM False int = fun cont -> cont (Read (fun _ -> x_bad ())) *)


(********************************************************************************)
(*                                                                              *)
(*                            Elaboration to wp's                               *)
(*                                                                              *)
(********************************************************************************)



let cps_star (datatype_star : Type0 -> Type0 -> Tot Type) (ans a:Type0) : Type =
  (datatype_star ans a -> (ans -> Type0) -> Type0 ) -> (ans -> Type0) -> Type0

noeq type io_star (ans a : Type0) : Type =
  | ReturnStar : (unit -> (a -> Type0) -> Type0) -> io_star ans a
  | ReadStar : (input -> cps_star io_star ans a) -> io_star ans a
  | WriteStar : cps_star io_star ans a -> output -> io_star ans a

let ioM_star (ans a : Type0) = cps_star io_star ans a


let return_star (#ans #a:Type0) (x:a) : ioM_star ans a = fun wp_cont -> wp_cont (ReturnStar (fun _ p -> p x))

let rec bind_star (ans a b:Type0) (x:ioM_star ans a) (f:a -> ioM_star ans b) : ioM_star ans b =
  fun wp_cont -> admit () ; (* There does not seem to be any simple way to prove that calls to cont' *inside* x will be smaller than x *)
              x (cont_star ans a b wp_cont f)

and cont_star (ans a b:Type0) (wp_cont: io_star ans b -> (ans -> Type0) -> Type0) (f:a -> ioM_star ans b) (x : io_star ans a) : (ans -> Type0) -> Type0 =
  match x with
  | ReturnStar x0 -> fun p -> x0 () (fun xa -> f xa wp_cont p) (* bind_wp (x0 ()) (f xa wp_cont) *)
  | ReadStar input_cont -> wp_cont (ReadStar (fun (ci:input) -> bind_star ans a b (apply input_cont ci) f))
  | WriteStar xio co -> wp_cont (WriteStar (bind_star ans a b xio f) co)




(********************************************************************************)
(*                                                                              *)
(*                            Elaboration to terms                              *)
(*                                                                              *)
(********************************************************************************)

unfold let f_cps (datatype_star : Type0 -> Type0 -> Type)
          (f_datatype : ans:Type0 -> a:Type0 -> wp:(datatype_star ans a) -> Tot Type)
          (ans a : Type0)
          (wp : cps_star datatype_star ans a)
          : Type =
  wp_cont:(datatype_star ans a -> (ans -> Type0) -> Type0 ) ->
  (wp_dat:datatype_star ans a -> f_datatype ans a wp_dat -> PURE ans (wp_cont wp_dat)) -> (* <-- BREAKS HERE : f_datatype should be called only on wps smaller than wp  *)
  PURE ans (wp wp_cont)

(* let rec f_io (ans a : Type0) (wp : io_star ans a) : Type = *)
(*   match wp with *)
(*   | ReturnStar x0 -> ( u:unit -> PURE a (x0 u) ) * Type0 (\* <-- in order to raise artificially the universe level to S 0 *\) *)
(*   | ReadStar input_cont -> ( ci:input -> f_cps io_star f_io ans a (apply input_cont ci) ) * unit *)
(*   | WriteStar xio co -> ( f_cps io_star f_io ans a xio ) * ( ( y:output{ y == co } ) * unit ) *)


(* Trying to obtain something by artificially taming the beast (preceding annotations added) *)

unfold let f_cps' (datatype_star : Type0 -> Type0 -> Type)
             (ans a : Type0)
             (wp : cps_star datatype_star ans a)
             (f_datatype : ans:Type0 -> a:Type0 -> wp':(datatype_star ans a){wp' << wp} -> Tot Type)
             : Type =
             wp_cont:(datatype_star ans a -> (ans -> Type0) -> Type0 ) ->
             (wp_dat:(datatype_star ans a){wp_dat << wp} -> f_datatype ans a wp_dat -> PURE ans (wp_cont wp_dat)) -> (* <-- BREAKS HERE : f_datatype should be called only on wps smaller than wp  *)
             PURE ans (wp wp_cont)

let rec f_io' (ans a : Type0) (wp : io_star ans a) : Type =
  match wp with
  | ReturnStar x0 -> ( u:unit -> PURE a (x0 u) ) * Type0 (* <-- in order to raise artificially the universe level to S 0 *)
  | ReadStar input_cont -> ( ci:input -> f_cps' io_star ans a (apply input_cont ci) f_io' ) * unit
  | WriteStar xio co -> ( f_cps' io_star ans a xio f_io' ) * ( ( y:output{ y == co } ) * unit )

let f_ioM' (ans a : Type0) (wp : ioM_star ans a) : Type =
  f_cps' io_star ans a wp f_io'

#set-options "--admit_smt_queries true" (* Admitting since it needs internalizing monotonicity - see FStar.DM4F.Continuations.fst *)
(* TODO : try to prove it by explicitly giving the monotonicity as an hypothesis *)
let return_elab (#ans #a:Type0) (x:a) : f_ioM' ans a (return_star #ans #a x) =
      fun wp_cont cont -> cont (ReturnStar (fun _ p -> p x)) ((fun () -> x), unit)


let rec bind_elab (ans a b:Type0) (wp_x:ioM_star ans a) (x:f_ioM' ans a wp_x) (wp_f :a -> ioM_star ans b) (f:(x:a -> f_ioM' ans b (wp_f x))) : f_ioM' ans b (bind_star ans a b wp_x wp_f) =
  fun wp_cont cont -> admit () ; (* There does not seem to be any simple way to prove that calls to cont' *inside* x will be smaller than x *)
                 x (cont_star ans a b wp_cont wp_f) (cont_elab ans a b wp_cont cont wp_f f)

and cont_elab (ans a b:Type0)
              (wp_cont:( io_star ans a -> (ans -> Type0) -> Type0 ))
              (cont:(wp_dat:(io_star ans a) -> f_io' ans a wp_dat -> PURE ans (wp_cont wp_dat)))
              (wp_f :a -> ioM_star ans b)
              (f:(x:a -> f_ioM' ans b (wp_f x)))
              (wp_x : io_star ans a)
              (x : f_io' ans a wp_x)
              : PURE ans (cont_star ans a b wp_cont wp_f wp_x) =
  match wp_x with
  | ReturnStar wp_x0 ->
    let (x0, _unused) : ( u:unit -> PURE a (wp_x0 u) ) * Type0 = x in
    let xa = x0 () in
    f xa wp_cont cont   (* bind_M (x0 ()) (f xa cont) *)
  | ReadStar wp_input_cont ->
    let (input_cont, _) : ( ci:input -> f_cps' io_star ans a (apply wp_input_cont ci) f_io' ) * unit = x in
      cont (ReadStar (fun (ci:input) -> bind_star ans a b (apply wp_input_cont ci) wp_f))
          ((fun (ci:input) -> bind_elab ans a b (apply wp_input_cont ci) (input_cont ci) wp_f f), ())
  | WriteStar wp_xio wp_co ->
    let (xio, (co, _)) : ( f_cps' io_star ans a wp_xio f_io' ) * ( ( y:output{ y == wp_co } ) * unit ) = x in
    cont (WriteStar (bind_star ans a b wp_xio wp_f) co)
         (bind_elab ans a b wp_xio xio wp_f f, (co, ()))

#set-options "--admit_smt_queries false"

(*
noeq type io (c:Type0) : Type0 =
  | Return : c -> io c
  | Read : (input -> Tot (io c)) -> io c
  | Write : io c -> output -> io c


let return (a:Type0) (x:a) : io (unit -> M a) = Return (fun _ -> x)
let rec bind (a b:Type0) (x:io (unit -> M a)) (f:a -> io (unit -> M b)) : io (unit -> M b) =
  match x with
  | Return x0 -> let xa = x0 () in f xa (* !!! DOES NOT TYPE !!! *)
  | Read cont -> Read (fun (ci : input) -> bind (cont ci) f)
  | Write xio co -> Write (bind xio f) co



assume type c0: Type0

val rec_io_c0 : (b:Type0) ->
                (c0 -> M b) ->
                ((input -> M b) -> M b) ->
                (b -> output -> M b) ->
                io c0 -> M b
let rec rec_io_c0 b x_ret x_in x_out x_io =
  match x_io with
  | Return xc0 -> x_ret xc0
    | Read xcont -> x_in (fun (ci : input) -> rec_io_c0 b x_ret x_in x_out (apply xcont ci))
  | Write x_io' co -> x_out (rec_io_c0 b x_ret x_in x_out x_io') co



assume type c0_star : Type0

noeq type io_star (c_star:Type0) : Type0 =
  | ReturnStar : c_star -> io_star c_star
  | ReadStar : (input -> Tot (io_star c_star)) -> io_star c_star
  | WriteStar : io_star c_star -> output -> io_star c_star

val rec_io_star : (b:Type0) ->
                  (c0_star -> (b -> Type0) -> Type0) ->
                  ((input -> (b -> Type0) -> Type0) -> (b -> Type0) -> Type0) ->
                  (b -> output -> (b -> Type0) -> Type0) ->
                  wp_io:io_star c0_star -> (b -> Type0) -> Tot Type0 (decreases wp_io)
let rec rec_io_star b wp_ret wp_in wp_out wp_io =
  match wp_io with
  | ReturnStar wpc0 -> wp_ret wpc0
    | ReadStar wpcont -> wp_in (fun (ci : input) -> admit () ; rec_io_star b wp_ret wp_in wp_out (apply wpcont ci))
  | WriteStar wp_io' co -> admit () ; wp_out (rec_io_star b wp_ret wp_in wp_out wp_io') co

#set-options "--print_implicits --print_universes"


assume val f_c0 : c0_star -> Type

let rec f_io_c0 (wp : io_star c0_star) : Type =
  match wp with
  | ReturnStar wpc0 -> n_ary_product [f_c0 wpc0]
  | ReadStar wpcont -> n_ary_product [ci:input -> Tot (f_io_c0 (apply wpcont ci))]
  | WriteStar wp_io' co -> n_ary_product [ f_io_c0 wp_io' ; y:output{ y == co } ]


val rec_io_elab : (b:Type) ->
                  (wp_ret : (c0_star -> (b -> Type0) -> Type0)) ->
                  (wpc0:c0_star -> f_c0 wpc0 -> PURE b (wp_ret wpc0)) ->
                  (wp_in : ((input -> (b -> Type0) -> Type0) -> (b -> Type0) -> Type0)) ->
                  (wpcont:(input -> (b -> Type0) -> Type0) -> (ci:input -> PURE b (wpcont ci)) -> PURE b (wp_in wpcont)) ->
                  (wp_out : (b -> output -> (b -> Type0) -> Type0)) ->
                  (xb:b -> co:output -> PURE b (wp_out xb co)) ->
                  wp_io:io_star c0_star -> f_io_c0 wp_io ->
                  PURE b (rec_io_star b wp_ret wp_in wp_out wp_io) (decreases wp_io)
let rec rec_io_elab b wp_ret x_ret wp_in x_in wp_out x_out wp_io x_io =
  match wp_io with
  | ReturnStar wpc0 -> let (x_c0, ()) : f_c0 wpc0 * unit = x_io in x_ret wpc0 x_c0
  | ReadStar wpcont -> admit () ; assert (f_io_c0 wp_io == n_ary_product [ci:input -> Tot (f_io_c0 (apply wpcont ci))] ) ;
                      let (x_cont, ()) : (ci:input -> Tot (f_io_c0 (wpcont ci))) * unit = x_io in
                        let wpcont' (ci:input) : (b -> Type0) -> Type0 = rec_io_star b wp_ret wp_in wp_out (apply wpcont ci) in
                        let x_cont' (ci:input) : PURE b (wpcont' ci) = rec_io_elab b wp_ret x_ret wp_in x_in wp_out x_out (apply wpcont ci) (x_cont ci) in
                      x_in wpcont' x_cont'
  | WriteStar wp_io' co ->
     admit (); assert (f_io_c0 wp_io == n_ary_product [ f_io_c0 wp_io' ; y:output{ y == co } ]) ;
    let (x_io', (_co, ())) : normalize_term (n_ary_product [ f_io_c0 wp_io' ; y:output{ y == co } ]) = x_io in
    x_out (rec_io_elab b wp_ret x_ret wp_in x_in wp_out x_out wp_io' x_io') _co (* = co *)
*)
