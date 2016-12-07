module FStar.DM4F.Io

let product a b = a * b

let n_ary_product (typs : list Type) : Type =
  List.Tot.fold_right product typs unit

assume val precede_app (#a #b : Type) (f : a -> Tot b) (x:a) : Lemma (requires True) (ensures (f x << f))


assume type input
assume type output

noeq type io (c:Type0) : Type0 =
  | Return : c -> io c
  | Read : (input -> Tot (io c)) -> io c
  | Write : io c -> output -> io c

assume type c0: Type0

val rec_io_c0 : (b:Type0) ->
                (c0 -> M b) ->
                ((input -> M b) -> M b) ->
                (b -> output -> M b) ->
                io c0 -> M b
let rec rec_io_c0 b x_ret x_in x_out x_io =
  match x_io with
  | Return xc0 -> x_ret xc0
  | Read xcont -> x_in (fun (ci : input) -> precede_app xcont ci ; rec_io_c0 b x_ret x_in x_out (xcont ci))
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
  | ReadStar wpcont -> wp_in (fun (ci : input) -> precede_app wpcont ci ; admit () ; rec_io_star b wp_ret wp_in wp_out (wpcont ci))
  | WriteStar wp_io' co -> admit () ; wp_out (rec_io_star b wp_ret wp_in wp_out wp_io') co

#set-options "--print_implicits --print_universes"


assume val f_c0 : c0_star -> Type

let rec f_io_c0 (wp : io_star c0_star) : Type =
  match wp with
  | ReturnStar wpc0 -> n_ary_product [f_c0 wpc0]
  | ReadStar wpcont -> n_ary_product [ci:input -> Tot (f_io_c0 (precede_app wpcont ci ; wpcont ci))]
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
  | ReadStar wpcont -> admit () ; assert (f_io_c0 wp_io == n_ary_product [ci:input -> Tot (f_io_c0 (precede_app wpcont ci ; wpcont ci))] ) ;
                      let (x_cont, ()) : (ci:input -> Tot (f_io_c0 (wpcont ci))) * unit = x_io in
                      let wpcont' (ci:input) : (b -> Type0) -> Type0 = precede_app wpcont ci ; rec_io_star b wp_ret wp_in wp_out (wpcont ci) in
                      let x_cont' (ci:input) : PURE b (wpcont' ci) = precede_app wpcont ci ; rec_io_elab b wp_ret x_ret wp_in x_in wp_out x_out (wpcont ci) (x_cont ci) in
                      x_in wpcont' x_cont'
  | WriteStar wp_io' co ->
     admit (); assert (f_io_c0 wp_io == n_ary_product [ f_io_c0 wp_io' ; y:output{ y == co } ]) ;
    let (x_io', (_co, ())) : normalize_term (n_ary_product [ f_io_c0 wp_io' ; y:output{ y == co } ]) = x_io in
    x_out (rec_io_elab b wp_ret x_ret wp_in x_in wp_out x_out wp_io' x_io') _co (* = co *)
