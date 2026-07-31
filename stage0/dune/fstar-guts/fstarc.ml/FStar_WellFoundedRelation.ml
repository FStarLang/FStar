open Prims
type ('a, 'r, 'x) acc_classical =
  | AccClassicalIntro of ('a -> ('a, 'r, Obj.t) acc_classical) 
let uu___is_AccClassicalIntro (r : unit) (x : 'a)
  (projectee : ('a, Obj.t, Obj.t) acc_classical) : Prims.bool= true
let __proj__AccClassicalIntro__item__access_smaller (r : unit) (x : 'a)
  (projectee : ('a, Obj.t, Obj.t) acc_classical) :
  'a -> ('a, Obj.t, Obj.t) acc_classical=
  match projectee with | AccClassicalIntro access_smaller -> access_smaller
type 'a wfr_t =
  {
  relation: unit ;
  decreaser: 'a -> ('a, Obj.t, Obj.t) acc_classical ;
  proof: unit }
let __proj__Mkwfr_t__item__decreaser (projectee : 'a wfr_t) :
  'a -> ('a, Obj.t, Obj.t) acc_classical=
  match projectee with | { relation; decreaser; proof;_} -> decreaser
let rec default_decreaser : 'a . 'a -> ('a, Obj.t, Obj.t) acc_classical =
  fun x -> let smaller y = default_decreaser y in AccClassicalIntro smaller
let default_wfr (uu___ : unit) : 'a wfr_t=
  { relation = (); decreaser = default_decreaser; proof = () }
let rec empty_decreaser : 'a . 'a -> ('a, Obj.t, Obj.t) acc_classical =
  fun x -> let smaller y = empty_decreaser y in AccClassicalIntro smaller
let empty_wfr (uu___ : unit) : 'a wfr_t=
  { relation = (); decreaser = empty_decreaser; proof = () }
let rec acc_decreaser :
  'a . unit -> unit -> 'a -> ('a, Obj.t, Obj.t) acc_classical =
  fun r f x ->
    let smaller y = acc_decreaser () () y in AccClassicalIntro smaller
let acc_to_wfr (r : unit) (f : unit) : 'a wfr_t=
  { relation = (); decreaser = (acc_decreaser () ()); proof = () }
let rec subrelation_decreaser :
  'a . unit -> 'a wfr_t -> 'a -> ('a, Obj.t, Obj.t) acc_classical =
  fun r wfr x ->
    let smaller y = subrelation_decreaser () wfr y in
    AccClassicalIntro smaller
let subrelation_to_wfr (r : unit) (wfr : 'a wfr_t) : 'a wfr_t=
  { relation = (); decreaser = (subrelation_decreaser () wfr); proof = () }
let rec inverse_image_decreaser :
  'a 'b .
    unit -> ('a -> 'b) -> 'b wfr_t -> 'a -> ('a, Obj.t, Obj.t) acc_classical
  =
  fun r f wfr x ->
    let smaller y = inverse_image_decreaser () f wfr y in
    AccClassicalIntro smaller
let inverse_image_to_wfr (r : unit) (f : 'a -> 'b) (wfr : 'b wfr_t) :
  'a wfr_t=
  { relation = (); decreaser = (inverse_image_decreaser () f wfr); proof = ()
  }
let rec lex_nondep_decreaser :
  'a 'b .
    'a wfr_t ->
      'b wfr_t -> ('a * 'b) -> (('a * 'b), Obj.t, Obj.t) acc_classical
  =
  fun wfr_a wfr_b xy ->
    let smaller xy' = lex_nondep_decreaser wfr_a wfr_b xy' in
    AccClassicalIntro smaller
let lex_nondep_wfr (wfr_a : 'a wfr_t) (wfr_b : 'b wfr_t) : ('a * 'b) wfr_t=
  { relation = (); decreaser = (lex_nondep_decreaser wfr_a wfr_b); proof = ()
  }
let rec lex_dep_decreaser :
  'a 'b .
    'a wfr_t ->
      ('a -> 'b wfr_t) ->
        ('a, 'b) Prims.dtuple2 ->
          (('a, 'b) Prims.dtuple2, Obj.t, Obj.t) acc_classical
  =
  fun wfr_a a_to_wfr_b xy ->
    let smaller xy' = lex_dep_decreaser wfr_a a_to_wfr_b xy' in
    AccClassicalIntro smaller
let lex_dep_wfr (wfr_a : 'a wfr_t) (a_to_wfr_b : 'a -> 'b wfr_t) :
  ('a, 'b) Prims.dtuple2 wfr_t=
  {
    relation = ();
    decreaser = (lex_dep_decreaser wfr_a a_to_wfr_b);
    proof = ()
  }
let bool_wfr : Prims.bool wfr_t=
  inverse_image_to_wfr ()
    (fun b -> if b then Prims.int_one else Prims.int_zero) (default_wfr ())
let option_wfr (wfr : 'a wfr_t) : 'a FStar_Pervasives_Native.option wfr_t=
  let f opt =
    match opt with
    | FStar_Pervasives_Native.Some x -> Prims.Mkdtuple2 (true, (Obj.magic x))
    | FStar_Pervasives_Native.None ->
        Prims.Mkdtuple2 (false, (Obj.magic (FStar_Universe.raise_val ()))) in
  let bool_to_wfr_a uu___ =
    (fun b ->
       if b
       then Obj.magic (Obj.repr wfr)
       else Obj.magic (Obj.repr (empty_wfr ()))) uu___ in
  let wfr_bool_a = lex_dep_wfr bool_wfr bool_to_wfr_a in
  inverse_image_to_wfr () f wfr_bool_a
