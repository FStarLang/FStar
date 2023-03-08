open Prims
type ('a, 'r, 'x) acc_classical =
  | AccClassicalIntro of ('a -> ('a, 'r, unit) acc_classical) 
let uu___is_AccClassicalIntro :
  'a 'r . 'a -> ('a, 'r, unit) acc_classical -> Prims.bool =
  fun x -> fun projectee -> true
let __proj__AccClassicalIntro__item__access_smaller :
  'a 'r .
    'a -> ('a, 'r, unit) acc_classical -> 'a -> ('a, 'r, unit) acc_classical
  =
  fun x ->
    fun projectee ->
      match projectee with
      | AccClassicalIntro access_smaller -> access_smaller
type 'a wfr_t =
  {
  relation: unit ;
  decreaser: 'a -> ('a, Obj.t, unit) acc_classical ;
  proof: unit }
let __proj__Mkwfr_t__item__decreaser :
  'a . 'a wfr_t -> 'a -> ('a, unit, unit) acc_classical =
  fun uu___1 ->
    fun uu___ ->
      (fun projectee ->
         match projectee with
         | { relation; decreaser; proof;_} -> Obj.magic decreaser) uu___1
        uu___
type ('a, 'x1, 'x2) default_relation = ('a, 'a, unit, unit) Prims.precedes
let rec default_decreaser :
  'a . 'a -> ('a, ('a, unit, unit) default_relation, unit) acc_classical =
  fun x -> let smaller y = default_decreaser y in AccClassicalIntro smaller
let default_wfr : 'a . unit -> 'a wfr_t =
  fun uu___ ->
    {
      relation = ();
      decreaser = (fun uu___1 -> (Obj.magic default_decreaser) uu___1);
      proof = ()
    }
type ('a, 'x1, 'x2) empty_relation = unit
let rec empty_decreaser :
  'a . 'a -> ('a, ('a, unit, unit) empty_relation, unit) acc_classical =
  fun x -> let smaller y = empty_decreaser y in AccClassicalIntro smaller
let empty_wfr : 'a . unit -> 'a wfr_t =
  fun uu___ ->
    {
      relation = ();
      decreaser = (fun uu___1 -> (Obj.magic empty_decreaser) uu___1);
      proof = ()
    }
type ('a, 'r, 'x1, 'x2) acc_relation = unit
let rec acc_decreaser :
  'a 'r .
    unit -> 'a -> ('a, ('a, 'r, unit, unit) acc_relation, unit) acc_classical
  =
  fun f ->
    fun x -> let smaller y = acc_decreaser () y in AccClassicalIntro smaller
let acc_to_wfr : 'a 'r . unit -> 'a wfr_t =
  fun f ->
    {
      relation = ();
      decreaser = (fun uu___ -> (Obj.magic (acc_decreaser ())) uu___);
      proof = ()
    }
let rec subrelation_decreaser :
  'a 'r . 'a wfr_t -> 'a -> ('a, 'r, unit) acc_classical =
  fun wfr ->
    fun x ->
      let smaller y = subrelation_decreaser wfr y in
      AccClassicalIntro smaller
let subrelation_to_wfr : 'a 'r . 'a wfr_t -> 'a wfr_t =
  fun wfr ->
    {
      relation = ();
      decreaser =
        (fun uu___ -> (Obj.magic (subrelation_decreaser wfr)) uu___);
      proof = ()
    }
let rec inverse_image_decreaser :
  'a 'b 'r . ('a -> 'b) -> 'b wfr_t -> 'a -> ('a, 'r, unit) acc_classical =
  fun f ->
    fun wfr ->
      fun x ->
        let smaller y = inverse_image_decreaser f wfr y in
        AccClassicalIntro smaller
let inverse_image_to_wfr : 'a 'b 'r . ('a -> 'b) -> 'b wfr_t -> 'a wfr_t =
  fun f ->
    fun wfr ->
      {
        relation = ();
        decreaser =
          (fun uu___ -> (Obj.magic (inverse_image_decreaser f wfr)) uu___);
        proof = ()
      }
type ('a, 'b, 'wfrua, 'wfrub, 'xy1, 'xy2) lex_nondep_relation = Obj.t
let rec lex_nondep_decreaser :
  'a 'b .
    'a wfr_t ->
      'b wfr_t -> ('a * 'b) -> (('a * 'b), Obj.t, unit) acc_classical
  =
  fun wfr_a ->
    fun wfr_b ->
      fun xy ->
        let smaller xy' = lex_nondep_decreaser wfr_a wfr_b xy' in
        AccClassicalIntro smaller
let lex_nondep_wfr : 'a 'b . 'a wfr_t -> 'b wfr_t -> ('a * 'b) wfr_t =
  fun wfr_a ->
    fun wfr_b ->
      {
        relation = ();
        decreaser = (lex_nondep_decreaser wfr_a wfr_b);
        proof = ()
      }
type ('a, 'b, 'wfrua, 'autouwfrub, 'xy1, 'xy2) lex_dep_relation = Obj.t
let rec lex_dep_decreaser :
  'a 'b .
    'a wfr_t ->
      ('a -> 'b wfr_t) ->
        ('a, 'b) Prims.dtuple2 ->
          (('a, 'b) Prims.dtuple2, Obj.t, unit) acc_classical
  =
  fun wfr_a ->
    fun a_to_wfr_b ->
      fun xy ->
        let smaller xy' = lex_dep_decreaser wfr_a a_to_wfr_b xy' in
        AccClassicalIntro smaller
let lex_dep_wfr :
  'a 'b . 'a wfr_t -> ('a -> 'b wfr_t) -> ('a, 'b) Prims.dtuple2 wfr_t =
  fun wfr_a ->
    fun a_to_wfr_b ->
      {
        relation = ();
        decreaser = (lex_dep_decreaser wfr_a a_to_wfr_b);
        proof = ()
      }
type ('x1, 'x2) bool_relation = unit
let (bool_wfr : Prims.bool wfr_t) =
  inverse_image_to_wfr (fun b -> if b then Prims.int_one else Prims.int_zero)
    (default_wfr ())
type ('a, 'wfr, 'opt1, 'opt2) option_relation = unit
let option_wfr : 'a . 'a wfr_t -> 'a FStar_Pervasives_Native.option wfr_t =
  fun wfr ->
    let f opt =
      match opt with
      | FStar_Pervasives_Native.Some x ->
          Prims.Mkdtuple2 (true, (Obj.magic x))
      | FStar_Pervasives_Native.None ->
          Prims.Mkdtuple2 (false, (Obj.magic (FStar_Universe.raise_val ()))) in
    let bool_to_wfr_a uu___ =
      (fun b ->
         if b
         then Obj.magic (Obj.repr wfr)
         else Obj.magic (Obj.repr (empty_wfr ()))) uu___ in
    let wfr_bool_a = lex_dep_wfr bool_wfr bool_to_wfr_a in
    inverse_image_to_wfr f wfr_bool_a