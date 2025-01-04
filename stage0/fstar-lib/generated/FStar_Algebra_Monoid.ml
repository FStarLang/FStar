open Prims
type ('m, 'u, 'mult) right_unitality_lemma = unit
type ('m, 'u, 'mult) left_unitality_lemma = unit
type ('m, 'mult) associativity_lemma = unit
type 'm monoid =
  | Monoid of 'm * ('m -> 'm -> 'm) * unit * unit * unit 
let uu___is_Monoid : 'm . 'm monoid -> Prims.bool = fun projectee -> true
let __proj__Monoid__item__unit : 'm . 'm monoid -> 'm =
  fun projectee ->
    match projectee with
    | Monoid (unit, mult, right_unitality, left_unitality, associativity) ->
        unit
let __proj__Monoid__item__mult : 'm . 'm monoid -> 'm -> 'm -> 'm =
  fun projectee ->
    match projectee with
    | Monoid (unit, mult, right_unitality, left_unitality, associativity) ->
        mult
let intro_monoid : 'm . 'm -> ('m -> 'm -> 'm) -> 'm monoid =
  fun u -> fun mult -> Monoid (u, mult, (), (), ())
let (nat_plus_monoid : Prims.nat monoid) =
  let add x y = x + y in intro_monoid Prims.int_zero add
let (int_plus_monoid : Prims.int monoid) = intro_monoid Prims.int_zero (+)
let (conjunction_monoid : unit monoid) =
  intro_monoid () (fun uu___1 -> fun uu___ -> ())
let (disjunction_monoid : unit monoid) =
  intro_monoid () (fun uu___1 -> fun uu___ -> ())
let (bool_and_monoid : Prims.bool monoid) =
  let and_ b1 b2 = b1 && b2 in intro_monoid true and_
let (bool_or_monoid : Prims.bool monoid) =
  let or_ b1 b2 = b1 || b2 in intro_monoid false or_
let (bool_xor_monoid : Prims.bool monoid) =
  let xor b1 b2 = (b1 || b2) && (Prims.op_Negation (b1 && b2)) in
  intro_monoid false xor
let lift_monoid_option :
  'a . 'a monoid -> 'a FStar_Pervasives_Native.option monoid =
  fun m ->
    let mult x y =
      match (x, y) with
      | (FStar_Pervasives_Native.Some x0, FStar_Pervasives_Native.Some y0) ->
          FStar_Pervasives_Native.Some (__proj__Monoid__item__mult m x0 y0)
      | (uu___, uu___1) -> FStar_Pervasives_Native.None in
    intro_monoid
      (FStar_Pervasives_Native.Some (__proj__Monoid__item__unit m)) mult
type ('a, 'b, 'f, 'ma, 'mb) monoid_morphism_unit_lemma = unit
type ('a, 'b, 'f, 'ma, 'mb) monoid_morphism_mult_lemma = unit
type ('a, 'b, 'f, 'ma, 'mb) monoid_morphism =
  | MonoidMorphism of unit * unit 
let uu___is_MonoidMorphism :
  'a 'b .
    ('a -> 'b) ->
      'a monoid ->
        'b monoid -> ('a, 'b, unit, unit, unit) monoid_morphism -> Prims.bool
  = fun f -> fun ma -> fun mb -> fun projectee -> true
let intro_monoid_morphism :
  'a 'b .
    ('a -> 'b) ->
      'a monoid -> 'b monoid -> ('a, 'b, unit, unit, unit) monoid_morphism
  = fun f -> fun ma -> fun mb -> MonoidMorphism ((), ())
let (embed_nat_int : Prims.nat -> Prims.int) = fun n -> n
let (uu___0 : (Prims.nat, Prims.int, unit, unit, unit) monoid_morphism) =
  intro_monoid_morphism embed_nat_int nat_plus_monoid int_plus_monoid
type 'p neg = unit
let (uu___1 : (unit, unit, unit neg, unit, unit) monoid_morphism) =
  intro_monoid_morphism (fun uu___ -> ()) conjunction_monoid
    disjunction_monoid
let (uu___2 : (unit, unit, unit neg, unit, unit) monoid_morphism) =
  intro_monoid_morphism (fun uu___ -> ()) disjunction_monoid
    conjunction_monoid
type ('m, 'a, 'mult, 'act) mult_act_lemma = unit
type ('m, 'a, 'u, 'act) unit_act_lemma = unit
type ('m, 'mm, 'a) left_action =
  | LAct of ('m -> 'a -> 'a) * unit * unit 
let uu___is_LAct :
  'm . 'm monoid -> unit -> ('m, unit, Obj.t) left_action -> Prims.bool =
  fun mm -> fun a -> fun projectee -> true
let __proj__LAct__item__act :
  'm .
    'm monoid ->
      unit -> ('m, unit, Obj.t) left_action -> 'm -> Obj.t -> Obj.t
  =
  fun mm ->
    fun a ->
      fun projectee ->
        match projectee with | LAct (act, mult_lemma, unit_lemma) -> act
type ('a, 'b, 'ma, 'mb, 'f, 'mf, 'mma, 'mmb, 'la, 'lb) left_action_morphism =
  unit