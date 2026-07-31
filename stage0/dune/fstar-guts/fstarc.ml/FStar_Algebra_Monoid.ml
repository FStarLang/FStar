open Prims
type 'm monoid =
  | Monoid of 'm * ('m -> 'm -> 'm) * unit * unit * unit 
let uu___is_Monoid (projectee : 'm monoid) : Prims.bool= true
let __proj__Monoid__item__unit (projectee : 'm monoid) : 'm=
  match projectee with
  | Monoid (unit, mult, right_unitality, left_unitality, associativity) ->
      unit
let __proj__Monoid__item__mult (projectee : 'm monoid) : 'm -> 'm -> 'm=
  match projectee with
  | Monoid (unit, mult, right_unitality, left_unitality, associativity) ->
      mult
let intro_monoid (u : 'm) (mult : 'm -> 'm -> 'm) : 'm monoid=
  Monoid (u, mult, (), (), ())
let nat_plus_monoid : Prims.nat monoid=
  let add x y = x + y in intro_monoid Prims.int_zero add
let int_plus_monoid : Prims.int monoid= intro_monoid Prims.int_zero (+)
let conjunction_monoid : unit monoid=
  intro_monoid () (fun uu___1 uu___ -> ())
let disjunction_monoid : unit monoid=
  intro_monoid () (fun uu___1 uu___ -> ())
let bool_and_monoid : Prims.bool monoid=
  let and_ b1 b2 = b1 && b2 in intro_monoid true and_
let bool_or_monoid : Prims.bool monoid=
  let or_ b1 b2 = b1 || b2 in intro_monoid false or_
let bool_xor_monoid : Prims.bool monoid=
  let xor b1 b2 = (b1 || b2) && (Prims.op_Negation (b1 && b2)) in
  intro_monoid false xor
let lift_monoid_option (m : 'a monoid) :
  'a FStar_Pervasives_Native.option monoid=
  let mult x y =
    match (x, y) with
    | (FStar_Pervasives_Native.Some x0, FStar_Pervasives_Native.Some y0) ->
        FStar_Pervasives_Native.Some (__proj__Monoid__item__mult m x0 y0)
    | (uu___, uu___1) -> FStar_Pervasives_Native.None in
  intro_monoid (FStar_Pervasives_Native.Some (__proj__Monoid__item__unit m))
    mult
type ('a, 'b, 'f, 'ma, 'mb) monoid_morphism =
  | MonoidMorphism of unit * unit 
let uu___is_MonoidMorphism (f : 'a -> 'b) (ma : 'a monoid) (mb : 'b monoid)
  (projectee : ('a, 'b, Obj.t, Obj.t, Obj.t) monoid_morphism) : Prims.bool=
  true
let intro_monoid_morphism (f : 'a -> 'b) (ma : 'a monoid) (mb : 'b monoid) :
  ('a, 'b, Obj.t, Obj.t, Obj.t) monoid_morphism= MonoidMorphism ((), ())
let embed_nat_int (n : Prims.nat) : Prims.int= n
let uu___0 : (Prims.nat, Prims.int, Obj.t, Obj.t, Obj.t) monoid_morphism=
  intro_monoid_morphism embed_nat_int nat_plus_monoid int_plus_monoid
let uu___1 : (unit, unit, Obj.t, Obj.t, Obj.t) monoid_morphism=
  intro_monoid_morphism (fun uu___ -> ()) conjunction_monoid
    disjunction_monoid
let uu___2 : (unit, unit, Obj.t, Obj.t, Obj.t) monoid_morphism=
  intro_monoid_morphism (fun uu___ -> ()) disjunction_monoid
    conjunction_monoid
type ('m, 'mm, 'a) left_action =
  | LAct of ('m -> 'a -> 'a) * unit * unit 
let uu___is_LAct (mm : 'm monoid) (a : unit)
  (projectee : ('m, Obj.t, Obj.t) left_action) : Prims.bool= true
let __proj__LAct__item__act (mm : 'm monoid) (a : unit)
  (projectee : ('m, Obj.t, Obj.t) left_action) : 'm -> Obj.t -> Obj.t=
  match projectee with | LAct (act, mult_lemma, unit_lemma) -> act
