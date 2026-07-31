open Prims
type 'a binrel = unit
type 'a predicate = unit
type 'a preorder = unit
type ('a, 'r, 'dummyV0, 'dummyV1) _closure =
  | Refl of 'a 
  | Step of 'a * 'a * unit 
  | Closure of 'a * 'a * 'a * ('a, 'r, Obj.t, Obj.t) _closure * ('a, 
  'r, Obj.t, Obj.t) _closure 
let uu___is_Refl (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : Prims.bool=
  match projectee with | Refl x -> true | uu___2 -> false
let __proj__Refl__item__x (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : 'a=
  match projectee with | Refl x -> x
let uu___is_Step (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : Prims.bool=
  match projectee with | Step (x, y, _2) -> true | uu___2 -> false
let __proj__Step__item__x (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : 'a=
  match projectee with | Step (x, y, _2) -> x
let __proj__Step__item__y (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : 'a=
  match projectee with | Step (x, y, _2) -> y
let uu___is_Closure (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : Prims.bool=
  match projectee with | Closure (x, y, z, _3, _4) -> true | uu___2 -> false
let __proj__Closure__item__x (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : 'a=
  match projectee with | Closure (x, y, z, _3, _4) -> x
let __proj__Closure__item__y (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : 'a=
  match projectee with | Closure (x, y, z, _3, _4) -> y
let __proj__Closure__item__z (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) : 'a=
  match projectee with | Closure (x, y, z, _3, _4) -> z
let __proj__Closure__item___3 (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) :
  ('a, Obj.t, Obj.t, Obj.t) _closure=
  match projectee with | Closure (x, y, z, _3, _4) -> _3
let __proj__Closure__item___4 (r : unit) (uu___ : 'a) (uu___1 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) _closure) :
  ('a, Obj.t, Obj.t, Obj.t) _closure=
  match projectee with | Closure (x, y, z, _3, _4) -> _4

let rec closure_one_aux :
  'a .
    unit ->
      'a ->
        'a ->
          ('a, Obj.t, Obj.t, Obj.t) _closure ->
            (unit,
              ('a, unit, ('a, Obj.t, Obj.t, Obj.t) _closure)
                FStar_Pervasives.dtuple3)
              FStar_Pervasives.either
  =
  fun r x y xy ->
    match xy with
    | Refl uu___ -> FStar_Pervasives.Inl ()
    | Step (uu___, uu___1, pr) ->
        FStar_Pervasives.Inr (FStar_Pervasives.Mkdtuple3 (y, (), (Refl y)))
    | Closure (x1, i, y1, xi, iy) ->
        (match closure_one_aux () i y1 iy with
         | FStar_Pervasives.Inl uu___ -> closure_one_aux () x1 y1 xi
         | FStar_Pervasives.Inr (FStar_Pervasives.Mkdtuple3
             (z, r_i_z, c_z_y)) ->
             let c_z_y1 = c_z_y in
             (match closure_one_aux () x1 i xi with
              | FStar_Pervasives.Inl uu___ ->
                  FStar_Pervasives.Inr
                    (FStar_Pervasives.Mkdtuple3 (z, (), c_z_y1))
              | FStar_Pervasives.Inr (FStar_Pervasives.Mkdtuple3
                  (w, r_x_w, c_w_i)) ->
                  let step = Step (i, z, ()) in
                  let c_i_y = Closure (i, z, y1, step, c_z_y1) in
                  let c_w_y = Closure (w, i, y1, c_w_i, c_i_y) in
                  FStar_Pervasives.Inr
                    (FStar_Pervasives.Mkdtuple3 (w, (), c_w_y))))
