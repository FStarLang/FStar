open Prims
type 'a symrel = unit
type 'a pcm' = {
  composable: unit ;
  op: 'a -> 'a -> 'a ;
  one: 'a }
let __proj__Mkpcm'__item__op : 'a . 'a pcm' -> 'a -> 'a -> 'a =
  fun projectee -> match projectee with | { composable; op; one;_} -> op
let __proj__Mkpcm'__item__one : 'a . 'a pcm' -> 'a =
  fun projectee -> match projectee with | { composable; op; one;_} -> one
type ('a, 'p) lem_commutative = unit
type ('a, 'p) lem_assoc_l = unit
type ('a, 'p) lem_assoc_r = unit
type ('a, 'p) lem_is_unit = unit
type 'a pcm =
  {
  p: 'a pcm' ;
  comm: unit ;
  assoc: unit ;
  assoc_r: unit ;
  is_unit: unit ;
  refine: unit }
let __proj__Mkpcm__item__p : 'a . 'a pcm -> 'a pcm' =
  fun projectee ->
    match projectee with | { p; comm; assoc; assoc_r; is_unit; refine;_} -> p




type ('a, 'p, 'x, 'y) composable = Obj.t
let op : 'a . 'a pcm -> 'a -> 'a -> 'a =
  fun p -> fun x -> fun y -> (p.p).op x y
type ('a, 'pcm1, 'x, 'y) compatible = unit
type ('a, 'p, 'x, 'y) joinable = unit
type ('a, 'p, 'x, 'v, 'y) frame_compatible = unit
type ('a, 'p, 'x, 'y) frame_preserving_upd = 'a -> 'a
type ('a, 'pcm1, 'x, 'y) frame_preserving = unit
let frame_preserving_val_to_fp_upd :
  'a . 'a pcm -> unit -> 'a -> ('a, unit, unit, unit) frame_preserving_upd =
  fun p -> fun x -> fun v -> fun uu___ -> v
type ('a, 'p, 'x) exclusive = unit
let no_op_is_frame_preserving :
  'a . 'a pcm -> 'a -> ('a, unit, unit, unit) frame_preserving_upd =
  fun p -> fun x -> fun v -> v
let compose_frame_preserving_updates :
  'a .
    'a pcm ->
      'a ->
        'a ->
          'a ->
            ('a, unit, unit, unit) frame_preserving_upd ->
              ('a, unit, unit, unit) frame_preserving_upd ->
                ('a, unit, unit, unit) frame_preserving_upd
  = fun p -> fun x -> fun y -> fun z -> fun f -> fun g -> fun v -> g (f v)
let frame_preserving_subframe :
  'a .
    'a pcm ->
      'a ->
        'a ->
          'a ->
            ('a, unit, unit, unit) frame_preserving_upd ->
              ('a, unit, unit, unit) frame_preserving_upd
  =
  fun p ->
    fun x -> fun y -> fun subframe -> fun f -> fun v -> let w = f v in w