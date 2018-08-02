module HighComp

module U32 = FStar.UInt32



type mint = U32.t
type state = mint * mint
//type state = int

// High-level specs live in [comp]
let comp a = state -> M (a * state)

type hwp 'a = state -> ('a * state -> Type) -> Type

// [comp] type with wp
type comp_wp 'a (wp : hwp 'a) = s0:state -> PURE ('a * state) (wp s0)

let comp_p (a:Type) (pre : state -> Type) (post : state -> a * state -> Type) : GTot Type  =
    s0:state -> Pure (a * state) (pre s0) (post s0)

// can I get these for free?
let return_wp (x : 'a) : hwp 'a = fun s0 post -> post (x, s0)

unfold
let bind_wp (wp1 : state -> ('a * state -> Type) -> Type)
            (wp2 : 'a -> state -> ('b * state -> Type) -> Type) : state -> ('b * state -> Type) -> Type =
            fun s0 post -> wp1 s0 (function (x, s1) -> wp2 x s1 post)

val hreturn : (a:Type) -> a -> comp a
let hreturn (a:Type) (x : a) = fun s -> (x, s)

val hreturn' : (#a:Type) -> (x:a) -> comp_wp a (return_wp x)
let hreturn' (#a:Type) (x : a) = fun s -> (x, s)

val hbind : (a:Type) -> (b:Type) -> comp a -> (a -> comp b) -> comp b
let hbind (a:Type) (b:Type) (m : comp a) (f : a -> comp b) =
    fun s -> let (a, s1) = m s in f a s1

#set-options "--debug HighComp --debug_level SMTQuery"

let hbind' (#a:Type) (#b:Type) (#wp1:hwp a) (#wp2:a -> hwp b) (m : comp_wp a wp1) (f : (x:a) -> comp_wp b (wp2 x)) :
  comp_wp b (bind_wp wp1 wp2) =
  fun s ->
    admit ();
    let (a, s1) = m s in
    f a s1

val hread : i:int -> comp mint
let hread (i:int) : comp mint =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

val hwrite : i:int -> v:mint -> comp unit
let hwrite (i:int) (v:mint) : comp unit =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))

let write_wp (i:nat) (v:mint) : hwp unit = fun s0 post -> post (hwrite i v s0)

let read_wp (i:nat) : hwp mint = fun s0 post -> post (hread i s0)

val hread' : i:nat -> comp_wp mint (read_wp i)
let hread' (i:nat) : comp_wp mint (read_wp i) =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

val hwrite' : i:nat -> v:mint -> comp_wp unit (write_wp i v)
let hwrite' (i:nat) (v:mint) : comp_wp unit (write_wp i v) =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))

val dread : unit -> comp state
let dread (_ : unit) : comp state = fun s -> (s, s)

val dwrite : v:state -> comp unit
let dwrite (v : state) : comp unit = fun s -> ((), v)

// NOTE : ommiting type annotations from hread and hwrite defs
// makes the effect definition fail

total reifiable reflectable new_effect {
      HIGH : a:Type -> Effect
      with repr  = comp
       ; bind     = hbind
       ; return   = hreturn
       ; get      = hread
       ; put      = hwrite
       }
