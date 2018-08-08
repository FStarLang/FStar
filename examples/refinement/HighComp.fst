module HighComp

module U32 = FStar.UInt32



type mint = U32.t
type state = mint * mint

// High-level specs live in [comp]
let comp a = state -> M (a * state)

type hwp 'a = state -> ('a * state -> Type) -> Type  // x:hwp a { monotonic x } 

// [comp] type with wp
type comp_wp 'a (wp : hwp 'a) = s0:state -> PURE ('a * state) (wp s0)

type comp_wp' 'a (wp : hwp 'a) = s0:state -> PURE ('a * state) (wp s0)

// [comp] type with preconditions
let comp_p (a:Type) (pre : state -> Type) (post : state -> a * state -> Type) : GTot Type  =
    s0:state -> Pure (a * state) (pre s0) (post s0)

// WPs 

// can I get these for free?
unfold
let return_wp (x : 'a) : hwp 'a = fun s0 post -> post (x, s0)


// TODO use the provided HighComp._dm4f_HIGH_return_wp 
unfold
let bind_wp (wp1 : state -> ('a * state -> Type) -> Type)
            (wp2 : 'a -> state -> ('b * state -> Type) -> Type) : state -> ('b * state -> Type) -> Type =
            fun s0 post -> wp1 s0 (function (x, s1) -> wp2 x s1 post)

// Pre and postconditions

unfold
let trivial_pre = fun s0 -> True

unfold
let return_post (#a : Type) (x : a) = fun s0 r -> let (x1, s1) = r in x1 == x /\ s0 == s1

unfold
let bind_pre (#a : Type) (x : a) = fun s0 r -> let (x1, s1) = r in x1 == x /\ s0 == s1

unfold
let bind_post (#a : Type) (x : a) = fun s0 r -> let (x1, s1) = r in x1 == x /\ s0 == s1

// High-level DSL

val hreturn : (a:Type) -> a -> comp a
let hreturn (a:Type) (x : a) = fun s -> (x, s)

val hreturn' : (#a:Type) -> (x:a) -> comp_wp a (return_wp x)
let hreturn' (#a:Type) (x : a) = fun s -> (x, s)


val hbind : (a:Type) -> (b:Type) -> comp a -> (a -> comp b) -> comp b
let hbind (a:Type) (b:Type) (m : comp a) (f : a -> comp b) =
    fun s -> let (x, s1) = m s in f x s1

let hbind' (#a:Type) (#b:Type) (#wp1:hwp a) (#wp2:a -> hwp b) 
  (m : comp_wp a wp1) (f : (x:a) -> comp_wp b (wp2 x)) :
  comp_wp b (bind_wp wp1 wp2) =
  fun s -> admit (); 
        let (a, s1) = m s in f a s1


val hread : i:int -> comp mint
let hread (i:int) : comp mint =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

let read_wp (i:nat) : hwp mint = fun s0 post -> post (hread i s0)

val hread' : i:nat -> comp_wp mint (read_wp i)
let hread' (i:nat) : comp_wp mint (read_wp i) =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)


val hwrite : i:int -> v:mint -> comp unit
let hwrite (i:int) (v:mint) : comp unit =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))

let write_wp (i:nat) (v:mint) : hwp unit = fun s0 post -> post (hwrite i v s0)

val hwrite' : i:nat -> v:mint -> comp_wp unit (write_wp i v)
let hwrite' (i:nat) (v:mint) : comp_wp unit (write_wp i v) =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))


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

// Commutation
val h_eq' : (#a:Type) -> (wp1:hwp a) -> (wp2:hwp a) -> (comp_wp a wp1) -> (comp_wp a wp2) -> GTot Type0
let h_eq' #a wp1 wp2 c1 c2 = 
    (forall s0. wp1 s0 (fun _ -> True) <==> wp2 s0 (fun _ -> True)) /\
    (forall s0. wp1 s0 (fun _ -> True) ==> // suddenly stoped working... 
           // wp2 s0 (fun _ -> True) ==> // even with this
           (let r1 = c1 s0 in 
            let r2 = c2 s0 in 
            r2 == r2))

// Note : At some point the above was typechecked 


// Confusion comes next :) 

let hbind_commut (a:Type) (b:Type) (#wp1:hwp a) (#wp2:a -> hwp b) 
     (c1 : unit -> HIGH a wp1) (c2 : (x:a) -> HIGH b (wp2 x)) :
     Lemma (h_eq' (bind_wp wp1 wp2) (bind_wp wp1 wp2)
                  (reify (let x = c1 () in c2 x)) 
                  (hbind' (reify (c1 ())) (fun x -> reify (c2 x)))) =
     ()



