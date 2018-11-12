module ReifiedTc

open FStar.Tactics

type mint = int
type state = mint * mint
let comp a = state -> M (a * state)

let hreturn (a:Type) (x : a) : comp a = fun s -> (x, s)
let hbind (a:Type) (b:Type) (m : comp a) (f : a -> comp b) : comp b =
    fun s -> let (x, s1) = m s in f x s1

total reifiable reflectable new_effect {
      HIGH : a:Type -> Effect
      with repr  = comp
      ; bind     = hbind
      ; return   = hreturn
}

effect HTot (a:Type) = ReifiedTc.HIGH a (fun s post -> forall x. post x)
let test_return () : HTot bool = true
assume val eq_any : #a:Type -> #b:Type -> x:a -> y:b -> Lemma (x === y)

let hwp_mon = HIGH?.wp

type comp_wp 'a (wp : hwp_mon 'a) = s0:state -> PURE ('a * state) (wp s0)

unfold
let return_wp (#a:Type) (x : a) : hwp_mon a = HIGH?.return_wp a x

let return_elab (#a:Type) (x : a) : comp_wp a (return_wp x) =
  HIGH?.return_elab a x

let test1 =
    assert (reify (test_return ()) === return_elab true)
        by (apply_lemma (`eq_any))

let test2 =
    assert (set_range_of 1 (range_of 2) === 1)
        by (apply_lemma (`eq_any))
