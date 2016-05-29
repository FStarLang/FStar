module Unit1.WPsAndTriples_ST
open FStar.Heap
type as_requires (#a:Type) (wp:st_wp_h heap a)  = wp (fun x h -> True)
type as_ensures  (#a:Type) (wlp:st_wp_h heap a) (h0:heap) (x:a) (h1:heap) = ~ (wlp (fun y h1' -> y<>x \/ h1<>h1') h0)
assume val as_ST: #a:Type -> #b:(a -> Type)
          -> #wp:(x:a -> GTot (st_wp_h heap (b x)))
          -> #wlp:(x:a -> GTot (st_wp_h heap (b x)))
          -> $f:(x:a -> STATE (b x) (wp x) (wlp x))
          -> x:a -> ST (b x) (as_requires (wp x))
                             (as_ensures (wlp x))

let f x = op_Multiply !x !x

val h : #req:(ref int -> heap -> Type)
     -> #ens:(ref int -> heap -> int -> heap -> Type)
     -> $f:(x:ref int -> ST int (req x) (ens x))
     -> y:ref int -> ST int (req y) (ens y)
let h #req #ens f y = f y

val g : x:ref int -> ST int (fun h -> True) (fun h0 y h1 -> h0=h1 /\ y >= 0)
let g = h (as_ST f)
