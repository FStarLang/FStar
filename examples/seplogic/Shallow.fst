module Shallow
open FStar.SL.Heap


let st_wp (a:Type0) = (a * heap -> Type0) -> heap -> Type0
let st (a:Type0) (wp:st_wp a) =
    h0:heap -> PURE (a * heap)
                   (fun post -> wp post h0)

let return (#a:Type) (x:a) 
    : st a (fun post h0 -> is_emp h0 /\ post (x, h0))
    = fun h0 -> x, h0

assume
val bind (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post h3 ->
         exists (h2':heap) (h2'':heap).
           h3 == join_tot h2' h2'' /\
           wp1 
             (fun (x, h1) ->
               exists (h1':heap) (h1'':heap).
                 join_tot h1 h2'' == join_tot h1' h1'' /\
                 wp2 x 
                   (fun (y, h2) -> post (y, join_tot h2 h1''))
                   h1') 
              h2')
//implementing this is tricky, since there isn't a direct way to
//compute the split of h3 into h2' and h2''
//it suggests that we might use a slightly difference style of spec

assume 
val points_to_contains (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (points_to r x `contains` r))
          [SMTPat (points_to r x)]

assume
val points_to_sel (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (sel_tot (points_to r x) r == x))
          [SMTPat (sel_tot (points_to r x) r)]

let read (#a:Type) (r:ref a)
    : st a (fun post h0 ->
                   (exists (x:a). h0 == points_to r x)
                 /\ (forall x. h0 == points_to r x ==> post (x, h0)))
    = fun h0 -> sel_tot h0 r, h0

assume
val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a)
  : Lemma (ensures (upd_tot (points_to r x) r v == points_to r v))
          [SMTPat (upd_tot (points_to r x) r v)]

let write (#a:Type) (r:ref a) (v:a)
    : st unit (fun post h0 ->
                   (exists (x:a). h0 == points_to r x)
                 /\ post ((), points_to r v))
    = fun h0 -> (), upd_tot h0 r v

let swap (r:ref int) (s:ref int) =
  x <-- read r ;
  y <-- read s ;
  write r y  ;;
  write s x
  




// // assume 
// // val read : #a:Type 
// //          -> r:ref a
// //          -> ST a
