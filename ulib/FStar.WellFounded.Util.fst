module FStar.WellFounded.Util
open FStar.WellFounded

let intro_lift_binrel (#a:Type) (r:binrel a) (y:a) (x:a)
  : Lemma
    (requires r y x)
    (ensures lift_binrel r (| a, y |) (| a, x |))
  = ()

let elim_lift_binrel (#a:Type) (r:binrel a) (y:top) (x:a)
  : Lemma
    (requires lift_binrel r y (| a, x |))
    (ensures dfst y == a /\ r (dsnd y) x)
  = ()

let lower_binrel (#a:Type)
                 (#r:binrel a)
                 (x y:top)
                 (p:lift_binrel r x y)
  : r (dsnd x) (dsnd y)
  = ()


let lift_binrel_well_founded (#a:Type u#a)
                             (#r:binrel u#a a)
                             (wf_r:well_founded r)
  : well_founded (lift_binrel r)
  = let rec aux (y:top{dfst y == a})
                (pf:acc r (dsnd y))
        : Tot (acc (lift_binrel r) y)
              (decreases pf)
        = AccIntro (fun (z:top) (p:lift_binrel r z y) ->
            aux z (pf.access_smaller (dsnd z) (lower_binrel z y p)))
    in
    let aux' (y:top{dfst y =!= a})
        : acc (lift_binrel r) y
        = AccIntro (fun y p -> false_elim ())
    in
    fun (x:top) ->
      if dfst x == a
      then aux x (wf_r (dsnd x))
      else aux' x
