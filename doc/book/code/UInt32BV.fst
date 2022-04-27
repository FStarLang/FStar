module UInt32BV
//SNIPPET_START: UInt32BV$
open FStar.BV
open FStar.Tactics

let t = bv_t 32
let v (x:t) = bv2int x
let u x = int2bv x

let sym (#a:Type) (x y:a)
  : Lemma (requires x == y)
          (ensures y == x)
  = ()

let dec_eq (#a:eqtype) (x y:a)
  : Lemma (requires x = y)
          (ensures x == y)
  = ()

let uv_inv (x:t)
  = assert (u (v x) == x)
        by (mapply (`sym);
            mapply (`dec_eq);
            mapply (`inverse_vec_lemma))

let ty (x y:u32_nat)
  : Lemma (requires eq2 #(FStar.UInt.uint_t 32) x y)
          (ensures x == y)
  = ()

let vu_inv (x:u32_nat)
  = assert (v (u x) == x)
        by (mapply (`ty);
            mapply (`sym);
            mapply (`dec_eq);
            mapply (`inverse_num_lemma))

let add_mod a b =
  let y = bvadd #32 a b in
  assert (y == u (FStar.UInt.add_mod #32 (v a) (v b)))
     by  (mapply (`sym);
          mapply (quote (int2bv_add #32));
          pointwise
              (fun _ -> try mapply (`uv_inv) with | _ -> trefl());
          trefl());
  vu_inv ((FStar.UInt.add_mod #32 (v a) (v b)));
  y

let sub_mod a b =
  let y = bvsub #32 a b in
  assert (y == u (FStar.UInt.sub_mod #32 (v a) (v b)))
     by
         (mapply (`sym);
          mapply (quote (int2bv_sub #32));
          pointwise
              (fun _ -> try mapply (`uv_inv) with | _ -> trefl());
          trefl());
  vu_inv ((FStar.UInt.sub_mod #32 (v a) (v b)));
  y

let add a b =
  let y = add_mod a b in
  FStar.Math.Lemmas.modulo_lemma (v a + v b) (pow2 32);
  y

let sub a b =
  let y = sub_mod a b in
  FStar.Math.Lemmas.modulo_lemma (v a - v b) (pow2 32);
  y

let lt (a:t) (b:t) = v a < v b
//SNIPPET_END: UInt32BV$
