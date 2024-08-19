module Lib.Exponentiation.Definition

open FStar.Mul

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let lemma_inverse_one #t k =
  lemma_inverse k.cm.one;
  assert (k.cm.mul (inverse cm.one) cm.one == cm.one);
  k.cm.lemma_one (inverse cm.one);
  assert (inverse k.cm.one == cm.one)


val lemma_mul_cancel_inverse: #t:Type -> k:abelian_group t -> a:t -> b:t ->
  Lemma (cm.mul (inverse a) (cm.mul a b) == b)

let lemma_mul_cancel_inverse #t k a b =
  calc (==) {
    cm.mul (inverse a) (cm.mul a b);
    (==) { cm.lemma_mul_assoc (inverse a) a b }
    cm.mul (cm.mul (inverse a) a) b;
    (==) { lemma_inverse a }
    cm.mul cm.one b;
    (==) { cm.lemma_mul_comm cm.one b }
    cm.mul b cm.one;
    (==) { cm.lemma_one b }
    b;
  }

val lemma_cancellation: #t:Type -> k:abelian_group t -> a:t -> b:t -> c:t -> Lemma
  (requires cm.mul a b == cm.mul a c)
  (ensures  b == c)

let lemma_cancellation #t k a b c =
  assert (cm.mul (inverse a) (cm.mul a b) == cm.mul (inverse a) (cm.mul a c));
  lemma_mul_cancel_inverse #t k a b;
  lemma_mul_cancel_inverse #t k a c


let lemma_inverse_id #t k a =
  lemma_inverse a;
  lemma_inverse (inverse a);
  assert (cm.mul (inverse a) a == cm.one);
  assert (cm.mul (inverse (inverse a)) (inverse a) == cm.one);
  cm.lemma_mul_comm (inverse (inverse a)) (inverse a);
  lemma_cancellation k (inverse a) a (inverse (inverse a));
  assert (a == (inverse (inverse a)))


let lemma_inverse_mul #t k a b =
  lemma_inverse (cm.mul a b);
  cm.lemma_mul_comm (inverse (cm.mul a b)) (cm.mul a b);
  assert (cm.mul (cm.mul a b) (inverse (cm.mul a b)) == cm.one);
  calc (==) {
    cm.mul (cm.mul a b) (cm.mul (inverse a) (inverse b));
    (==) { cm.lemma_mul_assoc (cm.mul a b) (inverse a) (inverse b) }
    cm.mul (cm.mul (cm.mul a b) (inverse a)) (inverse b);
    (==) { cm.lemma_mul_comm (cm.mul a b) (inverse a) }
    cm.mul (cm.mul (inverse a) (cm.mul a b)) (inverse b);
    (==) { lemma_mul_cancel_inverse k a b }
    cm.mul b (inverse b);
    (==) { cm.lemma_mul_comm b (inverse b) }
    cm.mul (inverse b) b;
    (==) { lemma_inverse b }
    cm.one;
  };

  assert (cm.mul (cm.mul a b) (inverse (cm.mul a b)) ==
    cm.mul (cm.mul a b) (cm.mul (inverse a) (inverse b)));
  lemma_cancellation k (cm.mul a b) (inverse (cm.mul a b))
    (cm.mul (inverse a) (inverse b))

//---------------------

#push-options "--fuel 2"
let lemma_pow0 #t k x = ()

let lemma_pow1 #t k x = lemma_one x

let lemma_pow_unfold #t k x n = ()
#pop-options

let rec lemma_pow_one #t k n =
  if n = 0 then
    lemma_pow0 k one
  else begin
    lemma_pow_unfold k one n;
    //assert (pow k one n == mul one (pow k one (n - 1)));
    lemma_pow_one k (n - 1);
    //assert (pow k one n == mul one one);
    lemma_one k.one;
    () end


let rec lemma_pow_add #t k x n m =
  if n = 0 then begin
    calc (==) {
      mul (pow k x n) (pow k x m);
      (==) { lemma_pow0 k x }
      mul one (pow k x m);
      (==) { lemma_mul_comm one (pow k x m) }
      mul (pow k x m) one;
      (==) { lemma_one (pow k x m) }
      pow k x m;
      }; () end
  else begin
    calc (==) {
      mul (pow k x n) (pow k x m);
      (==) { lemma_pow_unfold k x n }
      mul (mul x (pow k x (n - 1))) (pow k x m);
      (==) { lemma_mul_assoc x (pow k x (n - 1)) (pow k x m) }
      mul x (mul (pow k x (n - 1)) (pow k x m));
      (==) { lemma_pow_add #t k x (n - 1) m }
      mul x (pow k x (n - 1 + m));
      (==) { lemma_pow_unfold k x (n + m) }
      pow k x (n + m);
      }; () end


let rec lemma_pow_mul #t k x n m =
  if m = 0 then begin
    lemma_pow0 k (pow k x n);
    lemma_pow0 k x;
    () end
  else begin
    calc (==) {
      pow k (pow k x n) m;
      (==) { lemma_pow_unfold k (pow k x n) m }
      mul (pow k x n) (pow k (pow k x n) (m - 1));
      (==) { lemma_pow_mul k x n (m - 1) }
      mul (pow k x n) (pow k x (n * (m - 1)));
      (==) { lemma_pow_add k x n (n * (m - 1)) }
      pow k x (n * m);
    }; () end


let rec lemma_pow_mul_base #t k a b n =
  if n = 0 then begin
    lemma_pow0 k a;
    lemma_pow0 k b;
    lemma_one k.one;
    lemma_pow0 k (mul a b) end
  else begin
    calc (==) {
      mul (pow k a n) (pow k b n);
      (==) { lemma_pow_unfold k a n; lemma_pow_unfold k b n }
      mul (mul a (pow k a (n - 1))) (mul b (pow k b (n - 1)));
      (==) { lemma_mul_comm b (pow k b (n - 1));
       lemma_mul_assoc a (pow k a (n - 1)) (mul (pow k b (n - 1)) b) }
      mul a (mul (pow k a (n - 1)) (mul (pow k b (n - 1)) b));
      (==) { lemma_mul_assoc (pow k a (n - 1)) (pow k b (n - 1)) b }
      mul a (mul (mul (pow k a (n - 1)) (pow k b (n - 1))) b);
      (==) { lemma_pow_mul_base #t k a b (n - 1) }
      mul a (mul (pow k (mul a b) (n - 1)) b);
      (==) { lemma_mul_comm (pow k (mul a b) (n - 1)) b;
	lemma_mul_assoc a b (pow k (mul a b) (n - 1)) }
      mul (mul a b) (pow k (mul a b) (n - 1));
      (==) { lemma_pow_unfold k (mul a b) n }
      pow k (mul a b) n;
    }; () end


let lemma_pow_double #t k x b =
  calc (==) {
    pow k (mul x x) b;
    (==) { lemma_pow_mul_base k x x b}
    mul (pow k x b) (pow k x b);
    (==) { lemma_pow_add k x b b }
    pow k x (b + b);
    }


let rec lemma_inverse_pow #t k x n =
  if n = 0 then begin
    lemma_pow0 cm x;
    assert (inverse (pow cm x n) == inverse cm.one);
    lemma_pow0 cm (inverse x);
    assert (pow cm (inverse x) n == cm.one);
    lemma_inverse_one k end
  else begin
    calc (==) {
      k.inverse (pow k.cm x n);
      (==) { lemma_pow_unfold k.cm x n }
      k.inverse (k.cm.mul x (pow k.cm x (n - 1)));
      (==) { lemma_inverse_mul k x (pow k.cm x (n - 1)) }
      k.cm.mul (k.inverse x) (k.inverse (pow k.cm x (n - 1)));
      (==) { lemma_inverse_pow k x (n - 1) }
      k.cm.mul (k.inverse x) (pow k.cm (k.inverse x) (n - 1));
      (==) { lemma_pow_unfold k.cm (inverse x) n }
      pow k.cm (k.inverse x) n;
    } end


let lemma_pow_neg_one #t k n =
  if n >= 0 then lemma_pow_one k.cm n
  else begin
    lemma_pow_one k.cm (- n);
    lemma_inverse_one k end


val lemma_pow_neg_add_aux: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n < 0 && m >= 0)
  (ensures  cm.mul (pow_neg k x n) (pow_neg k x m) == pow_neg k x (n + m))

let lemma_pow_neg_add_aux #t k x n m =
  assert (cm.mul (pow_neg k x n) (pow_neg k x m) ==
    cm.mul (k.inverse (pow k.cm x (-n))) (pow k.cm x m));

  if -n <= m then begin
  calc (==) {
    k.cm.mul (k.inverse (pow k.cm x (-n))) (pow k.cm x m);
    (==) { lemma_pow_add k.cm x (-n) (m + n) }
    k.cm.mul (k.inverse (pow k.cm x (-n))) (k.cm.mul (pow k.cm x (-n)) (pow k.cm x (m + n)));
    (==) { k.cm.lemma_mul_assoc
      (k.inverse (pow k.cm x (-n))) (pow k.cm x (-n)) (pow k.cm x (m + n)) }
    k.cm.mul (k.cm.mul (k.inverse (pow k.cm x (- n))) (pow k.cm x (-n))) (pow k.cm x (m + n));
    (==) { k.lemma_inverse (pow k.cm x (- n)) }
    k.cm.mul k.cm.one (pow k.cm x (m + n));
    (==) { k.cm.lemma_mul_comm k.cm.one (pow k.cm x (m + n)) }
    k.cm.mul (pow k.cm x (m + n)) k.cm.one;
    (==) { k.cm.lemma_one (pow k.cm x (m + n)) }
    pow k.cm x (m + n);
  } end
  else begin
  calc (==) {
    k.cm.mul (k.inverse (pow k.cm x (-n))) (pow k.cm x m);
    (==) { lemma_pow_add k.cm x (-n-m) m }
    k.cm.mul (k.inverse (k.cm.mul (pow k.cm x (-n-m)) (pow k.cm x m))) (pow k.cm x m);
    (==) { lemma_inverse_mul k (pow k.cm x (-n-m)) (pow k.cm x m) }
    k.cm.mul (k.cm.mul (k.inverse (pow k.cm x (-n-m))) (k.inverse (pow k.cm x m))) (pow k.cm x m);
    (==) { k.cm.lemma_mul_assoc
      (k.inverse (pow k.cm x (-n-m))) (k.inverse (pow k.cm x m)) (pow k.cm x m) }
    k.cm.mul (k.inverse (pow k.cm x (-n-m))) (k.cm.mul (k.inverse (pow k.cm x m)) (pow k.cm x m));
    (==) { k.lemma_inverse (pow k.cm x m) }
    k.cm.mul (k.inverse (pow k.cm x (-n-m))) k.cm.one;
    (==) { k.cm.lemma_one (k.inverse (pow k.cm x (-n-m))) }
    k.inverse (pow k.cm x (-n-m));
  } end


let lemma_pow_neg_add #t k x n m =
  if n >= 0 && m >= 0 then
    lemma_pow_add k.cm x n m
  else begin
    if n < 0 && m < 0 then begin
      calc (==) {
        k.cm.mul (pow_neg k x n) (pow_neg k x m);
        (==) { }
        k.cm.mul (k.inverse (pow k.cm x (- n))) (k.inverse (pow k.cm x (- m)));
        (==) { lemma_inverse_mul k (pow k.cm x (- n)) (pow k.cm x (- m)) }
        k.inverse (k.cm.mul (pow k.cm x (- n)) (pow k.cm x (- m)));
        (==) { lemma_pow_add k.cm x (- n) (- m) }
        k.inverse (pow k.cm x (- n - m));
      } end
    else begin
      if n < 0 && m >= 0 then
        lemma_pow_neg_add_aux k x n m
      else begin
        k.cm.lemma_mul_comm (pow_neg k x n) (pow_neg k x m);
        lemma_pow_neg_add_aux k x m n end
    end
  end


val lemma_pow_neg_mul_mzero: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n < 0 && m = 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_mzero #t k x n m =
  assert (pow_neg k (pow_neg k x n) m ==
    pow k.cm (k.inverse (pow k.cm x (-n))) m);
  assert (pow_neg k x (n * m) == pow k.cm x 0);
  lemma_pow0 k.cm x;
  lemma_pow0 k.cm (k.inverse (pow k.cm x (-n)))


val lemma_pow_neg_mul_nzero: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires m < 0 && n = 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_nzero #t k x n m =
  assert (pow_neg k (pow_neg k x n) m ==
    k.inverse (pow k.cm (pow k.cm x 0) (-m)));
  assert (pow_neg k x (n * m) == pow k.cm x 0);
  lemma_pow0 k.cm x;
  lemma_pow_neg_one #t k m


val lemma_pow_neg_mul_nneg: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n < 0 && m > 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_nneg #t k x n m =
  calc (==) {
    pow_neg k (pow_neg k x n) m;
    (==) { }
    pow k.cm (k.inverse (pow k.cm x (-n))) m;
    (==) { lemma_inverse_pow k (pow k.cm x (-n)) m }
    k.inverse (pow k.cm (pow k.cm x (-n)) m);
    (==) { lemma_pow_mul k.cm x (-n) m }
    k.inverse (pow k.cm x (-n * m));
  }


val lemma_pow_neg_mul_mneg: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n > 0 && m < 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_mneg #t k x n m =
  calc (==) {
    pow_neg k (pow_neg k x n) m;
    (==) { }
    k.inverse (pow k.cm (pow k.cm x n) (-m));
    (==) { lemma_pow_mul k.cm x n (-m) }
    k.inverse (pow k.cm x (-n * m));
  }


let lemma_pow_neg_mul #t k x n m =
  if n >= 0 && m >= 0 then
    lemma_pow_mul k.cm x n m
  else begin
    if n < 0 && m < 0 then
    calc (==) {
      pow_neg k (pow_neg k x n) m;
      (==) { }
      k.inverse (pow k.cm (k.inverse (pow k.cm x (-n))) (-m));
      (==) { lemma_inverse_pow k (pow k.cm x (-n)) (-m) }
      k.inverse (k.inverse (pow k.cm (pow k.cm x (-n)) (-m)));
      (==) { lemma_inverse_id k (pow k.cm (pow k.cm x (-n)) (-m)) }
      pow k.cm (pow k.cm x (-n)) (-m);
      (==) { lemma_pow_mul k.cm x (-n) (-m) }
      pow k.cm x (n * m);
    }
    else begin
      if n < 0 && m >= 0 then begin
        if m = 0 then lemma_pow_neg_mul_mzero k x n m
        else lemma_pow_neg_mul_nneg k x n m end
      else begin
        if n = 0 then lemma_pow_neg_mul_nzero k x n m
        else lemma_pow_neg_mul_mneg k x n m end
      end
  end


let lemma_pow_neg_mul_base #t k a b n =
  if n >= 0 then lemma_pow_mul_base k.cm a b n
  else begin
    calc (==) {
      k.cm.mul (pow_neg k a n) (pow_neg k b n);
      (==) { }
      k.cm.mul (k.inverse (pow k.cm a (-n))) (k.inverse (pow k.cm b (-n)));
      (==) { lemma_inverse_mul k (pow k.cm a (-n)) (pow k.cm b (-n)) }
      k.inverse (k.cm.mul (pow k.cm a (-n)) (pow k.cm b (-n)));
      (==) { lemma_pow_mul_base k.cm a b (- n) }
      k.inverse (pow k.cm (k.cm.mul a b) (-n));
     } end


let lemma_pow_neg_double #t k x b =
  calc (==) {
    pow_neg k (k.cm.mul x x) b;
    (==) { lemma_pow_neg_mul_base k x x b}
    k.cm.mul (pow_neg k x b) (pow_neg k x b);
    (==) { lemma_pow_neg_add k x b b }
    pow_neg k x (b + b);
  }
