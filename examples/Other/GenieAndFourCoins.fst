module GenieAndFourCoins
(*
  A verified algorithm which solves the 'Genie and Four Coins' Problem
  'http://echochamber.me/viewtopic.php?t=110425'
  Author: A Manning
  github.com/A-Manning
*)

(*
  We represent the table as
  [a b]
  [d c]
  Each variable [a,b,c,d] represents a coin on the table.
  The coins [a,c] and [b,d] are on opposite corners to one another.
*)
type table =
  | Tab : a:bool -> b:bool -> c:bool -> d:bool -> table

// Define the different 'forms' of table.

(*
  A winning table is
  [a a]
  [a a]
  Such that a is either true or false
*)
val is_W: (t:table) -> Tot bool
let is_W (t:table) =
  if (t.a = t.b && t.b = t.c && t.c = t.d) then true
  else false
(*
  A diagonal table is
  [a b]
  [b a]
  Such that a is true or false and b is not a.
*)
val is_D: (t:table) -> Tot bool
let is_D (t:table) =
  if (t.a = t.c && t.b = t.d && t.a <> t.b) then true
  else false
(*
  A side table is either
  [a a] or [a b]
  [b b]    [a b]
  Such that a is true or false and b is not a.
*)
val is_S: (t:table) -> Tot bool
let is_S (t:table) =
  if ((t.a = t.b && t.d = t.c && t.a <> t.d)
    ||(t.a = t.d && t.b = t.c && t.a <> t.b))
    then true
  else false

(*
  A corner table is either
  [a b] or [b a] or [b b] or [b b]
  [b b]    [b b]    [a b]    [b a]
  Such that a is true or false and b is not a.
*)
val is_C: (t:table) -> Tot bool
let is_C (t:table) =
  if ((t.a <> t.b && t.b = t.c && t.c = t.d)
    ||(t.b <> t.a && t.a = t.c && t.c = t.d)
    ||(t.c <> t.b && t.a = t.b && t.b = t.d)
    ||(t.a = t.b && t.b = t.c && t.c <> t.d))
    then true
  else false

// Rotates the table counterclockwise 90 degrees
val rotate: (t:table) -> Tot (t':table)
let rotate (t:table) = Tab t.b t.c t.d t.a

// Rotates the table counterclockwise 90 degrees N times.
val rotateN: (t:table) -> (n:nat) -> Tot (t':table) (decreases n)
let rec rotateN (t:table) (n:nat) =
  match n with
  | 0 -> t
  | 1 -> rotate t
  | _ -> rotate(rotateN t (n-1))

// Proofs that table form is invariant w.r.t single 90 degree rotation
(*
val rotate_inv_D: (t:table) -> Lemma (requires is_D t) (ensures is_D (rotate t))
let rec rotate_inv_D (t:table) = ()

val rotate_inv_S: (t:table) -> Lemma (requires is_S t) (ensures is_S (rotate t))
let rec rotate_inv_S (t:table) = ()

val rotate_inv_C: (t:table) -> Lemma (requires is_C t) (ensures is_C (rotate t))
let rec rotate_inv_C (t:table) = ()

val rotate_inv_W: (t:table) -> Lemma (requires is_W t) (ensures is_W (rotate t))
let rec rotate_inv_W (t:table) = ()
*)
// Proofs that table form is invariant w.r.t several 90 degree rotations

val rotateN_inv_D: (t:table) -> (n:nat) ->
  Lemma (requires is_D t) (ensures is_D (rotateN t n))
  [SMTPat (rotateN t n)]
let rec rotateN_inv_D (t:table) (n:nat) =
  match n with
  | 0 -> ()
  | _ -> rotateN_inv_D t (n-1)

val rotateN_inv_S: (t:table) -> (n:nat) ->
  Lemma (requires is_S t) (ensures is_S (rotateN t n))
  [SMTPat (rotateN t n)]
let rec rotateN_inv_S (t:table) (n:nat) =
  match n with
  | 0 -> ()
  | _ -> rotateN_inv_S t (n-1)

val rotateN_inv_C: (t:table) -> (n:nat) ->
  Lemma (requires is_C t) (ensures is_C (rotateN t n))
  [SMTPat (rotateN t n)]
let rec rotateN_inv_C (t:table) (n:nat) =
  match n with
  | 0 -> ()
  | _ -> rotateN_inv_C t (n-1)

val rotateN_inv_W: (t:table) -> (n:nat) ->
  Lemma (requires is_W t) (ensures is_W (rotateN t n))
  [SMTPat (rotateN t n)]
let rec rotateN_inv_W (t:table) (n:nat) =
  match n with
  | 0 -> ()
  | _ -> rotateN_inv_W t (n-1)

// Introduce the possible moves the player may make

(*
  flipD ('Flip Diagonal'):
  let x' = (not x)
  then
  flipD ([a b]) -> [a b']
        ([d c])    [d' c]
  Such that a is true or false and b is not a.
*)
val flipD: (t:table) -> Tot (t':table)
let flipD (t:table) = Tab t.a (not t.b) t.c (not t.d)

// Proofs about the effects of flipD on different table forms
val flipD_inv_C: (t:table) ->
  Lemma (requires is_C t) (ensures is_C (flipD t))
  [SMTPat (flipD t)]
let flipD_inv_C (t:table) = ()
val flipD_var_D: (t:table) ->
  Lemma (requires is_D t) (ensures is_W (flipD t))
  [SMTPat (flipD t)]
let flipD_var_D (t:table) = ()
val flipD_var_S: (t:table) ->
  Lemma (requires is_S t) (ensures (is_D (flipD t) \/ is_S (flipD t)))
  [SMTPat (flipD t)]
let flipD_var_S (t:table) = ()

(*
  flipS('Flip Side'):
  flipS ([a b]) -> [a b']
        ([d c])    [d c']
  Such that a is true or false and b is not a.
*)
val flipS: (t:table) -> Tot (t':table)
let flipS (t:table) = Tab t.a (not t.b) (not t.c) t.d

// Proofs about the effects of flipS on different table forms
val flipS_inv_C: (t:table) ->
  Lemma (requires is_C t) (ensures is_C (flipS t))
  [SMTPat (flipS t)]
let flipS_inv_C (t:table) = ()
val flipS_var_D: (t:table) ->
  Lemma (requires is_D t) (ensures is_S (flipS t))
  [SMTPat (flipS t)]
let flipS_var_D (t:table) = ()
val flipS_var_S: (t:table) ->
  Lemma (requires is_S t) (ensures (is_D (flipS t) \/ is_W (flipS t)))
  [SMTPat (flipS t)]
let flipS_var_S (t:table) = ()

(*
  flipC('Flip Corner'):
  flipC ([a b]) -> [a' b]
        ([d c])    [d  c]
  Such that a is true or false and b is not a.
*)
val flipC: (t:table) -> Tot (t':table)
let flipC (t:table) = Tab (not t.a) t.b t.c t.d

// Proofs about the effects of flipC on different table forms
val flipC_var_S: (t:table) ->
  Lemma (requires is_S t) (ensures is_C (flipC t))
  [SMTPat (flipC t)]
let flipC_var_S (t:table) = ()
val flipC_var_D: (t:table) ->
  Lemma (requires is_D t) (ensures is_C (flipC t))
  [SMTPat (flipC t)]
let flipC_var_D (t:table) = ()
val flipC_var_C: (t:table) -> Lemma (requires is_C t)
  (ensures (is_D (flipC t) \/ is_S (flipC t) \/ is_W (flipC t)))
  [SMTPat (flipC t)]
let flipC_var_C (t:table) = ()

(*
// Lemmas necessary to prove the algorithm's correctness
// First move
val flipD_var_T_0: (t:table) -> Lemma (requires is_W t = false)
  (ensures (is_W (flipD t) \/ is_S (flipD t) \/ is_C (flipD t)))
  [SMTPat (flipD t)]
let flipD_var_T_0 (t:table) = ()

// Second move
val flipS_var_T_1: (t:table) -> Lemma (requires (is_S t \/ is_C t))
  (ensures (is_W (flipS t) \/ is_D (flipS t) \/ is_C (flipS t)))
  [SMTPat (flipS t)]
let flipS_var_T_1 (t:table) = ()

// Third move
val flipD_var_T_2: (t:table) -> Lemma (requires (is_D t \/ is_C t))
  (ensures (is_W (flipD t) \/ is_C (flipD t)))
  [SMTPat (flipD t)]
let flipD_var_T_2 (t:table) = ()

// Fourth move
val flipC_var_T_3: (t:table) -> Lemma (requires is_C t)
  (ensures (is_W (flipC t) \/ is_S (flipC t) \/ is_D (flipC t)))
  [SMTPat (flipC t)]
let flipC_var_T_3 (t:table) = ()

// Fifth move
val flipD_var_T_4: (t:table) -> Lemma (requires (is_S t \/ is_D t))
  (ensures (is_W (flipD t) \/ is_S (flipD t)))
  [SMTPat (flipD t)]
let flipD_var_T_4 (t:table) = ()

// Sixth move
val flipS_var_T_5: (t:table) -> Lemma (requires is_S t)
  (ensures (is_W (flipS t) \/ is_D (flipS t)))
  [SMTPat (flipS t)]
let flipS_var_T_5 (t:table) = ()

// Seventh move
val flipD_var_T_6: (t:table) -> Lemma (requires is_D t)
  (ensures is_W (flipD t))
  [SMTPat (flipD t)]
let flipD_var_T_6 (t:table) = ()
*)


// solveTable takes a table and 6 rotations and produces a winning table
val solveTable: (t_0:table) -> (r_0:nat) -> (r_1:nat) -> (r_2:nat) ->
(r_3:nat) -> (r_4:nat) -> (r_5:nat) -> (r_6:nat) -> Tot (t':table{is_W t'})
let solveTable (t_0:table) (r_0:nat) (r_1:nat) (r_2:nat) (r_3:nat)
(r_4:nat) (r_5:nat) (r_6:nat) =
  if is_W t_0 then t_0
  else // First move is Flip Diagonal
    let (t_1:table{is_W t_1 \/ is_S t_1 \/ is_C t_1}) =
      rotateN (flipD t_0) r_0 in
    if is_W t_1 then t_1
    else // Second move is Flip Side
      let (t_2:table{is_W t_2 \/ is_D t_2 \/ is_C t_2}) =
       rotateN (flipS t_1) r_1 in
      if is_W t_2 then t_2
      else // Third move is Flip Diagonal
        let (t_3:table{is_W t_3 \/ is_C t_3}) =
         rotateN (flipD t_2) r_2 in
        if is_W t_3 then t_3
        else // Fourth move is Flip Corner
         let (t_4:table{is_W t_4 \/ is_S t_4 \/ is_D t_4}) =
          rotateN (flipC t_3) r_3 in
          if is_W t_4 then t_4
          else // Fifth move is Flip Diagonal
            let (t_5:table{is_W t_5 \/ is_S t_5}) =
             rotateN (flipD t_4) r_4 in
            if is_W t_5 then t_5
            else // Sixth move is Flip Side
              let (t_6:table{is_W t_6 \/ is_D t_6}) =
               rotateN (flipS t_5) r_5 in
              if is_W t_6 then t_6
              else // Final move is Flip Diagonal
                let (t_7:table{is_W t_7}) =
                 rotateN (flipD t_6) r_6 in
                t_7
