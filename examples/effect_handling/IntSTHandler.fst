module IntSTHandler

open IntST

open FStar.Heap
open FStar.ST
open FStar.Tactics

open FStar.Printf

(* *********************************************** *)

let handle_return (#a:Type) (r:ref int) (v:a) : ST a (requires (fun _ -> True)) 
                                                     (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.return v (sel h0 r))) = 
  v

let handle_get (r:ref int) : ST int (requires (fun _ -> True)) 
                                    (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.get () (sel h0 r))) = 
  read r

let handle_put (r:ref int) (i:int) : ST unit (requires (fun _ -> True))
                                             (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.put i (sel h0 r))) =
  write r i

(* *********************************************** *)

val handle_st : #a:Type -> st a -> ref int -> tactic term
let handle_st #a f r = 
  t <-- quote f;
  t <-- norm_term [delta_only ["IntSTHandler.prog"]] t;

  match inspect t with
  | Tv_App t (arg,argq) -> 
      t_return <-- quote (IntST.return #a);
      t_get    <-- quote IntST.get;
      t_put    <-- quote IntST.put;

      // Handle IntST.return with handle_return
      if (term_eq t t_return) then (t <-- quote (handle_return #a);
                                    r <-- quote r;
                                    return (mk_e_app t [r;arg]))

      // Handle IntST.get_st with handle_get (i.e., with read)
      else if (term_eq t t_get) then (t <-- quote handle_get; 
                                      r <-- quote r;
                                      return (mk_e_app t [r])) 
                                  
      // Handle IntST.put_st with handle_put (i.e., with write)
      else if (term_eq t t_put) then (t <-- quote handle_put;
                                      r <-- quote r;
                                      return (mk_e_app t [r;arg])) 

      else fail "not implemented application case"
  | _ -> fail "not implemented case"

let prog_type = unit

let prog : st prog_type = 
  //IntST.return "foo"
  IntST.put 42
  //IntST.get ()

let synth_prog (r:ref int) : unit -> ST prog_type (requires (fun _ -> True)) 
                                                  (ensures  (fun h0 x h1 -> (x,sel h1 r) == prog (sel h0 r))) 
  = synth_by_tactic
    (
      t  <-- handle_st prog r;
      ty <-- quote Prims.unit;
      f  <-- return (pack (Tv_Abs (fresh_binder ty) t));
      exact (return f)
    )




