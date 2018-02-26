module IntSTHandler

open IntST

open FStar.Heap
open FStar.ST
open FStar.Tactics

open FStar.Printf

(* *********************************************** *)

let handle_return (r:ref int) (#a:Type) (v:a) : ST a (requires (fun _ -> True)) 
                                                     (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.return v (sel h0 r))) = 
  v

let handle_get (r:ref int) : ST int (requires (fun _ -> True)) 
                                       (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.get () (sel h0 r))) = 
  read r

let handle_put (r:ref int) (i:int) : ST unit (requires (fun _ -> True))
                                             (ensures  (fun h0 x h1 -> (x,sel h1 r) == IntST.put i (sel h0 r))) =
  write r i

(* *********************************************** *)

let rec collect_app_ref' (ref:term) (args:list (a:argv{a << ref})) (t:term{t == ref \/ t << ref}) 
  : Tot (t:term{t == ref \/ t << ref} * list (a:argv{a << ref})) (decreases t) =
  match inspect t with
  | Tv_App l r ->
      collect_app_ref' ref (r::args) l
  | _ -> (t, args)

val collect_app_ref : ref:term -> t:term{t == ref \/ t << ref} -> (t:term{t == ref \/ t << ref}) * list (a:argv{a << ref})
let collect_app_ref ref = collect_app_ref' ref []

val args_wo_ref : #ref:term -> list (a:argv{a << ref}) -> list argv
let rec args_wo_ref #ref args =
  match args with 
  | [] -> []
  | a::args -> a :: args_wo_ref args

val handle_st : #a:Type -> st a -> ref int -> tactic term
let handle_st #a f r = 
  t <-- quote f;
  r <-- quote r;
  t <-- norm_term [delta_only ["IntSTHandler.prog"]] t;

  t_ret <-- quote IntST.return;
  t_get <-- quote IntST.get;
  t_put <-- quote IntST.put;

  match inspect t with
  | Tv_App _ _ ->
      let (t_fun,args) = collect_app_ref t t in

      // Handle IntST.return with handle_return (i.e., with ST's return)
      if (term_eq t_fun t_ret) then (t_fun <-- quote handle_return;
                                     let args = (r,Q_Explicit)::(args_wo_ref args) in
                                     return (mk_app t_fun args))

      // Handle IntST.get_st with handle_get (i.e., with ST's read)
      else if (term_eq t_fun t_get) then (t_fun <-- quote handle_get; 
                                          let args = [r,Q_Explicit] in
                                          return (mk_app t_fun args))

      // Handle IntST.put_st with handle_put (i.e., with ST's write)
      else if (term_eq t_fun t_put) then (t_fun <-- quote handle_put; 
                                          let args = (r,Q_Explicit)::(args_wo_ref args) in
                                          return (mk_app t_fun args))

      else fail "not implemented application case"
  | _ -> fail "not implemented case"

let prog_type = int

let prog : st prog_type = 
  //IntST.return 0
  IntST.get ()
  //IntST.put 42

let synth_prog (r:ref int) : unit -> ST prog_type (requires (fun _ -> True)) 
                                                  (ensures  (fun h0 x h1 -> (x,sel h1 r) == prog (sel h0 r))) 
  = synth_by_tactic
    (
      t  <-- handle_st prog r;
      ty <-- quote Prims.unit;
      let f = pack (Tv_Abs (fresh_binder ty) t) in
      //print (term_to_string f);;
      exact (return f)
    )




