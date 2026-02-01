open Prims
type 'a appemb =
  FStarC_Syntax_Syntax.args ->
    ('a * FStarC_Syntax_Syntax.args) FStar_Pervasives_Native.option
let one (e : 'a FStarC_Syntax_Embeddings_Base.embedding) : 'a appemb=
  fun args ->
    match args with
    | (t, uu___)::xs ->
        let uu___1 =
          FStarC_Syntax_Embeddings_Base.try_unembed e t
            FStarC_Syntax_Embeddings_Base.id_norm_cb in
        (match uu___1 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some v ->
             FStar_Pervasives_Native.Some (v, xs))
let op_let_Question (o : 'uuuuu FStar_Pervasives_Native.option)
  (f : 'uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) :
  'uuuuu1 FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> f v
let op_Less_Star_Greater (u1 : ('a -> 'b) appemb) (u2 : 'a appemb) :
  'b appemb=
  fun args ->
    let uu___ = u1 args in
    op_let_Question uu___
      (fun uu___1 ->
         match uu___1 with
         | (f, args') ->
             let uu___2 = u2 args' in
             op_let_Question uu___2
               (fun uu___3 ->
                  match uu___3 with
                  | (v, args'') ->
                      let uu___4 = let uu___5 = f v in (uu___5, args'') in
                      FStar_Pervasives_Native.Some uu___4))
let op_Less_Star_Star_Greater (u1 : ('a -> 'b) appemb)
  (u2 : 'a FStarC_Syntax_Embeddings_Base.embedding) : 'b appemb=
  let uu___ = one u2 in op_Less_Star_Greater u1 uu___
let pure (x : 'a) : 'a appemb=
  fun args -> FStar_Pervasives_Native.Some (x, args)
let op_Less_Dollar_Greater (u1 : 'a -> 'b) (u2 : 'a appemb) : 'b appemb=
  let uu___ = pure u1 in op_Less_Star_Greater uu___ u2
let op_Less_Dollar_Dollar_Greater (u1 : 'a -> 'b)
  (u2 : 'a FStarC_Syntax_Embeddings_Base.embedding) : 'b appemb=
  let uu___ = pure u1 in
  let uu___1 = one u2 in op_Less_Star_Greater uu___ uu___1
let run (args : FStarC_Syntax_Syntax.args) (u : 'a appemb) :
  'a FStar_Pervasives_Native.option=
  let uu___ = u args in
  match uu___ with
  | FStar_Pervasives_Native.Some (r, []) -> FStar_Pervasives_Native.Some r
  | uu___1 -> FStar_Pervasives_Native.None
let wrap (f : FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
  : 'a appemb=
  fun args ->
    match args with
    | (t, uu___)::xs ->
        let uu___1 = f t in
        (match uu___1 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some v ->
             FStar_Pervasives_Native.Some (v, xs))
