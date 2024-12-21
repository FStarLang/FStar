open Prims
type 'a pretty = {
  pp: 'a -> FStarC_Pprint.document }
let __proj__Mkpretty__item__pp :
  'a . 'a pretty -> 'a -> FStarC_Pprint.document =
  fun projectee -> match projectee with | { pp;_} -> pp
let pp : 'a . 'a pretty -> 'a -> FStarC_Pprint.document =
  fun projectee -> match projectee with | { pp = pp1;_} -> pp1
let (gparens : FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun a ->
    let uu___ =
      let uu___1 = FStarC_Pprint.parens a in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___1 in
    FStarC_Pprint.group uu___
let (gbrackets : FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun a ->
    let uu___ =
      let uu___1 = FStarC_Pprint.brackets a in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___1 in
    FStarC_Pprint.group uu___
let (pp_unit : unit pretty) =
  { pp = (fun uu___ -> FStarC_Pprint.doc_of_string "()") }
let (pp_int : Prims.int pretty) =
  { pp = (fun x -> FStarC_Pprint.doc_of_string (Prims.string_of_int x)) }
let (pp_bool : Prims.bool pretty) = { pp = FStarC_Pprint.doc_of_bool }
let pp_list : 'a . 'a pretty -> 'a Prims.list pretty =
  fun uu___ ->
    {
      pp =
        (fun l ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Pprint.break_ Prims.int_one in
               FStarC_Pprint.op_Hat_Hat FStarC_Pprint.semi uu___3 in
             FStarC_Pprint.flow_map uu___2 (pp uu___) l in
           gbrackets uu___1)
    }
let pp_option : 'a . 'a pretty -> 'a FStar_Pervasives_Native.option pretty =
  fun uu___ ->
    {
      pp =
        (fun o ->
           match o with
           | FStar_Pervasives_Native.Some v ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_Pprint.doc_of_string "Some" in
                   let uu___4 = pp uu___ v in
                   FStarC_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
                 FStarC_Pprint.nest (Prims.of_int (2)) uu___2 in
               FStarC_Pprint.group uu___1
           | FStar_Pervasives_Native.None ->
               FStarC_Pprint.doc_of_string "None")
    }
let pp_either :
  'a 'b . 'a pretty -> 'b pretty -> ('a, 'b) FStar_Pervasives.either pretty =
  fun uu___ ->
    fun uu___1 ->
      {
        pp =
          (fun e ->
             let uu___2 =
               let uu___3 =
                 match e with
                 | FStar_Pervasives.Inl x ->
                     let uu___4 = FStarC_Pprint.doc_of_string "Inl" in
                     let uu___5 = pp uu___ x in
                     FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5
                 | FStar_Pervasives.Inr x ->
                     let uu___4 = FStarC_Pprint.doc_of_string "Inr" in
                     let uu___5 = pp uu___1 x in
                     FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
               FStarC_Pprint.nest (Prims.of_int (2)) uu___3 in
             FStarC_Pprint.group uu___2)
      }
let (comma_space : FStarC_Pprint.document) =
  let uu___ = FStarC_Pprint.break_ Prims.int_one in
  FStarC_Pprint.op_Hat_Hat FStarC_Pprint.comma uu___
let pp_tuple2 : 'a 'b . 'a pretty -> 'b pretty -> ('a * 'b) pretty =
  fun uu___ ->
    fun uu___1 ->
      {
        pp =
          (fun uu___2 ->
             match uu___2 with
             | (x1, x2) ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = pp uu___ x1 in
                     let uu___6 = let uu___7 = pp uu___1 x2 in [uu___7] in
                     uu___5 :: uu___6 in
                   FStarC_Pprint.separate comma_space uu___4 in
                 gparens uu___3)
      }
let pp_tuple3 :
  'a 'b 'c . 'a pretty -> 'b pretty -> 'c pretty -> ('a * 'b * 'c) pretty =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        {
          pp =
            (fun uu___3 ->
               match uu___3 with
               | (x1, x2, x3) ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = pp uu___ x1 in
                       let uu___7 =
                         let uu___8 = pp uu___1 x2 in
                         let uu___9 = let uu___10 = pp uu___2 x3 in [uu___10] in
                         uu___8 :: uu___9 in
                       uu___6 :: uu___7 in
                     FStarC_Pprint.separate comma_space uu___5 in
                   gparens uu___4)
        }
let pp_tuple4 :
  'a 'b 'c 'd .
    'a pretty ->
      'b pretty -> 'c pretty -> 'd pretty -> ('a * 'b * 'c * 'd) pretty
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          {
            pp =
              (fun uu___4 ->
                 match uu___4 with
                 | (x1, x2, x3, x4) ->
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = pp uu___ x1 in
                         let uu___8 =
                           let uu___9 = pp uu___1 x2 in
                           let uu___10 =
                             let uu___11 = pp uu___2 x3 in
                             let uu___12 =
                               let uu___13 = pp uu___3 x4 in [uu___13] in
                             uu___11 :: uu___12 in
                           uu___9 :: uu___10 in
                         uu___7 :: uu___8 in
                       FStarC_Pprint.separate comma_space uu___6 in
                     gparens uu___5)
          }
let pp_tuple5 :
  'a 'b 'c 'd 'e .
    'a pretty ->
      'b pretty ->
        'c pretty ->
          'd pretty -> 'e pretty -> ('a * 'b * 'c * 'd * 'e) pretty
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            {
              pp =
                (fun uu___5 ->
                   match uu___5 with
                   | (x1, x2, x3, x4, x5) ->
                       let uu___6 =
                         let uu___7 =
                           let uu___8 = pp uu___ x1 in
                           let uu___9 =
                             let uu___10 = pp uu___1 x2 in
                             let uu___11 =
                               let uu___12 = pp uu___2 x3 in
                               let uu___13 =
                                 let uu___14 = pp uu___3 x4 in
                                 let uu___15 =
                                   let uu___16 = pp uu___4 x5 in [uu___16] in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         FStarC_Pprint.separate comma_space uu___7 in
                       gparens uu___6)
            }
let pp_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a pretty ->
      'b pretty ->
        'c pretty ->
          'd pretty ->
            'e pretty -> 'f pretty -> ('a * 'b * 'c * 'd * 'e * 'f) pretty
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              {
                pp =
                  (fun uu___6 ->
                     match uu___6 with
                     | (x1, x2, x3, x4, x5, x6) ->
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = pp uu___ x1 in
                             let uu___10 =
                               let uu___11 = pp uu___1 x2 in
                               let uu___12 =
                                 let uu___13 = pp uu___2 x3 in
                                 let uu___14 =
                                   let uu___15 = pp uu___3 x4 in
                                   let uu___16 =
                                     let uu___17 = pp uu___4 x5 in
                                     let uu___18 =
                                       let uu___19 = pp uu___5 x6 in
                                       [uu___19] in
                                     uu___17 :: uu___18 in
                                   uu___15 :: uu___16 in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             uu___9 :: uu___10 in
                           FStarC_Pprint.separate comma_space uu___8 in
                         gparens uu___7)
              }
let pretty_from_showable : 'a . 'a FStarC_Class_Show.showable -> 'a pretty =
  fun uu___ ->
    {
      pp =
        (fun x ->
           let uu___1 = FStarC_Class_Show.show uu___ x in
           FStarC_Pprint.arbitrary_string uu___1)
    }
let showable_from_pretty : 'a . 'a pretty -> 'a FStarC_Class_Show.showable =
  fun uu___ ->
    {
      FStarC_Class_Show.show =
        (fun x -> let uu___1 = pp uu___ x in FStarC_Pprint.render uu___1)
    }