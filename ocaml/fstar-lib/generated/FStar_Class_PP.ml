open Prims
type 'a pretty = {
  pp: 'a -> FStar_Pprint.document }
let __proj__Mkpretty__item__pp :
  'a . 'a pretty -> 'a -> FStar_Pprint.document =
  fun projectee -> match projectee with | { pp;_} -> pp
let pp : 'a . 'a pretty -> 'a -> FStar_Pprint.document =
  fun projectee -> match projectee with | { pp = pp1;_} -> pp1
let (pp_unit : unit pretty) =
  { pp = (fun uu___ -> FStar_Pprint.doc_of_string "()") }
let (pp_int : Prims.int pretty) =
  { pp = (fun x -> FStar_Pprint.doc_of_string (Prims.string_of_int x)) }
let (pp_bool : Prims.bool pretty) = { pp = FStar_Pprint.doc_of_bool }
let pp_list : 'a . 'a pretty -> 'a Prims.list pretty =
  fun uu___ ->
    {
      pp =
        (fun l ->
           let uu___1 =
             FStar_Pprint.separate_map FStar_Pprint.colon (pp uu___) l in
           FStar_Pprint.brackets uu___1)
    }
let pp_option : 'a . 'a pretty -> 'a FStar_Pervasives_Native.option pretty =
  fun uu___ ->
    {
      pp =
        (fun o ->
           match o with
           | FStar_Pervasives_Native.Some v ->
               let uu___1 = FStar_Pprint.doc_of_string "Some" in
               let uu___2 = pp uu___ v in
               FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2
           | FStar_Pervasives_Native.None ->
               FStar_Pprint.doc_of_string "None")
    }
let pp_either :
  'a 'b . 'a pretty -> 'b pretty -> ('a, 'b) FStar_Pervasives.either pretty =
  fun uu___ ->
    fun uu___1 ->
      {
        pp =
          (fun e ->
             match e with
             | FStar_Pervasives.Inl x ->
                 let uu___2 = FStar_Pprint.doc_of_string "Inl" in
                 let uu___3 = pp uu___ x in
                 FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3
             | FStar_Pervasives.Inr x ->
                 let uu___2 = FStar_Pprint.doc_of_string "Inr" in
                 let uu___3 = pp uu___1 x in
                 FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3)
      }
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
                   FStar_Pprint.separate FStar_Pprint.comma uu___4 in
                 FStar_Pprint.parens uu___3)
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
                     FStar_Pprint.separate FStar_Pprint.comma uu___5 in
                   FStar_Pprint.parens uu___4)
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
                       FStar_Pprint.separate FStar_Pprint.comma uu___6 in
                     FStar_Pprint.parens uu___5)
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
                         FStar_Pprint.separate FStar_Pprint.comma uu___7 in
                       FStar_Pprint.parens uu___6)
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
                           FStar_Pprint.separate FStar_Pprint.comma uu___8 in
                         FStar_Pprint.parens uu___7)
              }
let from_showable : 'a . 'a FStar_Class_Show.showable -> 'a pretty =
  fun uu___ ->
    {
      pp =
        (fun x ->
           let uu___1 = FStar_Class_Show.show uu___ x in
           FStar_Pprint.arbitrary_string uu___1)
    }