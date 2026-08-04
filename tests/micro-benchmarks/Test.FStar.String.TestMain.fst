(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
   Author: Brian Milnes <briangmilnes@gmail.com>

*)

module Test.FStar.String.TestMain

open FStar.String
open FStar.String.Base
open FStar.String.Properties
open FStar.String.Match
open FStar.IO
open FStar.Class.Printable

let main () =
 print_string "Running TestMain.main() \n";
 print_string("lines \"\" 0 " ^ (to_string (lines "" 0)) ^ "\n");
 assert_norm(strlen "ABCDEF" = 6);
 assert_norm(strlen "ABC123" = 6);
 print_string("streq_upto' \"ABCDEF\" \"ABC123\" 1 " ^ 
             (to_string (streq_upto' "ABCDEF" "ABC123" 1))  ^ "\n");
 print_string("streq_upto' \"ABCDEF\" \"ABC123\" 2 " ^ 
             (to_string (streq_upto' "ABCDEF" "ABC123" 2))  ^ "\n");
 print_string("streq_upto' \"ABCDEF\" \"ABC123\" 3 " ^ 
             (to_string (streq_upto' "ABCDEF" "ABC123" 3))  ^ "\n");
 print_string("streq_upto' \"ABCDEF\" \"ABC123\" 4 " ^ 
             (to_string (streq_upto' "ABCDEF" "ABC123" 4))  ^ "\n")

#push-options "--warn_error -272"
let _ = main ()
#pop-options
