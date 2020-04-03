(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Alt

open FStar.Tactics

let tfail s () = fail s

let _ = assert True by (tfail "1" <|> tfail "2" <|> tfail "3" <|> trivial) ()

let _ = assert True by (let i =
                          Tactics.first [(fun () -> fail "1"; 1);
                                         (fun () -> fail "2"; 2);
                                         (fun () -> fail "3"; 3);
                                         (fun () ->           4);
                                         (fun () -> fail "5"; 5);
                                         (fun () ->           6);
                                         ]
                        in guard (i = 4))
