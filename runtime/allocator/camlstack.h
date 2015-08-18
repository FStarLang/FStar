/*
   Copyright 2015 Michael Hicks, Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#ifndef _CAMLSTACK_H_
#define _CAMLSTACK_H_

#include <caml/mlvalues.h>

value stack_caml_alloc(mlsize_t wosize, tag_t tag, int nbits, int *mask);
value stack_caml_alloc_string (mlsize_t lenb);
value stack_caml_alloc_tuple (mlsize_t n, int nbits, int *mask);

#endif
