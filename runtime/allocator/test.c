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
#include <stdio.h>
#include <assert.h>
#include "stack.h"

void foo(int n) {
  int *x;
  int *y;
  int *z;
  if (n == 0) {
    return;
  } else {
    if (n % 3 == 0) push_frame(0);
    x = stack_alloc(sizeof(int));
    y = stack_alloc(sizeof(int));
    z = stack_alloc(sizeof(int));
    *x = n;
    *y = n+1;
    *z = n+2;
    foo(n-1);
    assert(is_stack_pointer(x) && is_stack_pointer(y) && is_stack_pointer(z));
    assert(*x == n);
    assert(*y == n+1);
    assert(*z == n+2);
    if (n % 3 == 0) { 
      pop_frame();
      assert(!is_stack_pointer(x) && !is_stack_pointer(y) && !is_stack_pointer(z));
    }
  }
}

int main(int argc, char *argv[]) {
  push_frame(0);
  foo(10);
  pop_frame();
}
