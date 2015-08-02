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

#ifndef __BITMASK_H__
#define __BITMASK_H__

/*
  This file implements a library for implementing sets of natural
  numbers via bitmasks (bits are numbered starting at 0).  A bitmask
  is represented as an array of unsigned characters.  

  As an example usage:
  unsigned char m[4] = {0,0,0,0}; // set = {}
  setbit(m,0);  // set = {0}
  setbit(m,1);  // set = {0,1}
  unsetbit(m,1); // set = {0}
  setbit(m,2);  // set = {0,2}
  unsetbit_rng(m,0,2); // set = {}

  The eachbit function, explained below, is an iterator over the set,
  invoking the provided function with each bit in that set, as an
  argument.
*/

/* [setbit m b] sets bit [b] in the given map [m]. We assume [m] has
   sufficient memory allocated to it to set [b]. */
void setbit(unsigned char *map, int bit);

/* [unsetbit m b] unsets bit [b] in the given map [m]. We assume [m]
   has sufficient memory allocated to it to unset [b]. */
void unsetbit(unsigned char *map, int bit);

/* [unsetbit_rng m b l] unsets bits [b] up to [b+l-1] in the given map
   [m]. We assume [m] has sufficient memory allocated to it to unset this range. */
void unsetbit_rng(unsigned char *map, int bit, int len);

/* [eachbit m f e] invokes function [f] on each set bit in [m]. In
   particular, for each bit b that is set in [m], this routine will
   call [f(e,b)].  */
typedef void (*bitfun)(void *env, int index);
void eachbit(unsigned char *map, int maxbit, bitfun f, void *env);

#endif
