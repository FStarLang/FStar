# Notes on primitives

   ## Reusing code instead of copying

   For now each modules for SHA and HMAC functions are separated and
   are hardcoding parameters like block sizes etc...

   I expect that factoring all those is not very complicated and
   we should do it at some point.


   ## Security

   When writing the code for the functions, I made assumptions on
   the fact that some operations as they used the SBuffer and SBytes
   modules are performed in constant-time. In particular I feel that
   the "blit" function might be a problem.

   We should discuss this with JK and Karthik to define the best
   course of action.
