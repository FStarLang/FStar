# Notes on primitives

   ## Overall status

   This work is an experiment and should not be used as it is.
   It is probably incorrect and has anyway a weak specification
   for now. At some point, when we are happy with it, it will be
   relased in the master branch.


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


   ## Verification

   For some reason, after updating FStar, verification fails for
   some primitives... I do not understand why this is happening.
   =(   <-- This is my not so happy face...

   Extraction and execution still works though, I expect that
   mostly, the specs are incorrect.

   Update: It seems that the commit I compiled F* in, introduced
   inconcistencies, so basically my verification was broken and
   I was able to prove things I should not have been able to...
   This doesn't change my schedule for the future work.


   ## Future work

   In the few next weeks, after discussing with Karthik and JK,
   I'll proceed with:
   - Improving the specifications (mem. safety everywhere + more ?)
   - Factor out the duplicated code
   - Port all the primitives to Universes
   - Extract and run after compilation to C
