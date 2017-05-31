JavaScript backend
===================================================================
#### Extraction F\* code to JavaScript ####

As an intermediate step, we translate F\* code to Flow for type checking 
of the extracted code:

.fst -[step 1]-> .flow -[step 2]-> .js -[step 3]-> .js

#### Step 1 ####

To extract F\* code to Flow, F\* has the command line argument `--codegen JavaScript`.
The JavaScript extractor will produce `<ModuleName>.flow` files, which will be saved 
in the directory specified with `--out`. 

#### Step 2 ####

Step 2 is only used for pretty printing of the extracted code.

To verify the code by Flow, one needs to link the extracted code with library `ulib/js`
that is a version of the standard F\* library written in Flow.

#### Step 3 ####

To compile the verified code, one needs to erasure types from `.flow` files and translate
ES modules (export/import) to CommandJS modules.

###  Getting started ###

1. install Node v8.0.0
  
2. install Flow package (https://github.com/facebook/flow)

   - to create `.flowconfig` file, one can use the following command:
   
   ```
   flow init
   ```
   
   - to verify Flow code:
   
   ```
   flow check
   ```

3. how to run Flow code, see https://flow.org/en/docs/install/

   - to erasure Flow types, one can install the following plugin:
   
   ```
   npm install --save-dev babel-cli babel-preset-flow
   ```

   - to translate ES modules (export/import) to CommandJS modules:

   ```
   npm install --save-dev babel-plugin-transform-es2015-modules-simple-commonjs
   ```
   
   - the above plugins should be added to `.babelrc` file
 
4. The `Esformatter` with plugin `esformatter-flow` can be used for pretty printing 
   of Flow code: (see https://github.com/millermedeiros/esformatter)
  
   ```
   esformatter --plugins=esformatter-flow SimpleTest.flow > SimpleTest.js
   ```
   
  ###  Example ###
  
  Example that demonstrates how it works can be found in `examples/javascript` directory.
  The structure of the `javascript` directory can be the following:
  
   /
   
  |- js
  
  |- build
  
  |- node_modules
  
  |- .flowconfig
  
  |- .babelrc
  
  |- package.json
  
  |- Makefile
  
  |- `<ModuleName>.fst` files
  
 where `js` is the directory specified with `--odir` and `build` is the directory spicified 
 with `--out-dir` for babel:
 
   ```
   babel --watch=./js --out-dir=./build
   ```