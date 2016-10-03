JavaScript backend
===================================================================
### Example ###

1. Create project `javascript`:
   ```
   $ mkdir javascript
   $ cd javascript
   $ echo '{"name": "javascript", "scripts": {"flow": "flow"}}' > package.json
   ```
   
2. Create folders `src` and `build` that would be contain results of 
   running F\* and Babel respectively.

3. Add Flow to our main project: 
   ```
   $ touch .flowconfig
   $ npm install --save-dev flow-bin
   ```
   
4. Create `SimpleTest.fst` file and write some code in F\*

5. Verify this code and extract it in Flow:
   ```
   $ fstar.exe SimpleTest.fst --codegen JavaScript --odir src
   ```
   
   Flow code also can be checked:
   ```
   $ cd src
   $ npm run-script flow
   ```
   
6. Add Babel to our project (to remove types from Flow program):
   ```
   $ npm install -g babel-cli
   $ mkdir -p node_modules && npm install babel-plugin-transform-flow-strip-types
   $ echo '{"plugins": ["transform-flow-strip-types"]}' > .babelrc
   ```
   
   And we can run Babel in the background:
   ```
   $ babel --watch=./src --out-dir=./build
   ```
   
7. Now we can run JavaScript code (version of Node should be 6.6.0):
   ```
   $ cd build
   $ babel-node SimpleTest.js
   ```
