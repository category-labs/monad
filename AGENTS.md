If you are given a Coq programming task, consider reading the following in  monadproofs/fmai/prompts/ depending on the task at hand
- coding.md  : tips for general Coq programming
- sep.md : tips for Coq programs involving separation logic assertions
- specs.md : tips for writing specs of C++ programs in Coq

This repo uses a dune build system for Coq stuff. to build a Coq .v file, execute `dune build target` where target is "o" appended to the path of the .v file relative to the current directory, e.g. `dune build monadproofs/proofs/dbspecs.vo`
When you are asked to edit a Coq .v file, you must do dune build to ensure it compiles.
If you want to issue Coq queries like Search/Print/... you can put them in the .v file at a place BEFORE the first error and then `dune build`, which invokes `coqc`, will show the output of the query.


