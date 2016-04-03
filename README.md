# SearchRepair-SymEx
OCaml utilities to support Java-based SearchRepair.

This repository contains two OCaml programs that support the semantic search for
program repair project:

transform: statically transforms IntroClass programs to make them easier for
Yalin's Java code to reason about.

pathgen: statically generates paths through a C program using symbolic
execution.

### Dependencies ###

This is needlessly complicated because of various deprecated language features
and annoying incompatabilities between OCaml and...everything.  Note that I use
opam (http://opam.ocaml.org/) to manage my OCaml and OCaml package
installations.  I recommend you do the same.

Both transform and pathgen require:

+ OCaml: I'm currently runing version 4.01.0, which is not the latest.  As of last time I tried, the latest version of OCaml and the latest version of Cil are not compatible.  This may no longer be true, but I haven't checked recently.  

+ findlib/ocamlfind: opam makes this easy.

+ a local gcc:  If I remember correctly, various aspects of this toolchain don't play nicely with Clang, which OS X silently swapped in for gcc sometime around version 10.8.  I maintain a local root (at ~/local-root, which has a bin/ and lib/ and so on) where I've installed (from source!) gcc 4.9.0 (...among other things; it's actually a pretty useful setup).  I don't recommend replacing clang outright, at the system level; that causes even more headaches. Among other things, building the Z3 API for ocaml won't work without it.  Having built it, and before I try to build the Z3 api (see below), I do export PATH=/Users/clegoues/local-root/bin:$PATH.  

+ Cil: http://kerneis.github.io/cil/  The version I have installed is 1.7.3. Cil has other dependencies, but opam should manage them for you. 


pathgen also requires:

+ z3: https://github.com/Z3Prover/z3  Specifically, you need the ocaml bindings.  This is where things get complicated.  See next section.


### Z3 OCaml Bindings ###

This requires camlidl, which opam should be able to install for you.

First, from the Z3 github page, clone the z3 project and then checkout 40269c8511; this may or may not correspond to the tagged 4.3.2 release; I don't remember.  One day we will update this code to use the latest bindings, but today is not that day.

Second, build the regular z3.  This is relatively straightforward/the toplevel README does not lie. 

After building the regular z3, but before building the ml API, do:
`export PATH=/path/to/real/gccbin:$PATH`
`eval \`opam config env\``

Then, cd src/api/ml

`sh generate_mlapi.sh`  This modifies z3\_stubs.c (this step took me a long time to reconstruct!)

Next, there is a script in this directory called build-lib.sh.  It's close to what we need, but not quite.  

First, add camlidl to the include directories for the ocaml compiler.  Below/near the lines that define CFLAGS, XCDBG, etc, add:
`CAMLIDL=$(ocamlfind query camlidl)`

Add the include argument to the first three calls to ocamlc/ocamlopt (lines 11, 13, and 17, in the version I'm looking at.  So line 11 will look like: 
`ocamlc -I $CAMLIDL -c $XCDBG z3_stubs.c z3_theory_stubs.c z3.mli z3.ml`)

Second, tell the subsequent commands where the z3 library is located; it assumes (incorrectly) that it can be found at ../lib/.  At the top, I add:
`Z3LIB="/path/to/z3/build/"`

Then, after the second ar command (the one that makes libz3stubs.a, about halfway through the script), all subsequent calls to ocamlc and ocamlopt need to have the -L$PWD/../lib changed to -L$Z3LIB.  

Then:

`sh build-lib.sh`

It will spit out a gigantic pile of warnings; so long as no errors are issued (I grep for them), the warnings can be ignored.


### How can I tell if it works? ###

At the toplevel of this repository, edit the Makefile so that the PATH\_TO\_Z3A points to the ML API directory on your machine.

`make pathgen`

`./pathgen atris_comb.c` should then spit out a bunch of paths to stdout.  You can give it a smaller C program if you want, but really you just want to make sure it produces output/doesn't segfault.
