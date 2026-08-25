# Saida

[![Build Status](https://github.com/rse-verification/saida/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/rse-verification/saida/actions/workflows/build.yml)

This program is licensed under the GPL2 license, see license headers in source code files
and the full license in the LICENSE file.

This is a plugin for Frama-C. Given an entry-point function with an ACSL contract, it infers
ACSL contracts for helper functions, i.e. functions further down the call tree. Current version
has been tested with Frama-C v31.
Please note that the plugin is experimental and still under development so that no results
are guaranteed.


## Install TriCera
This plugin requires TriCera to be installed on your system, see: 
https://github.com/uuverifiers/tricera  


## Install and run Saida

* Installation:  
Register as plug-in using these commands (Ubuntu):
```dune build @install && dune install```

* Execution:  
Run the plugin on one C translation unit, such as `test.c`, as:
```frama-c -saida -saida-tricera-path <path-to-tricera> test.c```  
where path-to-tricera is the path to the TriCera executable (tri). If no path is
provided, the plugin will use `tri` in `$PATH`. Included headers are processed
normally, but Saida rejects invocations with zero input files or more than one
input C source file. Cross-translation-unit inference is not supported; the one
input translation unit must contain the functions Saida is expected to analyze.

TriCera options supplied through `-saida-tricera-opts` are split into an argument
vector; shell expansion is not performed. Quotes may be used to keep spaces inside
one option value. Source, executable, and output paths may contain spaces or shell
metacharacters.

* Lib-entry option:  
Optionally, use the Frama-C lib-entry option to non-deterministically assign all global
  variables in TriCera before analysis, e.g.:  
```frama-c -saida test.c -saida-tricera-path <path-to-tricera> -lib-entry```

* Verification option:  
Use the *-saida-wp* option for running the -wp plugin to verify the inferred contracts and verify that the top-level
  contract for the main function can be verified by relying on inferred contract, use as:  
  ```frama-c -saida -saida-tricera-path <path-to-tricera> -saida-wp test.c```


### Summary
The execution of the plugin can be summarized as:  
Step 1: convert the top-level contract to a TriCera harness function  
Step 2: Merge the harness function with the source code 
  (this result is stored in `/tmp/saida_harness_<file-name>.c`)  
Step 3: Run tricera on the result from step 2
  (this result is stored in `/tmp/saida_result_<file-name>.c`)  
Step 4: Merge the inferred contracts from step 3 with the source code
  (this result is stored in `saida.out` or file given by `-saida-out=<file>` option)  
Step 5: (optional) Run the wp plugin on the result from step 4

## Development

A suitable development environment for the plugin is provided by the
[AutoDeduct toolchain docker image](https://github.com/rse-verification/auto-deduct-toolchain).

Please note that there are several `TODO` and `FIX ME` sprinkled around the code base.
There are several test cases with `TODO` to indicate that their oracle file contains
the result of an unsupported feature. 

## Limitations
The plugin is currently limited to programs/specifications following these rules:
* The entry-point function should contain a top-level contract containing a requires
  clause and an ensures clause.
* The non-entry-point functions has to be called somewhere from within the file
* Currently does not support floating points.
* Partial support for arrays and stack pointers.
* Heap pointers are generally supported (but bugs exist in some cases in the translation to ACSL).
* Does not support inference of contracts for functions with local static variables.
* In the ACSL contract, only ensures, requires, and supported behavior-assumes clauses over C expressions are supported.
  Universal quantification is supported only in postconditions. Universal preconditions and
  behavior assumptions are rejected with `SAIDA-E004`; existential quantification is rejected in
  every clause position with `SAIDA-E001`. Saida does not approximate unsupported quantifiers.
  User-defined predicates remain unsupported. Saida supports a deliberately small, pure subset
  of term-valued ACSL logic functions: mathematical-integer formals and result; integer literals;
  direct formal references; unary negation; and `+`, `-`, or `*`. Applications may use direct
  signed C `int` values, `\\result`, or one `\\old` wrapper. The reducer requires TriCera's
  mathematical arithmetic mode (the default, or `-arithMode:math`) and expands the definition in
  Frama-C's typed ACSL AST before building the harness. Casts, labels other than `\\old`, memory
  reads, offsets, globals, type parameters, recursion, calls to other logic functions, and
  predicate applications are rejected with `SAIDA-E001` rather than approximated.
* Function behaviors with supported C-expression clauses preserve their ACSL roles: a named
  behavior's `assumes` guards its postconditions, while `assumes ==> requires` constrains valid
  harness inputs after `complete` and `disjoint` have been checked under the function's main
  preconditions. `complete` declarations become pre-call coverage assertions and `disjoint`
  declarations become pre-call pairwise-exclusion assertions; neither is assumed by the harness,
  and Saida accepts them only when TriCera reports that the resulting harness is safe.
* `check` and `admit` requires/ensures are rejected before inference because the current TriCera
  harness does not preserve their distinct proof semantics.
* Function-level `assigns` clauses are preserved and reported as `SAIDA-W001` because Saida does
  not encode their frame semantics in the inference harness. The complete generated contract must
  therefore be checked by downstream WP. Behavior-specific `assigns` clauses are rejected.
  Allocation clauses, `terminates`/`decreases` clauses, extended clauses, and non-normal
  postconditions are also rejected rather than silently omitted.
* A `\let` binding created outside `\old` or `\at` cannot be used inside that labelled
   expression. Saida rejects this pattern instead of inlining a post-state alias into an
   old-state expression; move the binding inside the label or write the expression explicitly.
  
Aside from the limitations listed above, many more limitations/bugs expected to exist.  
