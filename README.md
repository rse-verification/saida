# Saida

This program is licensed under the GPL2 license, see license headers in source code files
and the full license in the LICENSE file.

This is a plugin for Frama-C. Given ab entry-point function with an ACSL contract, it infers
ACSL contracts for helper functions, i.e. functions further down the call tree. It was
originally developed for Frama-C v23.1 but has been tested with Frama-C versions <= 28.1.
Please note that the plugin is experimental and still under development so that no results
are guaranteed.


## Install TriCera  
This plugin requires TriCera to be installed on your system, see:  
https://github.com/uuverifiers/tricera  


## Install and run Saida

* Installation:  
Register as plug-in using these commands (Ubuntu):

	* For Frama-C version <= 25:
```make; make install```
	* For Frama-C version 26 and onward:
```dune build @install && dune install```

* Execution:  
Run the plugin on file test.c as: 
```frama-c -saida -saida-tricera-path <path-to-tricera> test.c```  
where path-to-tricera is the path to the TriCera executable (tri). If no path is provided, defaults to `~/Documents/tricera/tri`

* Lib-entry option:  
Optionally, use the Frama-C lib-entry option to non-deterministically assign all global
  variables in TriCera before analysis, e.g.:  
```frama-c -saida test.c -saida-tricera-path <path-to-tricera> -lib-entry```

* Verification option:  
Use the *-saida-wp* option for running the -wp plugin to verify the inferred contracts and verify that the top-level
  contract for the main function can be verified by relying on inferred contract, use as:  
  ```frama-c -saida -saida-tricera-path <path-to-tricera> -saida-wp test.c```


## Limitations
The plugin is currently limited to programs/specifications following these rules:
* Only one main function, with return type void.s
* The main function should contain a top-level contract containing a requires
  clause and an ensures clause.
* Any non-main function should _not_ contain a contract.
  I.e., only 1 contract allowed in the file.
* The non-main functions has to be called somewhere from within the file
* Currently does not work for arrays or floats.

Aside from the limitations listed above, many more limitations/bugs expected to exist.  

## *Summary*  
The execution of the plugin can be summarized as:  
Step 1: convert the top-level contract to a TriCera harness function  
Step 2: Merge the harness function with the source code (this result is stored in `tmp_harness_source_merged.c`)  
Step 3: Run tricera on the result from step 2  
Step 4: Merge the inferred contracts from step 3 with the source code (this result is stored in `tmp_inferred_source_merged.c`)  
Step 5: (optional) Run the wp plugin on the result from step 4
