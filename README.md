# Saida

This program is licensed under the GPL2 license, see license headers in source code files
and the full license in the LICENSE file.

ACSL Contract inference for helper functions.
Developed for Frama-C v23.1 but also seems to work for v24.  
Please note that the plugin is experimental and still under development so that no results are guaranteed.


## Install TriCera  
This plugin requires TriCera to be installed on your system, see:  
https://github.com/uuverifiers/tricera  


## Install and run Saida

* Installation:  
Register as plug-in using these commands (Ubuntu)
```make; make install```

* Execution:  
Run the plugin on file test.c as: 
```frama-c -saida -tri-path <path-to-tri> test.c```  
where path-to-tri is the path to the TriCera executable (tri). If no path is provided, defaults to `~/Documents/tricera/tri`

* Lib-entry option:  
Optionally, use the Frama-C lib-entry option to non-deterministically assign all global
  variables in TriCera before analysis, e.g.:  
```frama-c -saida test.c -tri-path <path-to-tri> -lib-entry```

* Verification option:  
Use the *-saida-wp* option for running the -wp plugin to verify the inferred contracts and verify that the top-level
  contract for the main function can be verified by relying on inferred contract, use as:  
  ```frama-c -saida -tri-path <path-to-tri> -saida-wp test.c```


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
Step 2: Merge the harness function with the source code  
Step 3: Run tricera on the result from step 2  
Step 4: Merge the inferred contracts from step 3 with the source code  
Step 5: (optional) Run the wp plugin on the result from step 4
