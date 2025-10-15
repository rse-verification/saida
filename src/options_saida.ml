(*option for setting the path to the tricera-binary*)
(*
 * Copyright 2021 Scania CV AB
 * Copyright 2021 KTH
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *
 *  SPDX-License-Identifier: GPL-2.0+
 *)

(*Register the plugin to frama-c*)
module Self = Plugin.Register
  (struct
    let name = "Saida"
    let shortname = "saida"
    let help = "Plug-in for inferring ACSL function contracts for helper functions"
  end)


(*option for setting the output-file*)
(*TODO: use builtin -ocode instead*)
module OutputFile = Self.String
  (struct
    let option_name = "-saida-out"
    let default = "saida.out"
    let arg_name = "output_file"
    let help = "Name of file to store the source code with inferred contracts in."
  end)


(* option to set the path to the "tri" executable *)
module TriceraPath = Self.String
  (struct
    let option_name = "-saida-tricera-path"
    let default = "tri"
    let arg_name = "tricera_path"
    let help = "Sets the path to the TriCera executable"
  end)

(* option to pass custom command line arguments to TriCera *)
module TriceraOptions = Self.String
  (struct
    let option_name = "-saida-tricera-opts"
    let default = "-log"
    let arg_name = "tricera_opts"
    let help = "Options to pass to TriCera (default: -log)."
  end)  

(*option for keeping temporary generated files to/from TriCera*)
module KeepTempFiles = Self.False
  (struct
    let option_name = "-saida-keep-tmp"
    let help = 
      "Keep temporary files. They will be placed in the same \
       directory as the source file. The name follow the template \
       'saida_{harness|result}_<source_file_name>'"
  end)

(*option for enabling the plugin when running frama-c*)
module Enabled = Self.False
  (struct
    let option_name = "-saida"
    let help = "Plug-in for inferring ACSL function contracts for helper functions"
  end)


  (*option for running the -auto plugin on the program with inferred contracts*)
  module Run_wp = Self.False
    (struct
      let option_name = "-saida-wp"
      let help = "Runs the -wp plugin to verify the output using inferred contracts."
    end)
