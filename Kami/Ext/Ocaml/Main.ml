open Format
open Target
open PP
open Arg

let iAddrSize: int = 10

let arg_debug = ref false
let set_debug () = arg_debug := true
let arg_header_file_name = ref "Header.bsv"
let set_header_file_name fn = arg_header_file_name := fn
let arg_output_file_name = ref ""
let set_output_file_name fn = arg_output_file_name := fn
let arg_top_module_name = ref "Top"
let set_top_module_name mn = arg_top_module_name := mn

let arg_spec =
  [("-d", Arg.Unit set_debug, "Enables debug mode");
   ("-header", Arg.String set_header_file_name, "Sets a header");
   ("-top", Arg.String set_top_module_name, "Sets a top-module name")]

let usage_msg =
  "Usage: ./Main.native [-d] [-header header_file_name] [-top top_module_name] output_file_name\n"

let () =
  Arg.parse arg_spec set_output_file_name usage_msg;
  if String.length !arg_output_file_name = 0 then
    Printf.printf "Usage: %s [-d] [-header header_file_name] [-top top_module_name] output_file_name\n" Sys.argv.(0)
  else
    let oc = open_out !arg_output_file_name in
    set_formatter_out_channel oc;
    try
      let ic = open_in !arg_header_file_name in
      (match targetB iAddrSize with
       | Some bml -> ppBModulesFullDbg bml
                       { cfg_debug = !arg_debug;
                         cfg_top_module_name = !arg_top_module_name
                       } ic
       | _ -> raise (Should_not_happen "Empty bModules"));
      close_out oc
    with Sys_error _ ->
      Printf.printf "Error: Header file not found. Use -header to specify the header file.\n"
