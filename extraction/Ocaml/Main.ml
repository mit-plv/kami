open Format
open Target
open PP

let () =
  let argnum = Array.length Sys.argv in
  if argnum < 2 then
    Printf.printf "Usage: %s [-d] output_file_name\n" Sys.argv.(0)
  else
    (let output_file = Sys.argv.(argnum - 1) in
     let oc = open_out output_file in
     set_formatter_out_channel oc;
     (match target.extProc with
      | Some bml -> ppBModulesFullInitPgmRfs bml target.extPgms target.extRfs (argnum > 2)
      | _ -> raise (Should_not_happen "Empty bModules"));
     close_out oc)
      
