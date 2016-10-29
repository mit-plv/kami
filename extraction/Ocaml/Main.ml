open Format
open Target
open PP

let () =
  let argnum = Array.length Sys.argv in
  if argnum < 2 then
    Printf.printf "Usage: %s output_file_name\n" Sys.argv.(0)
  else
    (let output_file = Sys.argv.(1) in
     let oc = open_out output_file in
     set_formatter_out_channel oc;
     (match target.extProc with
      | Some bml -> ppBModulesFullInitMemRfs bml target.extPgm target.extRfs
      | _ -> raise (Should_not_happen "Empty bModules"));
     close_out oc)
      
