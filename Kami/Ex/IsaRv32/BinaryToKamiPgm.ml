open String
open List
open Batteries

let pgm_size = 256

let inst_line_regex_str =
  "[0-9a-f]+:[ \t]+[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]"
let inst_regex_str = "[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]"
                   
let pgm : string list ref = ref []
let add_pgm_line (s: string) = pgm := (append !pgm [s])

let inst_prefix = "  - exact (ConstBit "
let inst_postfix = ")."

let hex_char_to_bin (c: char) =
  if c = '0' then "0000"
  else if c = '1' then "0001"
  else if c = '2' then "0010"
  else if c = '3' then "0011"
  else if c = '4' then "0100"
  else if c = '5' then "0101"
  else if c = '6' then "0110"
  else if c = '7' then "0111"
  else if c = '8' then "1000"
  else if c = '9' then "1001"
  else if c = 'a' then "1010"
  else if c = 'b' then "1011"
  else if c = 'c' then "1100"
  else if c = 'd' then "1101"
  else if c = 'e' then "1110"
  else if c = 'f' then "1111"
  else ""

let rec hex_string_to_bin (s: string) =
  if s = "" then ""
  else if String.length s = 1 then hex_char_to_bin s.[0]
  else (hex_char_to_bin s.[0]) ^ (hex_string_to_bin (sub s 1 (String.length s - 1)))

let rec bin_to_kami_word_rec (s: string) =
  if s = "" then ""
  else if String.length s = 1 then s
  else (sub s 0 1) ^ "~" ^ (bin_to_kami_word_rec (sub s 1 (String.length s - 1)))

let bin_to_kami_word (s: string) =
  "WO~" ^ (bin_to_kami_word_rec s)

let hex_to_kami_word (s: string) =
  bin_to_kami_word (hex_string_to_bin s)

let pgm_nop = "00000013" (* NOP *)
let pgm_ret = "00008067" (* RET *)

(* first RET should be substituted to "TOHOST a0; J 0x0",
 * assuming the main function is located first.
 *)
let pgm_last = "00050008"
let pgm_back (sz: int) = (Printf.sprintf "%03x" (4 * (pgm_size - sz))) ^ "0006f"

let rec substitute_ret (p: string list) (main_sz: int) =
  match p with
  | [] -> []
  | i :: p' ->
     if i = pgm_ret
     then pgm_last :: (pgm_back (main_sz + 1)) :: p'
     else i :: (substitute_ret p' (main_sz + 1))

let rec print_kami_pgm_rec (p: string list) (sz: int) =
  if (sz <= 0) then ()
  else if (sz = 1) then
    match p with
    | [] -> print_string inst_prefix; print_string (hex_to_kami_word pgm_nop);
            print_string inst_postfix
    | i :: _ -> print_string inst_prefix; print_string (hex_to_kami_word i);
                print_string inst_postfix
  else (* sz > 1 *)
    match p with
    | [] -> print_string inst_prefix; print_string (hex_to_kami_word pgm_nop);
            print_string inst_postfix;
            print_newline (); print_kami_pgm_rec [] (sz - 1)
    | i :: p' -> print_string inst_prefix; print_string (hex_to_kami_word i);
                 print_string inst_postfix;
                 print_newline (); print_kami_pgm_rec p' (sz - 1)

let print_kami_pgm_header (_: unit) =
  print_string "Require Import Bool String List."; print_newline ();
  print_string "Require Import Lib.CommonTactics Lib.Word Lib.Struct."; print_newline ();
  print_string "Require Import Kami.Syntax."; print_newline ();
  print_string "Require Import Ex.IsaRv32 Ex.IsaRv32Pgm."; print_newline ();
  print_newline ();
  print_string "Definition pgmExt: Rv32Program."; print_newline ();
  print_string "  init_pgm."

let print_kami_pgm_footer (_: unit) =
  print_string "Defined."; print_newline ()

let print_kami_pgm (_: unit) =
  print_kami_pgm_header ();
  print_newline ();
  print_kami_pgm_rec (substitute_ret !pgm 0) pgm_size;
  print_newline ();
  print_kami_pgm_footer ()
                   
let () =
  let argnum = Array.length Sys.argv in
  if argnum < 2 then
    Printf.printf "Usage: %s (disassembled_file_name)\n" Sys.argv.(0)
  else
    let _ = 
      (let input_file = Sys.argv.(1) in
       let ic = open_in input_file in
       let inst_line_regexp = Str.regexp inst_line_regex_str in
       let inst_regexp = Str.regexp inst_regex_str in
       try
         while true do
           let line = input_line ic in
           try
             let _ = Str.search_forward inst_line_regexp line 0 in
             let found = Str.search_forward inst_regexp line 0 in
             let pgm_line = sub line found 8 in
             add_pgm_line pgm_line
           with Not_found -> ()
         done
       with End_of_file -> close_in ic) in
    print_kami_pgm ()
