[@@@part "0"] ;;
open Printf
(*open Stdlib*)
open Lexer
open Lexing
open MapleLightTypes
open MapleLight
open MapleLightExec
open MapleLightDenotation
open Errors
open Camlcoq
open Values
open ITreeDefinition
open Exceptions

exception InvalidReturnValue

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Some (Parser.program Lexer.read lexbuf) with
  | LexError msg ->
    printf "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    printf "%a: syntax error\n" print_position lexbuf;
    None

[@@@part "1"] ;;

let parse_and_print filename lexbuf =
  match parse_with_error lexbuf with
  | Some p ->
     (try
        let oc = open_out (filename ^ ".ast") in
        PrintMapleAST.print_program oc p;
        close_out oc;
        let oc = open_out (filename ^ ".inter") in
        let p = MapleAST2MapleInter.convert_program p in
        PrintMapleInter.print_program oc p;
        close_out oc;
        let oc = open_out (filename ^ ".light") in
        let p = MapleInter2MapleLight.convert_program p in
        PrintMapleLight.print_program oc p;
        close_out oc;
        Some p
      with
      | CompilationError -> None)
  | None -> None;;

let rec do_step ge st =
  match final_state st with
  | Some vmtl -> Some vmtl
  | None ->
     match step ge st with
     | Some st -> do_step ge st
     | None -> None

let print_errcode oc ec =
  match ec with
  | MSG cl -> fprintf oc "%s" (camlstring_of_coqstring cl)
  | CTX p -> PrintMapleLight.print_positive oc p
  | POS p -> PrintMapleLight.print_positive oc p

let rec print_errmsg oc ecl =
  match ecl with
  | [] -> ()
  | ec :: ecl -> printf "%a\n%a" print_errcode ec print_errmsg ecl

let run p =
  match initial_state p [] with
  | OK (ge, st) -> do_step ge st
  | Error msg -> print_errmsg stdout msg; print_endline "fail to initialize"; None

let rec traverse t =
  match (observe t) with
  | RetF r -> r
  | TauF t' -> traverse t'
  | VisF (_, _) -> None;;

let run' p =
  traverse (exec_program p [])

(*let is_signed t =
  match t with
  | Tprim pt ->
     (match pt with
      | PTint (_, Signed) -> true
      | _ -> false)
  | _ -> false*)

(* no idea about how to print integers of u64 type, since ocaml does not have unsigned int type. *)

let print_coq_val oc v =
  match v with
  | Vundef -> raise InvalidReturnValue
  | Vint i -> PrintMapleLight.print_int oc i
  | Vlong l -> PrintMapleLight.print_int64 oc l
  | Vfloat f -> PrintMapleLight.print_float oc f
  | Vsingle s -> PrintMapleLight.print_float32 oc s
  | Vptr _ -> raise InvalidReturnValue

let rec print_result (oc: out_channel) (vmtl: (Values.coq_val * MapleLightTypes.coq_type) list) =
  match vmtl with
  | [] -> ();
  | (v, t) :: [] -> fprintf oc "%a" print_coq_val v
  | (v, t) :: vmtl -> fprintf oc "%a, %a" print_coq_val v print_result vmtl

let loop filename =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  (match parse_and_print filename lexbuf with
   | Some p ->
      printf "Compilation succeeded.\n";
      (match run p with
       | Some vmtl ->
          (try fprintf stdout "Program exited normally with return valuelist (%a).\n" print_result vmtl
           with InvalidReturnValue -> fprintf stdout "Program exited abnormally with invalid return valuelist.\n")
       | None -> printf "Program abort.\n")
   | None -> printf "Compilation failed.\n");
  close_in inx;;

let () =
  for i = 1 to Array.length Sys.argv - 1 do
    loop Sys.argv.(i)
  done;;
  (*Command.basic_spec ~summary:"Parse and display JSON"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command.run*)
