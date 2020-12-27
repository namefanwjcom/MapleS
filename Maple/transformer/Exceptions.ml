open MapleAST
open Printf

exception CompilationError
exception Abort

let comp_error (oloc: location option) f s =
  match oloc with
  | Some loc ->
     fprintf stdout "error(%d): %a" loc.lineno (fun oc -> fprintf oc f) s; raise CompilationError
  | None ->
     fprintf stdout "error: %a" (fun oc -> fprintf oc f) s; raise CompilationError

(*let _ = comp_error None "hello"*)
