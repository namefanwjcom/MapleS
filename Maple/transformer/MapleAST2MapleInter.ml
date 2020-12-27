(* source: MapleAST *)
(* target: MapleInter *)
open MapleAST
open Exceptions

let isPrefix (s1: ident) (s2: ident) : bool =
  if String.length s1 > String.length s2
  then false
  else s1 = String.sub s2 0 (String.length s1)

let rec findPrefix (idl: ident list) (id: ident) : ident option =
  match idl with
  | [] -> None
  | id':: idl' ->
     if isPrefix id' id
     then Some id'
     else findPrefix idl' id

let class_interface_idlist : ident list ref = ref []

let rec convert_type (id: ident) (t: coq_type) : MapleInter.coq_type =
  match t with
  | Tprim pt ->
     MapleInter.Tprim pt
  | Tpointer t' ->
     MapleInter.Tpointer t'
  | Tarray (t', n) ->
     MapleInter.Tarray (t', n)
  | Tfunction (tl, t') ->
     MapleInter.Tfunction (tl, t')
  | Tstruct mv ->
     let mv' = convert_membervars mv in
     MapleInter.Tstruct mv'
  | Tunion mv ->
     let mv' = convert_membervars mv in
     MapleInter.Tunion mv'
  | Tclass (pid, idl, mv, mf) ->
     let mv' = convert_membervars mv in
     let mf' = convert_memberfuncs mf (String.length id) in
     class_interface_idlist := id :: !class_interface_idlist; MapleInter.Tclass (pid, idl, mv', mf')
  | Tinterface (idl, mv, mf) ->
     let mv' = convert_membervars mv in
     let mf' = convert_memberfuncs mf (String.length id) in
     class_interface_idlist := id :: !class_interface_idlist; MapleInter.Tinterface (idl, mv', mf')
  | Tglobal s ->
     MapleInter.Tglobal s
  | Tlocal s ->
     MapleInter.Tlocal s
and convert_membervars (mv: membervars) : MapleInter.membervars =
  match mv with
  | MVnil -> MapleInter.MVnil
  | MVcons (s, t, mal, mv', loc) ->
     let mv'' = convert_membervars mv' in
     MapleInter.MVcons (s, t, mal, mv'', loc)
and convert_memberfuncs (mf: memberfuncs) (n: int) : MapleInter.memberfuncs =
  match mf with
  | MFnil -> MapleInter.MFnil
  | MFcons (s, tl, t, fal, mf', loc) ->
     let mf'' = convert_memberfuncs mf' n in
     MapleInter.MFcons (String.sub s n (String.length s - n), s, tl, t, fal, mf'', loc)

let rec convert_statement (s: statement) : MapleInter.statement =
  match s with
  | S_skip loc ->
     MapleInter.S_skip loc
  | S_dassign (vid, fi, ee, loc) ->
     MapleInter.S_dassign (vid, fi, ee, loc)
  | S_iassign (t, fi, e, ee, loc) ->
     MapleInter.S_iassign (t, fi, e, ee, loc)
  | S_regassign (pt, rid, ee, loc) ->
     MapleInter.S_regassign (pt, rid, ee, loc)
  | S_seq (s1, s2) ->
     MapleInter.S_seq (convert_statement s1, convert_statement s2)
  | S_label (lbl, s, loc) ->
     MapleInter.S_label (lbl, convert_statement s, loc)
  | S_if (e, s1, s2, loc) ->
     MapleInter.S_if (e, convert_statement s1, convert_statement s2, loc)
  | S_while (e, s, loc) ->
     MapleInter.S_while (e, convert_statement s, loc)
  | S_brtrue (lbl, e, loc) ->
     MapleInter.S_if (e, MapleInter.S_goto (lbl, loc), MapleInter.S_skip loc, loc)
  | S_brfalse (lbl, e, loc) ->
     MapleInter.S_if (e, MapleInter.S_skip loc, MapleInter.S_goto (lbl, loc), loc)
  | S_goto (lbl, loc) ->
     MapleInter.S_goto (lbl, loc)
  | S_return (el, loc) ->
     MapleInter.S_return (el, loc)
  | S_switch (e, lbl, l, loc) ->
     MapleInter.S_switch (e, lbl, l, loc)
  | S_callassigned (id, el, l, loc) ->
     MapleInter.S_callassigned (id, el, l, loc)
  | S_icallassigned (el, l, loc) ->
     MapleInter.S_icallassigned (el, l, loc)
  | S_virtualcallassigned (id, el, l, loc) ->
     (match findPrefix !class_interface_idlist id with
      | Some cid -> MapleInter.S_virtualcallassigned (cid, String.sub id (String.length cid) (String.length id - String.length cid), el, l, loc)
      | None -> raise (CompilationError))
  | S_interfacecallassigned (id, el, l, loc) ->
     (match findPrefix !class_interface_idlist id with
      | Some cid -> MapleInter.S_interfacecallassigned (cid, String.sub id (String.length cid) (String.length id - String.length cid), el, l, loc)
      | None -> raise (CompilationError))
  | S_javatry (ll, s, loc) -> MapleInter.S_javatry (ll, convert_statement s, loc)
  | S_throw (e, loc) -> MapleInter.S_throw (e, loc)
  | S_javacatch (lbl, tl, loc) -> MapleInter.S_javacatch (lbl, tl, loc)
  | S_decref (e, loc) -> MapleInter.S_decref (e, loc)
  | S_free (e, loc) -> MapleInter.S_free (e, loc)
  | S_incref (e, loc) -> MapleInter.S_incref (e, loc)
  | S_eval (e, loc) -> MapleInter.S_eval (e, loc)

let rec convert_local_declaration_list (ldl: local_declaration list) : ((ident * var_def) * location) list * ((ident * MapleInter.coq_type) * location) list * ((intInfo * MapleLightTypes.prim_type) * location) list =
  match ldl with
  | [] -> ([], [], [])
  | ld :: ldl' ->
     match ld with
     | LD_var (id, vd, loc) ->
        let (varl, typel, pregl) = convert_local_declaration_list ldl' in (((id, vd), loc) :: varl, typel, pregl)
     | LD_type (id, t, loc) ->
        let (varl, typel, pregl) = convert_local_declaration_list ldl' in (varl, ((id, convert_type id t), loc) :: typel, pregl)
     | LD_preg (id, pt, loc) ->
        let (varl, typel, pregl) = convert_local_declaration_list ldl' in (varl, typel, ((id, pt), loc) :: pregl)

let convert_function_body (fb: function_body) : MapleInter.function_body =
  let (varl, typel, pregl) = convert_local_declaration_list (fb.fun_localdecl) in
  { MapleInter.fun_vars = varl;
    MapleInter.fun_types = typel;
    MapleInter.fun_pregs = pregl;
    MapleInter.fun_statement = convert_statement fb.fun_statement;
  }

let convert_function (f: coq_function) : MapleInter.coq_function =
  match f with
  | fp, Some fb -> (fp, Some (convert_function_body fb))
  | fp, None -> (fp, None)

type program' =
  { prog_vars : ((ident * var_def) * location) list;
    prog_types : ((ident * MapleInter.coq_type) * location) list;
    prog_funcs : ((ident * MapleInter.coq_function) * location) list;
    prog_javaclass : (((ident * ident) * MapleAST.class_attr list) * location) list;
    prog_javainterface : (((ident * ident) * MapleAST.class_attr list) * location) list;
    prog_main : (ident * location) option;
  }

let init_program : program' =
  { prog_vars = [];
    prog_types = [];
    prog_funcs = [];
    prog_javaclass = [];
    prog_javainterface = [];
    prog_main = None;
  }

let update_program_rec (p: program') (gd: global_declaration) : program' =
  match gd with
  | GD_var (id, vd, loc) ->
     { p with prog_vars = ((id, vd), loc) :: p.prog_vars }
  | GD_type (id, t, loc) ->
     { p with prog_types = ((id, convert_type id t), loc) :: p.prog_types }
  | GD_func (id, f, loc) ->
     { p with prog_funcs = p.prog_funcs @ [((id, convert_function f), loc)] }
  | GD_javaclass (id1, id2, cal, loc) ->
     { p with prog_javaclass = (((id1, id2), cal), loc) :: p.prog_javaclass }
  | GD_javainterface (id1, id2, cal, loc) ->
     { p with prog_javainterface = (((id1, id2), cal), loc) :: p.prog_javainterface }
  | GD_entryfunc (id, loc) ->
     match p.prog_main with
     | Some (id', loc') ->
        if id = id' then p else raise (CompilationError)
     | None -> { p with prog_main = Some (id, loc) }

let rec update_program (p: program') (gdl: global_declaration list) : program' =
  match gdl with
  | [] -> p
  | gd :: gdl' -> update_program (update_program_rec p gd) gdl'

let convert_program (p: program) : MapleInter.program =
  let p' = update_program (init_program) p in
  match p'.prog_main with
  | Some id ->
     { MapleInter.prog_vars = p'.prog_vars;
       MapleInter.prog_types = p'.prog_types;
       MapleInter.prog_funcs = p'.prog_funcs;
       MapleInter.prog_javaclass = p'.prog_javaclass;
       MapleInter.prog_javainterface = p'.prog_javainterface;
       MapleInter.prog_main = id }
  | None -> raise (CompilationError)
