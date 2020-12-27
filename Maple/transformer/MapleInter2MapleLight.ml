(* source: MapleInter *)
(* target: MapleLight *)
open MapleAST
open MapleInter
open Camlcoq
open Floats
open Values
open AST
open Printf
open Exceptions

exception Overflow
exception Bad_digit

let parse_int (base: int) (s: string) =
  let max_val = (* (2^64-1) / base, unsigned *)
    match base with
    (*|  8 -> 2305843009213693951L*)
    | 10 -> 1844674407370955161L
    | 16 -> 1152921504606846975L
    |  _ -> assert false in
  let v = ref 0L in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    let digit =
      if c >= '0' && c <= '9' then Char.code c - 48
      else if c >= 'A' && c <= 'F' then Char.code c - 55
      else raise Bad_digit in
    if digit >= base then raise Bad_digit;
    if !v < 0L || !v > max_val then raise Overflow;
    (* because (2^64 - 1) % 10 = 5, not 9 *)
    if base = 10 && !v = max_val && digit > 5 then raise Overflow;
    v := Int64.mul !v (Int64.of_int base);
    v := Int64.add !v (Int64.of_int digit)
  done;
  !v

let elab_int_constant (i: intInfo) (loc: location) =
  let s = String.map (fun d -> match d with
  | '0'..'9' | 'A'..'F' -> d
  | 'a'..'f' -> Char.chr (Char.code d - 32)
  | _ -> raise Bad_digit) i.coq_II_integer in
  (* Determine base *)
  let base =
    if i.coq_II_isHex then 16 else 10
  in
  (* Parse digits *)
  let v =
    try parse_int base s
    with
    | Overflow ->
        comp_error (Some loc) "integer literal %s is too large to be represented in any integer type" i.coq_II_source
    | Bad_digit ->
        comp_error (Some loc) "bad digit in integer literal %s" i.coq_II_source
  in
  if i.coq_II_isNegative then Int64.neg v else v

(** Kinds of floating-point numbers*)

type fkind =
    FFloat      (** [float] *)
  | FDouble     (** [double] *)
  | FLongDouble (** [long double] *)

type float_cst = {
  hex : bool;
  intPart : string;
  fracPart : string;
  exp : string;
}

let elab_float_constant (f: floatInfo) =
  let ty = match f.coq_FI_suffix with
    | Some ("l"|"L") -> FLongDouble
    | Some ("f"|"F") -> FFloat
    | None -> FDouble
    | _ -> assert false (* The lexer should not accept anything else. *)
  in
  let v = {
    hex=f.coq_FI_isHex;
    intPart=begin match f.coq_FI_integer with Some s -> s | None -> "0" end;
    fracPart=begin match f.coq_FI_fraction with Some s -> s | None -> "0" end;
    exp=begin match f.coq_FI_exponent with Some s -> s | None -> "0" end }
  in
  (v, ty)

(** Floating point constants *)

let z_of_str hex str fst =
  let res = ref Z.Z0 in
  let base = if hex then 16 else 10 in
  for i = fst to String.length str - 1 do
    let d = int_of_char str.[i] in
    let d =
      if hex && d >= int_of_char 'a' && d <= int_of_char 'f' then
	d - int_of_char 'a' + 10
      else if hex && d >= int_of_char 'A' && d <= int_of_char 'F' then
	d - int_of_char 'A' + 10
      else
	d - int_of_char '0'
    in
    assert (d >= 0 && d < base);
    res := Z.add (Z.mul (Z.of_uint base) !res) (Z.of_uint d)
  done;
  !res

(*let checkFloatOverflow f typ =
  match f with
  | Binary.B754_finite _ -> ()
  | Binary.B754_zero _ ->
      warning Diagnostics.Literal_range "magnitude of floating-point constant too small for type '%s'"  typ
  | Binary.B754_infinity _ ->
      warning Diagnostics.Literal_range "magnitude of floating-point constant too large for type '%s'"  typ
  | Binary.B754_nan _ ->
      warning Diagnostics.Literal_range "floating-point converts converts to 'NaN'"*)

let convertFloat (f: float_cst) (kind: fkind) =
  let mant = z_of_str f.hex (f.intPart ^ f.fracPart) 0 in
  match mant with
    | Z.Z0 ->
      begin match kind with
      | FFloat ->
	 MapleLight.C_single (Float.to_single Float.zero)
      | FDouble | FLongDouble ->
	 MapleLight.C_float (Float.zero)
      end
    | Z.Zpos mant ->

      let sgExp = match f.exp.[0] with '+' | '-' -> true | _ -> false in
      let exp = z_of_str false f.exp (if sgExp then 1 else 0) in
      let exp = if f.exp.[0] = '-' then Z.neg exp else exp in
      let shift_exp =
	(if f.hex then 4 else 1) * String.length f.fracPart in
      let exp = Z.sub exp (Z.of_uint shift_exp) in

      let base = P.of_int (if f.hex then 2 else 10) in

      begin match kind with
      | FFloat ->
	  let f = Float32.from_parsed base mant exp in
          (*checkFloatOverflow f "float";*)
          MapleLight.C_single f
      | FDouble | FLongDouble ->
	  let f = Float.from_parsed base mant exp in
          (*checkFloatOverflow f "double";*)
          MapleLight.C_float f
      end

    | Z.Zneg _ -> assert false

let convert_constant (c: constant) (loc: location) : MapleLight.constant =
  match c with
  | C_int iI ->
     C_long (coqint_of_camlint64 (elab_int_constant iI loc))
  | C_float fI ->
     let (f, k) = elab_float_constant fI in
     convertFloat f k

module IdentMap = Map.Make(String)

let print_string_int (s: string) (i: int) =
  fprintf stdout "%s %d\n" s i

let print_IdentMap (m: int IdentMap.t) =
  IdentMap.iter print_string_int m

let print_string_coq_type (s: string) (t: MapleLightTypes.coq_type) =
  fprintf stdout "%s %a\n" s PrintMapleLight.print_coq_type t

let print_typeMap (m: MapleLightTypes.coq_type IdentMap.t) =
  IdentMap.iter print_string_coq_type m

let globalvarMap : int IdentMap.t ref = ref IdentMap.empty

let globalvarMaxIdent = ref 0

let convert_globalvar_id (s: string) : ident =
  let n =
    try IdentMap.find s !globalvarMap
    with Not_found ->
      incr globalvarMaxIdent;
      globalvarMap := IdentMap.add s !globalvarMaxIdent !globalvarMap;
      !globalvarMaxIdent
  in P.of_int n

let localvarMap : int IdentMap.t ref = ref IdentMap.empty

let localvarMaxIdent = ref 0

let clear_localvarMap () =
  localvarMap := IdentMap.empty; localvarMaxIdent := 0

let convert_localvar_id (s: string) : ident =
  let n =
    try IdentMap.find s !localvarMap
    with Not_found ->
      incr localvarMaxIdent;
      localvarMap := IdentMap.add s !localvarMaxIdent !localvarMap;
      !localvarMaxIdent
  in P.of_int n

let compositeMap : int IdentMap.t ref = ref IdentMap.empty

let compositeMaxIdent = ref 0

let convert_composite_id (s: string) : ident =
  let n =
    try IdentMap.find s !compositeMap
    with Not_found ->
      incr compositeMaxIdent;
      compositeMap := IdentMap.add s !compositeMaxIdent !compositeMap;
      !compositeMaxIdent
  in P.of_int n

let globaltypeMap : MapleLightTypes.coq_type IdentMap.t ref = ref IdentMap.empty

let get_globaltype (s: string) (loc: location) : MapleLightTypes.coq_type =
  try IdentMap.find s !globaltypeMap
  with Not_found ->
    try Tcomposite (P.of_int (IdentMap.find s !compositeMap))
    with Not_found -> comp_error (Some loc) "type &%s is not declared" s

let bind_globaltype (s: string) (t: MapleLightTypes.coq_type) : unit =
  globaltypeMap := IdentMap.add s t !globaltypeMap; ()

let localtypeMap : MapleLightTypes.coq_type IdentMap.t ref = ref IdentMap.empty

let get_localtype (s: string) (loc: location) : MapleLightTypes.coq_type =
  try IdentMap.find s !localtypeMap
  with Not_found ->
    try Tcomposite (P.of_int (IdentMap.find s !compositeMap))
    with Not_found -> comp_error (Some loc) "type %%%s is not declared" s

let bind_localtype (s: string) (t: MapleLightTypes.coq_type) : unit =
  localtypeMap := IdentMap.add s t !localtypeMap; ()

let clear_localtypeMap ()  =
  localtypeMap := IdentMap.empty

let funcMap : int IdentMap.t ref = ref IdentMap.empty

let funcMaxIdent = ref 0

let convert_func_id (s: string) : ident =
  let n =
    try IdentMap.find s !funcMap
    with Not_found ->
      incr funcMaxIdent;
      funcMap := IdentMap.add s !funcMaxIdent !funcMap;
      !funcMaxIdent
  in P.of_int n

let memberfuncMap : int IdentMap.t ref = ref IdentMap.empty

let memberfuncMaxIdent = ref 0

let convert_memberfunc_id (s: string) : ident =
  let n =
    try IdentMap.find s !memberfuncMap
    with Not_found ->
      incr memberfuncMaxIdent;
      memberfuncMap := IdentMap.add s !memberfuncMaxIdent !memberfuncMap;
      !memberfuncMaxIdent
  in P.of_int n

let labelMap : int IdentMap.t ref = ref IdentMap.empty

let labelMaxIdent = ref 0

let clear_labelvarMap ()  =
  labelMap := IdentMap.empty; labelMaxIdent := 0

let convert_label (s: string) : ident =
  let n =
    try IdentMap.find s !labelMap
    with Not_found ->
      incr labelMaxIdent;
      labelMap := IdentMap.add s !labelMaxIdent !labelMap;
      !labelMaxIdent
  in P.of_int n

let cdlist : (ident * MapleLightTypes.composite_definition) list ref = ref []

let cdMaxIdent = ref 0

let convert_composite_definition (id: ident) (cd: MapleLightTypes.composite_definition) : MapleLightTypes.coq_type =
  cdlist := (id, cd) :: !cdlist; MapleLightTypes.Tcomposite id

let rec update_composite_attr_aux (id: ident) (ca: MapleLightTypes.class_attr) (l: (ident * MapleLightTypes.composite_definition) list) (loc: location) : (ident * MapleLightTypes.composite_definition) list =
  match l with
  | [] -> l
  | (id', cd) :: l' ->
     if id = id' then
       match cd with
       | MapleLightTypes.CDclass (oid, idl, mv, mf, ca') ->
          (id, MapleLightTypes.CDclass (oid, idl, mv, mf, ca)) :: update_composite_attr_aux id ca l' loc
       | MapleLightTypes.CDinterface (idl, mv, mf, ca') ->
          (id, MapleLightTypes.CDinterface (idl, mv, mf, ca)) :: update_composite_attr_aux id ca l' loc
       | _ -> comp_error (Some loc) "type %s is not a class or an interface" (string_of_int (P.to_int id))
     else (id', cd) :: update_composite_attr_aux id ca l' loc

let update_composite_attr (id: ident) (ca: MapleLightTypes.class_attr) (loc: location) : unit =
  cdlist := update_composite_attr_aux id ca !cdlist loc

let default_field_attr : MapleLightTypes.field_attr = MapleLightTypes.AM_friendly

let default_func_attr : MapleLightTypes.func_attr =
  { fa_access = AM_friendly;
    fa_abstract = false;
    fa_final = false;
    fa_static = false;
    fa_virtual = false;
    fa_constructor = false; }

let rec convert_typespec (t: MapleAST.typespec) (loc: location) : MapleLightTypes.coq_type =
  match t with
  | TSprim pt -> MapleLightTypes.Tprim pt
  | TSpointer t' ->
     let t'' = convert_typespec t' loc
     in MapleLightTypes.Tpointer t''
  | TSarray (t', Some i) ->
     let t'' = convert_typespec t' loc
     in MapleLightTypes.Tarray (t'', Z.of_uint64 (elab_int_constant i loc))
  | TSarray (t', None) -> comp_error (Some loc) "the length of the array type %d is not specified" 0
  | TSfunction (tl, t') ->
     let tl' = convert_typespeclist tl loc in
     let t'' = convert_typespec t' loc in
     MapleLightTypes.Tfunction (tl', MapleLightTypes.Tcons (t'', MapleLightTypes.Tnil))
  | TSglobal s -> get_globaltype s loc
  | TSlocal s -> get_localtype s loc
and convert_typespeclist (tl: MapleAST.typespeclist) (loc: location) : MapleLightTypes.typelist =
  match tl with
  | TSnil -> MapleLightTypes.Tnil
  | TScons (t, tl') ->
     let t' = convert_typespec t loc in
     let tl'' = convert_typespeclist tl' loc in
     MapleLightTypes.Tcons (t', tl'')

(*let convert_composite_id (s: string) : ident =
  match convert_typevar_id s with
  | MapleLightTypes.Tcomposite id -> id
  | _ -> raise (SyntaxError ("type " ^ s ^ " is not a composite"))*)

let rec convert_composite_idlist (sl: string list) : ident list =
  match sl with
  | [] -> []
  | s :: sl' ->
     convert_composite_id s :: convert_composite_idlist sl'

let default_class_attr : MapleLightTypes.class_attr =
  { MapleLightTypes.ca_access = AM_friendly;
    MapleLightTypes.ca_abstract = false;
    MapleLightTypes.ca_final = false; }

let rec convert_type (s: string) (t: coq_type) (loc: location) : MapleLightTypes.coq_type =
  match t with
  | Tprim pt -> MapleLightTypes.Tprim pt
  | Tpointer t' ->
     let t'' = convert_typespec t' loc
     in MapleLightTypes.Tpointer t''
  | Tarray (t', Some i) ->
     let t'' = convert_typespec t' loc
     in MapleLightTypes.Tarray (t'', Z.of_uint64 (elab_int_constant i loc))
  | Tarray (t', None) -> raise (CompilationError)
  | Tfunction (tl, t') ->
     let tl' = convert_typespeclist tl loc in
     let t'' = convert_typespec t' loc in
     MapleLightTypes.Tfunction (tl', MapleLightTypes.Tcons (t'', MapleLightTypes.Tnil))
  | Tstruct mv ->
     let id = convert_composite_id s in
     let mv' = convert_membervars mv 1 loc in
     convert_composite_definition id (MapleLightTypes.CDstruct mv')
  | Tunion mv ->
     let id = convert_composite_id s in
     let mv' = convert_membervars mv 1 loc in
     convert_composite_definition id (MapleLightTypes.CDunion mv')
  | Tclass (oid, idl, mv, mf) ->
     let id = convert_composite_id s in
     let idl' = convert_composite_idlist idl in
     let mv' = convert_membervars mv 1 loc in
     (*print_endline s;*)
     let mf' = convert_memberfuncs mf loc in
     (match oid with
      | Some pid ->
         let pid' = convert_composite_id pid in
         convert_composite_definition id (MapleLightTypes.CDclass (Some pid', idl', mv', mf', default_class_attr))
      | None ->
         convert_composite_definition id (MapleLightTypes.CDclass (None, idl', mv', mf', default_class_attr)))
  | Tinterface (idl, mv, mf) ->
     let id = convert_composite_id s in
     let idl' = convert_composite_idlist idl in
     let mv' = convert_membervars mv 1 loc in
     (*print_endline s;*)
     let mf' = convert_memberfuncs mf loc in
     convert_composite_definition id (MapleLightTypes.CDinterface (idl', mv', mf', default_class_attr))
  | Tglobal s -> get_globaltype s loc
  | Tlocal s -> get_localtype s loc
and convert_membervars (mv: membervars) (n: int) (loc: location) : MapleLightTypes.membervars =
  match mv with
  | MVnil -> MapleLightTypes.MVnil
  | MVcons (s, t, mal, mv', loc) ->
     let t' = convert_typespec t loc in
     let mv'' = convert_membervars mv' (n + 1) loc in
     let (ta, fa) = convert_membervar_attr_list mal MapleLightTypes.default_type_attr default_field_attr loc in
     MapleLightTypes.MVcons (P.of_int n, t', ta, fa, mv'')
and convert_membervar_attr_list (mal: membervar_attr list) (ta: MapleLightTypes.type_attr) (fa: MapleLightTypes.field_attr) (loc: location) : (MapleLightTypes.type_attr * MapleLightTypes.field_attr) =
  match mal with
  | [] -> (ta, fa)
  | ma :: mal' ->
     match ma with
     | MVA_access am ->
        if (am = fa || fa = MapleLightTypes.AM_friendly)
        then convert_membervar_attr_list mal' ta am loc
        else raise (CompilationError)
     | MVA_align i ->
        let n = N.of_int64 (elab_int_constant i loc) in
        match ta with
        | Some m ->
           if (n = m)
           then convert_membervar_attr_list mal' ta fa loc
           else raise CompilationError
        | None ->
           convert_membervar_attr_list mal' (Some n) fa loc
and convert_memberfuncs (mf: memberfuncs) (loc: location) : MapleLightTypes.memberfuncs =
  match mf with
  | MFnil -> MapleLightTypes.MFnil
  | MFcons (s1, s2, tl, t, fal, mf', loc) ->
     let tl' = convert_typespeclist tl loc in
     let t' = convert_typespec t loc in
     let mf'' = convert_memberfuncs mf' loc in
     let fa = convert_func_attr_list fal default_func_attr in
     let n1 = try IdentMap.find s1 !memberfuncMap
              with Not_found -> incr memberfuncMaxIdent; memberfuncMap := IdentMap.add s1 !memberfuncMaxIdent !memberfuncMap; !memberfuncMaxIdent in
     let n2 = try IdentMap.find s2 !funcMap
              with Not_found -> incr funcMaxIdent; funcMap := IdentMap.add s2 !funcMaxIdent !funcMap; !funcMaxIdent in
     MapleLightTypes.MFcons (P.of_int n1, P.of_int n2, MapleLightTypes.Tfunction (tl', MapleLightTypes.Tcons (t', MapleLightTypes.Tnil)), fa, mf'')
and convert_func_attr_list (fal: func_attr list) (fa: MapleLightTypes.func_attr) : MapleLightTypes.func_attr =
  match fal with
  | [] -> fa
  | fa' :: fal' ->
     match fa' with
     | FA_access am ->
        if (am = fa.fa_access || fa.fa_access = MapleLightTypes.AM_friendly)
        then convert_func_attr_list fal' { fa with fa_access = am }
        else raise CompilationError
     | FA_virtual ->
        convert_func_attr_list fal' { fa with fa_virtual = true }
     | FA_abstract ->
        convert_func_attr_list fal' { fa with fa_abstract = true }
     | FA_final ->
        convert_func_attr_list fal' { fa with fa_final = true }
     | FA_static ->
        convert_func_attr_list fal' { fa with fa_static = true }
     | FA_constructor ->
        convert_func_attr_list fal' { fa with fa_constructor = true }

let convert_unary_operation (uop: unary_operation) (loc: location) : MapleLightOp.unary_operation =
  match uop with
  | O_abs -> MapleLightOp.O_abs
  | O_bnot -> MapleLightOp.O_bnot
  | O_lnot -> MapleLightOp.O_lnot
  | O_neg -> MapleLightOp.O_neg
  | O_recip -> MapleLightOp.O_recip
  | O_sext i -> MapleLightOp.O_sext (N.of_int64 (elab_int_constant i loc))
  | O_zext i -> MapleLightOp.O_zext (N.of_int64 (elab_int_constant i loc))
  | O_sqrt -> MapleLightOp.O_sqrt

let convert_field_id (ofi: field_id option) (loc: location) : MapleLight.field_id =
  match ofi with
  | Some i -> N.of_int64 (elab_int_constant i loc)
  | None -> N.of_int64 0L

let convert_var_id (vid: var_id) : MapleLight.var_id =
  match vid with
  | VI_global id -> MapleLight.V_global (convert_globalvar_id id)
  | VI_local id -> MapleLight.V_local (convert_localvar_id id)

let convert_reg_id (rid: reg_id) (loc: location) : MapleLight.reg_id =
  match rid with
  | RI_pseudo i ->
     let id = P.of_int64 (elab_int_constant i loc) in
     MapleLight.Preg id
  | RI_thrownval ->
     MapleLight.Thrownval

let rec convert_expr (e: expr) (loc: location) : MapleLight.expr =
  match e with
  | E_dread (pt, vid, ofi) ->
     MapleLight.E_dread (pt, convert_var_id vid, convert_field_id ofi loc)
  | E_regread (pt, rid) ->
     MapleLight.E_regread (pt, convert_reg_id rid loc)
  | E_iread (pt, ts, ofi, e) ->
     MapleLight.E_iread (pt, convert_typespec ts loc, convert_field_id ofi loc, convert_expr e loc)
  | E_addrof (pt, vid, ofi) ->
     MapleLight.E_addrof (pt, convert_var_id vid, convert_field_id ofi loc)
  | E_addroffunc (pt, id) ->
     MapleLight.E_addroffunc (pt, convert_func_id id)
  | E_constval (pt, c) ->
     MapleLight.E_constval (pt, convert_constant c loc)
  | E_sizeoftype (pt, ts) ->
     MapleLight.E_sizeoftype (pt, convert_typespec ts loc)
  | E_unary (uop, pt, e) ->
     MapleLight.E_unary (convert_unary_operation uop loc, pt, convert_expr e loc)
  | E_iaddrof (pt, ts, ofi, e) ->
     MapleLight.E_iaddrof (pt, convert_typespec ts loc, convert_field_id ofi loc, convert_expr e loc)
  | E_ceil (pt1, pt2, e) ->
     MapleLight.E_ceil (pt1, pt2, convert_expr e loc)
  | E_cvt (pt1, pt2, e) ->
     MapleLight.E_cvt (pt1, pt2, convert_expr e loc)
  | E_floor (pt1, pt2, e) ->
     MapleLight.E_floor (pt1, pt2, convert_expr e loc)
  | E_retype (pt, ts, e) ->
     MapleLight.E_retype (pt, convert_typespec ts loc, convert_expr e loc)
  | E_trunc (pt1, pt2, e) ->
     MapleLight.E_trunc (pt1, pt2, convert_expr e loc)
  | E_binary (bop, pt, e1, e2) ->
     MapleLight.E_binary (bop, pt, convert_expr e1 loc, convert_expr e2 loc)
  | E_cand (pt, e1, e2) ->
     MapleLight.E_cand (pt, convert_expr e1 loc, convert_expr e2 loc)
  | E_cior (pt, e1, e2) ->
     MapleLight.E_cior (pt, convert_expr e1 loc, convert_expr e2 loc)
  | E_select (pt, e1, e2, e3) ->
     MapleLight.E_select (pt, convert_expr e1 loc, convert_expr e2 loc, convert_expr e3 loc)
  | E_array (i, pt, ts, el) ->
     let n = elab_int_constant i loc in
     let b = if n = 1L then true else if n = 0L then false else raise (CompilationError) in
     MapleLight.E_array (b, pt, convert_typespec ts loc, convert_exprlist el loc)
and convert_exprlist (el: exprlist) (loc: location) : MapleLight.exprlist =
  match el with
  | E_nil -> MapleLight.E_nil
  | E_cons (e, el') -> MapleLight.E_cons (convert_expr e loc, convert_exprlist el' loc)

let convert_ext_expr (ee: ext_expr) (loc: location) : MapleLight.ext_expr =
  match ee with
  | EE_pure e ->
     MapleLight.EE_pure (convert_expr e loc)
  | EE_malloc (pt, e) ->
     MapleLight.EE_malloc (pt, convert_expr e loc)
  | EE_gcmalloc (pt, ts) ->
     MapleLight.EE_gcmalloc (pt, convert_typespec ts loc)
  | EE_gcmallocjarray (pt, ts, e) ->
     MapleLight.EE_gcmallocjarray (pt, convert_typespec ts loc, convert_expr e loc)
  | EE_gcpermalloc (pt, ts) ->
     MapleLight.EE_gcmalloc (pt, convert_typespec ts loc)

let rec convert_statement (s: statement) (loc: location) : MapleLight.statement =
  match s with
  | S_skip loc -> MapleLight.S_skip
  | S_dassign (vid, ofi, ee, loc) ->
     MapleLight.S_dassign (convert_var_id vid, convert_field_id ofi loc, convert_ext_expr ee loc)
  | S_iassign (ts, ofi, e, ee, loc) ->
     MapleLight.S_iassign (convert_typespec ts loc, convert_field_id ofi loc, convert_expr e loc, convert_ext_expr ee loc)
  | S_regassign (pt, rid, ee, loc) ->
     MapleLight.S_regassign (pt, convert_reg_id rid loc, convert_ext_expr ee loc)
  | S_seq (s1, s2) ->
     MapleLight.S_seq (convert_statement s1 loc, convert_statement s2 loc)
  | S_label (lbl, s, loc) ->
     MapleLight.S_label (convert_label lbl, convert_statement s loc)
  | S_if (e, s1, s2, loc) ->
     MapleLight.S_if (convert_expr e loc, convert_statement s1 loc, convert_statement s2 loc)
  | S_while (e, s, loc) ->
     MapleLight.S_while (convert_expr e loc, convert_statement s loc)
  | S_goto (lbl, loc) ->
     MapleLight.S_goto (convert_label lbl)
  | S_return (el, loc) ->
     MapleLight.S_return (convert_exprlist el loc)
  | S_switch (e, lbl, l, loc) ->
     MapleLight.S_switch (convert_expr e loc, convert_label lbl, convert_switch_table l)
  | S_callassigned (id, el, l, loc) ->
     MapleLight.S_callassigned (convert_func_id id, convert_exprlist el loc, convert_assign_list l)
  | S_icallassigned (el, l, loc) ->
     (match el with
      | E_nil -> raise (CompilationError)
      | E_cons (e, el') ->
         MapleLight.S_icallassigned (convert_expr e loc, convert_exprlist el loc, convert_assign_list l))
  | S_virtualcallassigned (cid, mfid, el, l, loc) ->
     (match el with
      | E_nil -> raise (CompilationError)
      | E_cons (e, el') ->
         MapleLight.S_virtualcallassigned (convert_composite_id cid, convert_memberfunc_id mfid, convert_expr e loc, convert_exprlist el' loc, convert_assign_list l))
  | S_interfacecallassigned (cid, mfid, el, l, loc) ->
     (match el with
      | E_nil -> raise (CompilationError)
      | E_cons (e, el') ->
         MapleLight.S_interfacecallassigned (convert_composite_id cid, convert_memberfunc_id mfid, convert_expr e loc, convert_exprlist el' loc, convert_assign_list l))
  | S_javatry (ll, s, loc) ->
     MapleLight.S_javatry (convert_label_list ll, convert_statement s loc)
  | S_throw (e, loc) ->
     MapleLight.S_throw (convert_expr e loc)
  | S_javacatch (lbl, tsl, loc) ->
     MapleLight.S_javacatch (convert_label lbl, convert_typespec_list tsl loc)
  | S_decref (e, loc) ->
     MapleLight.S_decref (convert_expr e loc)
  | S_free (e, loc) ->
     MapleLight.S_free (convert_expr e loc)
  | S_incref (e, loc) ->
     MapleLight.S_incref (convert_expr e loc)
  | S_eval (e, loc) ->
     MapleLight.S_eval (convert_expr e loc)
and convert_switch_table (l: ((intInfo * label) * location) list) : (BinNums.coq_Z * MapleLight.label) list =
  match l with
  | [] -> []
  | ((i, lbl), loc) :: l' ->
     (Z.of_uint64 (elab_int_constant i loc), convert_label lbl) :: convert_switch_table l'
and convert_assign_list (l: ((var_id * field_id option) * location) list) : (MapleLight.var_id * MapleLight.field_id) list =
  match l with
  | [] -> []
  | ((vid, ofi), loc) :: l' ->
     (convert_var_id vid, convert_field_id ofi loc) :: convert_assign_list l'
and convert_label_list (l: label list) : MapleLight.label list =
  match l with
  | [] -> []
  | lbl :: l' ->
     convert_label lbl :: convert_label_list l'
and typelist_to_listtype (tl: MapleLightTypes.typelist) : MapleLightTypes.coq_type list =
  match tl with
  | Tnil -> []
  | Tcons (t, tl') -> t :: typelist_to_listtype tl'
and convert_typespec_list (tsl: typespec list) (loc: location) : MapleLightTypes.coq_type list =
  match tsl with
  | [] -> []
  | ts :: tsl' -> convert_typespec ts loc :: convert_typespec_list tsl' loc

let rec convert_params (l: (string * typespec) list) (loc: location) : (ident * MapleLightTypes.coq_type) list =
  match l with
  | [] -> []
  | (s, ts) :: l' ->
     (convert_localvar_id s, convert_typespec ts loc) :: convert_params l' loc

let convert_function_prototype (fp: function_prototype) (loc: location) : MapleLight.function_prototype =
  { MapleLight.fun_attr = convert_func_attr_list fp.fun_attr default_func_attr;
    MapleLight.fun_returns = [convert_typespec fp.fun_returns loc];
    MapleLight.fun_params = convert_params fp.fun_params loc; }

let rec convert_type_attr_list (tal: type_attr list) (ta: MapleLightTypes.type_attr) (loc: location) : MapleLightTypes.type_attr =
  match tal with
  | [] -> ta
  | i :: tal' ->
     let n = N.of_int64 (elab_int_constant i loc) in
     match ta with
     | Some m ->
        if (n = m)
        then convert_type_attr_list tal' ta loc
        else raise CompilationError
     | None ->
        convert_type_attr_list tal' (Some n) loc

let convert_var_def (vd: var_def) (loc: location) : MapleLight.var_def =
  let (ts, tal) = vd in
  (convert_typespec ts loc, (MapleLight.SC_default, convert_type_attr_list tal MapleLightTypes.default_type_attr loc))

let rec convert_localvars (l: (string * var_def) list) (loc: location) : (ident * MapleLight.var_def) list =
  match l with
  | [] -> []
  | (s, vd) :: l' ->
     (convert_localvar_id s, convert_var_def vd loc) :: convert_localvars l' loc

let rec convert_pregs (l: (intInfo * MapleLightTypes.prim_type) list) (loc: location) : (ident * MapleLightTypes.prim_type) list =
  match l with
  | [] -> []
  | (i, pt) :: l' -> (P.of_int64 (elab_int_constant i loc), pt) :: convert_pregs l' loc

let rec construct_localtypeMap (l: ((string * coq_type) * location) list) : unit =
  match l with
  | [] -> ()
  | ((s, t), loc) :: l' -> bind_localtype s (convert_type s t loc); construct_localtypeMap l'

let convert_function_body (fb: function_body) (loc: location) : MapleLight.function_body =
  construct_localtypeMap (fb.fun_types);
  (*print_typeMap !localtypeMap;*)
  { MapleLight.fun_vars = convert_localvars (List.map fst fb.fun_vars) loc;
    MapleLight.fun_pregs = convert_pregs (List.map fst fb.fun_pregs) loc;
    MapleLight.fun_statement = convert_statement fb.fun_statement loc; }

let convert_function (f: coq_function) (loc: location) : MapleLight.coq_function =
  (*clear_localvarMap ();*) clear_labelvarMap (); clear_localtypeMap ();
  match f with
  | fp, Some fb -> (convert_function_prototype fp loc, Some (convert_function_body fb loc))
  | fp, None -> (convert_function_prototype fp loc, None)

let rec convert_globalvars (l: ((string * var_def) * location) list) : (ident * MapleLight.var_def) list =
  match l with
  | [] -> []
  | ((s, vd), loc) :: l' -> (convert_globalvar_id s, convert_var_def vd loc) :: convert_globalvars l'

let rec convert_functions (l: ((string * coq_function) * location) list) : (ident * MapleLight.coq_function) list =
  match l with
  | [] -> []
  | ((s, f), loc) :: l' ->
     (convert_func_id s, convert_function f loc) :: (convert_functions l')

let rec construct_compositeMap (l: (string * coq_type) list) : unit =
  match l with
  | [] -> ()
  | (s, t) :: l' ->
     match t with
     | Tstruct _ | Tunion _ | Tclass _ | Tinterface _ ->
        let _ = convert_composite_id s in construct_compositeMap l'; ()
     | _ -> ()

let rec construct_globaltypeMap (l: ((string * coq_type) * location) list) : unit =
  match l with
  | [] -> ()
  | ((s, t), loc) :: l' -> bind_globaltype s (convert_type s t loc); construct_globaltypeMap l'

let rec convert_class_attr_list (cal: class_attr list) (ca: MapleLightTypes.class_attr) : MapleLightTypes.class_attr =
  match cal with
  | [] -> ca
  | ca' :: cal' ->
     match ca' with
     | CA_access am ->
        if (am = ca.ca_access || ca.ca_access = MapleLightTypes.AM_friendly)
        then convert_class_attr_list cal' { ca with ca_access = am }
        else raise CompilationError
     | CA_abstract ->
        convert_class_attr_list cal' { ca with ca_abstract = true }
     | CA_final ->
        convert_class_attr_list cal' { ca with ca_final = true }

let rec convert_javaclass (l: (((string * string) * class_attr list) * location) list) : unit =
  match l with
  | [] -> ()
  | (((s1, s2), cal), loc) :: l' ->
     if
       s1 = s2
     then
       let id = convert_composite_id s1 in
       update_composite_attr id (convert_class_attr_list cal default_class_attr) loc;
       convert_javaclass l'
     else
       raise (CompilationError)

let convert_program (p: MapleInter.program) : MapleLight.program =
  (*print_endline "constructing compositeMap";*)
  construct_compositeMap (List.map fst p.prog_types);
  (*print_IdentMap !compositeMap;*)
  (*print_endline "";*)
  construct_globaltypeMap (p.prog_types);
  (*print_typeMap !globaltypeMap;*)
  (*print_endline "";*)
  convert_javaclass (p.prog_javaclass);
  convert_javaclass (p.prog_javainterface);
  let globalvars = convert_globalvars (p.prog_vars) in
  let functions = convert_functions (p.prog_funcs) in
  (*print_IdentMap !globalvarMap;
  print_endline "";
  print_IdentMap !memberfuncMap;
  print_endline "";
  print_IdentMap !funcMap;*)
  { MapleLight.prog_vars = globalvars;
    MapleLight.prog_comps = !cdlist;
    MapleLight.prog_funcs = functions;
    MapleLight.prog_main = convert_func_id (fst p.prog_main); }
