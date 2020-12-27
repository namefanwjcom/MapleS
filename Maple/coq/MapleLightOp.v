(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Arithmetic and logical operators for the Compcert C and Clight languages *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import MapleLightTypes.
Require Archi.

(** * Syntax of operators. *)

Definition boffset := N.

Definition bsize := N.

Definition Boffset := N.

Inductive unary_operation : Type :=
  | O_abs : unary_operation
  | O_bnot : unary_operation
  | O_lnot : unary_operation
  | O_neg : unary_operation
  | O_recip : unary_operation
  | O_sext : bsize -> unary_operation
  | O_zext : bsize -> unary_operation
  (*| O_extractbits : boffset -> bsize -> unary_operation*)
  | O_sqrt : unary_operation.

Inductive binary_operation : Type :=
  | O_add : binary_operation
  | O_ashr : binary_operation
  | O_band : binary_operation
  | O_bior : binary_operation
  | O_bxor : binary_operation
  | O_cmp : prim_type -> binary_operation
  | O_cmpg : prim_type -> binary_operation
  | O_cmpl : prim_type -> binary_operation
  (*| O_depositbits : boffset -> bsize -> binary_operation*)
  | O_div : binary_operation
  | O_eq : prim_type -> binary_operation
  | O_ge : prim_type -> binary_operation
  | O_gt : prim_type -> binary_operation
  | O_land : binary_operation
  | O_lior : binary_operation
  | O_le : prim_type -> binary_operation
  | O_lshr : binary_operation
  | O_lt : prim_type -> binary_operation
  | O_max : binary_operation
  | O_min : binary_operation
  | O_mul : binary_operation
  | O_ne : prim_type -> binary_operation
  | O_rem : binary_operation
  | O_shl : binary_operation
  | O_sub : binary_operation.

Inductive incr_or_decr : Type := Incr | Decr.

(** * Type classification and semantics of operators. *)

(** Most C operators are overloaded (they apply to arguments of various
  types) and their semantics depend on the types of their arguments.
  The following [classify_*] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  This classification is used in the
  compiler (module [Cshmgen]) to resolve overloading statically.

  The [sem_*] functions below compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  The corresponding [classify_*] function is first called on the
  types of the arguments to resolve static overloading.  It is then
  followed by a case analysis on the values of the arguments. *)

(** ** Casts and truth values *)

Inductive classify_cast_cases : Type :=
  | cast_case_pointer                              (**r between pointer types or intptr_t types *)
  | cast_case_i2i (sz2:intsize) (si2:signedness)   (**r int -> int *)
  | cast_case_f2f                                  (**r double -> double *)
  | cast_case_s2s                                  (**r single -> single *)
  | cast_case_f2s                                  (**r double -> single *)
  | cast_case_s2f                                  (**r single -> double *)
  | cast_case_i2f (si1: signedness)                (**r int -> double *)
  | cast_case_i2s (si1: signedness)                (**r int -> single *)
  | cast_case_f2i (sz2:intsize) (si2:signedness)   (**r double -> int *)
  | cast_case_s2i (sz2:intsize) (si2:signedness)   (**r single -> int *)
  | cast_case_l2l                       (**r long -> long *)
  | cast_case_i2l (si1: signedness)     (**r int -> long *)
  | cast_case_l2i (sz2: intsize) (si2: signedness) (**r long -> int *)
  | cast_case_l2f (si1: signedness)                (**r long -> double *)
  | cast_case_l2s (si1: signedness)                (**r long -> single *)
  | cast_case_f2l (si2:signedness)                 (**r double -> long *)
  | cast_case_s2l (si2:signedness)                 (**r single -> long *)
  | cast_case_i2bool                               (**r int -> bool *)
  | cast_case_l2bool                               (**r long -> bool *)
  | cast_case_f2bool                               (**r double -> bool *)
  | cast_case_s2bool                               (**r single -> bool *)
  | cast_case_composite (id1 id2: ident)           (**r struct -> struct *)
  | cast_case_void                                 (**r any -> void *)
  | cast_case_agg
  | cast_case_default.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  (* To [void] *)
  | Tprim PTvoid, _ => cast_case_void
  (* To [bool] *)
  | Tprim PTbool, Tprim (PTint I64 _ | PTaddr A64) => cast_case_l2bool
  | Tprim PTbool, Tprim (PTint _ _ | PTaddr A32) => cast_case_i2bool
  | Tprim PTbool, Tprim (PTfloat F32) => cast_case_s2bool
  | Tprim PTbool, Tprim (PTfloat F64) => cast_case_f2bool
  | Tprim PTbool, (Tpointer _ | Tarray _ _ | Tprim PTptr | Tprim PTref) => 
    if Archi.ptr64 then cast_case_l2bool else cast_case_i2bool
  (* To [long] *)
  | Tprim (PTint I64 _), Tprim (PTint I64 _ | PTaddr A64) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2l
  | Tprim (PTint I64 _), Tprim (PTint _ si1) => cast_case_i2l si1
  | Tprim (PTint I64 _), Tprim (PTaddr A32) => cast_case_i2l Unsigned
  | Tprim (PTint I64 si2), Tprim (PTfloat F64) => cast_case_f2l si2
  | Tprim (PTint I64 si2), Tprim (PTfloat F32) => cast_case_s2l si2
  | Tprim (PTint I64 si2), (Tpointer _ | Tarray _ _ | Tprim PTptr | Tprim PTref) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_i2l si2
  (* To [int] *)
  | Tprim (PTint sz2 si2), Tprim (PTint I64 _ | PTaddr A64) => cast_case_l2i sz2 si2
  | Tprim (PTint sz2 si2), Tprim (PTint _ _ | PTaddr A32) =>
      if Archi.ptr64 then cast_case_i2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  | Tprim (PTint sz2 si2), Tprim (PTfloat F64) => cast_case_f2i sz2 si2
  | Tprim (PTint sz2 si2), Tprim (PTfloat F32) => cast_case_s2i sz2 si2
  | Tprim (PTint sz2 si2), (Tpointer _ | Tarray _ _ | Tprim PTptr | Tprim PTref) =>
      if Archi.ptr64 then cast_case_l2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  (* To [float] *)
  | Tprim (PTfloat F64), Tprim (PTint I64 si1) => cast_case_l2f si1
  | Tprim (PTfloat F32), Tprim (PTint I64 si1) => cast_case_l2s si1
  | Tprim (PTfloat F64), Tprim (PTint sz1 si1) => cast_case_i2f si1
  | Tprim (PTfloat F32), Tprim (PTint sz1 si1) => cast_case_i2s si1
  | Tprim (PTfloat F64), Tprim (PTfloat F64) => cast_case_f2f
  | Tprim (PTfloat F32), Tprim (PTfloat F32) => cast_case_s2s
  | Tprim (PTfloat F64), Tprim (PTfloat F32) => cast_case_s2f
  | Tprim (PTfloat F32), Tprim (PTfloat F64) => cast_case_f2s
  (* To pointer types *)
  | (Tpointer _ | Tprim PTptr | Tprim PTref), Tprim (PTint I64 _ | PTaddr A64) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2i I32 Unsigned
  | (Tpointer _ | Tprim PTptr | Tprim PTref), Tprim (PTint _ si) =>
    if Archi.ptr64 then cast_case_i2l si else cast_case_pointer
  | (Tpointer _ | Tprim PTptr | Tprim PTref), Tprim (PTaddr A32) =>
    if Archi.ptr64 then cast_case_i2l Unsigned else cast_case_pointer
  | (Tpointer _ | Tprim PTptr | Tprim PTref), (Tpointer _ | Tarray _ _ | Tprim PTptr | Tprim PTref) => cast_case_pointer
  (* To [addr] *)
  | Tprim (PTaddr A64), Tprim (PTint I64 _ | PTaddr A64) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2l
  | Tprim (PTaddr A64), Tprim (PTint _ si1) => cast_case_i2l si1
  | Tprim (PTaddr A64), Tprim (PTaddr A32) => cast_case_i2l Unsigned
  | Tprim (PTaddr A64), Tprim (PTfloat F64) => cast_case_f2l Unsigned
  | Tprim (PTaddr A64), Tprim (PTfloat F32) => cast_case_s2l Unsigned
  | Tprim (PTaddr A64), (Tpointer _ | Tarray _ _ | Tprim PTptr | Tprim PTref) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_i2l Unsigned
  | Tprim (PTaddr A32), Tprim (PTint I64 _ | PTaddr A64) => cast_case_l2i I32 Unsigned
  | Tprim (PTaddr A32), Tprim (PTint _ _ | PTaddr A32) =>
      if Archi.ptr64 then cast_case_i2i I32 Unsigned
      else cast_case_pointer
  | Tprim (PTaddr A32), Tprim (PTfloat F64) => cast_case_f2i I32 Unsigned
  | Tprim (PTaddr A32), Tprim (PTfloat F32) => cast_case_s2i I32 Unsigned
  | Tprim (PTaddr A32), (Tpointer _ | Tarray _ _ | Tprim PTptr | Tprim PTref) =>
      if Archi.ptr64 then cast_case_l2i I32 Unsigned
      else cast_case_pointer
  (* To agg *)
  | Tprim PTagg, Tcomposite _ => cast_case_agg
  (* To composite types *)
  | Tcomposite id1, Tcomposite id2 => cast_case_composite id1 id2
  (* Catch-all *)
  | _, _ => cast_case_default
  end.

(** Semantics of casts.  [sem_cast v1 t1 t2 m = Some v2] if value [v1],
  viewed with static type [t1], can be converted  to type [t2],
  resulting in value [v2].  *)

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i
  | _, _ => i
  end.

Definition cast_int_float (si: signedness) (i: int) : float :=
  match si with
  | Signed => Float.of_int i
  | Unsigned => Float.of_intu i
  end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
  match si with
  | Signed => Float.to_int f
  | Unsigned => Float.to_intu f
  end.

Definition cast_int_single (si: signedness) (i: int) : float32 :=
  match si with
  | Signed => Float32.of_int i
  | Unsigned => Float32.of_intu i
  end.

Definition cast_single_int (si : signedness) (f: float32) : option int :=
  match si with
  | Signed => Float32.to_int f
  | Unsigned => Float32.to_intu f
  end.

Definition cast_int_long (si: signedness) (i: int) : int64 :=
  match si with
  | Signed => Int64.repr (Int.signed i)
  | Unsigned => Int64.repr (Int.unsigned i)
  end.

Definition cast_long_float (si: signedness) (i: int64) : float :=
  match si with
  | Signed => Float.of_long i
  | Unsigned => Float.of_longu i
  end.

Definition cast_long_single (si: signedness) (i: int64) : float32 :=
  match si with
  | Signed => Float32.of_long i
  | Unsigned => Float32.of_longu i
  end.

Definition cast_float_long (si : signedness) (f: float) : option int64 :=
  match si with
  | Signed => Float.to_long f
  | Unsigned => Float.to_longu f
  end.

Definition cast_single_long (si : signedness) (f: float32) : option int64 :=
  match si with
  | Signed => Float32.to_long f
  | Unsigned => Float32.to_longu f
  end.

Definition sem_cast (v: val) (t1 t2: type) (m: mem) (ce: composite_env) : option val :=
  match classify_cast t1 t2 with
  | cast_case_pointer =>
      match v with
      | Vptr _ _ => Some v
      | Vint _ => if Archi.ptr64 then None else Some v
      | Vlong _ => if Archi.ptr64 then Some v else None
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f =>
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end
  | cast_case_s2s =>
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end
  | cast_case_s2f =>
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end
  | cast_case_f2s =>
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end
  | cast_case_i2f si1 =>
      match v with
      | Vint i => Some (Vfloat (cast_int_float si1 i))
      | _ => None
      end
  | cast_case_i2s si1 =>
      match v with
      | Vint i => Some (Vsingle (cast_int_single si1 i))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
          match cast_single_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_i2bool =>
      match v with
      | Vint n =>
          Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None
      | _ => None
      end
  | cast_case_l2bool =>
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None

      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_s2bool =>
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2l =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | cast_case_i2l si =>
      match v with
      | Vint n => Some(Vlong (cast_int_long si n))
      | _ => None
      end
  | cast_case_l2i sz si =>
      match v with
      | Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end
  | cast_case_l2f si1 =>
      match v with
      | Vlong i => Some (Vfloat (cast_long_float si1 i))
      | _ => None
      end
  | cast_case_l2s si1 =>
      match v with
      | Vlong i => Some (Vsingle (cast_long_single si1 i))
      | _ => None
      end
  | cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
          match cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
          match cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_composite id1 id2 =>
    if ident_eq id1 id2
       || In_dec ident_eq id1 (superclasses_id ce id2)
       || In_dec ident_eq id1 (superinterfaces_id ce id2)
    then Some v
    else None
  | cast_case_agg => Some v
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of
  the [!] and [?] operators, as well as the [if], [while],
  and [for] statements. *)

Inductive classify_bool_cases : Type :=
  | bool_case_i                           (**r integer *)
  | bool_case_l                           (**r long *)
  | bool_case_f                           (**r double float *)
  | bool_case_s                           (**r single float *)
  | bool_default.

Definition classify_bool (mt: type) : classify_bool_cases :=
  match typeconv mt with
  | Tprim (PTint (I8 | I16 | I32) _) => bool_case_i
  | Tprim (PTint I64 _) => bool_case_l
  | Tprim (PTaddr A32) => bool_case_i
  | Tprim (PTaddr A64) => bool_case_l
  | Tprim (PTptr | PTref) | Tpointer _ => if Archi.ptr64 then bool_case_l else bool_case_i
  | Tprim (PTfloat F64) => bool_case_f
  | Tprim (PTfloat F32) => bool_case_s
  | _ => bool_default
  end.

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Definition bool_val (v: val) (mt: type) (m: mem) : option bool :=
  match classify_bool mt with
  | bool_case_i =>
      match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | Vptr b ofs =>
          if Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
      | _ => None
      end
  | bool_case_l =>
      match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_case_s =>
      match v with
      | Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end
  | bool_default => None
  end.

(** ** Unary operators *)

(** *** Boolean negation *)

Definition sem_lnot (v: val) (mt: type) (m: mem): option val :=
  option_map (fun b => Val.of_bool (negb b)) (bool_val v mt m).

(** *** Opposite and absolute value *)

Inductive classify_neg_cases : Type :=
  | neg_case_i(s: signedness)              (**r int *)
  | neg_case_f                             (**r double float *)
  | neg_case_s                             (**r single float *)
  | neg_case_l(s: signedness)              (**r long *)
  | neg_default.

Definition classify_neg (mt: type) : classify_neg_cases :=
  match mt with
  | Tprim pt =>
    match pt with
    | PTint I32 Unsigned | PTbool => neg_case_i Unsigned
    | PTint I64 si => neg_case_l si
    | PTint _ _ => neg_case_i Signed
    | PTfloat F64 => neg_case_f
    | PTfloat F32 => neg_case_s
    | _ => neg_default
    end
  | _ => neg_default
  end.

Definition sem_neg (v: val) (mt: type) : option val :=
  match classify_neg mt with
  | neg_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | neg_case_s =>
      match v with
      | Vsingle f => Some (Vsingle (Float32.neg f))
      | _ => None
      end
  | neg_case_l sg =>
      match v with
      | Vlong n => Some (Vlong (Int64.neg n))
      | _ => None
      end
  | neg_default => None
  end.

Definition sem_abs (v: val) (mt: type) : option val :=
  match classify_neg mt with
  | neg_case_i Unsigned =>
      match v with
      | Vint n => Some (Vint n)
      | _ => None
      end
  | neg_case_i Signed =>
      match v with
      | Vint n => Some (Vint (Int.repr (Z.abs (Int.signed n))))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.abs f))
      | _ => None
      end
  | neg_case_s =>
      match v with
      | Vsingle f => Some (Vsingle (Float32.abs f))
      | _ => None
      end
  | neg_case_l Unsigned =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | neg_case_l Signed =>
      match v with
      | Vlong n => Some (Vlong (Int64.repr (Z.abs (Int64.signed n))))
      | _ => None
      end
  | neg_default => None
  end.

(** *** Bitwise complement *)

Inductive classify_bnot_cases : Type :=
  | bnot_case_i(s: signedness)              (**r int *)
  | bnot_case_l(s: signedness)              (**r long *)
  | bnot_default.

Definition classify_bnot (mt: type) : classify_bnot_cases :=
  match mt with
  | Tprim pt =>
    match pt with
    | PTint I32 Unsigned | PTbool => bnot_case_i Unsigned
    | PTint I64 si => bnot_case_l si
    | PTint _ _ => bnot_case_i Signed
    | _ => bnot_default
    end
  | _ => bnot_default
  end.

Definition sem_bnot (v: val) (mt: type): option val :=
  match classify_bnot mt with
  | bnot_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.not n))
      | _ => None
      end
  | bnot_case_l sg =>
      match v with
      | Vlong n => Some (Vlong (Int64.not n))
      | _ => None
      end
  | notint_default => None
  end.

(** *** Reciprocal *)

Inductive classify_recip_cases : Type :=
  | recip_case_f              (**r float *)
  | recip_case_s              (**r single *)
  | recip_default.

Definition classify_recip (mt: type) : classify_recip_cases :=
  match mt with
  | Tprim pt =>
    match pt with
    | PTfloat F32 => recip_case_s
    | PTfloat F64 => recip_case_f
    | _ => recip_default
    end
  | _ => recip_default
  end.

Definition sem_recip (v: val) (mt: type) : option val :=
  match classify_recip mt with
  | recip_case_f =>
    match v with
    | Vfloat f =>
      Some (Vfloat (Float.div (Float.of_int Int.one) f))
    | _ => None
    end
  | recip_case_s =>
    match v with
    | Vsingle s =>
      Some (Vsingle (Float32.div (Float32.of_int Int.one) s))
    | _ => None
    end
  | recip_case_default => None
  end.

(** *** Signed extension & Zero extension *)

Inductive classify_ext_cases : Type :=
  | zext_case_i
  | zext_case_l
  | sext_case_i
  | sext_case_l
  | ext_default.

Definition classify_ext (mt: type) : classify_ext_cases :=
  match mt with
  | Tprim pt =>
    match pt with
    | PTint I64 Unsigned => zext_case_l
    | PTint I64 Signed => sext_case_l
    | PTint _ Unsigned => zext_case_i
    | PTint _ Signed => sext_case_i
    | _ => ext_default
    end
  | _ => ext_default
  end.

Definition sem_zext (v: val) (sz: N) (mt: type): option val :=
  match classify_ext mt with
  | zext_case_i =>
      match v with
      | Vint n => Some (Vint (Int.zero_ext (Z.of_N sz) n))
      | _ => None
      end
  | zext_case_l =>
      match v with
      | Vlong n => Some (Vlong (Int64.zero_ext (Z.of_N sz) n))
      | _ => None
      end
  | _ => None
  end.

Definition sem_sext (v: val) (sz: N) (mt: type): option val :=
  match classify_ext mt with
  | sext_case_i =>
      match v with
      | Vint n => Some (Vint (Int.sign_ext (Z.of_N sz) n))
      | _ => None
      end
  | sext_case_l =>
      match v with
      | Vlong n => Some (Vlong (Int64.sign_ext (Z.of_N sz) n))
      | _ => None
      end
  | _ => None
  end.

(** *** Sqrt *)

Definition sem_sqrt (v: val) (mt: type) : option val :=
  match classify_recip mt with
  | recip_case_f =>
    match v with
    | Vfloat f =>
      Some (Vfloat (Float.sqrt f))
    | _ => None
    end
  | recip_case_s =>
    match v with
    | Vsingle s =>
      Some (Vsingle (Float32.sqrt s))
    | _ => None
    end
  | recip_case_default => None
  end.

(** ** Binary operators *)

(** For binary operations, the "usual binary conversions" consist in
- determining the type at which the operation is to be performed
  (a form of least upper bound of the types of the two arguments);
- casting the two arguments to this common type;
- performing the operation at that type.
*)

Inductive binarith_cases: Type :=
  | bin_case_i (s: signedness)         (**r at int type *)
  | bin_case_l (s: signedness)         (**r at long int type *)
  | bin_case_f                         (**r at double float type *)
  | bin_case_s                         (**r at single float type *)
  | bin_default.                       (**r error *)

Definition classify_binarith (mt1: type) (mt2: type) : binarith_cases :=
  match mt1, mt2 with
  | Tprim pt1, Tprim pt2 =>
    match pt1, pt2 with
    | PTint I64 Signed, PTint I64 Signed => bin_case_l Signed
    | PTint I64 _, PTint I64 _ => bin_case_l Unsigned
    | PTint I64 sg, PTint _ _ => bin_case_l sg
    | PTint _ _, PTint I64 sg => bin_case_l sg
    | PTint I32 Unsigned, PTint _ _ => bin_case_i Unsigned
    | PTint _ _, PTint I32 Unsigned => bin_case_i Unsigned
    | PTint _ _, PTint _ _ => bin_case_i Signed
    | PTfloat F32, PTfloat F32 => bin_case_s
    | PTfloat _, PTfloat _ => bin_case_f
    | PTfloat F64, PTint _ _ => bin_case_f
    | PTint _ _, PTfloat F64 => bin_case_f
    | PTfloat F32, PTint _ _ => bin_case_s
    | PTint _ _, PTfloat F32 => bin_case_s
    | _, _ => bin_default
    end
  | _, _ => bin_default
  end.

(** The static type of the result. Both arguments are converted to this type
    before the actual computation. *)

Definition binarith_type (c: binarith_cases) : type :=
  match c with
  | bin_case_i sg => Tprim (PTint I32 sg)
  | bin_case_l sg => Tprim (PTint I64 sg)
  | bin_case_f    => Tprim (PTfloat F64)
  | bin_case_s    => Tprim (PTfloat F32)
  | bin_default   => Tprim (PTvoid)
  end.

Lemma binarith_type_of_int_preserve:
  forall si,
    binarith_type (classify_binarith (Tprim (PTint I32 si)) (Tprim (PTint I32 si))) = (Tprim (PTint I32 si)).
Proof.
  intros. destruct si; simpl; auto.
Qed.

Lemma binarith_type_of_long_preserve:
  forall si,
    binarith_type (classify_binarith (Tprim (PTint I64 si)) (Tprim (PTint I64 si))) = (Tprim (PTint I64 si)).
Proof.
  intros. destruct si; simpl; auto.
Qed.

Lemma binarith_type_of_float_preserve:
  binarith_type (classify_binarith (Tprim (PTfloat F64)) (Tprim (PTfloat F64))) = (Tprim (PTfloat F64)).
Proof.
  intros. simpl; auto.
Qed.

Lemma binarith_type_of_single_preserve:
  binarith_type (classify_binarith (Tprim (PTfloat F32)) (Tprim (PTfloat F32))) = (Tprim (PTfloat F32)).
Proof.
  intros. simpl; auto.
Qed.

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env): option val :=
  let c := classify_binarith mt1 mt2 in
  let mt := binarith_type c in
  match sem_cast v1 mt1 mt m ce with
  | None => None
  | Some v1' =>
  match sem_cast v2 mt2 mt m ce with
  | None => None
  | Some v2' =>
  match c with
  | bin_case_i sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => sem_int sg n1 n2
      | _,  _ => None
      end
  | bin_case_f =>
      match v1, v2 with
      | Vfloat n1, Vfloat n2 => sem_float n1 n2
      | _,  _ => None
      end
  | bin_case_s =>
      match v1, v2 with
      | Vsingle n1, Vsingle n2 => sem_single n1 n2
      | _,  _ => None
      end
  | bin_case_l sg =>
      match v1, v2 with
      | Vlong n1, Vlong n2 => sem_long sg n1 n2
      | _,  _ => None
      end
  | bin_default => None
  end end end.

(** *** Addition *)

Definition sem_add (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
    v1 mt1 v2 mt2 m ce.

(** *** Subtraction *)

Definition sem_sub (v1: val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
    v1 mt1 v2 mt2 m ce.

(** *** Multiplication, division, modulus *)

Definition sem_mul (v1: val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    v1 mt1 v2 mt2 m ce.

Definition sem_div (v1: val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.divs n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.divu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.divs n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.divu n1 n2))
      end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    v1 mt1 v2 mt2 m ce.

Definition sem_rem (v1: val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 mt1 v2 mt2 m ce.

Definition sem_band (v1: val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 mt1 v2 mt2 m ce.

Definition sem_bior (v1: val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 mt1 v2 mt2 m ce.

Definition sem_bxor (v1:val) (mt1: type) (v2: val) (mt2: type) (m:mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 mt1 v2 mt2 m ce.

(** *** Shifts *)

(** Shifts do not perform the usual binary conversions.  Instead,
  each argument is converted independently, and the signedness
  of the result is always that of the first argument. *)

Inductive classify_shift_cases : Type:=
  | shift_case_ii(s: signedness)         (**r int , int *)
  | shift_case_ll(s: signedness)         (**r long, long *)
  | shift_case_il(s: signedness)         (**r int, long *)
  | shift_case_li(s: signedness)         (**r long, int *)
  | shift_default.

Definition classify_shift (mt1: type) (mt2: type) :=
  match typeconv mt1, typeconv mt2 with
  | Tprim pt1, Tprim pt2 =>
    match pt1, pt2 with
    | PTint I64 s, PTint I64 _ => shift_case_ll s
    | PTint I64 s, PTint _ _ => shift_case_li s
    | PTint I32 Unsigned, PTint I64 _ => shift_case_il Unsigned
    | PTint _ _, PTint I64 _ => shift_case_il Signed
    | PTint I32 Unsigned, PTint _ _ => shift_case_ii Unsigned
    | PTint _ _, PTint _ _ => shift_case_ii Signed
    | _,_  => shift_default
    end
  | _, _ => shift_default
  end.

Definition sem_shift
    (sem_int: signedness -> int -> int -> int)
    (sem_long: signedness -> int64 -> int64 -> int64)
    (v1: val) (mt1: type) (v2: val) (mt2: type) : option val :=
  match classify_shift mt1 mt2 with
  | shift_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.ltu n2 Int.iwordsize
          then Some(Vint(sem_int sg n1 n2)) else None
      | _, _ => None
      end
  | shift_case_il sg =>
      match v1, v2 with
      | Vint n1, Vlong n2 =>
          if Int64.ltu n2 (Int64.repr 32)
          then Some(Vint(sem_int sg n1 (Int64.loword n2))) else None
      | _, _ => None
      end
  | shift_case_li sg =>
      match v1, v2 with
      | Vlong n1, Vint n2 =>
          if Int.ltu n2 Int64.iwordsize'
          then Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else None
      | _, _ => None
      end
  | shift_case_ll sg =>
      match v1, v2 with
      | Vlong n1, Vlong n2 =>
          if Int64.ltu n2 Int64.iwordsize
          then Some(Vlong(sem_long sg n1 n2)) else None
      | _, _ => None
      end
  | shift_default => None
  end.

Definition sem_shl (v1: val) (mt1: type) (v2: val) (mt2: type) : option val :=
  sem_shift
    (fun sg n1 n2 => Int.shl n1 n2)
    (fun sg n1 n2 => Int64.shl n1 n2)
    v1 mt1 v2 mt2.

Definition sem_ashr (v1: val) (mt1: type) (v2: val) (mt2: type) : option val :=
  sem_shift
    (fun sg n1 n2 => Int.shr n1 n2)
    (fun sg n1 n2 => Int64.shr n1 n2)
    v1 mt1 v2 mt2.

Definition sem_lshr (v1: val) (mt1: type) (v2: val) (mt2: type) : option val :=
  sem_shift
    (fun sg n1 n2 => Int.shru n1 n2)
    (fun sg n1 n2 => Int64.shru n1 n2)
    v1 mt1 v2 mt2.

(** *** Comparisons *)

Inductive classify_cmp_cases : Type :=
  | cmp_case_pp                       (**r pointer, pointer *)
  | cmp_case_pi (si: signedness)      (**r pointer, int *)
  | cmp_case_ip (si: signedness)      (**r int, pointer *)
  | cmp_case_pl                       (**r pointer, long *)
  | cmp_case_lp                       (**r long, pointer *)
  | cmp_default.                      (**r numerical, numerical *)

Definition classify_cmp (mt1: type) (mt2: type) :=
  match typeconv mt1, typeconv mt2 with
  | (Tpointer _ | Tprim (PTptr | PTref)), Tprim (PTint I64 _ | PTaddr A64) => cmp_case_pl
  | Tprim (PTint I64 _ | PTaddr A64), (Tpointer _ | Tprim (PTptr | PTref)) => cmp_case_lp
  | (Tpointer _ | Tprim (PTptr | PTref)), (Tpointer _ | Tprim (PTptr | PTref)) => cmp_case_pp
  | (Tpointer _ | Tprim (PTptr | PTref)), Tprim (PTint _ si) => cmp_case_pi si
  | (Tpointer _ | Tprim (PTptr | PTref)), Tprim (PTaddr A32) => cmp_case_pi Unsigned
  | Tprim (PTint _ si), (Tpointer _ | Tprim (PTptr | PTref)) => cmp_case_ip si
  | _, _ => cmp_default
  end.

Definition cmp_ptr (m: mem) (c: comparison) (v1 v2: val): option val :=
  option_map Val.of_bool
   (if Archi.ptr64
    then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
    else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2).

Definition ptrofs_of_int (si: signedness) (n: int) : ptrofs :=
  match si with
  | Signed => Ptrofs.of_ints n
  | Unsigned => Ptrofs.of_intu n
  end.

Definition sem_cmp_bool (c:comparison) (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env): option val :=
  match classify_cmp mt1 mt2 with
  | cmp_case_pp =>
      cmp_ptr m c v1 v2
  | cmp_case_pi si =>
      match v2 with
      | Vint n2 =>
          let v2' := Vptrofs (ptrofs_of_int si n2) in
          cmp_ptr m c v1 v2'
      | Vptr b ofs =>
          if Archi.ptr64 then None else cmp_ptr m c v1 v2
      | _ =>
          None
      end
  | cmp_case_ip si =>
      match v1 with
      | Vint n1 =>
          let v1' := Vptrofs (ptrofs_of_int si n1) in
          cmp_ptr m c v1' v2
      | Vptr b ofs =>
          if Archi.ptr64 then None else cmp_ptr m c v1 v2
      | _ =>
          None
      end
  | cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
          let v2' := Vptrofs (Ptrofs.of_int64 n2) in
          cmp_ptr m c v1 v2'
      | Vptr b ofs =>
          if Archi.ptr64 then cmp_ptr m c v1 v2 else None
      | _ =>
          None
      end
  | cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
          let v1' := Vptrofs (Ptrofs.of_int64 n1) in
          cmp_ptr m c v1' v2
      | Vptr b ofs =>
          if Archi.ptr64 then cmp_ptr m c v1 v2 else None
      | _ =>
          None
      end
  | cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float32.cmp c n1 n2)))
        v1 mt1 v2 mt2 m ce
  end.

Definition cmp_int (sg: signedness) (x y: int) : Datatypes.comparison :=
  match sg with
  | Signed => Z.compare (Int.signed x) (Int.signed y)
  | Unsigned => Z.compare (Int.unsigned x) (Int.unsigned y)
  end.

Definition cmp_long (sg: signedness) (x y: int64) : Datatypes.comparison :=
  match sg with
  | Signed => Z.compare (Int64.signed x) (Int64.signed y)
  | Unsigned => Z.compare (Int64.unsigned x) (Int64.unsigned y)
  end.

Definition val_of_comparison (c: Datatypes.comparison) :=
  match c with
  | Eq => Vint Int.zero
  | Gt => Vint Int.one
  | Lt => Vint Int.mone
  end.

Definition sem_cmp (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (val_of_comparison (cmp_int sg n1 n2)))
    (fun sg n1 n2 => Some (val_of_comparison (cmp_long sg n1 n2)))
    (fun n1 n2 => option_map val_of_comparison (Float.compare n1 n2))
    (fun n1 n2 => option_map val_of_comparison (Float32.compare n1 n2))
    v1 mt1 v2 mt2 m ce.

Definition cmpg_float (x y: float) : Datatypes.comparison :=
  match Float.compare x y with
  | Some c => c
  | None => Gt
  end.

Definition cmpg_single (x y: float32) : Datatypes.comparison :=
  match Float32.compare x y with
  | Some c => c
  | None => Gt
  end.

Definition sem_cmpg (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (val_of_comparison (cmp_int sg n1 n2)))
    (fun sg n1 n2 => Some (val_of_comparison (cmp_long sg n1 n2)))
    (fun n1 n2 => Some (val_of_comparison (cmpg_float n1 n2)))
    (fun n1 n2 => Some (val_of_comparison (cmpg_single n1 n2)))
    v1 mt1 v2 mt2 m ce.

Definition cmpl_float (x y: float) : Datatypes.comparison :=
  match Float.compare x y with
  | Some c => c
  | None => Lt
  end.

Definition cmpl_single (x y: float32) : Datatypes.comparison :=
  match Float32.compare x y with
  | Some c => c
  | None => Lt
  end.

Definition sem_cmpl (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (val_of_comparison (cmp_int sg n1 n2)))
    (fun sg n1 n2 => Some (val_of_comparison (cmp_long sg n1 n2)))
    (fun n1 n2 => Some (val_of_comparison (cmpl_float n1 n2)))
    (fun n1 n2 => Some (val_of_comparison (cmpl_single n1 n2)))
    v1 mt1 v2 mt2 m ce.

Definition sem_max (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (Vint (match cmp_int sg n1 n2 with Lt => n2 | _ => n1 end)))
    (fun sg n1 n2 => Some (Vlong (match cmp_long sg n1 n2 with Lt => n2 | _ => n1 end)))
    (fun n1 n2 => match Float.compare n1 n2 with Some Lt => Some (Vfloat n2) | Some _ => Some (Vfloat n1) | None => None end)
    (fun n1 n2 => match Float32.compare n1 n2 with Some Lt => Some (Vsingle n2) | Some _ => Some (Vsingle n1) | None => None end)
    v1 mt1 v2 mt2 m ce.

Definition sem_min (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (Vint (match cmp_int sg n1 n2 with Gt => n2 | _ => n1 end)))
    (fun sg n1 n2 => Some (Vlong (match cmp_long sg n1 n2 with Gt => n2 | _ => n1 end)))
    (fun n1 n2 => match Float.compare n1 n2 with Some Gt => Some (Vfloat n2) | Some _ => Some (Vfloat n1) | None => None end)
    (fun n1 n2 => match Float32.compare n1 n2 with Some Gt => Some (Vsingle n2) | Some _ => Some (Vsingle n1) | None => None end)
    v1 mt1 v2 mt2 m ce.
(*
Definition bool_int (n: int) := negb (Int.eq n Int.zero).

Definition land_int (x y: int) := bool_int x && bool_int y.

Definition lior_int (x y: int) := bool_int x || bool_int y.

Definition bool_long (n: int64) := negb (Int64.eq n Int64.zero).

Definition land_long (x y: int64) := bool_long x && bool_long y.

Definition lior_long (x y: int64) := bool_long x || bool_long y.

Definition sem_land (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (Val.of_bool (land_int n1 n2)))
    (fun sg n1 n2 => Some (Val.of_bool (land_long n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 mt1 v2 mt2 m ce.

Definition sem_lior (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some (Val.of_bool (lior_int n1 n2)))
    (fun sg n1 n2 => Some (Val.of_bool (lior_long n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 mt1 v2 mt2 m ce.
*)
Definition sem_land (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  match bool_val v1 mt1 m, bool_val v2 mt2 m with
  | Some b1, Some b2 => Some (Val.of_bool (b1 && b2))
  | _, _ => None
  end.

Definition sem_lior (v1: val) (mt1: type) (v2: val) (mt2: type) (m: mem) (ce: composite_env) : option val :=
  match bool_val v1 mt1 m, bool_val v2 mt2 m with
  | Some b1, Some b2 => Some (Val.of_bool (b1 || b2))
  | _, _ => None
  end.

(** ** Argument of a [switch] statement *)

Inductive classify_switch_cases : Type :=
  | switch_case_i
  | switch_case_l
  | switch_default.

Definition classify_switch (mt: type) :=
  match mt with
  | Tprim pt =>
    match pt with
    | PTint I64 _ => switch_case_l
    | PTint _ _ => switch_case_i
    | _ => switch_default
    end
  | _ => switch_default
  end.

Definition sem_switch_arg (v: val) (mt: type): option Z :=
  match classify_switch mt with
  | switch_case_i =>
      match v with Vint n => Some (Int.unsigned n) | _ => None end
  | switch_case_l =>
      match v with Vlong n => Some (Int64.unsigned n) | _ => None end
  | switch_default =>
      None
  end.

(** * Combined semantics of unary and binary operators *)

Definition sem_unary_operation
           (op: unary_operation) (v: val) (tfrom tto: type) (m: mem) (ce: composite_env) : option val :=
  match sem_cast v tto tfrom m ce with
  | Some v' =>
    match op with
    | O_abs => sem_abs v' tto
    | O_bnot => sem_bnot v' tto
    | O_lnot =>
      match sem_lnot v' tto m with
      | Some v'' => sem_cast v'' (Tprim (PTint I32 Signed)) tto m ce
      | None => None
      end
    | O_neg => sem_neg v' tto
    | O_recip => sem_recip v' tto
    | O_sext sz => sem_sext v' sz tto
    | O_zext sz => sem_zext v' sz tto
    | O_sqrt => sem_sqrt v' tto
    end
  | None => None
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (mt1: type) (v2: val) (mt2: type) (mt: type)
    (m: mem) (ce: composite_env) : option val :=
  match op with
  | O_add =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_add v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_sub =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_sub v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_mul =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_mul v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_div =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_div v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_rem =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_rem v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_band =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_band v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_bior =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_bior v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_bxor =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_bxor v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_land =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' =>
      match sem_land v1' mt v2' mt m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_lior =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' =>
      match sem_lior v1' mt v2' mt m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_ashr =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_ashr v1' mt v2' mt
    | _, _ => None
    end
  | O_lshr =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_lshr v1' mt v2' mt
    | _, _ => None
    end
  | O_shl =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_shl v1' mt v2' mt
    | _, _ => None
    end
  | O_max =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_max v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_min =>
    match sem_cast v1 mt1 mt m ce, sem_cast v2 mt2 mt m ce with
    | Some v1', Some v2' => sem_min v1' mt v2' mt m ce
    | _, _ => None
    end
  | O_cmp pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_cmpg pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmpg v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_cmpl pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmpl v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_eq pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp_bool Ceq v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_ne pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp_bool Cne v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_lt pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp_bool Clt v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_gt pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp_bool Cgt v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_le pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp_bool Cle v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  | O_ge pt =>
    match sem_cast v1 mt1 (Tprim pt) m ce, sem_cast v2 mt2 (Tprim pt) m ce with
    | Some v1', Some v2' =>
      match sem_cmp_bool Cge v1' (Tprim pt) v2' (Tprim pt) m ce with
      | Some v => sem_cast v (Tprim (PTint I32 Signed)) mt m ce
      | None => None
      end
    | _, _ => None
    end
  end.

Definition sem_trunc (v: val) (ptfrom ptto: prim_type) : option val :=
  match classify_cast (Tprim ptfrom) (Tprim ptto), v with
  | cast_case_f2i sz si, Vfloat f =>
    match cast_float_int si f with
    | Some i => Some (Vint (cast_int_int sz si i))
    | None => None
    end
  | cast_case_f2l si, Vfloat f =>
    match cast_float_long si f with
    | Some i => Some (Vlong i)
    | None => None
    end
  | cast_case_s2i sz si, Vsingle f =>
    match cast_single_int si f with
    | Some i => Some (Vint (cast_int_int sz si i))
    | None => None
    end
  | cast_case_f2l si, Vsingle f =>
    match cast_single_long si f with
    | Some i => Some (Vlong i)
    | None => None
    end
  | _, _ => None
  end.

Definition ceil_float_int (si: signedness) (f: float) : option int :=
  match si with
  | Signed =>
    match Float.to_int f with
    | Some n =>
      match Float.compare f (Float.of_int n) with
      | Some Gt => Some (Int.add n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float.to_intu f with
    | Some n =>
      match Float.compare f (Float.of_intu n) with
      | Some Gt => Some (Int.add n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition ceil_float_long (si: signedness) (f: float) : option int64 :=
  match si with
  | Signed =>
    match Float.to_long f with
    | Some n =>
      match Float.compare f (Float.of_long n) with
      | Some Gt => Some (Int64.add n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float.to_longu f with
    | Some n =>
      match Float.compare f (Float.of_longu n) with
      | Some Gt => Some (Int64.add n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition ceil_single_int (si: signedness) (f: float32) : option int :=
  match si with
  | Signed =>
    match Float32.to_int f with
    | Some n =>
      match Float32.compare f (Float32.of_int n) with
      | Some Gt => Some (Int.add n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float32.to_intu f with
    | Some n =>
      match Float32.compare f (Float32.of_intu n) with
      | Some Gt => Some (Int.add n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition ceil_single_long (si: signedness) (f: float32) : option int64 :=
  match si with
  | Signed =>
    match Float32.to_long f with
    | Some n =>
      match Float32.compare f (Float32.of_long n) with
      | Some Gt => Some (Int64.add n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float32.to_longu f with
    | Some n =>
      match Float32.compare f (Float32.of_longu n) with
      | Some Gt => Some (Int64.add n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition sem_ceil (v: val) (ptfrom ptto: prim_type) : option val :=
  match classify_cast (Tprim ptfrom) (Tprim ptto), v with
  | cast_case_f2i sz si, Vfloat f =>
    match ceil_float_int si f with
    | Some i => Some (Vint (cast_int_int sz si i))
    | None => None
    end
  | cast_case_f2l si, Vfloat f =>
    match ceil_float_long si f with
    | Some i => Some (Vlong i)
    | None => None
    end
  | cast_case_s2i sz si, Vsingle f =>
    match ceil_single_int si f with
    | Some i => Some (Vint (cast_int_int sz si i))
    | None => None
    end
  | cast_case_f2l si, Vsingle f =>
    match ceil_single_long si f with
    | Some i => Some (Vlong i)
    | None => None
    end
  | _, _ => None
  end.

Definition floor_float_int (si: signedness) (f: float) : option int :=
  match si with
  | Signed =>
    match Float.to_int f with
    | Some n =>
      match Float.compare f (Float.of_int n) with
      | Some Lt => Some (Int.sub n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float.to_intu f with
    | Some n =>
      match Float.compare f (Float.of_intu n) with
      | Some Lt => Some (Int.sub n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition floor_float_long (si: signedness) (f: float) : option int64 :=
  match si with
  | Signed =>
    match Float.to_long f with
    | Some n =>
      match Float.compare f (Float.of_long n) with
      | Some Lt => Some (Int64.sub n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float.to_longu f with
    | Some n =>
      match Float.compare f (Float.of_longu n) with
      | Some Lt => Some (Int64.sub n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition floor_single_int (si: signedness) (f: float32) : option int :=
  match si with
  | Signed =>
    match Float32.to_int f with
    | Some n =>
      match Float32.compare f (Float32.of_int n) with
      | Some Lt => Some (Int.sub n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float32.to_intu f with
    | Some n =>
      match Float32.compare f (Float32.of_intu n) with
      | Some Lt => Some (Int.sub n Int.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition floor_single_long (si: signedness) (f: float32) : option int64 :=
  match si with
  | Signed =>
    match Float32.to_long f with
    | Some n =>
      match Float32.compare f (Float32.of_long n) with
      | Some Lt => Some (Int64.sub n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  | Unsigned =>
    match Float32.to_longu f with
    | Some n =>
      match Float32.compare f (Float32.of_longu n) with
      | Some Lt => Some (Int64.sub n Int64.one)
      | Some _ => Some n
      | None => None
      end
    | None => None
    end
  end.

Definition sem_floor (v: val) (ptfrom ptto: prim_type) : option val :=
  match classify_cast (Tprim ptfrom) (Tprim ptto), v with
  | cast_case_f2i sz si, Vfloat f =>
    match floor_float_int si f with
    | Some i => Some (Vint (cast_int_int sz si i))
    | None => None
    end
  | cast_case_f2l si, Vfloat f =>
    match floor_float_long si f with
    | Some i => Some (Vlong i)
    | None => None
    end
  | cast_case_s2i sz si, Vsingle f =>
    match floor_single_int si f with
    | Some i => Some (Vint (cast_int_int sz si i))
    | None => None
    end
  | cast_case_f2l si, Vsingle f =>
    match floor_single_long si f with
    | Some i => Some (Vlong i)
    | None => None
    end
  | _, _ => None
  end.

(*
Definition sem_incrdecr (cenv: composite_env) (id: incr_or_decr) (v: val) (ty: type) (m: mem) :=
  match id with
  | Incr => sem_add cenv v ty (Vint Int.one) type_int32s m
  | Decr => sem_sub cenv v ty (Vint Int.one) type_int32s m
  end.

Definition incrdecr_type (ty: type) :=
  match typeconv ty with
  | Tpointer ty a => Tpointer ty a
  | Tint sz sg a => Tint sz sg noattr
  | Tlong sg a => Tlong sg noattr
  | Tfloat sz a => Tfloat sz noattr
  | _ => Tvoid
  end.

(** * Compatibility with extensions and injections *)

Section GENERIC_INJECTION.

Variable f: meminj.
Variables m m': mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Remark val_inject_vtrue: forall f, Val.inject f Vtrue Vtrue.
Proof. unfold Vtrue; auto. Qed.

Remark val_inject_vfalse: forall f, Val.inject f Vfalse Vfalse.
Proof. unfold Vfalse; auto. Qed.

Remark val_inject_of_bool: forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof. intros. unfold Val.of_bool. destruct b; [apply val_inject_vtrue|apply val_inject_vfalse].
Qed.

Remark val_inject_vptrofs: forall n, Val.inject f (Vptrofs n) (Vptrofs n).
Proof. intros. unfold Vptrofs. destruct Archi.ptr64; auto. Qed.

Local Hint Resolve val_inject_vtrue val_inject_vfalse val_inject_of_bool val_inject_vptrofs : core.

Ltac TrivialInject :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; TrivialInject
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x; TrivialInject
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; TrivialInject
  | [ |- exists v', Some ?v = Some v' /\ _ ] => exists v; split; auto
  | _ => idtac
  end.

Lemma sem_cast_inj:
  forall v1 ty1 ty v tv1,
  sem_cast v1 ty1 ty m = Some v ->
  Val.inject f v1 tv1 ->
  exists tv, sem_cast tv1 ty1 ty m'= Some tv /\ Val.inject f v tv.
Proof.
  unfold sem_cast; intros; destruct (classify_cast ty1 ty); inv H0; TrivialInject.
- econstructor; eauto.
- erewrite weak_valid_pointer_inj by eauto. TrivialInject. 
- erewrite weak_valid_pointer_inj by eauto. TrivialInject. 
- destruct (ident_eq id1 id2); TrivialInject. econstructor; eauto.
- destruct (ident_eq id1 id2); TrivialInject. econstructor; eauto.
- econstructor; eauto.
Qed.

Lemma bool_val_inj:
  forall v ty b tv,
  bool_val v ty m = Some b ->
  Val.inject f v tv ->
  bool_val tv ty m' = Some b.
Proof.
  unfold bool_val; intros.
  destruct (classify_bool ty); inv H0; try congruence.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) eqn:VP; inv H.
  erewrite weak_valid_pointer_inj by eauto. auto.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) eqn:VP; inv H.
  erewrite weak_valid_pointer_inj by eauto. auto.
Qed.

Lemma sem_unary_operation_inj:
  forall op v1 ty v tv1,
  sem_unary_operation op v1 ty m = Some v ->
  Val.inject f v1 tv1 ->
  exists tv, sem_unary_operation op tv1 ty m' = Some tv /\ Val.inject f v tv.
Proof.
  unfold sem_unary_operation; intros. destruct op.
- (* notbool *)
  unfold sem_notbool in *. destruct (bool_val v1 ty m) as [b|] eqn:BV; simpl in H; inv H.
  erewrite bool_val_inj by eauto. simpl. TrivialInject.
- (* notint *)
  unfold sem_notint in *; destruct (classify_notint ty); inv H0; inv H; TrivialInject.
- (* neg *)
  unfold sem_neg in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
- (* absfloat *)
  unfold sem_absfloat in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
Qed.

Definition optval_self_injects (ov: option val) : Prop :=
  match ov with
  | Some (Vptr b ofs) => False
  | _ => True
  end.

Remark sem_binarith_inject:
  forall sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2',
  sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m = Some v ->
  Val.inject f v1 v1' -> Val.inject f v2 v2' ->
  (forall sg n1 n2, optval_self_injects (sem_int sg n1 n2)) ->
  (forall sg n1 n2, optval_self_injects (sem_long sg n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_float n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_single n1 n2)) ->
  exists v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m' = Some v' /\ Val.inject f v v'.
Proof.
  intros.
  assert (SELF: forall ov v, ov = Some v -> optval_self_injects ov -> Val.inject f v v).
  {
    intros. subst ov; simpl in H7. destruct v0; contradiction || constructor.
  }
  unfold sem_binarith in *.
  set (c := classify_binarith t1 t2) in *.
  set (t := binarith_type c) in *.
  destruct (sem_cast v1 t1 t m) as [w1|] eqn:C1; try discriminate.
  destruct (sem_cast v2 t2 t m) as [w2|] eqn:C2; try discriminate.
  exploit (sem_cast_inj v1); eauto. intros (w1' & C1' & INJ1).
  exploit (sem_cast_inj v2); eauto. intros (w2' & C2' & INJ2).
  rewrite C1'; rewrite C2'.
  destruct c; inv INJ1; inv INJ2; discriminate || eauto.
Qed.

Remark sem_shift_inject:
  forall sem_int sem_long v1 t1 v2 t2 v v1' v2',
  sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
  Val.inject f v1 v1' -> Val.inject f v2 v2' ->
  exists v', sem_shift sem_int sem_long v1' t1 v2' t2 = Some v' /\ Val.inject f v v'.
Proof.
  intros. exists v.
  unfold sem_shift in *; destruct (classify_shift t1 t2); inv H0; inv H1; try discriminate.
  destruct (Int.ltu i0 Int.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 Int64.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 (Int64.repr 32)); inv H; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); inv H; auto.
Qed.

Remark sem_cmp_ptr_inj:
  forall c v1 v2 v tv1 tv2,
  cmp_ptr m c v1 v2 = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  exists tv, cmp_ptr m' c tv1 tv2 = Some tv /\ Val.inject f v tv.
Proof.
  unfold cmp_ptr; intros. 
  remember (if Archi.ptr64
       then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
       else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as ob.
  destruct ob as [b|]; simpl in H; inv H.
  exists (Val.of_bool b); split; auto.
  destruct Archi.ptr64. 
  erewrite Val.cmplu_bool_inject by eauto. auto.
  erewrite Val.cmpu_bool_inject by eauto. auto.
Qed.

Remark sem_cmp_inj:
  forall cmp v1 tv1 ty1 v2 tv2 ty2 v,
  sem_cmp cmp v1 ty1 v2 ty2 m = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  exists tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof.
  intros.
  unfold sem_cmp in *; destruct (classify_cmp ty1 ty2).
- (* pointer - pointer *)
  eapply sem_cmp_ptr_inj; eauto.
- (* pointer - int *)
  inversion H1; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* int - pointer *)
  inversion H0; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* pointer - long *)
  inversion H1; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* long - pointer *)
  inversion H0; subst; TrivialInject; eapply sem_cmp_ptr_inj; eauto.
- (* numerical - numerical *)
  assert (SELF: forall b, optval_self_injects (Some (Val.of_bool b))).
  {
    destruct b; exact I.
  }
  eapply sem_binarith_inject; eauto.
Qed.

Lemma sem_binary_operation_inj:
  forall cenv op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
  Val.inject f v1 tv1 -> Val.inject f v2 tv2 ->
  exists tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof.
  unfold sem_binary_operation; intros; destruct op.
- (* add *)
  assert (A: forall cenv ty si v1' v2' tv1' tv2',
             Val.inject f v1' tv1' -> Val.inject f v2' tv2' ->
             sem_add_ptr_int cenv ty si v1' v2' = Some v ->
             exists tv, sem_add_ptr_int cenv ty si tv1' tv2' = Some tv /\ Val.inject f v tv).
  { intros. unfold sem_add_ptr_int in *; inv H2; inv H3; TrivialInject.
    econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. }
  assert (B: forall cenv ty v1' v2' tv1' tv2',
             Val.inject f v1' tv1' -> Val.inject f v2' tv2' ->
             sem_add_ptr_long cenv ty v1' v2' = Some v ->
             exists tv, sem_add_ptr_long cenv ty tv1' tv2' = Some tv /\ Val.inject f v tv).
  { intros. unfold sem_add_ptr_long in *; inv H2; inv H3; TrivialInject.
    econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. }
  unfold sem_add in *; destruct (classify_add ty1 ty2); eauto.
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* sub *)
  unfold sem_sub in *; destruct (classify_sub ty1 ty2).
  + inv H0; inv H1; TrivialInject.
    econstructor. eauto. rewrite Ptrofs.sub_add_l. auto. 
  + inv H0; inv H1; TrivialInject.
    destruct (eq_block b1 b0); try discriminate. subst b1.
    rewrite H0 in H2; inv H2. rewrite dec_eq_true.
    destruct (zlt 0 (sizeof cenv ty) && zle (sizeof cenv ty) Ptrofs.max_signed); inv H.
    rewrite Ptrofs.sub_shifted. TrivialInject.
  + inv H0; inv H1; TrivialInject.
    econstructor. eauto. rewrite Ptrofs.sub_add_l. auto. 
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* mul *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* div *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
  exact I.
- (* mod *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
  exact I.
- (* and *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* or *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* xor *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* shl *)
  eapply sem_shift_inject; eauto.
- (* shr *)
  eapply sem_shift_inject; eauto.
  (* comparisons *)
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
Qed.

End GENERIC_INJECTION.

Lemma sem_cast_inject:
  forall f v1 ty1 ty m v tv1 tm,
  sem_cast v1 ty1 ty m = Some v ->
  Val.inject f v1 tv1 ->
  Mem.inject f m tm ->
  exists tv, sem_cast tv1 ty1 ty tm = Some tv /\ Val.inject f v tv.
Proof.
  intros. eapply sem_cast_inj; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma sem_unary_operation_inject:
  forall f m m' op v1 ty1 v tv1,
  sem_unary_operation op v1 ty1 m = Some v ->
  Val.inject f v1 tv1 ->
  Mem.inject f m m' ->
  exists tv, sem_unary_operation op tv1 ty1 m' = Some tv /\ Val.inject f v tv.
Proof.
  intros. eapply sem_unary_operation_inj; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

Lemma sem_binary_operation_inject:
  forall f m m' cenv op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation cenv op v1 ty1 v2 ty2 m = Some v ->
  Val.inject f v1 tv1 -> Val.inject f v2 tv2 ->
  Mem.inject f m m' ->
  exists tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = Some tv /\ Val.inject f v tv.
Proof.
  intros. eapply sem_binary_operation_inj; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

Lemma bool_val_inject:
  forall f m m' v ty b tv,
  bool_val v ty m = Some b ->
  Val.inject f v tv ->
  Mem.inject f m m' ->
  bool_val tv ty m' = Some b.
Proof.
  intros. eapply bool_val_inj; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
Qed.

(** * Some properties of operator semantics *)

(** This section collects some common-sense properties about the type
  classification and semantic functions above.  Some properties are used
  in the CompCert semantics preservation proofs.  Others are not, but increase
  confidence in the specification and its relation with the ISO C99 standard. *)

(** Relation between Boolean value and casting to [_Bool] type. *)

Lemma cast_bool_bool_val:
  forall v t m,
  sem_cast v t (Tint IBool Signed noattr) m =
  match bool_val v t m with None => None | Some b => Some(Val.of_bool b) end.
  intros.
  assert (A: classify_bool t =
    match t with
    | Tint _ _ _ => bool_case_i
    | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
    | Tfloat F64 _ => bool_case_f
    | Tfloat F32 _ => bool_case_s
    | Tlong _ _ => bool_case_l
    | _ => bool_default
    end).
  {
    unfold classify_bool; destruct t; simpl; auto. destruct i; auto.
  }
  unfold bool_val. rewrite A.
  unfold sem_cast, classify_cast; remember Archi.ptr64 as ptr64; destruct t; simpl; auto; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)); auto.
  destruct (Int64.eq i Int64.zero); auto.
  destruct (negb ptr64); auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct f; auto.
  destruct f; auto.
  destruct f; auto.
  destruct f; auto.
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct f; auto.
  destruct (Float32.cmp Ceq f0 Float32.zero); auto.
  destruct f; auto. 
  destruct ptr64; auto.
  destruct (Int.eq i Int.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Int.eq i Int.zero); auto.
  destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Int.eq i Int.zero); auto.
  destruct ptr64; auto. destruct (Int64.eq i Int64.zero); auto.
  destruct ptr64; auto.
  destruct ptr64; auto.
  destruct ptr64; auto. destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); auto.
Qed.

(** Relation between Boolean value and Boolean negation. *)

Lemma notbool_bool_val:
  forall v t m,
  sem_notbool v t m =
  match bool_val v t m with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof.
  intros. unfold sem_notbool. destruct (bool_val v t m) as [[] | ]; reflexivity.
Qed.

(** Properties of values obtained by casting to a given type. *)

Section VAL_CASTED.

Inductive val_casted: val -> type -> Prop :=
  | val_casted_int: forall sz si attr n,
      cast_int_int sz si n = n ->
      val_casted (Vint n) (Tint sz si attr)
  | val_casted_float: forall attr n,
       val_casted (Vfloat n) (Tfloat F64 attr)
  | val_casted_single: forall attr n,
       val_casted (Vsingle n) (Tfloat F32 attr)
  | val_casted_long: forall si attr n,
      val_casted (Vlong n) (Tlong si attr)
  | val_casted_ptr_ptr: forall b ofs ty attr,
      val_casted (Vptr b ofs) (Tpointer ty attr)
  | val_casted_int_ptr: forall n ty attr,
      Archi.ptr64 = false -> val_casted (Vint n) (Tpointer ty attr)
  | val_casted_ptr_int: forall b ofs si attr,
      Archi.ptr64 = false -> val_casted (Vptr b ofs) (Tint I32 si attr)
  | val_casted_long_ptr: forall n ty attr,
      Archi.ptr64 = true -> val_casted (Vlong n) (Tpointer ty attr)
  | val_casted_ptr_long: forall b ofs si attr,
      Archi.ptr64 = true -> val_casted (Vptr b ofs) (Tlong si attr)
  | val_casted_struct: forall id attr b ofs,
      val_casted (Vptr b ofs) (Tstruct id attr)
  | val_casted_union: forall id attr b ofs,
      val_casted (Vptr b ofs) (Tunion id attr)
  | val_casted_void: forall v,
      val_casted v Tvoid.

Local Hint Constructors val_casted : core.

Remark cast_int_int_idem:
  forall sz sg i, cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i.
Proof.
  intros. destruct sz; simpl; auto.
  destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
  destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
  destruct (Int.eq i Int.zero); auto.
Qed.

Ltac DestructCases :=
  match goal with
  | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: Some _ = Some _ |- _ ] => inv H; DestructCases
  | [H: None = Some _ |- _ ] => discriminate H
  | [H: @eq intsize _ _ |- _ ] => discriminate H || (clear H; DestructCases)
  | [ |- val_casted (Vint (if ?x then Int.zero else Int.one)) _ ] =>
       try (constructor; destruct x; reflexivity)
  | [ |- val_casted (Vint _) (Tint ?sz ?sg _) ] =>
       try (constructor; apply (cast_int_int_idem sz sg))
  | _ => idtac
  end.

Lemma cast_val_is_casted:
  forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> val_casted v' ty'.
Proof.
  unfold sem_cast; intros.
  destruct ty, ty'; simpl in H; DestructCases; constructor; auto.
Qed.

End VAL_CASTED.

(** As a consequence, casting twice is equivalent to casting once. *)

Lemma cast_val_casted:
  forall v ty m, val_casted v ty -> sem_cast v ty ty m = Some v.
Proof.
  intros. unfold sem_cast; inversion H; clear H; subst v ty; simpl.
- destruct Archi.ptr64; [ | destruct (intsize_eq sz I32)].
+ destruct sz; f_equal; f_equal; assumption.
+ subst sz; auto.
+ destruct sz; f_equal; f_equal; assumption.
- auto.
- auto.
- destruct Archi.ptr64; auto.
- auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite H0; auto.
- rewrite dec_eq_true; auto.
- rewrite dec_eq_true; auto.
- auto. 
Qed.

Lemma cast_idempotent:
  forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> sem_cast v' ty' ty' m = Some v'.
Proof.
  intros. apply cast_val_casted. eapply cast_val_is_casted; eauto.
Qed.

(** Moreover, casted values belong to the machine type corresponding to the
    C type. *)

Lemma val_casted_has_type:
  forall v ty, val_casted v ty -> ty <> Tvoid -> Val.has_type v (typ_of_type ty).
Proof.
  intros. inv H; simpl typ_of_type.
- exact I.
- exact I.
- exact I.
- exact I.
- apply Val.Vptr_has_type.
- red; unfold Tptr; rewrite H1; auto.
- red; unfold Tptr; rewrite H1; auto.
- red; unfold Tptr; rewrite H1; auto.
- red; unfold Tptr; rewrite H1; auto.
- apply Val.Vptr_has_type.
- apply Val.Vptr_has_type.
- congruence.
Qed.

(** Relation with the arithmetic conversions of ISO C99, section 6.3.1 *)

Module ArithConv.

(** This is the ISO C algebra of arithmetic types, without qualifiers.
    [S] stands for "signed" and [U] for "unsigned".  *)

Inductive int_type : Type :=
  | _Bool
  | Char | SChar | UChar
  | Short | UShort
  | Int | UInt
  | Long | ULong
  | Longlong | ULonglong.

Inductive arith_type : Type :=
  | I (it: int_type)
  | Float
  | Double
  | Longdouble.

Definition eq_int_type: forall (x y: int_type), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition is_unsigned (t: int_type) : bool :=
  match t with
  | _Bool => true
  | Char => false    (**r as in most of CompCert's target ABIs *)
  | SChar => false
  | UChar => true
  | Short => false
  | UShort => true
  | Int => false
  | UInt => true
  | Long => false
  | ULong => true
  | Longlong => false
  | ULonglong => true
  end.

Definition unsigned_type (t: int_type) : int_type :=
  match t with
  | Char => UChar
  | SChar => UChar
  | Short => UShort
  | Int => UInt
  | Long => ULong
  | Longlong => ULonglong
  | _ => t
  end.

Definition int_sizeof (t: int_type) : Z :=
  match t with
  | _Bool | Char | SChar | UChar => 1
  | Short | UShort => 2
  | Int | UInt | Long | ULong => 4
  | Longlong | ULonglong => 8
  end.

(** 6.3.1.1 para 1: integer conversion rank *)

Definition rank (t: int_type) : Z :=
  match t with
  | _Bool => 1
  | Char | SChar | UChar => 2
  | Short | UShort => 3
  | Int | UInt => 4
  | Long | ULong => 5
  | Longlong | ULonglong => 6
  end.

(** 6.3.1.1 para 2: integer promotions, a.k.a. usual unary conversions *)

Definition integer_promotion (t: int_type) : int_type :=
  if zlt (rank t) (rank Int) then Int else t.

(** 6.3.1.8: Usual arithmetic conversions, a.k.a. binary conversions.
  This function returns the type to which the two operands must be
  converted. *)

Definition usual_arithmetic_conversion (t1 t2: arith_type) : arith_type :=
  match t1, t2 with
  (* First, if the corresponding real type of either operand is long
     double, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is long double. *)
  | Longdouble, _ | _, Longdouble => Longdouble
  (* Otherwise, if the corresponding real type of either operand is
     double, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is double. *)
  | Double, _ | _, Double => Double
  (* Otherwise, if the corresponding real type of either operand is
     float, the other operand is converted, without change of type domain,
     to a type whose corresponding real type is float. *)
  | Float, _ | _, Float => Float
  (* Otherwise, the integer promotions are performed on both operands. *)
  | I i1, I i2 =>
    let j1 := integer_promotion i1 in
    let j2 := integer_promotion i2 in
    (* Then the following rules are applied to the promoted operands:
       If both operands have the same type, then no further conversion
       is needed. *)
    if eq_int_type j1 j2 then I j1 else
    match is_unsigned j1, is_unsigned j2 with
    (* Otherwise, if both operands have signed integer types or both
       have unsigned integer types, the operand with the type of lesser
       integer conversion rank is converted to the type of the operand with
       greater rank. *)
    | true, true | false, false =>
        if zlt (rank j1) (rank j2) then I j2 else I j1
    | true, false =>
    (* Otherwise, if the operand that has unsigned integer type has
       rank greater or equal to the rank of the type of the other operand,
       then the operand with signed integer type is converted to the type of
       the operand with unsigned integer type. *)
        if zle (rank j2) (rank j1) then I j1 else
    (* Otherwise, if the type of the operand with signed integer type
       can represent all of the values of the type of the operand with
       unsigned integer type, then the operand with unsigned integer type is
       converted to the type of the operand with signed integer type. *)
        if zlt (int_sizeof j1) (int_sizeof j2) then I j2 else
    (* Otherwise, both operands are converted to the unsigned integer type
       corresponding to the type of the operand with signed integer type. *)
        I (unsigned_type j2)
    | false, true =>
    (* Same logic as above, swapping the roles of j1 and j2 *)
        if zle (rank j1) (rank j2) then I j2 else
        if zlt (int_sizeof j2) (int_sizeof j1) then I j1 else
        I (unsigned_type j1)
    end
  end.

(** Mapping ISO arithmetic types to CompCert types *)

Definition proj_type (t: arith_type) : type :=
  match t with
  | I _Bool => Tint IBool Unsigned noattr
  | I Char => Tint I8 Unsigned noattr
  | I SChar => Tint I8 Signed noattr
  | I UChar => Tint I8 Unsigned noattr
  | I Short => Tint I16 Signed noattr
  | I UShort => Tint I16 Unsigned noattr
  | I Int => Tint I32 Signed noattr
  | I UInt => Tint I32 Unsigned noattr
  | I Long => Tint I32 Signed noattr
  | I ULong => Tint I32 Unsigned noattr
  | I Longlong => Tlong Signed noattr
  | I ULonglong => Tlong Unsigned noattr
  | Float => Tfloat F32 noattr
  | Double => Tfloat F64 noattr
  | Longdouble => Tfloat F64 noattr
  end.

(** Relation between [typeconv] and integer promotion. *)

Lemma typeconv_integer_promotion:
  forall i, typeconv (proj_type (I i)) = proj_type (I (integer_promotion i)).
Proof.
  destruct i; reflexivity.
Qed.

(** Relation between [classify_binarith] and arithmetic conversion. *)

Lemma classify_binarith_arithmetic_conversion:
  forall t1 t2,
  binarith_type (classify_binarith (proj_type t1) (proj_type t2)) =
  proj_type (usual_arithmetic_conversion t1 t2).
Proof.
  destruct t1; destruct t2; try reflexivity.
- destruct it; destruct it0; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
- destruct it; reflexivity.
Qed.

End ArithConv.
*)




