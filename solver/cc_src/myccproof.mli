(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is copied from Coq Verson 8.16.1                          *)

open Myccalgo
open Constr

type rule=
    Ax of constr
  | SymAx of constr
  | Refl of ATerm.t
  | Trans of proof*proof
  | Congr of proof*proof
  | Inject of proof*pconstructor*int*int
and proof =
    private {p_lhs:ATerm.t;p_rhs:ATerm.t;p_rule:rule}

(** Proof smart constructors *)

val prefl:ATerm.t -> proof

val pcongr: proof -> proof -> proof

val ptrans: proof -> proof -> proof

val psym: proof -> proof

val pax : (ATerm.t * ATerm.t) Myccalgo.Constrhash.t ->
           Myccalgo.Constrhash.key -> proof

val psymax :  (ATerm.t * ATerm.t) Myccalgo.Constrhash.t ->
           Myccalgo.Constrhash.key -> proof

val pinject :  proof -> pconstructor -> int -> int -> proof

(** Proof building functions *)

val equal_proof : Environ.env -> Evd.evar_map -> forest -> int -> int -> proof

val edge_proof : Environ.env -> Evd.evar_map -> forest -> (int*int)*equality -> proof

val path_proof : Environ.env -> Evd.evar_map -> forest -> int -> ((int*int)*equality) list -> proof

val congr_proof : Environ.env -> Evd.evar_map -> forest -> int -> int -> proof

val ind_proof : Environ.env -> Evd.evar_map -> forest -> int -> pa_constructor -> int -> pa_constructor -> proof

(** Main proof building function *)

val build_proof :
  Environ.env -> Evd.evar_map -> forest ->
  [ `Discr of int * pa_constructor * int * pa_constructor
  | `Prove of int * int ] -> proof

