(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2val
open Names


(** Top-level module for Ltac2 OCaml APIs.

    Note: avoid [open Ltac2], as built-in Ltac2 types will shadow built-in OCaml types. *)
module Ltac2 : sig
  (** Built-in types *)
  type int = Int.t
  type string = String.t
  type char = Char.t
  type ident = Id.t
  type uint63 = Uint63.t
  type float = Float64.t
  type pstring = Pstring.t
  type meta = Constr.metavariable
  type evar = Evar.t
  type sort = Sorts.t
  type cast = Constr.cast_kind
  type instance = EConstr.EInstance.t
  type constant = Constant.t
  type inductive = Ind.t
  type constructor = Construct.t
  type projection = Projection.t
  type pattern = Pattern.constr_pattern
  type constr = EConstr.t
  type preterm = Ltac_pretype.closed_glob_constr
  type binder = Name.t EConstr.binder_annot * EConstr.types
  type message = Pp.t
  type ('a, 'b, 'c, 'd) format
  type nonrec 'a array = 'a array
  type err = Exninfo.iexn
  type exn = Exninfo.iexn
  type exninfo = Exninfo.info

  module Array : sig
    val empty : valexpr

    val make : int -> valexpr -> valexpr Proofview.tactic

    val length : int * valexpr array -> int
    val get : int * valexpr array -> int -> valexpr Proofview.tactic
    val set : int * valexpr array -> int -> valexpr -> unit Proofview.tactic

    val lowlevel_blit :
      int * valexpr array ->
      int ->
      int * valexpr array ->
      int ->
      int ->
      unit Proofview.tactic

    val lowlevel_fill :
      int * valexpr array -> int -> int -> valexpr -> unit Proofview.tactic

    val concat :
      (int * valexpr array) list -> valexpr
  end

  module Char : sig
    type t = char

    val of_int : int -> t Proofview.tactic
    val to_int : t -> int
  end

  module Constant : sig
    type t = constant

    val equal : t -> t -> bool
    val print : t -> message
  end

  module Constr : sig
    type t = constr

    val type_ : t -> valexpr Proofview.tactic
    val equal : t -> t -> bool Proofview.tactic

    module Binder : sig
      type t = binder
      type relevance = Sorts.relevance

      val make :
        ident option ->
        constr ->
        t Proofview.tactic

      val unsafe_make :
        ident option ->
        relevance ->
        constr ->
        t

      val name : t -> ident option
      val type_ : t -> constr
      val relevance : t -> relevance
    end

    module Relevance : sig
      type t = Binder.relevance

      val equal : t -> t -> Environ.env -> Evd.evar_map -> bool

      val relevant : t
      val irrelevant : t
    end


    val in_context :
      variable ->
      t ->
      (unit -> unit Proofview.tactic) ->
      t Proofview.tactic

    val has_evar : t -> bool Proofview.tactic
  end
end
