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

    module Unsafe : sig
      val kind : t -> Environ.env -> Evd.evar_map -> valexpr

      val make : valexpr -> Environ.env -> Evd.evar_map -> t

      val check : t -> valexpr Proofview.tactic

      val liftn : int -> int -> t -> t

      val substnl : EConstr.Vars.substl -> int -> t -> t

      val closenl : ident list -> int -> t -> t Proofview.tactic

      val closednl : int -> t -> bool Proofview.tactic

      val noccur_between :
        int -> int -> t -> bool Proofview.tactic

      val case :
        inductive -> valexpr Proofview.tactic

      type case = Constr.case_info

      module Case : sig
        val equal : case -> case -> bool
        val inductive : case -> inductive
      end
    end

    module Cast : sig
      type t = cast

      val default : valexpr
      val vm : valexpr
      val native : valexpr

      val equal : t -> t -> bool
    end

    val in_context :
      variable ->
      t ->
      (unit -> unit Proofview.tactic) ->
      t Proofview.tactic

    module Pretype : sig
      type expected_type = Pretyping.typing_constraint

      module Flags : sig
        type t = Pretyping.inference_flags

        val constr_flags : t

        val set_use_coercion : bool -> t -> t
        val set_use_typeclasses : bool -> t -> t
        val set_allow_evars : bool -> t -> t
        val set_nf_evars : bool -> t -> t
      end

      val expected_istype : expected_type

      val expected_oftype :
        constr -> expected_type

      val expected_without_type_constraint :
        expected_type

      val pretype :
        Flags.t ->
        expected_type ->
        preterm ->
        constr Proofview.tactic
    end

    val has_evar : t -> bool Proofview.tactic
  end

  module Constructor : sig
    type t = constructor

    val equal : t -> t -> bool

    val inductive : t -> inductive
    val index : t -> int
    val print : t -> message
  end

  module Control : sig
    val throw : exn -> 'a Proofview.tactic

    val zero : exn -> 'a Proofview.tactic

    val plus :
      (unit -> 'a Proofview.tactic) ->
      (exn -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val once :
      (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val case :
      (unit -> 'a Proofview.tactic) ->
      ('a * (exn -> 'a Proofview.tactic), exn) result Proofview.tactic

    val numgoals : unit -> int Proofview.tactic

    val dispatch :
      (unit -> unit Proofview.tactic) list ->
      unit Proofview.tactic

    val extend :
      (unit -> unit Proofview.tactic) list ->
      (unit -> unit Proofview.tactic) ->
      (unit -> unit Proofview.tactic) list ->
      unit Proofview.tactic

    val enter :
      (unit -> 'a Proofview.tactic) -> unit Proofview.tactic

    val focus :
      int ->
      int ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val shelve : unit -> unit Proofview.tactic
    val shelve_unifiable : unit -> unit Proofview.tactic

    val unshelve :
      (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val new_goal : Proofview_monad.goal -> unit Proofview.tactic
    val cycle : int -> unit Proofview.tactic
    val reorder_goals : Int.t list -> unit Proofview.tactic
    val goal : unit -> constr Proofview.tactic
    val hyp : variable -> constr Proofview.tactic

    val hyp_value :
      variable -> constr option Proofview.tactic

    val hyps : unit -> valexpr Proofview.tactic

    val refine :
      (unit -> constr Proofview.tactic) ->
      unit Proofview.tactic

    val solve_constraints : unit -> unit Proofview.tactic

    val with_holes :
      (unit -> 'a Proofview.tactic) ->
      ('a -> 'b Proofview.tactic) ->
      'b Proofview.tactic

    val progress :
      (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val abstract :
      ident option ->
      (unit -> unit Proofview.tactic) ->
      unit Proofview.tactic

    val time :
      string option ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val timeout :
      int -> (unit -> 'a Proofview.tactic) -> 'a Proofview.tactic

    val timeoutf :
      float ->
      (unit -> 'a Proofview.tactic) ->
      'a Proofview.tactic

    val check_interrupt : unit -> unit Proofview.tactic
    val clear_err_info : err -> err
    val current_exninfo : unit -> exninfo Proofview.tactic
    val print_err : err -> message

    val throw_bt : exn -> exninfo -> 'b Proofview.tactic

    val zero_bt : exn -> exninfo -> 'a Proofview.tactic

    val plus_bt :
      (unit -> 'a Proofview.tactic) ->
      (exn -> exninfo -> 'a Proofview.tactic) ->
      'a Proofview.tactic
  end

  module Env : sig
    val get : ident list -> GlobRef.t option
    val expand : ident list -> GlobRef.t list

    val path : GlobRef.t -> ident list Proofview.tactic

    val instantiate : GlobRef.t -> constr Proofview.tactic
  end

  module Evar : sig
    type t = evar

    val equal : t -> t -> bool
  end

  module Float : sig
    type t = float

    val equal : t -> t -> bool
  end

  module Fresh : sig
    module Free : sig
      type t = Nameops.Fresh.t

      val empty : t
      val add : ident -> t -> t

      val union : t -> t -> t

      val of_ids : ident list -> t
      val of_constr : constr -> t Proofview.tactic
    end

    val next : Free.t -> ident -> ident * Free.t
    val fresh : Free.t -> ident -> ident
  end

  module Ident : sig
    type t = ident

    val equal : ident -> ident -> bool
    val to_string : ident -> string
    val of_string : string -> ident option
  end

  module Ind : sig
    type t = inductive
    type data = inductive * Declarations.mutual_inductive_body

    val equal : t -> t -> bool

    val data : t -> data Proofview.tactic

    val repr : data -> t
    val index : t -> int
    val nblocks : data -> int

    val nconstructors : data -> int

    val get_block : data -> int -> data Proofview.tactic

    val get_constructor : data -> int -> constructor Proofview.tactic

    val nparams : data -> int
    val nparams_uniform : data -> int

    val get_projections : data -> projection array option

    val constructor_nargs : data -> int array
    val constructor_ndecls : data -> int array

    val print : t -> message
  end

  module Int : sig
    type t = int

    val equal : 'a -> 'a -> bool
    val compare : int -> int -> int
    val add : int -> int -> int
    val sub : int -> int -> int
    val mul : int -> int -> int
    val div : int -> int -> int Proofview.tactic
    val ( mod ) : int -> int -> int Proofview.tactic
    val neg : int -> int
    val abs : int -> int
    val ( asr ) : int -> int -> int
    val ( lsl ) : int -> int -> int
    val ( lsr ) : int -> int -> int
    val ( land ) : int -> int -> int
    val ( lor ) : int -> int -> int
    val ( lxor ) : int -> int -> int
    val lnot : int -> int
  end

  module Message : sig
    val print : message -> unit
    val empty : message
    val of_string : string -> message
    val to_string : message -> string
    val of_int : int -> message
    val of_ident : ident -> message
    val of_constr : constr -> message Proofview.tactic
    val of_lconstr : constr -> message Proofview.tactic

    val of_preterm : preterm -> message Proofview.tactic
    val of_lpreterm : preterm -> message Proofview.tactic

    val of_exn : valexpr -> Environ.env -> Evd.evar_map -> message
    val of_exninfo : exninfo -> message

    val concat : message -> message -> message
    val force_new_line : message
    val break : int -> int -> message
    val space : message
    val hbox : message -> message
    val vbox : int -> message -> message
    val hvbox : int -> message -> message
    val hovbox : int -> message -> message

  end
end
