(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Standard tactics sharing their implementation with Ltac1 *)

module Ltac2Std : sig
  type hypothesis = Tac2types.quantified_hypothesis
  type bindings = Tac2types.bindings
  type constr_with_bindings = Tac2types.constr_with_bindings
  type occurrences = Tac2types.occurrences
  type hyp_location_flag = Tac2types.hyp_location_flag
  type clause = Tac2types.clause
  type reference = GlobRef.t
  type strength = Genredexpr.strength
  type red_flags = Tac2types.red_flag
  type intro_pattern = Tac2types.intro_pattern
  and intro_pattern_naming = Tac2types.intro_pattern_naming
  and intro_pattern_action = Tac2types.intro_pattern_action
  and or_and_intro_pattern = Tac2types.or_and_intro_pattern
  type destruction_arg = Tac2types.destruction_arg
  type induction_clause = Tac2types.induction_clause
  type assertion = Tac2types.assertion
  type repeat = Equality.multi
  type orientation = Tac2types.orientation
  type rewriting = Tac2types.rewriting
  type evar_flag = Tac2types.evars_flag
  type advanced_flag = Tac2types.advanced_flag
  type move_location = Id.t Logic.move_location
  type inversion_kind = Inv.inversion_kind
end

val intro_pattern : Tac2types.intro_pattern Tac2ffi.repr
