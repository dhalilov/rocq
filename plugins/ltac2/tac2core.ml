(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Tac2val
open Tac2ffi
open Tac2expr
open Tac2externals
open Proofview.Notations

let ltac2_plugin = "rocq-runtime.plugins.ltac2"
let define ?(plugin = ltac2_plugin) s = define { mltac_plugin = plugin; mltac_tactic = s }

let constr_flags =
  let open Pretyping in
  {
    use_coercions = true;
    use_typeclasses = Pretyping.UseTC;
    solve_unification_constraints = true;
    fail_evar = true;
    expand_evars = true;
    program_mode = false;
    poly = PolyFlags.default;
    undeclared_evars_rr = false;
    unconstrained_sorts = false;
  }

let open_constr_no_classes_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = false;
  program_mode = false;
  poly = PolyFlags.default;
  undeclared_evars_rr = false;
  unconstrained_sorts = false;
  }

let preterm_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = false;
  program_mode = false;
  poly = PolyFlags.default;
  undeclared_evars_rr = false;
  unconstrained_sorts = false;
  }

(** Standard values *)

(** Helper functions *)

let fatal_flag : unit Exninfo.t = Exninfo.make "fatal_flag"

let has_fatal_flag info = match Exninfo.get info fatal_flag with
  | None -> false
  | Some () -> true

let set_bt info =
  if !Tac2bt.print_ltac2_backtrace then
    Tac2bt.get_backtrace >>= fun bt ->
    Proofview.tclUNIT (Exninfo.add info Tac2bt.backtrace bt)
  else Proofview.tclUNIT info

let throw ?(info = Exninfo.null) e =
  set_bt info >>= fun info ->
  let info = Exninfo.add info fatal_flag () in
  Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))

let catchable_exception = function
  | Logic_monad.Exception _ -> false
  | e -> CErrors.noncritical e

(* Adds ltac2 backtrace
   With [passthrough:false], acts like [Proofview.wrap_exceptions] + Ltac2 backtrace handling
*)
let wrap_exceptions ?(passthrough=false) f =
  try f ()
  with e ->
    let e, info = Exninfo.capture e in
    set_bt info >>= fun info ->
    if not passthrough && catchable_exception e
    then begin if has_fatal_flag info
      then Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))
      else Proofview.tclZERO ~info e
    end
    else Exninfo.iraise (e, info)

let pf_apply ?(catch_exceptions=false) f =
  let f env sigma = wrap_exceptions ~passthrough:(not catch_exceptions) (fun () -> f env sigma) in
  Proofview.Goal.goals >>= function
  | [] ->
    Proofview.tclENV >>= fun env ->
    Proofview.tclEVARMAP >>= fun sigma ->
    f env sigma
  | [gl] ->
    gl >>= fun gl ->
    f (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)
  | _ :: _ :: _ ->
    throw Tac2ffi.err_notfocussed


(** Error *)

let () = define "message_of_exninfo" (exninfo @-> ret pp) CErrors.print_extra

module MapTagDyn = Dyn.Make()

type ('a,'set,'map) map_tag = ('a * 'set * 'map) MapTagDyn.tag

type any_map_tag = Any : _ map_tag -> any_map_tag
type tagged_set = TaggedSet : (_,'set,_) map_tag * 'set -> tagged_set
type tagged_map = TaggedMap : (_,_,'map) map_tag * 'map -> tagged_map

let map_tag_ext : any_map_tag Tac2dyn.Val.tag = Tac2dyn.Val.create "fmap_tag"
let map_tag_repr = Tac2ffi.repr_ext map_tag_ext

let set_ext : tagged_set Tac2dyn.Val.tag = Tac2dyn.Val.create "fset"
let set_repr = Tac2ffi.repr_ext set_ext
let tag_set tag s = Tac2ffi.repr_of set_repr (TaggedSet (tag,s))

let map_ext : tagged_map Tac2dyn.Val.tag = Tac2dyn.Val.create "fmap"
let map_repr = Tac2ffi.repr_ext map_ext
let tag_map tag m = Tac2ffi.repr_of map_repr (TaggedMap (tag,m))

module type MapType = sig
  (* to have less boilerplate we use S.elt rather than declaring a toplevel type t *)
  module S : CSig.USetS
  module M : CMap.UExtS with type key = S.elt and module Set := S
  type valmap
  val valmap_eq : (valmap, valexpr M.t) Util.eq
  val repr : S.elt Tac2ffi.repr
end

module MapTypeV = struct
  type _ t = Map : (module MapType with type S.elt = 't and type S.t = 'set and type valmap = 'map)
    -> ('t * 'set * 'map) t
end

module MapMap = MapTagDyn.Map(MapTypeV)

let maps = ref MapMap.empty

let register_map ?(plugin=ltac2_plugin) ~tag_name x =
  let tag = MapTagDyn.create (plugin^":"^tag_name) in
  let () = maps := MapMap.add tag (Map x) !maps in
  let () = define ~plugin tag_name (ret map_tag_repr) (Any tag) in
  tag

let get_map (type t s m) (tag:(t,s,m) map_tag)
  : (module MapType with type S.elt = t and type S.t = s and type valmap = m) =
  let Map v = MapMap.find tag !maps in
  v

let map_tag_eq (type a b c a' b' c') (t1:(a,b,c) map_tag) (t2:(a',b',c') map_tag)
  : (a*b*c,a'*b'*c') Util.eq option
  = MapTagDyn.eq t1 t2

let ident_map_tag : _ map_tag = register_map ~tag_name:"fmap_ident_tag" (module struct
    module S = Id.Set
    module M = Id.Map
    let repr = Tac2ffi.ident
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let int_map_tag : _ map_tag = register_map ~tag_name:"fmap_int_tag" (module struct
    module S = Int.Set
    module M = Int.Map
    let repr = Tac2ffi.int
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let string_map_tag : _ map_tag = register_map ~tag_name:"fmap_string_tag" (module struct
    module S = String.Set
    module M = String.Map
    let repr = Tac2ffi.string
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let inductive_map_tag : _ map_tag = register_map ~tag_name:"fmap_inductive_tag" (module struct
    module S = Indset_env
    module M = Indmap_env
    let repr = inductive
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let constructor_map_tag : _ map_tag = register_map ~tag_name:"fmap_constructor_tag" (module struct
    module S = Constrset_env
    module M = Constrmap_env
    let repr = Tac2ffi.constructor
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let constant_map_tag : _ map_tag = register_map ~tag_name:"fmap_constant_tag" (module struct
    module S = Cset_env
    module M = Cmap_env
    let repr = Tac2ffi.constant
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)
