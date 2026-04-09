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

let return x = Proofview.tclUNIT x
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

(** String *)

let () =
  define "string_make" (int @-> char @-> tac bytes) @@ fun n c ->
  try return (Bytes.make n c) with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

let () = define "string_length" (bytes @-> ret int) Bytes.length

let () =
  define "string_set" (bytes @-> int @-> char @-> tac unit) @@ fun s n c ->
  try Bytes.set s n c; return () with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

let () =
  define "string_get" (bytes @-> int @-> tac char) @@ fun s n ->
  try return (Bytes.get s n) with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

let () = define "string_concat" (bytes @-> list bytes @-> ret bytes) Bytes.concat

let () =
  define "string_app" (bytes @-> bytes @-> ret bytes) @@ fun a b ->
  Bytes.concat Bytes.empty [a; b]

let () =
  define "string_sub" (bytes @-> int @-> int @-> tac bytes) @@ fun s off len ->
  try return (Bytes.sub s off len) with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

let () = define "string_equal" (bytes @-> bytes @-> ret bool) Bytes.equal

let () = define "string_compare" (bytes @-> bytes @-> ret int) Bytes.compare

(** Pstring *)

let () =
  define "pstring_max_length" (ret uint63) Pstring.max_length;
  define "pstring_to_string" (pstring @-> ret string) Pstring.to_string;
  define "pstring_of_string" (string @-> ret (option pstring)) Pstring.of_string;
  define "pstring_make" (uint63 @-> uint63 @-> ret pstring) Pstring.make;
  define "pstring_length" (pstring @-> ret uint63) Pstring.length;
  define "pstring_get" (pstring @-> uint63 @-> ret uint63) Pstring.get;
  define "pstring_sub" (pstring @-> uint63 @-> uint63 @-> ret pstring) Pstring.sub;
  define "pstring_cat" (pstring @-> pstring @-> ret pstring) Pstring.cat;
  define "pstring_equal" (pstring @-> pstring @-> ret bool) Pstring.equal;
  define "pstring_compare" (pstring @-> pstring @-> ret int) Pstring.compare

(** Uint63 *)

let () = define "uint63_compare" (uint63 @-> uint63 @-> ret int) Uint63.compare

let () = define "uint63_of_int" (int @-> ret uint63) Uint63.of_int

let () = define "uint63_print" (uint63 @-> ret pp) @@ fun i ->
  Pp.str (Uint63.to_string i)

(** Extra equalities *)

let () = define "uint63_equal" (uint63 @-> uint63 @-> ret bool) Uint63.equal

(** Error *)

let () = define "message_of_exninfo" (exninfo @-> ret pp) CErrors.print_extra



(** Schemes *)

let () =
  define "scheme_lookup" (scheme_kind @-> reference @-> ret (option reference))
  @@ DeclareScheme.lookup_scheme_opt

let define_scheme_kind name =
  define ("scheme_kind_" ^ name) (ret scheme_kind) name

let () = define_scheme_kind "rect_dep"
let () = define_scheme_kind "rec_dep"
let () = define_scheme_kind "ind_dep"
let () = define_scheme_kind "sind_dep"
let () = define_scheme_kind "rect_nodep"
let () = define_scheme_kind "rec_nodep"
let () = define_scheme_kind "ind_nodep"
let () = define_scheme_kind "sind_nodep"
let () = define_scheme_kind "case_dep"
let () = define_scheme_kind "case_nodep"
let () = define_scheme_kind "casep_dep"
let () = define_scheme_kind "casep_nodep"
let () = define_scheme_kind "scase_dep"
let () = define_scheme_kind "scase_nodep"
let () = define_scheme_kind "sym"
let () = define_scheme_kind "sym_involutive"
let () = define_scheme_kind "rew"
let () = define_scheme_kind "rew_dep"
let () = define_scheme_kind "rew_fwd_dep"
let () = define_scheme_kind "rew_r"
let () = define_scheme_kind "rew_r_dep"
let () = define_scheme_kind "rew_fwd_r_dep"
let () = define_scheme_kind "congr"
let () = define_scheme_kind "beq"
let () = define_scheme_kind "dec_bl"
let () = define_scheme_kind "dec_lb"
let () = define_scheme_kind "eq_dec"

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

let assert_map_tag_eq t1 t2 = match map_tag_eq t1 t2 with
  | Some v -> v
  | None -> assert false

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

let () =
  define "fset_empty" (map_tag_repr @-> ret valexpr) @@ fun (Any tag) ->
  let (module V) = get_map tag in
  tag_set tag V.S.empty

let () =
  define "fset_is_empty" (set_repr @-> ret bool) @@ fun (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  V.S.is_empty s

let () =
  define "fset_mem" (valexpr @-> set_repr @-> ret bool) @@ fun x (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  V.S.mem (repr_to V.repr x) s

let () =
  define "fset_add" (valexpr @-> set_repr @-> ret valexpr) @@ fun x (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  tag_set tag (V.S.add (repr_to V.repr x) s)

let () =
  define "fset_remove" (valexpr @-> set_repr @-> ret valexpr) @@ fun x (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  tag_set tag (V.S.remove (repr_to V.repr x) s)

let () =
  define "fset_union" (set_repr @-> set_repr @-> ret valexpr)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  tag_set tag (V.S.union s1 s2)

let () =
  define "fset_inter" (set_repr @-> set_repr @-> ret valexpr)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  tag_set tag (V.S.inter s1 s2)

let () =
  define "fset_diff" (set_repr @-> set_repr @-> ret valexpr)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  tag_set tag (V.S.diff s1 s2)

let () =
  define "fset_equal" (set_repr @-> set_repr @-> ret bool)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  V.S.equal s1 s2

let () =
  define "fset_subset" (set_repr @-> set_repr @-> ret bool)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  V.S.subset s1 s2

let () =
  define "fset_cardinal" (set_repr @-> ret int) @@ fun (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  V.S.cardinal s

let () =
  define "fset_elements" (set_repr @-> ret valexpr) @@ fun (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  Tac2ffi.of_list (repr_of V.repr) (V.S.elements s)

let () =
  define "fmap_empty" (map_tag_repr @-> ret valexpr) @@ fun (Any (tag)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_map tag V.M.empty

let () =
  define "fmap_is_empty" (map_repr @-> ret bool) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.is_empty m

let () =
  define "fmap_mem" (valexpr @-> map_repr @-> ret bool) @@ fun x (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.mem (repr_to V.repr x) m

let () =
  define "fmap_add" (valexpr @-> valexpr @-> map_repr @-> ret valexpr)
    @@ fun x v (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_map tag (V.M.add (repr_to V.repr x) v m)

let () =
  define "fmap_remove" (valexpr @-> map_repr @-> ret valexpr)
    @@ fun x (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_map tag (V.M.remove (repr_to V.repr x) m)

let () =
  define "fmap_find_opt" (valexpr @-> map_repr @-> ret (option valexpr))
    @@ fun x (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.find_opt (repr_to V.repr x) m

let () =
  define "fmap_mapi" (closure @-> map_repr @-> tac valexpr)
    @@ fun f (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  let module Monadic = V.M.Monad(Proofview.Monad) in
  Monadic.mapi (fun k v -> apply f [repr_of V.repr k;v]) m >>= fun m ->
  return (tag_map tag m)

let () =
  define "fmap_fold" (closure @-> map_repr @-> valexpr @-> tac valexpr)
    @@ fun f (TaggedMap (tag,m)) acc ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  let module Monadic = V.M.Monad(Proofview.Monad) in
  Monadic.fold (fun k v acc -> apply f [repr_of V.repr k;v;acc]) m acc

let () =
  define "fmap_cardinal" (map_repr @-> ret int) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.cardinal m

let () =
  define "fmap_bindings" (map_repr @-> ret valexpr) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  Tac2ffi.(of_list (of_pair (repr_of V.repr) identity) (V.M.bindings m))

let () =
  define "fmap_domain" (map_repr @-> ret valexpr) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_set tag (V.M.domain m)
