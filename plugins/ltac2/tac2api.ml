(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Tac2externals
open Tac2ffi
open Tac2val
open Tac2core
open Proofview.Notations

(** Helper methods *)
let v_blk = Valexpr.make_block

let of_relevance = function
  | Sorts.Relevant -> ValInt 0
  | Sorts.Irrelevant -> ValInt 1
  | Sorts.RelevanceVar q -> ValBlk (0, [|of_qvar q|])

let to_relevance = function
  | ValInt 0 -> Sorts.Relevant
  | ValInt 1 -> Sorts.Irrelevant
  | ValBlk (0, [|qvar|]) ->
    let qvar = to_qvar qvar in
    Sorts.RelevanceVar qvar
  | _ -> assert false

(* XXX ltac2 exposes relevance internals so breaks ERelevance abstraction
   ltac2 Constr.Binder.relevance probably needs to be made an abstract type *)
let relevance = make_repr of_relevance to_relevance

let return = Proofview.tclUNIT

let thaw f : _ Proofview.tactic = f ()

let set_bt info =
  if !Tac2bt.print_ltac2_backtrace then
    Tac2bt.get_backtrace >>= fun bt ->
    Proofview.tclUNIT (Exninfo.add info Tac2bt.backtrace bt)
  else Proofview.tclUNIT info

let fail ?(info = Exninfo.null) e =
  set_bt info >>= fun info ->
  Proofview.tclZERO ~info e

(** Array *)

module Ltac2Array = struct
  let empty = v_blk 0 [||]

  let make n x =
    try return (v_blk 0 (Array.make n x))
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let length (_, v) = Array.length v

  let set (_, v) n x =
    try Array.set v n x; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let get (_, v) n =
    try return (Array.get v n)
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let lowlevel_blit (_, v0) s0 (_, v1) s1 l =
    try Array.blit v0 s0 v1 s1 l; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let lowlevel_fill (_, d) s l v =
    try Array.fill d s l v; return ()
    with Invalid_argument _ -> throw Tac2ffi.err_outofbounds

  let concat l = v_blk 0 (Array.concat (List.map snd l))
end

let () = define "array_empty" (ret valexpr) Ltac2Array.empty
let () = define "array_make" (int @-> valexpr @-> tac valexpr) Ltac2Array.make
let () = define "array_length" (block @-> ret int) Ltac2Array.length
let () = define "array_set" (block @-> int @-> valexpr @-> tac unit) Ltac2Array.set
let () = define "array_get" (block @-> int @-> tac valexpr) Ltac2Array.get
let () = define "array_blit" (block @-> int @-> block @-> int @-> int @-> tac unit) Ltac2Array.lowlevel_blit
let () = define "array_fill" (block @-> int @-> int @-> valexpr @-> tac unit) Ltac2Array.lowlevel_fill
let () = define "array_concat" (list block @-> ret valexpr) Ltac2Array.concat

(** Char *)

module Ltac2Char = struct
  type t = char

  let of_int i =
    try return (Char.chr i)
    with Invalid_argument _ as e ->
      let e, info = Exninfo.capture e in
      throw ~info e

  let to_int = Char.code
end

let () = define "char_of_int" (int @-> tac char) Ltac2Char.of_int
let () = define "char_to_int" (char @-> ret int) Ltac2Char.to_int

(** Constant *)

module Ltac2Constant = struct
  type t = Constant.t
  let equal = Constant.UserOrd.equal
  let print c = Nametab.pr_global_env Id.Set.empty (ConstRef c)
end

let () = define "constant_equal" (constant @-> constant @-> ret bool) Ltac2Constant.equal
let () = define "constant_print" (constant @-> ret pp) Ltac2Constant.print

(** Constr *)

module Ltac2Constr = struct
  type t = EConstr.t

  let type_ c =
    let get_type env sigma =
      let (sigma, t) = Typing.type_of env sigma c in
      let t = Tac2ffi.of_constr t in
      Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
    in
    pf_apply ~catch_exceptions:true get_type

  let equal c1 c2 =
    Proofview.tclEVARMAP >>= fun sigma -> return (EConstr.eq_constr sigma c1 c2)

  module Binder = struct
    type t = binder
    type relevance = Sorts.relevance

    let make na ty =
      pf_apply @@ fun env sigma ->
      match Retyping.relevance_of_type env sigma ty with
      | rel ->
         let na = match na with None -> Anonymous | Some id -> Name id in
        return (Context.make_annot na rel, ty)
      | exception (Retyping.RetypeError _ as e) ->
        let e, info = Exninfo.capture e in
        fail ~info (CErrors.UserError Pp.(str "Not a type."))

    let unsafe_make na rel ty =
      let na =
        match na with
        | None -> Anonymous
        | Some id -> Name id
      in Context.make_annot na (EConstr.ERelevance.make rel), ty

    let name (bnd, _) =
      match bnd.Context.binder_name with
      | Anonymous -> None
      | Name id -> Some id

    (* type is a reserved keyword *)
    let type_ (_, ty) = ty

    let relevance (na, _) = EConstr.Unsafe.to_relevance na.Context.binder_relevance
  end


  let in_context id t c =
    Proofview.Goal.goals >>= function
    | [gl] ->
       gl >>= fun gl ->
       let env = Proofview.Goal.env gl in
       let sigma = Proofview.Goal.sigma gl in
       let has_var =
         try
           let _ = Environ.lookup_named id env in
           true
         with Not_found -> false
       in
       if has_var then
         Tacticals.tclZEROMSG (str "Variable already exists")
       else
         let open Context.Named.Declaration in
         let sigma, t_rel =
           let t_ty = Retyping.get_type_of env sigma t in
           (* If the user passed eg ['_] for the type we force it to indeed be a type *)
           let sigma, j = Typing.type_judgment env sigma {uj_val=t; uj_type=t_ty} in
           sigma, EConstr.ESorts.relevance_of_sort j.utj_type
         in
         let nenv = EConstr.push_named (LocalAssum (Context.make_annot id t_rel, t)) env in
         let (sigma, (evt, s)) = Evarutil.new_type_evar nenv sigma Evd.univ_flexible in
         let relevance = EConstr.ESorts.relevance_of_sort s in
         let (sigma, evk) = Evarutil.new_pure_evar (Environ.named_context_val nenv) sigma ~relevance evt in
         Proofview.Unsafe.tclEVARS sigma >>= fun () ->
         Proofview.Unsafe.tclSETGOALS [Proofview.with_empty_state evk] >>= fun () ->
         thaw c >>= fun _ ->
         Proofview.Unsafe.tclSETGOALS [Proofview.goal_with_state (Proofview.Goal.goal gl) (Proofview.Goal.state gl)] >>= fun () ->
         let args = EConstr.identity_subst_val (Environ.named_context_val env) in
         let args = SList.cons (EConstr.mkRel 1) args in
         let ans = EConstr.mkEvar (evk, args) in
         return (EConstr.mkLambda (Context.make_annot (Name id) t_rel, t, ans))
    | _ ->
       throw Tac2ffi.err_notfocussed


  let has_evar c =
    Proofview.tclEVARMAP >>= fun sigma ->
    return (Evarutil.has_undefined_evars sigma c)
end

let () = define "constr_type" (constr @-> tac valexpr) Ltac2Constr.type_
let () = define "constr_equal" (constr @-> constr @-> tac bool) Ltac2Constr.equal

let () = define "constr_binder_make" (option ident @-> constr @-> tac binder) Ltac2Constr.Binder.make
let () = define "constr_binder_unsafe_make" (option ident @-> relevance @-> constr @-> ret binder) Ltac2Constr.Binder.unsafe_make
let () = define "constr_binder_name" (binder @-> ret (option ident)) Ltac2Constr.Binder.name
let () = define "constr_binder_type" (binder @-> ret constr) Ltac2Constr.Binder.type_
let () =
  define "constr_binder_relevance" (binder @-> ret relevance) Ltac2Constr.Binder.relevance
let () = define "constr_in_context" (ident @-> constr @-> thunk unit @-> tac constr) Ltac2Constr.in_context

let () = define "constr_has_evar" (constr @-> tac bool) Ltac2Constr.has_evar
(** Ltac2 API *)

module Ltac2 = struct
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
  type ('a, 'b, 'c, 'd) format = Tac2types.format list
  type nonrec 'a array = 'a array
  type err = Exninfo.iexn
  type exn = Exninfo.iexn
  type exninfo = Exninfo.info

  module Array            = Ltac2Array
  module Char             = Ltac2Char
  module Constant         = Ltac2Constant
  module Constr           = Ltac2Constr
end
