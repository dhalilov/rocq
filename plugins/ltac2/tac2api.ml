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
open Util
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

let of_rec_declaration (nas, ts, cs) =
  let binders = Array.map2 (fun na t -> (na, t)) nas ts in
  (Tac2ffi.of_array of_binder binders,
  Tac2ffi.of_array Tac2ffi.of_constr cs)

let to_rec_declaration (nas, cs) =
  let nas = Tac2ffi.to_array to_binder nas in
  (Array.map fst nas,
  Array.map snd nas,
  Tac2ffi.to_array Tac2ffi.to_constr cs)

let of_case_invert = let open Constr in function
  | NoInvert -> ValInt 0
  | CaseInvert {indices} ->
    v_blk 0 [|of_array of_constr indices|]

let to_case_invert = let open Constr in function
  | ValInt 0 -> NoInvert
  | ValBlk (0, [|indices|]) ->
    let indices = to_array to_constr indices in
    CaseInvert {indices}
  | _ -> CErrors.anomaly Pp.(str "unexpected value shape")

let of_result f = function
| Inl c -> v_blk 0 [|f c|]
| Inr e -> v_blk 1 [|Tac2ffi.of_exn e|]

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

  module Relevance = struct
    type t = Binder.relevance
    let equal r1 r2 _env sigma =
      EConstr.ERelevance.(equal sigma (make r1) (make r2))

    let relevant = Sorts.Relevant
    let irrelevant = Sorts.Irrelevant
  end

  module Unsafe = struct
    let kind c env sigma =
      let open Constr in
      match EConstr.kind sigma c with
      | Rel n ->
         v_blk 0 [|Tac2ffi.of_int n|]
      | Var id ->
         v_blk 1 [|Tac2ffi.of_ident id|]
      | Meta n ->
         v_blk 2 [|Tac2ffi.of_int n|]
      | Evar (evk, args) ->
         let args = Evd.expand_existential sigma (evk, args) in
         v_blk 3 [|
             Tac2ffi.of_evar evk;
             Tac2ffi.of_array Tac2ffi.of_constr (Array.of_list args);
           |]
      | Sort s ->
         v_blk 4 [|Tac2ffi.of_sort s|]
      | Cast (c, k, t) ->
         v_blk 5 [|
             Tac2ffi.of_constr c;
             Tac2ffi.of_cast k;
             Tac2ffi.of_constr t;
           |]
      | Prod (na, t, u) ->
         v_blk 6 [|
             of_binder (na, t);
             Tac2ffi.of_constr u;
           |]
      | Lambda (na, t, c) ->
         v_blk 7 [|
             of_binder (na, t);
             Tac2ffi.of_constr c;
           |]
      | LetIn (na, b, t, c) ->
         v_blk 8 [|
             of_binder (na, t);
             Tac2ffi.of_constr b;
             Tac2ffi.of_constr c;
           |]
      | App (c, cl) ->
         v_blk 9 [|
             Tac2ffi.of_constr c;
             Tac2ffi.of_array Tac2ffi.of_constr cl;
           |]
      | Const (cst, u) ->
         v_blk 10 [|
             Tac2ffi.of_constant cst;
             Tac2ffi.of_instance u;
           |]
      | Ind (ind, u) ->
         v_blk 11 [|
             Tac2ffi.of_inductive ind;
             Tac2ffi.of_instance u;
           |]
      | Construct (cstr, u) ->
         v_blk 12 [|
             Tac2ffi.of_constructor cstr;
             Tac2ffi.of_instance u;
           |]
      | Case (ci, u, pms, c, iv, t, bl) ->
         (* FIXME: also change representation Ltac2-side? *)
         let (ci, c, iv, t, bl) = EConstr.expand_case env sigma (ci, u, pms, c, iv, t, bl) in
         let c = on_snd (EConstr.ERelevance.kind sigma) c in
         v_blk 13 [|
             Tac2ffi.of_case ci;
             Tac2ffi.(of_pair of_constr of_relevance c);
             of_case_invert iv;
             Tac2ffi.of_constr t;
             Tac2ffi.of_array Tac2ffi.of_constr bl;
           |]
      | Fix ((recs, i), def) ->
         let (nas, cs) = of_rec_declaration def in
         v_blk 14 [|
             Tac2ffi.of_array Tac2ffi.of_int recs;
             Tac2ffi.of_int i;
             nas;
             cs;
           |]
      | CoFix (i, def) ->
         let (nas, cs) = of_rec_declaration def in
         v_blk 15 [|
             Tac2ffi.of_int i;
             nas;
             cs;
           |]
      | Proj (p, r, c) ->
         v_blk 16 [|
             Tac2ffi.of_projection p;
             of_relevance (EConstr.ERelevance.kind sigma r);
             Tac2ffi.of_constr c;
           |]
      | Int n ->
         v_blk 17 [|Tac2ffi.of_uint63 n|]
      | Float f ->
         v_blk 18 [|Tac2ffi.of_float f|]
      | String s ->
         v_blk 19 [|Tac2ffi.of_pstring s|]
      | Array(u,t,def,ty) ->
         v_blk 20 [|
             of_instance u;
             Tac2ffi.of_array Tac2ffi.of_constr t;
             Tac2ffi.of_constr def;
             Tac2ffi.of_constr ty;
           |]

    let make knd env sigma =
      match Tac2ffi.to_block knd with
      | (0, [|n|]) ->
         let n = Tac2ffi.to_int n in
         EConstr.mkRel n
      | (1, [|id|]) ->
         let id = Tac2ffi.to_ident id in
         EConstr.mkVar id
      | (2, [|n|]) ->
         let n = Tac2ffi.to_int n in
         EConstr.mkMeta n
      | (3, [|evk; args|]) ->
         let evk = to_evar evk in
         let args = Tac2ffi.to_array Tac2ffi.to_constr args in
         EConstr.mkLEvar sigma (evk, Array.to_list args)
      | (4, [|s|]) ->
         let s = Tac2ffi.to_sort s in
         EConstr.mkSort s
      | (5, [|c; k; t|]) ->
         let c = Tac2ffi.to_constr c in
         let k = Tac2ffi.to_cast k in
         let t = Tac2ffi.to_constr t in
         EConstr.mkCast (c, k, t)
      | (6, [|na; u|]) ->
         let (na, t) = to_binder na in
         let u = Tac2ffi.to_constr u in
         EConstr.mkProd (na, t, u)
      | (7, [|na; c|]) ->
         let (na, t) = to_binder na in
         let u = Tac2ffi.to_constr c in
         EConstr.mkLambda (na, t, u)
      | (8, [|na; b; c|]) ->
         let (na, t) = to_binder na in
         let b = Tac2ffi.to_constr b in
         let c = Tac2ffi.to_constr c in
         EConstr.mkLetIn (na, b, t, c)
      | (9, [|c; cl|]) ->
         let c = Tac2ffi.to_constr c in
         let cl = Tac2ffi.to_array Tac2ffi.to_constr cl in
         EConstr.mkApp (c, cl)
      | (10, [|cst; u|]) ->
         let cst = Tac2ffi.to_constant cst in
         let u = to_instance u in
         EConstr.mkConstU (cst, u)
      | (11, [|ind; u|]) ->
         let ind = Tac2ffi.to_inductive ind in
         let u = to_instance u in
         EConstr.mkIndU (ind, u)
      | (12, [|cstr; u|]) ->
         let cstr = Tac2ffi.to_constructor cstr in
         let u = to_instance u in
         EConstr.mkConstructU (cstr, u)
      | (13, [|ci; c; iv; t; bl|]) ->
         let ci = Tac2ffi.to_case ci in
         let c = Tac2ffi.(to_pair to_constr to_relevance c) in
         let c = on_snd EConstr.ERelevance.make c in
         let iv = to_case_invert iv in
         let t = Tac2ffi.to_constr t in
         let bl = Tac2ffi.to_array Tac2ffi.to_constr bl in
         EConstr.mkCase (EConstr.contract_case env sigma (ci, c, iv, t, bl))
      | (14, [|recs; i; nas; cs|]) ->
         let recs = Tac2ffi.to_array Tac2ffi.to_int recs in
         let i = Tac2ffi.to_int i in
         let def = to_rec_declaration (nas, cs) in
         EConstr.mkFix ((recs, i), def)
      | (15, [|i; nas; cs|]) ->
         let i = Tac2ffi.to_int i in
         let def = to_rec_declaration (nas, cs) in
         EConstr.mkCoFix (i, def)
      | (16, [|p; r; c|]) ->
         let p = Tac2ffi.to_projection p in
         let r = to_relevance r in
         let c = Tac2ffi.to_constr c in
         EConstr.mkProj (p, EConstr.ERelevance.make r, c)
      | (17, [|n|]) ->
         let n = Tac2ffi.to_uint63 n in
         EConstr.mkInt n
      | (18, [|f|]) ->
         let f = Tac2ffi.to_float f in
         EConstr.mkFloat f
      | (19, [|s|]) ->
         let s = Tac2ffi.to_pstring s in
         EConstr.mkString s
      | (20, [|u;t;def;ty|]) ->
         let t = Tac2ffi.to_array Tac2ffi.to_constr t in
         let def = Tac2ffi.to_constr def in
         let ty = Tac2ffi.to_constr ty in
         let u = to_instance u in
         EConstr.mkArray(u,t,def,ty)
      | _ -> assert false

    let check c =
      pf_apply @@ fun env sigma ->
                  try
                    let (sigma, _) = Typing.type_of env sigma c in
                    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
                    return (of_result Tac2ffi.of_constr (Inl c))
                  with e when CErrors.noncritical e ->
                    let e = Exninfo.capture e in
                    return (of_result Tac2ffi.of_constr (Inr e))

    let liftn = EConstr.Vars.liftn
    let substnl = EConstr.Vars.substnl
    let closenl ids k c =
      Proofview.tclEVARMAP >>= fun sigma ->
      return (EConstr.Vars.substn_vars sigma k ids c)
    let closednl n c =
      Proofview.tclEVARMAP >>= fun sigma ->
      return (EConstr.Vars.closedn sigma n c)

    let noccur_between n m c =
      Proofview.tclEVARMAP >>= fun sigma ->
      return (EConstr.Vars.noccur_between sigma n m c)

    let case ind =
      Proofview.tclENV >>= fun env ->
      try
        let ans = Inductiveops.make_case_info env ind Constr.MatchStyle in
        return (Tac2ffi.of_case ans)
      with e when CErrors.noncritical e ->
        throw Tac2ffi.err_notfound

    type case = Constr.case_info

    module Case = struct
      open Constr

      let equal x y = Ind.UserOrd.equal x.ci_ind y.ci_ind
      let inductive case = case.ci_ind
    end
  end

  module Cast = struct
    type t = Constr.cast_kind
    let equal = Glob_ops.cast_kind_eq

    let default = of_cast DEFAULTcast
    let vm      = of_cast VMcast
    let native  = of_cast NATIVEcast
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

  module Pretype = struct
    open Pretyping
    type expected_type = Pretyping.typing_constraint

    module Flags = struct
      type t = Pretyping.inference_flags

      let constr_flags = Tac2core.constr_flags

      let set_use_coercion b (flags: t) =
        { flags with use_coercions = b }

      let set_use_typeclasses b flags =
        { flags with use_typeclasses = if b then UseTC else NoUseTC }

      let set_allow_evars b flags =
        { flags with fail_evar = not b }

      let set_nf_evars b flags =
        { flags with expand_evars = b }
    end

    let expected_istype = IsType
    let expected_oftype c = OfType c
    let expected_without_type_constraint = WithoutTypeConstraint

    let pretype flags expected_type c =
      let pretype env sigma =
        let sigma, t = Pretyping.understand_uconstr ~flags ~expected_type env sigma c in
        Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
      in
      pf_apply ~catch_exceptions:true pretype
  end

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

let () = define "constr_relevance_equal" (relevance @-> relevance @-> eret bool) Ltac2Constr.Relevance.equal
let () = define "constr_relevance_relevant" (ret relevance) Ltac2Constr.Relevance.relevant
let () = define "constr_relevance_irrelevant" (ret relevance) Ltac2Constr.Relevance.irrelevant

let () = define "constr_kind" (constr @-> eret valexpr) Ltac2Constr.Unsafe.kind
let () = define "constr_make" (valexpr @-> eret constr) Ltac2Constr.Unsafe.make
let () = define "constr_check" (constr @-> tac valexpr) Ltac2Constr.Unsafe.check
let () = define "constr_liftn" (int @-> int @-> constr @-> ret constr) Ltac2Constr.Unsafe.liftn
let () = define "constr_substnl" (list constr @-> int @-> constr @-> ret constr) Ltac2Constr.Unsafe.substnl
let () = define "constr_closenl" (list ident @-> int @-> constr @-> tac constr) Ltac2Constr.Unsafe.closenl
let () = define "constr_closedn" (int @-> constr @-> tac bool) Ltac2Constr.Unsafe.closednl
let () = define "constr_noccur_between" (int @-> int @-> constr @-> tac bool) Ltac2Constr.Unsafe.noccur_between
let () = define "constr_case" (inductive @-> tac valexpr) Ltac2Constr.Unsafe.case

let () = define "constr_case_equal" (case @-> case @-> ret bool) Ltac2Constr.Unsafe.Case.equal
let () = define "case_to_inductive" (case @-> ret inductive) Ltac2Constr.Unsafe.Case.inductive

let () = define "constr_cast_equal" (cast @-> cast @-> ret bool) Ltac2Constr.Cast.equal
let () = define "constr_cast_default" (ret valexpr) Ltac2Constr.Cast.default
let () = define "constr_cast_vm" (ret valexpr) Ltac2Constr.Cast.vm
let () = define "constr_cast_native" (ret valexpr) Ltac2Constr.Cast.native

let () = define "constr_in_context" (ident @-> constr @-> thunk unit @-> tac constr) Ltac2Constr.in_context

let () = define "constr_flags" (ret pretype_flags)
           Ltac2Constr.Pretype.Flags.constr_flags
let () = define "pretype_flags_set_use_coercions" (bool @-> pretype_flags @-> ret pretype_flags)
           Ltac2Constr.Pretype.Flags.set_use_coercion
let () = define "pretype_flags_set_use_typeclasses" (bool @-> pretype_flags @-> ret pretype_flags)
           Ltac2Constr.Pretype.Flags.set_use_typeclasses
let () = define "pretype_flags_set_allow_evars" (bool @-> pretype_flags @-> ret pretype_flags)
           Ltac2Constr.Pretype.Flags.set_allow_evars
let () = define "pretype_flags_set_nf_evars" (bool @-> pretype_flags @-> ret pretype_flags)
           Ltac2Constr.Pretype.Flags.set_nf_evars

let () = define "expected_istype" (ret expected_type) Ltac2Constr.Pretype.expected_istype
let () = define "expected_oftype" (constr @-> ret expected_type) Ltac2Constr.Pretype.expected_oftype
let () = define "expected_without_type_constraint" (ret expected_type) Ltac2Constr.Pretype.expected_without_type_constraint

let () = define "constr_pretype" (pretype_flags @-> expected_type @-> preterm @-> tac constr) Ltac2Constr.Pretype.pretype

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
