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
open Tac2extffi
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

let assert_focussed =
  Proofview.Goal.goals >>= fun gls ->
  match gls with
  | [_] -> Proofview.tclUNIT ()
  | [] | _ :: _ :: _ -> throw Tac2ffi.err_notfocussed

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

(** Constructor *)
module Ltac2Constructor = struct
  type t = Construct.t
  let equal = Construct.UserOrd.equal
  let inductive (ind, _) = ind
  let index (_, i) =
    (* WARNING: ML constructors are 1-indexed but Ltac2 constructors are 0-indexed *)
    i - 1
  let print ctor =
    Nametab.pr_global_env Id.Set.empty (ConstructRef ctor)
end

let () = define "constructor_equal" (constructor @-> constructor @-> ret bool) Ltac2Constructor.equal
let () = define "constructor_inductive" (constructor @-> ret inductive) Ltac2Constructor.inductive
let () = define "constructor_index" (constructor @-> ret int) Ltac2Constructor.index
let () = define "constructor_print" (constructor @-> ret pp) Ltac2Constructor.print

(** Control *)

module Ltac2Control = struct
  let zero (e, info) = fail ~info e
  let zero_bt (e, _) info = Proofview.tclZERO ~info e

  let plus x k = Proofview.tclOR (thaw x) k
  let plus_bt run handle =
    Proofview.tclOR (thaw run) (fun e -> handle e (snd e))

  let once f = Proofview.tclONCE (thaw f)
  let case f =
    Proofview.tclCASE (thaw f) >>= begin function
    | Proofview.Next (x, k) ->
      let k (e,info) = set_bt info >>= fun info -> k (e,info) in
      return (Ok (x, k))
    | Proofview.Fail e -> return (Error e)
    end

  let numgoals () = Proofview.numgoals

  let dispatch l =
    let l = List.map (fun f -> thaw f) l in
    Proofview.tclDISPATCH l

  let extend lft tac rgt =
    let lft = List.map (fun f -> thaw f) lft in
    let tac = thaw tac in
    let rgt = List.map (fun f -> thaw f) rgt in
    Proofview.tclEXTEND lft tac rgt

  let enter f =
    let f = Proofview.tclIGNORE (thaw f) in
    Proofview.tclINDEPENDENT f

  let focus i j tac =
    Proofview.tclFOCUS i j (thaw tac)

  let shelve () = Proofview.shelve
  let shelve_unifiable () = Proofview.shelve_unifiable
  let unshelve t =
    Proofview.with_shelf (thaw t) >>= fun (gls,v) ->
    let gls = List.map Proofview.with_empty_state gls in
    Proofview.Unsafe.tclGETGOALS >>= fun ogls ->
    Proofview.Unsafe.tclSETGOALS (gls @ ogls) >>= fun () ->
    return v

  let new_goal ev =
    Proofview.tclEVARMAP >>= fun sigma ->
    if Evd.mem sigma ev then
      let sigma = Evd.remove_future_goal sigma ev in
      let sigma = Evd.unshelve sigma [ev] in
      Proofview.Unsafe.tclEVARS sigma <*>
        Proofview.Unsafe.tclNEWGOALS [Proofview.with_empty_state ev] <*>
        Proofview.tclUNIT ()
    else throw Tac2ffi.err_notfound

  let cycle = Proofview.cycle
  let reorder_goals l =
    let is_permutation len l =
      if not (Int.equal len (Array.length l)) then false else
        let items = Array.make len false in
        (* returns true iff [l] (seen as a 1-indexed list) maps ints in [1; len] to [1; len] injectively.
           Thanks to pigeonhole theorem this means [l] is a permutation of [1; len]. *)
        Array.for_all (fun x ->
            if 1 <= x && x <= len && not items.(x-1) then
              let () = items.(x-1) <- true in
              true
            else false)
          l
    in
    Proofview.Unsafe.tclGETGOALS >>= fun gls ->
    let len = List.length gls in
    let l = Array.of_list l in
    if not (is_permutation len l) then
      throw (err_invalid_arg (Pp.str "reorder_goals"))
    else
      let gls = Array.of_list gls in
      let gls = List.init len (fun i -> gls.(l.(i) - 1)) in
      Proofview.Unsafe.tclSETGOALS gls

  let goal () =
    assert_focussed >>= fun () ->
    Proofview.Goal.enter_one @@ fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    return (Reductionops.nf_evar sigma concl)

  let hyp id =
    pf_apply @@ fun env _ ->
    let mem = try ignore (Environ.lookup_named id env); true with Not_found -> false in
    if mem then return (EConstr.mkVar id)
    else Tacticals.tclZEROMSG
      (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (* FIXME: Do something more sensible *)

  let hyp_value id =
    pf_apply @@ fun env _ ->
    match EConstr.lookup_named id env with
    | d -> return (Context.Named.Declaration.get_value d)
    | exception Not_found ->
      Tacticals.tclZEROMSG
      (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (* FIXME: Do something more sensible *)

  let hyps () =
    pf_apply @@ fun env _ ->
    let open Context in
    let open Named.Declaration in
    let hyps = List.rev (Environ.named_context env) in
    let map = function
    | LocalAssum (id, t) ->
      let t = EConstr.of_constr t in
      Tac2ffi.of_tuple [|
        Tac2ffi.of_ident id.binder_name;
        Tac2ffi.of_option Tac2ffi.of_constr None;
        Tac2ffi.of_constr t;
      |]
    | LocalDef (id, c, t) ->
      let c = EConstr.of_constr c in
      let t = EConstr.of_constr t in
      Tac2ffi.of_tuple [|
        Tac2ffi.of_ident id.binder_name;
        Tac2ffi.of_option Tac2ffi.of_constr (Some c);
        Tac2ffi.of_constr t;
      |]
    in
    return (Tac2ffi.of_list map hyps)

  let refine c =
    let c = thaw c >>= fun c -> Proofview.tclUNIT ((), c, None) in
    Proofview.Goal.enter @@ fun gl ->
    Refine.generic_refine ~typecheck:true c gl

  let solve_constraints () = Refine.solve_constraints
  let with_holes x f = Tacticals.tclRUNWITHHOLES false (thaw x) f

  let progress f = Proofview.tclPROGRESS (thaw f)
  let abstract id f = Abstract.tclABSTRACT id (thaw f)

  let time s f = Proofview.tclTIME s (thaw f)
  let timeout i f = Proofview.tclTIMEOUT i (thaw f)
  let timeoutf f64 f = Proofview.tclTIMEOUTF (Float64.to_float f64) (thaw f)

  let check_interrupt () = Proofview.tclCHECKINTERRUPT

  let clear_err_info (e,_) = (e, Exninfo.null)
  let current_exninfo () =
    return () >>= fun () ->
    set_bt (Exninfo.reify())

  let print_err (e, _) = CErrors.print e

  (* Defined last to avoid shadowing issues in this module *)
  let throw (e, info) = throw ~info e
  let throw_bt (e, _) info =
    Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))
end

let () = define "throw" (exn @-> tac valexpr) Ltac2Control.throw
let () = define "throw_bt" (exn @-> exninfo @-> tac valexpr) Ltac2Control.throw_bt
let () = define "zero" (exn @-> tac valexpr) Ltac2Control.zero
let () = define "zero_bt" (exn @-> exninfo @-> tac valexpr) Ltac2Control.zero_bt

let () = define "plus" (thunk valexpr @-> fun1 exn valexpr @-> tac valexpr) Ltac2Control.plus
let () = define "plus_bt" (thunk valexpr @-> fun2 exn exninfo valexpr @-> tac valexpr) Ltac2Control.plus_bt

let () = define "once" (thunk valexpr @-> tac valexpr) Ltac2Control.once
let () = define "case" (thunk valexpr @-> tac (result (pair valexpr (fun1 exn valexpr)))) Ltac2Control.case

let () = define "numgoals" (unit @-> tac int) Ltac2Control.numgoals

let () = define "dispatch" (list (thunk unit) @-> tac unit) Ltac2Control.dispatch
let () = define "extend" (list (thunk unit) @-> thunk unit @-> list (thunk unit) @-> tac unit) Ltac2Control.extend

let () = define "enter" (thunk unit @-> tac unit) Ltac2Control.enter
let () = define "focus" (int @-> int @-> thunk valexpr @-> tac valexpr) Ltac2Control.focus

let () = define "shelve" (unit @-> tac unit) Ltac2Control.shelve
let () = define "shelve_unifiable" (unit @-> tac unit) Ltac2Control.shelve_unifiable
let () = define "unshelve" (thunk valexpr @-> tac valexpr) Ltac2Control.unshelve

let () = define "new_goal" (evar @-> tac unit) Ltac2Control.new_goal
let () = define "reorder_goals" (list int @-> tac unit) Ltac2Control.reorder_goals
let () = define "cycle" (int @-> tac unit) Ltac2Control.cycle

let () = define "goal" (unit @-> tac constr) Ltac2Control.goal
let () = define "hyp" (ident @-> tac constr) Ltac2Control.hyp
let () = define "hyp_value" (ident @-> tac (option constr)) Ltac2Control.hyp_value
let () = define "hyps" (unit @-> tac valexpr) Ltac2Control.hyps

let () = define "refine" (thunk constr @-> tac unit) Ltac2Control.refine
let () = define "solve_constraints" (unit @-> tac unit) Ltac2Control.solve_constraints
let () = define "with_holes" (thunk valexpr @-> fun1 valexpr valexpr @-> tac valexpr) Ltac2Control.with_holes

let () = define "progress" (thunk valexpr @-> tac valexpr) Ltac2Control.progress
let () = define "abstract" (option ident @-> thunk unit @-> tac unit) Ltac2Control.abstract

let () = define "time" (option string @-> thunk valexpr @-> tac valexpr) Ltac2Control.time
let () = define "timeout" (int @-> thunk valexpr @-> tac valexpr) Ltac2Control.timeout
let () = define "timeoutf" (float @-> thunk valexpr @-> tac valexpr) Ltac2Control.timeoutf

let () = define "check_interrupt" (unit @-> tac unit) Ltac2Control.check_interrupt

let () = define "clear_err_info" (err @-> ret err) Ltac2Control.clear_err_info
let () = define "current_exninfo" (unit @-> tac exninfo) Ltac2Control.current_exninfo

let () = define "print_err" (err @-> ret pp) Ltac2Control.print_err

(** Env *)

module Ltac2Env = struct
  let get ids =
    match ids with
    | [] -> None
    | _ :: _ as ids ->
       let (id, path) = List.sep_last ids in
       let path = DirPath.make (List.rev path) in
       let fp = Libnames.make_path path id in
       try Some (Nametab.global_of_path fp) with Not_found -> None

  let expand ids =
    match ids with
    | [] -> []
    | _ :: _ as ids ->
       let (id, path) = List.sep_last ids in
       let path = DirPath.make (List.rev path) in
       let qid = Libnames.make_qualid path id in
       Nametab.locate_all qid

  let path r =
    match Nametab.path_of_global r with
    | fp ->
       let (path, id) = Libnames.repr_path fp in
       let path = DirPath.repr path in
       return (List.rev_append path [id])
    | exception Not_found ->
       throw Tac2ffi.err_notfound

  let instantiate r =
    Proofview.tclENV >>= fun env ->
    Proofview.tclEVARMAP >>= fun sigma ->
    let (sigma, c) = Evd.fresh_global env sigma r in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    return c
end

let () = define "env_get" (list ident @-> ret (option reference)) Ltac2Env.get
let () = define "env_expand" (list ident @-> ret (list reference)) Ltac2Env.expand
let () = define "env_path" (reference @-> tac (list ident)) Ltac2Env.path
let () = define "env_instantiate" (reference @-> tac constr) Ltac2Env.instantiate

(** Evar *)

module Ltac2Evar = struct
  type t = Evar.t
  let equal = Evar.equal
end

let () = define "evar_equal" (evar @-> evar @-> ret bool) Ltac2Evar.equal

(** Float *)

module Ltac2Float = struct
  type t = Float64.t
  let equal = Float64.equal
end

let () = define "float_equal" (float @-> float @-> ret bool) Ltac2Float.equal

(** Fresh *)

module Ltac2Fresh = struct
  module Free = struct
    type t = Nameops.Fresh.t

    let empty = Nameops.Fresh.empty
    let add = Nameops.Fresh.add
    let union = Nameops.Fresh.union

    let of_ids ids = List.fold_right Nameops.Fresh.add ids Nameops.Fresh.empty
    let of_constr c =
      Proofview.tclEVARMAP >>= fun sigma ->
      let rec fold accu c =
        match EConstr.kind sigma c with
        | Constr.Var id -> Nameops.Fresh.add id accu
        | _ -> EConstr.fold sigma fold accu c
      in
      return (fold Nameops.Fresh.empty c)
  end

  (* for backwards compat reasons the ocaml and ltac2 APIs
     exchange the meaning of "fresh" and "next" *)
  let next avoid id =
    let id = Namegen.mangle_id id in
    Nameops.Fresh.fresh id avoid

  let fresh avoid id =
    let id = Namegen.mangle_id id in
    Nameops.Fresh.next id avoid
end

let () = define "fresh_free_empty" (ret free) Ltac2Fresh.Free.empty
let () = define "fresh_free_add" (ident @-> free @-> ret free) Ltac2Fresh.Free.add
let () = define "fresh_free_union" (free @-> free @-> ret free) Ltac2Fresh.Free.union
let () = define "fresh_free_of_ids" (list ident @-> ret free) Ltac2Fresh.Free.of_ids
let () = define "fresh_free_of_constr" (constr @-> tac free) Ltac2Fresh.Free.of_constr

let () = define "fresh_next" (free @-> ident @-> ret (pair ident free)) Ltac2Fresh.next
let () = define "fresh_fresh" (free @-> ident @-> ret ident) Ltac2Fresh.fresh

(** Ident *)

module Ltac2Ident = struct
  type t = Id.t

  let equal = Id.equal
  let to_string = Id.to_string
  let of_string s =
    try Some (Id.of_string s)
    with e when CErrors.noncritical e -> None
end

let () = define "ident_equal" (ident @-> ident @-> ret bool) Ltac2Ident.equal
let () = define "ident_to_string" (ident @-> ret string) Ltac2Ident.to_string
let () = define "ident_of_string" (string @-> ret (option ident)) Ltac2Ident.of_string

(** Ind *)

module Ltac2Ind = struct
  type t = Ind.t
  type data = t * Declarations.mutual_inductive_body

  let equal = Ind.UserOrd.equal
  let data ind =
    Proofview.tclENV >>= fun env ->
    if Environ.mem_mind (fst ind) env then
      return (ind, Environ.lookup_mind (fst ind) env)
    else
      throw Tac2ffi.err_notfound

  let repr = fst
  let index = snd

  let nblocks (_, mib) = Array.length mib.Declarations.mind_packets
  let nconstructors ((_, n), mib) =
    Array.length Declarations.(mib.mind_packets.(n).mind_consnames)

  let get_block (ind, mib) n =
    if 0 <= n && n < Array.length mib.Declarations.mind_packets then
      return ((fst ind, n), mib)
    else throw Tac2ffi.err_notfound

  let get_constructor ((mind, n), mib) i =
    let open Declarations in
    let ncons = Array.length mib.mind_packets.(n).mind_consnames in
    if 0 <= i && i < ncons then
      (* WARNING: In the ML API constructors are indexed from 1 for historical
         reasons, but Ltac2 uses 0-indexing instead. *)
      return ((mind, n), i + 1)
    else throw Tac2ffi.err_notfound

  let nparams (_, mib) = mib.Declarations.mind_nparams
  let nparams_uniform (_, mib) = mib.Declarations.mind_nparams_rec

  let get_projections (ind,mib) =
    Declareops.inductive_make_projections ind mib
    |> Option.map (Array.map (fun (p,_) -> Projection.make p false))

  let constructor_nargs ((_,i),mib) =
    let open Declarations in
    mib.mind_packets.(i).mind_consnrealargs

  let constructor_ndecls ((_,i),mib) =
    let open Declarations in
    mib.mind_packets.(i).mind_consnrealdecls

  let print ind = Nametab.pr_global_env Id.Set.empty (IndRef ind)
end

let () = define "ind_equal" (inductive @-> inductive @-> ret bool) Ltac2Ind.equal
let () = define "ind_data" (inductive @-> tac ind_data) Ltac2Ind.data
let () = define "ind_repr" (ind_data @-> ret inductive) Ltac2Ind.repr
let () = define "ind_index" (inductive @-> ret int) Ltac2Ind.index

let () = define "ind_nblocks" (ind_data @-> ret int) Ltac2Ind.nblocks
let () = define "ind_nconstructors" (ind_data @-> ret int) Ltac2Ind.nconstructors

let () = define "ind_get_block" (ind_data @-> int @-> tac ind_data) Ltac2Ind.get_block
let () = define "ind_get_constructor" (ind_data @-> int @-> tac constructor) Ltac2Ind.get_constructor
let () = define "ind_get_nparams" (ind_data @-> ret int) Ltac2Ind.nparams
let () = define "ind_get_nparams_rec" (ind_data @-> ret int) Ltac2Ind.nparams_uniform

let () = define "ind_get_projections" (ind_data @-> ret (option (array projection))) Ltac2Ind.get_projections

let () = define "constructor_nargs" (ind_data @-> ret (array int)) Ltac2Ind.constructor_nargs
let () = define "constructor_ndecls" (ind_data @-> ret (array int)) Ltac2Ind.constructor_ndecls

let () = define "ind_print" (inductive @-> ret pp) Ltac2Ind.print

(** Int *)
module Ltac2Int = struct
  type t = int

  let equal = (==)
  let compare = Int.compare

  let add = (+)
  let sub = (-)
  let mul = ( * )

  let div m n =
    if n == 0 then throw Tac2ffi.err_division_by_zero
    else return (m / n)
  let (mod) m n =
    if n == 0 then throw Tac2ffi.err_division_by_zero
    else return (m mod n)

  let neg = (~-)
  let abs = Stdlib.abs

  let (asr) = (asr)
  let (lsl) = (lsl)
  let (lsr) = (lsr)
  let (land) = (land)
  let (lor) = (lor)
  let (lxor) = (lxor)
  let (lnot) = (lnot)
end

let () = define "int_equal" (int @-> int @-> ret bool) Ltac2Int.equal
let () = define "int_compare" (int @-> int @-> ret int) Ltac2Int.compare

let () = define "int_add" (int @-> int @-> ret int) Ltac2Int.add
let () = define "int_sub" (int @-> int @-> ret int) Ltac2Int.sub
let () = define "int_mul" (int @-> int @-> ret int) Ltac2Int.mul

let () = define "int_neg" (int @-> ret int) Ltac2Int.neg
let () = define "int_abs" (int @-> ret int) Ltac2Int.abs

let () = define "int_div" (int @-> int @-> tac int) Ltac2Int.div
let () = define "int_mod" (int @-> int @-> tac int) Ltac2Int.(mod)

let () = define "int_asr" (int @-> int @-> ret int)  Ltac2Int.(asr)
let () = define "int_lsl" (int @-> int @-> ret int)  Ltac2Int.(lsl)
let () = define "int_lsr" (int @-> int @-> ret int)  Ltac2Int.(lsr)
let () = define "int_land" (int @-> int @-> ret int) Ltac2Int.(land)
let () = define "int_lor" (int @-> int @-> ret int)  Ltac2Int.(lor)
let () = define "int_lxor" (int @-> int @-> ret int) Ltac2Int.(lxor)
let () = define "int_lnot" (int @-> ret int) Ltac2Int.(lnot)

(** Message *)

module Ltac2Message = struct
  let print m = Feedback.msg_notice m

  let empty = Pp.mt ()
  let of_string = Pp.str
  let to_string = Pp.string_of_ppcmds

  let of_int = Pp.int
  let of_ident = Id.print
  let of_constr c =
    pf_apply @@ fun env sigma -> return (Printer.pr_econstr_env env sigma c)
  let of_lconstr c =
    pf_apply @@ fun env sigma -> return (Printer.pr_leconstr_env env sigma c)
  let of_preterm c =
    pf_apply @@ fun env sigma -> return (Printer.pr_closed_glob_env env sigma c)
  let of_lpreterm c =
    pf_apply @@ fun env sigma -> return (Printer.pr_closed_lglob_env env sigma c)
  let of_exn v env sigma =
    let open Tac2quote.Refs in
    Tac2print.pr_valexpr env sigma v (GTypRef (Other t_exn, []))
  let of_exninfo = CErrors.print_extra

  let concat = Pp.app
  let force_new_line = Pp.fnl ()
  let break i j = Pp.brk (i, j)
  let space = Pp.spc ()
  let hbox = Pp.h
  let vbox = Pp.v
  let hvbox = Pp.hv
  let hovbox = Pp.hov

  module Format = struct
    open Tac2types

    let stop = []
    let string s = FmtString :: s
    let int s = FmtInt :: s
    let constr s = FmtConstr :: s
    let ident s = FmtIdent :: s
    let literal l s = FmtLiteral l :: s
    let alpha s = FmtAlpha :: s
    let alpha0 s = FmtAlpha0 :: s
    let message s = FmtMessage :: s

    let arity_of_format fmt =
      let fold accu = function
        | FmtLiteral _ -> accu
        | FmtString | FmtInt | FmtConstr | FmtIdent | FmtMessage -> 1 + accu
        | FmtAlpha | FmtAlpha0 -> 2 + accu
      in
      List.fold_left fold 0 fmt

    let kfprintf k fmt =
      let pop1 l = match l with [] -> assert false | x :: l -> (x, l) in
      let pop2 l = match l with [] | [_] -> assert false | x :: y :: l -> (x, y, l) in
      let arity = arity_of_format fmt in
      let rec eval accu args fmt = match fmt with
        | [] -> apply k [of_pp accu]
        | tag :: fmt ->
           match tag with
           | FmtLiteral s ->
              eval (Pp.app accu (Pp.str s)) args fmt
           | FmtString ->
              let (s, args) = pop1 args in
              let pp = Pp.str (Tac2ffi.to_string s) in
              eval (Pp.app accu pp) args fmt
           | FmtInt ->
              let (i, args) = pop1 args in
              let pp = Pp.int (to_int i) in
              eval (Pp.app accu pp) args fmt
           | FmtConstr ->
              let (c, args) = pop1 args in
              let c = to_constr c in
              pf_apply begin fun env sigma ->
                let pp = Printer.pr_econstr_env env sigma c in
                eval (Pp.app accu pp) args fmt
                end
           | FmtIdent ->
              let (i, args) = pop1 args in
              let pp = Id.print (to_ident i) in
              eval (Pp.app accu pp) args fmt
           | FmtMessage ->
              let (m, args) = pop1 args in
              let m = to_pp m in
              eval (Pp.app accu m) args fmt
           | FmtAlpha ->
              let (f, x, args) = pop2 args in
              Tac2val.apply_val f [of_unit (); x] >>= fun pp ->
              eval (Pp.app accu (to_pp pp)) args fmt
           | FmtAlpha0 ->
              let (f, x, args) = pop2 args in
              Tac2val.apply_val f [x] >>= fun pp ->
              eval (Pp.app accu (to_pp pp)) args fmt
      in
      let eval v = eval (Pp.mt ()) v fmt in
      if Int.equal arity 0 then eval []
      else return (Tac2ffi.of_closure (Tac2val.abstract arity eval))

    let ikfprintf k v fmt =
      let arity = arity_of_format fmt in
      let eval _args = apply k [v] in
      if Int.equal arity 0 then eval []
      else return (Tac2ffi.of_closure (Tac2val.abstract arity eval))
  end

end

let () = define "print" (pp @-> ret unit) Ltac2Message.print
let () = define "message_empty" (ret pp) Ltac2Message.empty
let () = define "message_of_int" (int @-> ret pp) Ltac2Message.of_int
let () = define "message_of_ident" (ident @-> ret pp) Ltac2Message.of_ident
let () = define "message_of_string" (string @-> ret pp) Ltac2Message.of_string
let () = define "message_to_string" (pp @-> ret string) Ltac2Message.to_string
let () = define "message_of_constr" (constr @-> tac pp) Ltac2Message.of_constr
let () = define "message_of_lconstr" (constr @-> tac pp) Ltac2Message.of_lconstr
let () = define "message_of_preterm" (preterm @-> tac pp) Ltac2Message.of_preterm
let () = define "message_of_lpreterm" (preterm @-> tac pp) Ltac2Message.of_lpreterm
let () = define "message_of_exn" (valexpr @-> eret pp) Ltac2Message.of_exn
let () = define "message_of_exninfo" (exninfo @-> ret pp) Ltac2Message.of_exninfo

let () = define "message_concat" (pp @-> pp @-> ret pp) Ltac2Message.concat
let () = define "message_force_new_line" (ret pp) Ltac2Message.force_new_line
let () = define "message_break" (int @-> int @-> ret pp) Ltac2Message.break
let () = define "message_space" (ret pp) Ltac2Message.space
let () = define "message_hbox" (pp @-> ret pp) Ltac2Message.hbox
let () = define "message_vbox" (int @-> pp @-> ret pp) Ltac2Message.vbox
let () = define "message_hvbox" (int @-> pp @-> ret pp) Ltac2Message.hvbox
let () = define "message_hovbox" (int @-> pp @-> ret pp) Ltac2Message.hovbox

let () = define "format_stop" (ret format) Ltac2Message.Format.stop
let () = define "format_string" (format @-> ret format) Ltac2Message.Format.string
let () = define "format_int" (format @-> ret format) Ltac2Message.Format.int
let () = define "format_constr" (format @-> ret format) Ltac2Message.Format.constr
let () = define "format_ident" (format @-> ret format) Ltac2Message.Format.ident
let () = define "format_literal" (string @-> format @-> ret format) Ltac2Message.Format.literal
let () = define "format_alpha" (format @-> ret format) Ltac2Message.Format.alpha
let () = define "format_alpha0" (format @-> ret format) Ltac2Message.Format.alpha0
let () = define "format_message" (format @-> ret format) Ltac2Message.Format.message

let () = define "format_kfprintf" (closure @-> format @-> tac valexpr) Ltac2Message.Format.kfprintf
let () = define "format_ikfprintf" (closure @-> valexpr @-> format @-> tac valexpr) @@ Ltac2Message.Format.ikfprintf

(** Meta *)

module Ltac2Meta = struct
  type t = Int.t
  let equal = Int.equal
end

let () = define "meta_equal" (int @-> int @-> ret bool) Ltac2Meta.equal

(** Module *)

module Ltac2Module = struct
  type t = ModPath.t

  let equal = ModPath.equal
  let to_message m =
  (* XXX use ModPath.print instead? (nametab is ambiguous since there's no single nametab)
     or expose ModPath.print as a separate external? *)
  try Nametab.Modules.pr m
  with Not_found ->
  try Nametab.ModTypes.pr m
  with Not_found ->
  try Nametab.OpenMods.pr (DirOpenModule m)
  with Not_found ->
  try Nametab.OpenMods.pr (DirOpenModtype m)
  with Not_found ->
    CErrors.anomaly Pp.(str "Unknown module or modtype " ++ ModPath.print m)

  let is_open m =
    ModPath.subpath m (Global.current_modpath())

  (* Find info about open module [m] in [senv_l] describing the open
     modules of some safe env with current module [senv_m].
     Returns [None] if [m] is the library, [Some v] if [m] is some inner open module. *)
  let rec find_openmod m senv_m senv_l =
    let open ModPath in
    match senv_m, senv_l with
    | MPbound _, _ -> assert false
    | MPfile _, [] -> assert (ModPath.equal m senv_m); None
    | MPfile _, _ :: _ -> assert false
    | MPdot (m0, _), is_modtype :: rest ->
       if ModPath.equal m senv_m then Some is_modtype
       else find_openmod m m0 rest
    | MPdot _, [] -> assert false

  (* Assuming [m] is currently open, tell whether it is modtype. *)
  let open_module_is_modtype m =
    let senv = Global.safe_env() in
    match find_openmod m (Safe_typing.current_modpath senv) (Safe_typing.module_is_modtype senv) with
    | None -> false
    | Some b -> b

  let open_module_is_functor m =
    let senv = Global.safe_env() in
    match find_openmod m (Safe_typing.current_modpath senv) (Safe_typing.module_num_parameters senv) with
    | None -> false
    | Some nparams -> not (Int.equal nparams 0)

  let is_modtype m env _ =
    if is_open m then open_module_is_modtype m
    else
      try ignore (Environ.lookup_modtype m env); true
      with Not_found -> false

  let is_functor m env _ =
    if is_open m then open_module_is_functor m
    else
      let modbody_is_functor m = match Mod_declarations.mod_type m with
        | NoFunctor _ -> false
        | MoreFunctor _ -> true
      in
      match Environ.lookup_module m env with
      | m -> modbody_is_functor m
      | exception Not_found -> match Environ.lookup_modtype m env with
                               | m -> modbody_is_functor m
                               | exception Not_found -> assert false

  let is_bound_module = function
  | MPbound _ -> true
  | MPfile _ | MPdot _ -> false

  let is_library = function
  | MPfile _ -> true
  | MPbound _ | MPdot _ -> false

  let parent_module = function
  | MPdot (m, _) -> Some m
  | MPbound _ | MPfile _ -> None

  open GlobRef
  let module_of_reference = function
  | VarRef _ -> throw (Invalid_argument "module_of_reference")
  | ConstRef c -> return (Constant.modpath c)
  | IndRef (mind,_) | ConstructRef ((mind,_),_) -> return (MutInd.modpath mind)

  let current_module () = Global.current_modpath ()

  let loaded_libraries () =
    List.map (fun dp -> MPfile dp) (Library.loaded_libraries())

  module Field = struct
    open ModField
    type t = ModField.t

    let handle f handler =
      let (handle_submodule, handle_reference, handle_rewrule) = handler in
      match f with
      | Ref x -> handle_reference x
      | Submodule x -> handle_submodule x
      | Rewrule -> handle_rewrule ()
  end

  let openmod_revstruct m senv =
    let rec close senv modtype =
      let curm = Safe_typing.current_modpath senv in
      if ModPath.equal m curm then senv
      else
        let l = match curm with
          | MPdot (_, l) -> l
          | _ -> assert false
        in
        match modtype with
        | [] -> assert false
        | false :: modtype ->
           (* None: type constraint of submodule doesn't matter since we
              will anyway only return "Submodule M" and not look at its
              contents *)
           close (snd @@ Safe_typing.end_module l None senv) modtype
        | true :: modtype -> close (snd @@ Safe_typing.end_modtype l senv) modtype
    in
    let modtype = Safe_typing.module_is_modtype senv in
    let senv = close senv modtype in
    Safe_typing.structure_body_of_safe_env senv

  let contents m =
    let body =
      if is_open m then
        (* XXX not sure what this does with side effects *)
        Some (List.rev (openmod_revstruct m (Global.safe_env())))
      else
        match Environ.lookup_module m (Global.env()) with
        | exception Not_found -> (* modtype *) None
        | body -> match Mod_declarations.mod_type body with
                  | MoreFunctor _ -> (* functor *) None
                  | NoFunctor body -> Some body
    in
    let to_field (lab, f) : ModField.t = match (f:_ Declarations.structure_field_body) with
      | SFBconst _ ->
         let kn = KerName.make m lab in
         Ref (ConstRef (Global.constant_of_delta_kn kn))
      | SFBmind _ ->
         let kn = KerName.make m lab in
         Ref (IndRef ((Global.mind_of_delta_kn kn, 0)))
      | SFBrules _ -> Rewrule
      | SFBmodule _ -> Submodule (MPdot (m, lab))
      | SFBmodtype _ -> Submodule (MPdot (m, lab))
    in
    Option.map (List.map to_field) body
end

let () = define "module_equal" (modpath @-> modpath @-> ret bool) Ltac2Module.equal
let () = define "module_to_message" (modpath @-> ret pp) Ltac2Module.to_message

let () = define "module_is_modtype" (modpath @-> eret bool) Ltac2Module.is_modtype
let () = define "module_is_functor" (modpath @-> eret bool) Ltac2Module.is_functor
let () = define "module_is_bound_module" (modpath @-> ret bool) Ltac2Module.is_bound_module
let () = define "module_is_library" (modpath @-> ret bool) Ltac2Module.is_library
let () = define "module_is_open" (modpath @-> ret bool) Ltac2Module.is_open

let () = define "module_parent_module" (modpath @-> ret (option modpath)) Ltac2Module.parent_module

let () = define "module_of_reference" (reference @-> tac modpath) Ltac2Module.module_of_reference

let () = define "current_module" (unit @-> ret modpath) Ltac2Module.current_module

let () = define "module_loaded_libraries" (unit @-> ret (list modpath)) Ltac2Module.loaded_libraries

let module_field_handler = triple (fun1 modpath valexpr) (fun1 reference valexpr) (fun1 unit valexpr)

let () = define "module_field_handle" (module_field @-> module_field_handler @-> tac valexpr) Ltac2Module.Field.handle

let () = define "module_contents" (modpath @-> ret (option (list module_field))) Ltac2Module.contents

(** Pattern *)
module Ltac2Pattern = struct
  type context = Constr_matching.context

  let empty_context = Constr_matching.empty_context

  let matches pat c =
    pf_apply begin fun env sigma ->
      let ans =
        try Some (Constr_matching.matches env sigma pat c)
        with Constr_matching.PatternMatchingFailure -> None
      in
      begin match ans with
      | None -> fail Tac2ffi.err_matchfailure
      | Some ans ->
         let ans = Id.Map.bindings ans in
         let of_pair (id, c) = Tac2ffi.of_tuple [| Tac2ffi.of_ident id; Tac2ffi.of_constr c |] in
         return (Tac2ffi.of_list of_pair ans)
      end
    end

  let matches_subterm pat c =
    let open Constr_matching in
    let rec of_ans s = match IStream.peek s with
      | IStream.Nil -> fail Tac2ffi.err_matchfailure
      | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
         let ans = Id.Map.bindings sub in
         Proofview.tclOR (return (m_ctx, ans)) (fun _ -> of_ans s)
    in
    pf_apply begin fun env sigma ->
      let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
      of_ans ans
    end

  let matches_vect pat c =
    pf_apply begin fun env sigma ->
      let ans =
        try Some (Constr_matching.matches env sigma pat c)
        with Constr_matching.PatternMatchingFailure -> None
      in
      match ans with
      | None -> fail Tac2ffi.err_matchfailure
      | Some ans ->
         let ans = Id.Map.bindings ans in
         let ans = Array.map_of_list snd ans in
         return (Tac2ffi.of_array Tac2ffi.of_constr ans)
    end

  let matches_subterm_vect pat c =
    let open Constr_matching in
    let rec of_ans s = match IStream.peek s with
      | IStream.Nil -> fail Tac2ffi.err_matchfailure
      | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
         let ans = Id.Map.bindings sub in
         let ans = Array.map_of_list snd ans in
         Proofview.tclOR (return (m_ctx,ans)) (fun _ -> of_ans s)
    in
    pf_apply begin fun env sigma ->
      let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
      of_ans ans
    end

  let matches_goal rev hp cp =
    assert_focussed >>= fun () ->
    Proofview.Goal.enter_one begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      Tac2match.match_goal env sigma concl ~rev (hp, cp) >>= fun (hyps, ctx, subst) ->
      let empty_context = Constr_matching.empty_context in
      let of_ctxopt ctx = Tac2ffi.of_matching_context (Option.default empty_context ctx) in
      let hids = Tac2ffi.of_array Tac2ffi.of_ident (Array.map_of_list pi1 hyps) in
      let hbctx = Tac2ffi.of_array of_ctxopt
                    (Array.of_list (CList.filter_map (fun (_,bctx,_) -> bctx) hyps))
      in
      let hctx = Tac2ffi.of_array of_ctxopt (Array.map_of_list pi3 hyps) in
      let subs = Tac2ffi.of_array Tac2ffi.of_constr (Array.map_of_list snd (Id.Map.bindings subst)) in
      let cctx = of_ctxopt ctx in
      let ans = Tac2ffi.of_tuple [| hids; hbctx; hctx; subs; cctx |] in
      Proofview.tclUNIT ans
    end

  let instantiate = Constr_matching.instantiate_context
end


let () = define "pattern_empty_context" (ret matching_context) Ltac2Pattern.empty_context
let () = define "pattern_matches" (pattern @-> constr @-> tac valexpr) Ltac2Pattern.matches
let () = define "pattern_matches_subterm" (pattern @-> constr @-> tac (pair matching_context (list (pair ident constr)))) Ltac2Pattern.matches_subterm
let () = define "pattern_matches_vect" (pattern @-> constr @-> tac valexpr) Ltac2Pattern.matches_vect
let () = define "pattern_matches_subterm_vect" (pattern @-> constr @-> tac (pair matching_context (array constr))) Ltac2Pattern.matches_subterm_vect

let match_pattern = Tac2ffi.map_repr
                      (fun (b,pat) -> if b then Tac2match.MatchPattern pat else Tac2match.MatchContext pat)
                      (function Tac2match.MatchPattern pat -> (true, pat) | MatchContext pat -> (false, pat))
                      (pair bool pattern)

let () = define "pattern_matches_goal" (bool @-> list (pair (option match_pattern) match_pattern) @-> match_pattern @-> tac valexpr) Ltac2Pattern.matches_goal
let () = define "pattern_instantiate" (matching_context @-> constr @-> ret constr) Ltac2Pattern.instantiate
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
  module Constructor      = Ltac2Constructor
  module Control          = Ltac2Control
  module Env              = Ltac2Env
  module Evar             = Ltac2Evar
  module Float            = Ltac2Float
  module Fresh            = Ltac2Fresh
  module Ident            = Ltac2Ident
  module Ind              = Ltac2Ind
  module Int              = Ltac2Int
  module Message          = Ltac2Message
  module Meta             = Ltac2Meta
  module Module           = Ltac2Module
  module Pattern          = Ltac2Pattern
end
