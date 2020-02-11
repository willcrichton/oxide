open Syntax
open Util

(* checks that omega_prime is at least omega *)
let is_at_least (omega : owned) (omega_prime : owned) : bool =
  match (omega, omega_prime) with
  | (Shared, _) -> true
  | (Unique, Unique) -> true
  | (Unique, Shared) -> false

(* looks up var in gamma, and if the type is a closure, returns its closed over environment *)
let env_of (var : var) (gamma : var_env) : env tc =
  match List.assoc_opt var gamma with
  | Some (_, Fun (_, _, _, _, gamma_c, _)) -> Succ gamma_c
  | Some ty -> Fail (TypeMismatchFunction ty)
  | None -> Fail (UnboundPlace ((dummy, (var, []))))

(* substitutes this for that in ty *)
let subst_env_var (ty : ty) (this : env) (that : env_var) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ | TyVar _ -> ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (prov, omega, ty) -> (loc, Ref (prov, omega, sub ty))
    | Fun (evs, pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that evs) then
        let gammaPrime =
          match gamma with
          | EnvVar ev -> if ev = that then this else gamma
          | Env _ | EnvOf _ -> gamma
        in (loc, Fun (evs, pvs, tvs, sub_many tys, gammaPrime, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      (loc, Struct (name, provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many_env_var (pairs : (env * env_var) list) (ty : ty) : ty =
  List.fold_right (fun pair ty -> subst_env_var ty (fst pair) (snd pair)) pairs ty

(* substitutes this for that in ty *)
let subst_prov (ty : ty) (this : prov) (that : prov) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ | TyVar _ -> ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (pv, omega, ty) ->
      let prov = if (snd pv) = (snd that) then this else pv
      in (loc, Ref (prov, omega, sub ty))
    | Fun (evs, pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that pvs) then (loc, Fun (evs, pvs, tvs, sub_many tys, gamma, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      let sub_next (pv : prov) (provs : provs) =
        List.cons (if (snd pv) = (snd that) then this else pv) provs
      in let new_provs = List.fold_right sub_next provs []
      in (loc, Struct (name, new_provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many_prov (pairs : (prov * prov) list) (ty : ty) : ty =
  List.fold_right (fun pair ty -> subst_prov ty (fst pair) (snd pair)) pairs ty

let subst (ty : ty) (this : ty)  (that : ty_var) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ -> ty
    | TyVar tv -> if tv = that then this else ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (pv, omega, ty) -> (loc, Ref (pv, omega, sub ty))
    | Fun (evs, pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that tvs) then (loc, Fun (evs, pvs, tvs, sub_many tys, gamma, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      (loc, Struct (name, provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many (pairs : (ty * ty_var) list) (ty : ty) : ty =
  List.fold_right (fun pair ty -> subst ty (fst pair) (snd pair)) pairs ty

let subtype_prov (mode : subtype_modality) (ell : loan_env)
    (prov1 : prov) (prov2 : prov) : loan_env tc =
  match (mode, loan_env_lookup_opt ell prov1, loan_env_lookup_opt ell prov2) with
  | (Combine, Some rep1, Some rep2) ->
    (* UP-CombineLocalProvenances*)
    let ellPrime = loan_env_exclude_all ell [prov1; prov2]
    in Succ (loan_env_include_all ellPrime [prov1; prov2] (list_union rep1 rep2))
  | (Override, Some rep1, Some _) ->
    (* UP-OverrideLocalProvenances *)
    let ellPrime = loan_env_exclude ell prov2
    in Succ (loan_env_include ellPrime prov2 rep1)
  | (_, None, Some _) ->
    (* UP-AbstractProvLocalProv *)
    if not (loan_env_is_abs ell prov1) then Fail (InvalidProv prov1)
    else if loan_env_abs_sub ell prov1 prov2 then Succ ell
    else Fail (InvalidProv prov1)
  | (_, Some _, None) ->
    (* UP-LocalProvAbstractProv *)
    if not (loan_env_is_abs ell prov2) then Fail (InvalidProv prov2)
    else let ellPrime = loan_env_add_abs_sub ell prov1 prov2
    in Succ ellPrime
  | (_, None, None) ->
    (* UP-AbstractProvenances *)
    if not (loan_env_is_abs ell prov1) then
      Fail (InvalidProv prov1)
    else if not (loan_env_is_abs ell prov2) then
      Fail (InvalidProv prov2)
    else if not (loan_env_abs_sub ell prov1 prov2) then
      Fail (AbsProvsNotSubtype (prov1, prov2))
    else Succ ell

let subtype_prov_many (mode : subtype_modality) (ell : loan_env)
    (provs1 : provs) (provs2 : provs) : loan_env tc =
  let* provs = combine_prov "subtype_prov_many" provs1 provs2
  in foldl (fun ell (prov1, prov2) -> subtype_prov mode ell prov1 prov2) ell provs

let subtype (mode : subtype_modality) (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
  let rec sub (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
    match (snd ty1, snd ty2) with
    (* UT-Refl for base types *)
    | (BaseTy bt1, BaseTy bt2) ->
      if bt1 = bt2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Refl for type variables *)
    | (TyVar v1, TyVar v2) ->
      if v1 = v2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Array *)
    | (Array (t1, m), Array (t2, n)) ->
      if m = n then sub ell t1 t2
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Slice *)
    | (Slice t1, Slice t2) -> sub ell t1 t2
    (* UT-SharedRef *)
    | (Ref (v1, Shared, t1), Ref (v2, Shared, t2)) ->
      let* ellPrime = subtype_prov mode ell v1 v2
      in sub ellPrime t1 t2
    (* UT-UniqueRef *)
    | (Ref (v1, Unique, t1), Ref (v2, _, t2)) ->
      let* ellPrime = subtype_prov mode ell v1 v2
      in let* ell1 = sub ellPrime t1 t2
      in let* ell2 = sub ellPrime t2 t1
      in if (canonize ell1) = (canonize ell2) then Succ ell2
      else Fail (UnificationFailed (t1, t2))
    (* UT-Tuple *)
    | (Tup tys1, Tup tys2) -> sub_many ell tys1 tys2
    (* UT-Record *)
    | (Rec fields1, Rec fields2) ->
      let fields1 = List.sort (fun x y -> compare (fst x) (fst y)) fields1
      in let fields2 = List.sort (fun x y -> compare (fst x) (fst y)) fields2
      in sub_many ell (List.map snd fields1) (List.map snd fields2)
    (* UT-Struct *)
    | (Struct (name1, provs1, tys1, tagged_ty1), Struct (name2, provs2, tys2, tagged_ty2)) ->
      if name1 = name2 then
        let* ell_provs = subtype_prov_many mode ell provs1 provs2
        in let* ell_tys = sub_many ell_provs tys1 tys2
        in sub_opt ell_tys tagged_ty1 tagged_ty2
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Function *)
    | (Fun (evs1, prov1, tyvar1, tys1, _, ret_ty1),
       Fun (evs2, prov2, tyvar2, tys2, _, ret_ty2)) ->
      let tyvar_for_sub = List.map (fun x -> (inferred, TyVar x)) tyvar1
      in let* ev_sub = combine_evs "UT-Function" (List.map (fun ev -> EnvVar ev) evs1) evs2
      in let* prov_sub = combine_prov "UT-Function" prov1 prov2
      in let* ty_sub = combine_ty "UT-Function" tyvar_for_sub tyvar2
      in let do_sub : ty -> ty =
         subst_many_prov prov_sub >> subst_many ty_sub >> subst_many_env_var ev_sub
      in let alpharenamed_tys2 = List.map do_sub tys2
      in let* ell_prime = sub_many ell alpharenamed_tys2 tys1
      in sub ell_prime ret_ty1 ret_ty2
    (* UT-Bottom *)
    | (Any, _) -> Succ ell
    (* UT-Uninit *)
    | (Uninit ty1, Uninit ty2) -> sub ell ty1 ty2
    (* UT-InitUninit *)
    | (_, Uninit inner_ty) -> sub ell ty1 inner_ty
    (* UT-UninitInit *)
    | (Uninit inner_ty, _) ->
       (match sub ell inner_ty ty2 with
        | Succ _ -> Fail (PartiallyMovedTypes (ty1, ty2))
        | Fail err -> Fail err)
    | (_, _) -> Fail (UnificationFailed (ty1, ty2))
  and sub_many (ell : loan_env) (tys1 : ty list) (tys2 : ty list) : loan_env tc =
    let* tys = combine_tys "subtype_many" tys1 tys2
    in foldl (fun ell (ty1, ty2) -> sub ell ty1 ty2) ell tys
  and sub_opt (ell : loan_env) (ty1 : ty option) (ty2 : ty option) : loan_env tc =
    match (ty1, ty2) with
    | (Some ty1, Some ty2) -> sub ell ty1 ty2
    | (Some _, None) | (None, Some _) | (None, None) -> Succ ell
  in sub ell ty1 ty2

(* use the path to decompose a type into a context and an inner type *)
let rec decompose (ty : ty) (path : path) : (ty_ctx * ty) tc =
  let (loc, ty) = ty
  in match (ty, path) with
  | (ty, []) -> Succ ((inferred, Hole), (loc, ty))
  | (Rec pairs, (Field f) :: path) ->
    let* (inner_ctx, ty) = decompose (List.assoc f pairs) path
    in let replace (pair : field * ty) : field * ty_ctx =
      if fst pair = f then (f, inner_ctx) else (fst pair, (fst ty, Ty ty))
    in let ctx : ty_ctx = (loc, Rec (List.map replace pairs))
    in Succ (ctx, ty)
  | (Tup tys, (Index n) :: path) ->
    let* (inner_ctx, ty) = decompose (List.nth tys n) path
    in let replace (idx : int) (ty : ty) : ty_ctx =
      if idx = n then inner_ctx else (fst ty, Ty ty)
    in let ctx : ty_ctx = (loc, Tup (List.mapi replace tys))
    in Succ (ctx, ty)
  | (Struct (_, _, _, Some ty), path) -> decompose ty path
  | (Uninit ty, path) -> Fail (PartiallyMovedPath (ty, path))
  | (ty, path) -> Fail (InvalidOperationOnType (path, (loc, ty)))

(* find the type of the expr path based on the original type in a context *)
(* this will error if the context doesn't allow the operation,
   e.g. dereferencing a shared reference in a unique context *)
let compute_ty_in (ctx : owned) (ell : loan_env) (ty : ty) (path : expr_path) : ty tc =
  let rec compute (passed : prov list) (ty : ty) (path : expr_path) : ty tc =
    let (loc, ty) = ty
    in match (ty, path) with
    | (ty, []) -> Succ (loc, ty)
    | (Ref (prov, omega, ty), Deref :: path) ->
      if is_at_least ctx omega then
        let* () = for_each passed
                           (fun prv -> let* _ = subtype_prov Combine ell prv prov in Succ ())
        in compute (List.cons prov passed) ty path
      else Fail (PermissionErr (ty, path, ctx))
    | (Rec pairs, (Field f) :: path) -> compute passed (List.assoc f pairs) path
    | (Tup tys, (Index n) :: path) -> compute passed (List.nth tys n) path
    | (Struct (_, _, _, Some ty), path) -> compute passed ty path
    | (Uninit ty, path) ->
      let* _ = compute passed ty path
      in Fail (PartiallyMovedExprPath (ty, path))
    | (ty, path) -> Fail (InvalidOperationOnTypeEP (path, (loc, ty)))
  in compute [] ty path

(* find the type of the expr path based on the original type, assuming a shared use context*)
let compute_ty (ell : loan_env) (ty : ty) (path : expr_path) : ty tc =
  compute_ty_in Shared ell ty path

let rec plug (fill : ty) (ctx : ty_ctx) : ty =
  let (loc, ctx) = ctx
  in match ctx with
  | Hole -> fill
  | Ty ty -> ty
  | Tagged (tag, provs, tys, ctx) -> (loc, Struct (tag, provs, tys, Some (plug fill ctx)))
  | Rec pair -> (loc, Rec (List.map (fun (f, ctx) -> (f, plug fill ctx)) pair))
  | Tup ctx -> (loc, Tup (List.map (plug fill) ctx))

(* var env operations *)

let var_env_lookup (gamma : var_env) (pi : place) : ty tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty ->
    let* (_, ty) = decompose ty path
    in Succ ty
  | None -> Fail (UnboundPlace pi)
let var_env_lookup_root (gamma : var_env) (pi : place) : ty tc =
  let (root, _) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty -> Succ ty
  | None -> Fail (UnboundPlace pi)
let var_env_lookup_expr_root (gamma : var_env) (phi : place_expr) : ty tc =
  let (root, _) = snd phi
  in match List.assoc_opt root gamma with
  | Some ty -> Succ ty
  | None -> Fail (UnboundPlaceExpr phi)
let var_env_lookup_many (gamma : var_env) (pis : place list) : ty list tc =
  let lookup_seq (pi : place) (tys : ty list) : ty list tc =
    let* ty = var_env_lookup gamma pi
    in Succ (List.cons ty tys)
  in foldr lookup_seq pis []
let var_env_lookup_opt (gamma : var_env) (pi : place) : (ty option) tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty ->
    let* (_, ty) = decompose ty path
    in Succ (Some ty)
  | None -> Succ None
let var_env_lookup_place_expr (gamma : var_env) (pi : place_expr) : ty tc =
  match place_expr_to_place pi with
  | Some pi -> var_env_lookup gamma pi
  | None -> Fail (PlaceExprNotAPlace pi)
let var_env_contains_place_expr (gamma : var_env) (pi : place_expr) : bool =
  let (root, _) = snd pi
  in match List.assoc_opt root gamma with
  | Some _ -> true
  | None -> false

let var_env_type_update (gamma : var_env) (pi : place) (ty : ty) : var_env tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some root_ty ->
    let* (ctx, _) = decompose root_ty path
    in Succ (replace_assoc gamma root (plug ty ctx))
  | None -> Fail (UnboundPlace pi)

let var_env_uninit_many (gamma : var_env) (vars : var list) : var_env =
  let work (entry : var * ty) : var * ty =
    if List.mem (fst entry) vars then (fst entry, (inferred, Uninit (snd entry))) else entry
  in List.map work gamma

let var_env_include (gamma : var_env) (x : var) (typ : ty) = List.cons (x, typ) gamma
let var_env_append (gamma1 : var_env) (gamma2 : var_env) = List.append gamma1 gamma2
let var_env_exclude (gamma : var_env) (x : var) = List.remove_assoc x gamma

(* find the root of a given place expr *)
let root_of (pi : place) : var = sndfst pi
(* find the path for the given place *)
let path_of (pi : place) : path = sndsnd pi

(* find the root of a given place expr *)
let expr_root_of (phi : place_expr) : var = sndfst phi
(* find the path for the given place_expr *)
let expr_path_of (phi : place_expr) : expr_path = sndsnd phi

(* is path2 a prefix of path1? *)
let rec is_prefix_of (path1 : path) (path2 : path) : bool =
  match (path1, path2) with
  | (_, []) -> true
  | ([], _) -> false
  | (Field f1 :: path1, Field f2 :: path2) -> if f1 = f2 then is_prefix_of path1 path2 else false
  | (Index i1 :: path1, Index i2 :: path2) -> if i1 = i2 then is_prefix_of path1 path2 else false
  | (_, _) -> false

(* is path2 a prefix of path1? *)
let rec is_expr_prefix_of (path1 : expr_path) (path2 : expr_path) : bool =
  match (path1, path2) with
  | (_, []) -> true
  | ([], _) -> false
  | (Field f1 :: path1, Field f2 :: path2) ->
    if f1 = f2 then is_expr_prefix_of path1 path2 else false
  | (Index i1 :: path1, Index i2 :: path2) ->
    if i1 = i2 then is_expr_prefix_of path1 path2 else false
  | (Deref :: path1, Deref :: path2) -> is_expr_prefix_of path1 path2
  | (_, _) -> false

let rec contains_prov (gamma : var_env) (prov : prov) : bool =
  let rec ty_contains (ty : ty) : bool =
    match snd ty with
    | Any | BaseTy _ | TyVar _ -> false
    | Ref (pv, _, ty) -> pv = prov || ty_contains ty
    | Fun (_, pvs, _, tys, gam, ret_ty) ->
      if not (List.mem prov pvs) then
        ty_contains ret_ty || tys_contains tys ||
        match gam with
        | Env gam -> contains_prov gam prov | EnvVar _ | EnvOf _ -> false
      else false
    | Uninit ty | Array (ty, _) | Slice ty -> ty_contains ty
    | Rec pairs -> tys_contains (List.map snd pairs)
    | Tup tys -> tys_contains tys
    | Struct (_, pvs, _, _) -> List.mem prov pvs
  and tys_contains (tys : ty list) : bool =
    List.exists ty_contains tys
  in List.exists (fun pair -> ty_contains (snd pair)) gamma

let envs_minus (ell : loan_env) (gamma : var_env) (pi : place) : (loan_env * var_env) tc =
  let rec loop (ty : ty option) (envs : loan_env * var_env) : (loan_env * var_env) tc =
    match ty with
    | Some (_, Ref (prov, _, ty)) ->
      let* (ell, gamma) = loop (Some ty) envs
      in let new_gamma = var_env_exclude gamma (sndfst pi)
      in if not (contains_prov new_gamma prov) then Succ (loan_env_exclude ell prov, new_gamma)
      else Succ (ell, new_gamma)
    | Some (_, Any) | Some (_, BaseTy _) | Some (_, TyVar _) | Some (_, Fun _)
    | Some (_, Struct _) -> Succ envs
    | Some (_, Uninit ty)
    | Some (_, Array (ty, _))
    | Some (_, Slice ty) -> loop (Some ty) envs
    | Some (_, Rec pairs) -> loops (List.map snd pairs) envs
    | Some (_, Tup tys) -> loops tys envs
    | None -> Succ envs
  and loops (tys : ty list) (envs : loan_env * var_env) =
    foldr loop (List.map (fun x -> Some x) tys) envs
  in let* opt = var_env_lookup_opt gamma pi
  in loop opt (ell, var_env_exclude gamma (sndfst pi))

let rec noncopyable (sigma : global_env) (typ : ty) : bool tc =
  match snd typ with
  | Any -> Succ false
  | BaseTy _ -> Succ false
  | TyVar _ -> Succ true
  | Uninit _ -> Succ true (* probably never ask this question anyway *)
  | Ref (_, Unique, _) -> Succ true
  | Ref (_, Shared, _) -> Succ false
  | Fun (_, _, _, _, _, _) -> Succ false
  | Array (typPrime, _) -> noncopyable sigma typPrime
  | Slice typPrime -> noncopyable sigma typPrime
  | Rec pairs ->
    let work (acc : bool tc) (pair : field * ty) : bool tc =
      let* res = acc
      in let* ty_noncopyable = noncopyable sigma (snd pair)
      in Succ (res || ty_noncopyable)
    in List.fold_left work (Succ false) pairs
  | Tup typs ->
    let work (acc : bool tc) (typ : ty) : bool tc =
      let* res = acc
      in let* ty_noncopyable = noncopyable sigma typ
      in Succ (res || ty_noncopyable)
    in List.fold_left work (Succ false) typs
  | Struct (name, _, _, _) ->
    match  global_env_find_struct sigma name with
    | Some (Rec (copyable, _, _, _, _)) | Some (Tup (copyable, _, _, _, _)) -> Succ (not copyable)
    | None -> Fail (UnknownStruct (fst typ, name))

let copyable (sigma : global_env) (typ : ty) : bool tc =
  let* res = noncopyable sigma typ
  in Succ (not res)

let valid_copy_impl (sigma : global_env) (def : struct_def) : unit tc =
  match def with
  | Rec (true, name, _, _, fields) ->
    let next_copyable (res : ty option) (typ : ty) : (ty option) tc =
      let* ty_copyable = copyable sigma typ
      in if (res == None) then
        if ty_copyable then Succ None
        else Succ res
      else Succ (Some typ)
    in (match foldl next_copyable None (List.map snd fields) with
    | Succ None -> Succ ()
    | Succ (Some ty) -> Fail (InvalidCopyImpl (name, ty))
    | Fail err -> Fail err)
  | Tup (true, name, _, _, tys) ->
    let next_copyable (res : ty option) (typ : ty) : (ty option) tc =
      let* ty_copyable = copyable sigma typ
      in if (res == None) then
        if ty_copyable then Succ None
        else Succ res
      else Succ (Some typ)
    in (match foldl next_copyable None tys with
    | Succ None -> Succ ()
    | Succ (Some ty) -> Fail (InvalidCopyImpl (name, ty))
    | Fail err -> Fail err)
  | Rec (false, _, _, _, _) | Tup (false, _, _, _, _) -> Succ ()

let rec free_provs_ty (ty : ty) : provs =
  match snd ty with
  | Any | BaseTy _ | TyVar _ -> []
  | Uninit ty -> free_provs_ty ty
  | Ref (prov, _, ty) -> List.cons prov (free_provs_ty ty)
  | Fun (_, provs, _, tys, _, ty) ->
    let free_in_tys = List.flatten (List.map free_provs_ty tys)
    in let free_in_ret = free_provs_ty ty
    in List.filter (fun prov -> not (List.mem prov provs)) (List.append free_in_tys free_in_ret)
  | Array (ty, _) | Slice ty -> free_provs_ty ty
  | Rec tys -> List.flatten (List.map (fun pair -> free_provs_ty (snd pair)) tys)
  | Tup tys -> List.flatten (List.map free_provs_ty tys)
  | Struct (_, provs, tys, _) -> List.flatten (List.cons provs (List.map free_provs_ty tys))
and free_provs (expr : expr) : provs =
  match snd expr with
  | Prim _ | Move _ | Fn _ | Abort _ | Ptr _ -> []
  | BinOp (_, e1, e2) -> List.append (free_provs e1) (free_provs e2)
  | Borrow (prov, _, _) -> [prov]
  | BorrowIdx (prov, _, _, e) -> List.cons prov (free_provs e)
  | BorrowSlice (prov, _, _, e1, e2) ->
    List.cons prov (List.append (free_provs e1) (free_provs e2))
  | LetProv (provs, e) ->
    List.filter (fun prov -> not (List.mem prov provs)) (free_provs e)
  | Let (_, ty, e1, e2) ->
    List.append (free_provs_ty ty) (List.append (free_provs e1) (free_provs e2))
  | Assign (_, e) -> free_provs e
  | Seq (e1, e2) -> List.append (free_provs e1) (free_provs e2)
  | Fun (provs, _, params, ret_ty, body) ->
    let free_in_params = List.flatten (List.map (fun pair -> free_provs_ty (snd pair)) params)
    in let free_in_ret =
      match ret_ty with
      | Some ty -> free_provs_ty ty
      | None -> []
    in let free_in_body = free_provs body
    in List.filter (fun prov -> not (List.mem prov provs))
                   (List.concat [free_in_params; free_in_ret; free_in_body])
  | App (e1, _, provs, tys, es) ->
    List.concat [free_provs e1; provs;
                 List.flatten (List.map free_provs_ty tys);
                 List.flatten (List.map free_provs es)]
  | Idx (_, e) -> free_provs e
  | Branch (e1, e2, e3) ->
    List.concat [free_provs e1; free_provs e2; free_provs e3]
  | While (e1, e2) | For (_, e1, e2) ->
    List.append (free_provs e1) (free_provs e2)
  | Tup es | Array es -> List.flatten (List.map free_provs es)
  | RecStruct (_, provs, _, es) ->
    List.flatten (provs :: List.map (fun x -> free_provs (snd x)) es)
  | TupStruct (_, provs, _, es) -> List.flatten (provs :: List.map free_provs es)

let free_vars_helper (expr : expr) (should_include : var -> bool tc) : vars tc =
   let rec free (expr : expr) : vars tc =
     match snd expr with
     | Prim _ | Fn _ | Abort _ -> Succ []
     | BinOp (_, e1, e2)
     | While (e1, e2)
     | Seq (e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in Succ (List.append free1 free2)
     | Move (_, (root, _))
     | Borrow (_, _, (_, (root, _)))
     | Ptr (_, (_, (root, _))) ->
       let* should_include = should_include root
       in if should_include then Succ [root] else Succ []
     | BorrowIdx (_, _, (_, (root, _)), e1)
     | Idx ((_, (root, _)), e1)
     | Assign ((_, (root, _)), e1) ->
       let* free1 = free e1
       in Succ (List.cons root free1)
     | BorrowSlice (_, _, (_, (root, _)), e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in let* should_include = should_include root
       in Succ (List.concat [if should_include then [root] else []; free1; free2])
     | LetProv (_, e) -> free e
     | Let (x, _, e1, e2)
     | For (x, e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in Succ (List.append free1 (List.filter ((<>) x) free2))
     | Fun _ -> Succ [] (* FIXME: actually implement *)
     | App (e1, _, _, _, exprs) ->
       let* frees = free_many exprs
       in let* free1 = free e1
       in Succ (List.append free1 frees)
     | Branch (e1, e2, e3) ->
       let* free1 = free e1
       in let* free2 = free e2
       in let* free3 = free e3
       in Succ (List.concat [free1; free2; free3])
     | Tup exprs | Array exprs -> free_many exprs
     | RecStruct _ | TupStruct _ -> Succ [] (* FIXME: implement *)
   and free_many (exprs : expr list) : vars tc =
     let next_free (expr : expr) (free_vars : var list) : vars tc =
       let* free = free expr
       in Succ (List.append free free_vars)
     in foldr next_free exprs []
   in free expr

let free_nc_vars (sigma : global_env) (gamma : var_env) (expr : expr) : vars tc =
  free_vars_helper expr
  (fun var ->
     match List.assoc_opt var gamma with
     | Some ty -> noncopyable sigma ty
     (* if it's not in gamma, that means it's local to the expression, thus isn't free *)
     | None -> Succ false)

let free_vars (expr : expr) : vars tc = free_vars_helper expr (fun _ -> Succ true)

let free_provs_var_env (gamma : var_env) : provs =
  List.flatten (List.map (fun x -> free_provs_ty (snd x)) gamma)
