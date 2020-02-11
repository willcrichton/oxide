open Syntax
open Edsl
open Meta
open Borrowck
open Util

let unify (loc : source_loc) (ell : loan_env) (ty1 : ty) (ty2 : ty) : (loan_env * ty) tc =
  let* ell1 = subtype Combine ell ty1 ty2
  in let* ell2 = subtype Combine ell ty2 ty1
  in if ell1 = ell2 then Succ (ell2, ty2)
  else Fail (LoanEnvMismatch (loc, ell1, ell2))

let unify_many (loc : source_loc) (ell : loan_env) (tys : ty list) : (loan_env * ty) tc =
  match tys with
  | [] -> Succ (ell, (loc, Any))
  | [ty] -> Succ (ell, ty)
  | ty :: tys ->
    foldl (fun (curr_ell, curr_ty) new_ty -> unify loc curr_ell curr_ty new_ty) (ell, ty) tys

let union (ell1 : loan_env) (ell2 : loan_env) : loan_env =
  let work (acc : loan_env) (pair : prov_var * loans) : loan_env =
    let (prov, loans) = pair
    in match loan_env_lookup_opt acc (dummy, prov) with
    | Some curr_loans ->
      loan_env_include (loan_env_exclude acc (dummy, prov))
        (dummy, prov) (list_union loans curr_loans)
    | None -> loan_env_include acc (dummy, prov) loans
  in let (prt1, (prt2, prt3)) = List.fold_left work ell1 (fst ell2)
  in (prt1, (list_union prt2 (sndfst ell2), list_union prt3 (sndsnd ell2)))

let intersect (envs1 : loan_env * var_env) (envs2 : loan_env * var_env) : loan_env * var_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in let ell = union ell1 ell2
  in let also_in_gamma2 (pair : var * ty) =
       let (x, ty) = pair
       in match List.assoc_opt x gamma2 with
       | Some ty2 -> ty == ty2 (* TODO: maybe unify, but then we're changing ell *)
       | None -> false
  in (ell, List.find_all also_in_gamma2 gamma1)

let var_env_diff (gam1 : var_env) (gam2 : var_env) : var_env =
  let not_in_gam2 (entry1 : var * ty) : bool =
    not (List.exists (fun entry2 -> fst entry2 = fst entry1) gam2)
  in List.filter not_in_gam2 gam1

let valid_prov (_ : tyvar_env) (ell : loan_env) (gamma : var_env) (prov : prov) : unit tc =
  (* FIXME: check tyvar_env_prov_mem, but then we need to add letprovs to programs in codegen *)
  if loan_env_mem ell prov then
    match loan_env_lookup_opt ell prov with
    | Some loans ->
      let invalid_loans = List.filter (not >> var_env_contains_place_expr gamma >> snd) loans
      in (match invalid_loans with
      | [] -> Succ ()
      | (omega, pi) :: _ -> Fail (InvalidLoan (omega, pi)))
    | None -> Fail (InvalidProv prov)
  else if loan_env_is_abs ell prov then Succ ()
  else Fail (InvalidProv prov)

let rec valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                   (ty : ty) : unit tc =
  let rec valid (ty : ty) : unit tc =
    match snd ty with
    | Any | BaseTy _ -> Succ ()
    | TyVar tyvar ->
      if tyvar_env_ty_mem tyvar delta then Succ ()
      else Fail (InvalidType ty)
    | Ref (prov, _, ty) ->
      let* () = valid_prov delta ell gamma prov
      in let* () = valid ty
      in let place_exprs = List.map snd (loan_env_lookup ell prov)
      in let check_ty (pi : place_expr) : unit tc =
        let* ty_root = var_env_lookup gamma (fst pi, (sndfst pi, []))
        in let* ty_pi = compute_ty ell ty_root (sndsnd pi)
        in if snd ty_pi = snd ty then Succ ()
        else Fail (TypeMismatch (ty, ty_pi))
      in for_each_rev check_ty place_exprs
    | Fun (evs, provs, tyvars, param_tys, gamma_c, ret_ty) ->
      let* () = valid_env gamma_c
      in let new_delta =
        delta |> tyvar_env_add_env_vars evs
              |> tyvar_env_add_provs provs
              |> tyvar_env_add_ty_vars tyvars
      in let* () = for_each_rev (valid_type sigma new_delta ell gamma) param_tys
      in valid_type sigma new_delta ell gamma ret_ty
    | Array (typ, n) ->
      if n >= 0 then valid typ
      else Fail (InvalidArrayLen (ty, n))
    | Uninit typ | Slice typ -> valid typ
    | Rec pairs -> valid_many (List.map snd pairs)
    | Tup tys -> valid_many tys
    | Struct _ -> Succ () (* TODO: use sigma *)
  and valid_many (tys : ty list) : unit tc = for_each_rev valid tys
  and valid_env (gamma : env) : unit tc =
    match gamma with
    | EnvVar ev ->
      if tyvar_env_env_var_mem ev delta then Succ ()
      else Fail (InvalidEnvVar (ev, ty))
    | Env gamma -> for_each_rev (fun (_, ty) -> valid ty) gamma
    | EnvOf var -> Fail (UnevaluatedEnvOf var)
  in valid ty

let valid_types (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
    (tys : ty list) : unit tc =
  for_each_rev (valid_type sigma delta ell gamma) tys

let type_of (prim : prim) : ty =
  (inferred, match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool)

(* flows closed environments forward in otherwise structurally the same types *)
let flow_closed_envs_forward (computed : ty) (annotated : ty) : ty tc =
  let rec flow (computed : ty) (annotated : ty) : ty tc =
    match (snd computed, snd annotated) with
    | (Any, Any)
    | (BaseTy _, BaseTy _)
    | (TyVar _, TyVar _) -> Succ annotated
    | (Ref (_, _, computed_inner), Ref (prov, omega, annotated_inner)) ->
      let* forward = flow computed_inner annotated_inner
      in Succ (fst annotated, Ref (prov, omega, forward))
    | (Fun (_, _, _, comp_tys, gamma_c, comp_ret), Fun (evs, provs, tyvars, ann_tys, _, ann_ret)) ->
      let* forward_tys = flow_many comp_tys ann_tys
      in let* forward_ret = flow comp_ret ann_ret
      in let fn_ty : prety = Fun (evs, provs, tyvars, forward_tys, gamma_c, forward_ret)
      in Succ (fst annotated, fn_ty)
    | (Array (computed_inner, _), Array (annotated_inner, len)) ->
      let* forward = flow computed_inner annotated_inner
      in let ty : prety = Array (forward, len)
      in Succ (fst annotated, ty)
    | (Slice computed_inner, Slice annotated_inner) ->
      let* forward = flow computed_inner annotated_inner
      in Succ (fst annotated, Slice forward)
    | (Rec comp_fields, Rec ann_fields) ->
      let flow_assoc (field, ann_ty) =
        let* forward = flow (List.assoc field comp_fields) ann_ty
        in Succ (field, forward)
      in let* forward_fields = map flow_assoc ann_fields
      in let ty : prety = Rec forward_fields
      in Succ (fst annotated, ty)
    | (Tup comp_tys, Tup ann_tys) ->
      let* forward_tys = flow_many comp_tys ann_tys
      in let ty : prety = Tup forward_tys
      in Succ (fst annotated, ty)
    | (Struct (_, _, comp_tys, comp_opt), Struct (name, provs, ann_tys, ann_opt)) ->
      let* forward_tys = flow_many comp_tys ann_tys
      in let* forward = flow (unwrap comp_opt) (unwrap ann_opt)
      in let ty : prety = Struct (name, provs, forward_tys, Some forward)
      in Succ (fst annotated, ty)
    | (Uninit computed_inner, Uninit annotated_inner) ->
      let* forward = flow computed_inner annotated_inner
      in Succ (fst annotated, Uninit forward)
    | _ -> Fail (TypeMismatch (annotated, computed))
  and flow_many (computed : ty list) (annotated : ty list) : ty list tc =
    let* combined_tys = combine_tys "flow_closed_envs_forward" computed annotated
    in map (fun (comp, ann) -> flow comp ann) combined_tys
  in flow computed annotated

let rec eval_env_of (gamma : var_env) (env : env) : env tc =
  match env with
  | EnvVar _ | Env _ -> Succ env
  | EnvOf var ->
    let* env = env_of var gamma
    in eval_env_of gamma env

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
               (expr : expr) : (ty * loan_env * var_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
             (expr : expr) : (ty * loan_env * var_env) tc =
    match snd expr with
    (* T-Unit, T-u32, T-True, T-False *)
    | Prim prim -> Succ (type_of prim, ell, gamma)
    (* binary operations *)
    | BinOp (op, e1, e2) ->
      (match binop_to_types op with
       | (Some lhs_ty, Some rhs_ty, out_ty) ->
         let* (t1, ell1, gamma1) = tc delta ell gamma e1
         in if (snd t1) = (snd lhs_ty) then
           let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
           in if (snd t2) = (snd rhs_ty) then
             let* (ellFinal, _) = unify (fst expr) ell2 t1 t2
             in Succ (out_ty, ellFinal, gamma2)
           else Fail (TypeMismatch (rhs_ty, t2))
         else Fail (TypeMismatch (lhs_ty, t1))
       | (None, None, out_ty) ->
         let* (t1, ell1, gamma1) = tc delta ell gamma e1
         in let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
         in let* (ellFinal, _) = unify (fst expr) ell2 t1 t2
         in Succ (out_ty, ellFinal, gamma2)
       | _ -> failwith "unreachable")
    (* T-Move and T-Copy *)
    | Move pi ->
      let* root_ty = var_env_lookup_expr_root gamma pi
      in let* unified_ty = expr_path_of pi |> compute_ty ell root_ty
      in let* copy = copyable sigma unified_ty
      in let omega = if copy then Shared else Unique
      in (match ownership_safe sigma ell gamma omega pi with
       | Succ (ty, [(Unique, pi)]) ->
         let* (ellPrime, gammaPrime) =
           match place_expr_to_place pi with
           | Some pi ->
             let* noncopy = noncopyable sigma ty
             in if is_init ty then
               if noncopy then
                 let* gammaPrime = var_env_type_update gamma pi (uninit ty)
                 in Succ (ell, gammaPrime)
               else Succ (ell, gamma)
             else Fail (PartiallyMoved (pi, ty))
           | None ->
             let* copy = copyable sigma ty
             in if copy then Succ (ell, gamma) else failwith "unreachable"
         in Succ (ty, ellPrime, gammaPrime)
       | Succ (ty, _) ->
         if copy then Succ (ty, ell, gamma)
         else failwith "unreachable"
       | Fail err -> Fail err)
    (* T-Borrow *)
    | Borrow (prov, omega, pi) ->
      let* (ty, loans) = ownership_safe sigma ell gamma omega pi
      in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
    (* T-BorrowIndex *)
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         let* (ty, loans) = ownership_safe sigma ell1 gamma1 omega pi
         in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    (* T-BorrowSlice *)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ ((_, BaseTy U32), ell2, gamma2) ->
            let* (ty, loans) = ownership_safe sigma ell2 gamma2 omega pi
            in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
          | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    (* T-IndexCopy *)
    | Idx (pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match ownership_safe sigma ell1 gamma1 Shared pi with
          | Succ ((_, Array (ty, _)), _) ->
            let* copy = copyable sigma ty
            in if copy then Succ (ty, ell1, gamma1)
            else Fail (CannotMove pi)
          | Succ (found, _) -> Fail (TypeMismatchArray found)
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    (* T-Seq *)
    | Seq (e1, e2) ->
      let* (_, ell1, gamma1) = tc delta ell gamma e1
      in tc delta ell1 gamma1 e2
    (* T-Branch *)
    | Branch (e1, e2, e3) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         let* (ty2, ell2, gamma2) = tc delta ell1 gamma1 e2
         in let* (ty3, ell3, gamma3) = tc delta ell1 gamma1 e3
         in let (ellPrime, gammaPrime) = intersect (ell2, gamma2) (ell3, gamma3)
         in let* (ellFinal, tyFinal) = unify (fst expr) ellPrime ty2 ty3
         in let* () = valid_type sigma delta ellFinal gammaPrime tyFinal
         in Succ (tyFinal, ellFinal, gammaPrime)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    (* T-LetProv *)
    | LetProv (new_provs, e) ->
      let to_loan_entry (var : prov) : prov_var * loans = (snd var, [])
      in let deltaPrime = tyvar_env_add_provs new_provs delta
      in let ellPrime = loan_env_append (provs_of delta |> List.map to_loan_entry, ([], [])) ell
      in tc deltaPrime ellPrime gamma e
    (* T-Let *)
    | Let (var, ann_ty, e1, e2) ->
      let* (ty1, ell1, gamma1) = tc delta ell gamma e1
      in let* () = valid_type sigma delta ell1 gamma ty1
      in let* ell1Prime = subtype Combine ell1 ty1 ann_ty
      in let* ann_ty = flow_closed_envs_forward ty1 ann_ty
      in let gamma1Prime = var_env_include gamma1 var ann_ty
      in let* (ty2, ell2, gamma2) = tc delta ell1Prime gamma1Prime e2
      in let* (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (fst expr, (var, []))
      in Succ (ty2, ell2Prime, gamma2Prime)
    (* T-Assign and T-AssignDeref *)
    | Assign (phi, e) ->
      let ell = kill_loans_for phi ell
      in let* (ty_old, _) = ownership_safe sigma ell gamma Unique phi
      in let* (ty_update, ell1, gamma1) = tc delta ell gamma e
      in let* ellPrime = subtype Override ell1 ty_update ty_old
      in (match place_expr_to_place phi with
       (* T-Assign *)
       | Some pi ->
         let* gammaPrime = var_env_type_update gamma1 pi ty_update
         in Succ ((inferred, BaseTy Unit), ellPrime, gammaPrime)
       (* T-AssignDeref *)
       | None -> Succ ((inferred, BaseTy Unit), ellPrime, gamma1))
    (* T-Abort *)
    | Abort _ -> Succ ((inferred, Any), ell, gamma)
    (* T-While *)
    | While (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         let* (_, ell2, gamma2) =  tc delta ell1 gamma1 e2
         in tc delta ell2 gamma2 e2
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    (* T-ForArray, T-ForSlice *)
    | For (var, e1, e2) ->
      (match tc delta ell gamma e1 with
       (* T-ForArray *)
       | Succ ((_, Array (elem_ty, _)), ell1, gamma1) ->
         let gamma1Prime = var_env_include gamma1 var elem_ty
         in let* (_, ell2, gamma2) = tc delta ell1 gamma1Prime e2
         in let* (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (fst expr, (var, []))
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
           else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
         else Fail (VarEnvMismatch (fst e2, gamma1, gamma2Prime))
       (* T-ForSlice *)
       | Succ ((_, Ref (prov, omega, (_, Slice elem_ty))), ell1, gamma1) ->
         let gamma1Prime = var_env_include gamma1 var (inferred, Ref (prov, omega, elem_ty))
         in let* (_, ell2, gamma2) = tc delta ell1 gamma1Prime e2
         in let* (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (fst expr, (var, []))
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
           else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
         else Fail (VarEnvMismatch (fst e2, gamma1, gamma2Prime))
       | Succ (found, _, _) -> Fail (TypeMismatchIterable found)
       | Fail err -> Fail err)
    (* T-Function *)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, evs, provs, tyvars, params, ret_ty, _, _) ->
         let fn_ty : ty = (inferred, Fun (evs, provs, tyvars, List.map snd params, Env [], ret_ty))
         in Succ (fn_ty, ell, gamma)
       | None ->
         (match List.assoc_opt fn gamma with
          (* T-Move for a closure *)
          | Some (_, Fun _) ->
            (match ownership_safe sigma ell gamma Unique (fst expr, (fn, [])) with
            | Succ (ty, [(Unique, _)]) ->
              let* gammaPrime = var_env_type_update gamma (fst expr, (fn, [])) (uninit ty)
              in Succ (ty, ell, gammaPrime)
            | Succ _ -> failwith "unreachable"
            | Fail err -> Fail err)
          | Some ((_, Uninit (_, Fun _)) as uninit_fn_ty) ->
            Fail (MovedFunction (expr, uninit_fn_ty))
          | Some ty -> Fail (TypeMismatchFunction ty)
          | None -> Fail (UnknownFunction (fst expr, fn))))
    (* T-Closure *)
    | Fun (provs, tyvars, params, opt_ret_ty, body) ->
      let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gammaPrime = List.fold_left var_include_fold gamma params
      in let deltaPrime = delta |> tyvar_env_add_provs provs |> tyvar_env_add_ty_vars tyvars
      in let ellPrime = loan_env_bindall ell provs
      in let* (ret_ty, _, _) = tc deltaPrime ellPrime gammaPrime body
      in let* free_vars = free_vars body
      in let free_vars = List.filter (fun var -> not (List.mem_assoc var params)) free_vars
      in let* moved_vars = free_nc_vars sigma gamma body
      in let gamma_c = List.map (fun var -> (var, List.assoc var gamma)) free_vars
      in let gammaPrime = var_env_uninit_many gamma moved_vars
      in let fn_ty (ret_ty : ty) : ty =
           (inferred, Fun ([], provs, tyvars, List.map snd params, Env gamma_c, ret_ty))
      in (match opt_ret_ty with
          | Some ann_ret_ty ->
            let* ellFinal = subtype Combine ell ret_ty ann_ret_ty
            in Succ (fn_ty ann_ret_ty, ellFinal, gammaPrime)
          | None -> Succ (fn_ty ret_ty, ell, gammaPrime))
    (* T-App *)
    | App (fn, envs, new_provs, new_tys, args) ->
      (match tc delta ell gamma fn with
       | Succ ((_, Fun (evs, provs, tyvars, params, _, ret_ty)), ellF, gammaF) ->
         let* (arg_tys, ellN, gammaN) = tc_many delta ellF gammaF args
         in let* evaled_envs = map (eval_env_of gammaF) envs
         in let* env_sub = combine_evs "T-App" evaled_envs evs
         in let* prov_sub = combine_prov "T-App" new_provs provs
         in let* ty_sub = combine_ty "T-App" new_tys tyvars
         in let do_sub : ty -> ty =
           subst_many_prov prov_sub >> subst_many_env_var env_sub >> subst_many ty_sub
         in let new_params = List.map do_sub params
         in let* ty_pairs = combine_tys "T-App" new_params arg_tys
         in let types_mismatch ((expected, found) : ty * ty) : bool tc =
           match subtype Combine ell found expected with
           | Succ _ -> Succ false
           | Fail (UnificationFailed _) -> Succ true
           | Fail err -> Fail err
         in let* type_mismatches = find types_mismatch ty_pairs
         in (match type_mismatches with
             | None ->
               let new_ret_ty = do_sub ret_ty
               in let* () = valid_type sigma delta ellN gammaN new_ret_ty
               in Succ (new_ret_ty, ellN, gammaN)
             | Some (expected, found) -> Fail (TypeMismatch (expected, found)))
       | Succ ((_, Uninit (_, Fun _) as uninit_fn_ty), _, _) ->
         Fail (MovedFunction (fn, uninit_fn_ty))
       | Succ (found, _, _) -> Fail (TypeMismatchFunction found)
       | Fail err -> Fail err)
    (* T-Tuple *)
    | Tup exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let final_ty : ty = (inferred, Tup tys)
      in Succ (final_ty, ellPrime, gammaPrime)
    (* T-Array *)
    | Array exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let* (ellFinal, unified_ty) = unify_many (fst expr) ellPrime tys
      in let final_ty : ty = (inferred, Array (unified_ty, List.length tys))
      in Succ (final_ty, ellFinal, gammaPrime)
    (* T-RecordStruct *)
    | RecStruct (name, provs, tys, fields) ->
      (match global_env_find_struct sigma name with
       | Some (Rec (_, _, dfn_provs, tyvars, dfn_fields)) ->
         let fields_sorted = List.sort (fun x y -> compare (fst x) (fst y)) fields
         in let dfn_fields_sorted = List.sort (fun x y -> compare (fst x) (fst y)) dfn_fields
         in let exprs = List.map snd fields_sorted
         in let* prov_sub = combine_prov "T-RecStruct" provs dfn_provs
         in let* ty_sub = combine_ty "T-RecStruct" tys tyvars
         in let do_sub : ty -> ty = subst_many_prov prov_sub >> subst_many ty_sub
         in let expected_fields = List.map (fun (f, ty) -> (f, do_sub ty)) dfn_fields_sorted
         in let expected_tys = List.map snd expected_fields
         in let* pairs = combine_expr "T-RecStruct" exprs expected_tys
         in let tc_exp ((ell, gamma) : loan_env * var_env) (p : expr * ty) =
           let (expr, expected_ty) = p
           in let* (found_ty, ell_prime, gamma_prime) = tc delta ell gamma expr
           in let* ell_final = subtype Combine ell_prime found_ty expected_ty
           in Succ (ell_final, gamma_prime)
         in let* (ell_prime, gamma_prime) = foldl tc_exp (ell, gamma) pairs
         in let tagged_ty : ty option = Some (inferred, Rec expected_fields)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), ell_prime, gamma_prime)
       | Some (Tup _) -> Fail (WrongStructConstructor (fst expr, name, Rec))
       | None -> Fail (UnknownStruct (fst expr, name)))
    (* T-TupleStruct *)
    | TupStruct (name, provs, tys, exprs) ->
      (match global_env_find_struct sigma name with
       | Some (Tup (_, _, dfn_provs, tyvars, dfn_tys)) ->
         let* prov_sub = combine_prov "T-TupStruct" provs dfn_provs
         in let* ty_sub = combine_ty "T-TupStruct" tys tyvars
         in let do_sub : ty -> ty = subst_many_prov prov_sub >> subst_many ty_sub
         in let expected_tys = List.map do_sub dfn_tys
         in let* pairs = combine_expr "T-TupStruct" exprs expected_tys
         in let tc_exp ((ell, gamma) : (loan_env * var_env)) (p : expr * ty) =
           let (expr, expected_ty) = p
           in let* (found_ty, ell_prime, gamma_prime) = tc delta ell gamma expr
           in let* ell_final = subtype Combine ell_prime found_ty expected_ty
           in Succ (ell_final, gamma_prime)
         in let* (ell_prime, gamma_prime) = foldl tc_exp (ell, gamma) pairs
         in let tagged_ty : ty option = Some (inferred, Tup dfn_tys)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), ell_prime, gamma_prime)
       | Some (Rec _) -> Fail (WrongStructConstructor (fst expr, name, Tup))
       | None ->
         if global_env_find_struct sigma name == None then Fail (UnknownStruct (fst expr, name))
         else Fail (WrongStructConstructor (fst expr, name, Tup)))
    (* T-Pointer *)
    | Ptr _ -> failwith "unimplemented: T-Pointer"
  and tc_many (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
      (exprs : expr list) : (ty list * loan_env * var_env) tc =
    let tc_next (e : expr) ((curr_tys, curr_ell, curr_gamma) : ty list * loan_env * var_env) =
      let* (ty, ellPrime, gammaPrime) = tc delta curr_ell curr_gamma e
      in Succ (List.cons ty curr_tys, ellPrime, gammaPrime)
    in foldr tc_next exprs ([], ell, gamma)
  in tc delta ell gamma expr

(* populate the tagged section of struct types based on the global environment *)
let struct_to_tagged (sigma : global_env) : global_env tc =
  let rec do_expr (ctx : struct_var list) (expr : expr) : expr tc =
    let (loc, expr) = expr
    in match expr with
    | Prim _ | Move _ | Borrow _ | Fn _ | Abort _ | Ptr _ -> Succ (loc, expr)
    | BinOp (op, e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, BinOp (op, e1, e2))
    | BorrowIdx (prov, omega, p, e) ->
      let* e = do_expr ctx e
      in Succ (loc, BorrowIdx (prov, omega, p, e))
    | BorrowSlice (prov, omega, p, e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, BorrowSlice (prov, omega, p, e1, e2))
    | LetProv (provs, e) ->
      let* e = do_expr ctx e
      in Succ (loc, LetProv (provs, e))
    | Let (x, ty, e1, e2) ->
      let* ty = do_ty ctx ty
      in let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, Let (x, ty, e1, e2))
    | Assign (p, e) ->
      let* e = do_expr ctx e
      in Succ (loc, Assign (p, e))
    | Seq (e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, Seq (e1, e2))
    | Fun (provs, tyvars, params, res, body) ->
      let* params = do_params ctx params
      in let* res = do_opt_ty ctx res
      in let* body = do_expr ctx body
      in let fn : preexpr = Fun (provs, tyvars, params, res, body)
      in Succ (loc, fn)
    | App (fn, envs, provs, tys, args) ->
      let* fn = do_expr ctx fn
      in let* tys = do_tys ctx tys
      in let* args = do_exprs ctx args
      in Succ (loc, App (fn, envs, provs, tys, args))
    | Idx (p, e) ->
      let* e = do_expr ctx e
      in Succ (loc, Idx (p, e))
    | Branch (e1, e2, e3) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in let* e3 = do_expr ctx e3
      in Succ (loc, Branch (e1, e2, e3))
    | While (e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, While (e1, e2))
    | For (x, e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, For (x, e1, e2))
    | Tup exprs ->
      let* exprs = do_exprs ctx exprs
      in let tup : preexpr = Tup exprs
      in Succ (loc, tup)
    | Array exprs ->
      let* exprs = do_exprs ctx exprs
      in let array : preexpr = Tup exprs
      in Succ (loc, array)
    | RecStruct (sn, provs, tys, args) ->
      let* tys = do_tys ctx tys
      in let* args = do_args ctx args
      in Succ (loc, RecStruct (sn, provs, tys, args))
    | TupStruct (sn, provs, tys, exprs) ->
      let* tys = do_tys ctx tys
      in let* exprs = do_exprs ctx exprs
      in Succ (loc, TupStruct (sn, provs, tys, exprs))
  and do_ty (ctx : struct_var list) (ty : ty) : ty tc =
    let (loc, ty) = ty
    in match ty with
    (* the interesting case: encountering a struct type *)
    | Struct (sn, provs, tys, None) ->
      let* tys = do_tys ctx tys
      in if List.mem sn ctx then Succ (loc, Struct (sn, provs, tys, None))
      else (match global_env_find_struct sigma sn with
      | Some (Rec (_, _, dfn_provs, tyvars, fields)) ->
        let fields_sorted = List.sort (fun x y -> compare (fst x) (fst y)) fields
        in let* prov_sub = combine_prov "T-RecStruct" provs dfn_provs
        in let* ty_sub = combine_ty "T-RecStruct" tys tyvars
        in let do_sub : ty -> ty = subst_many_prov prov_sub >> subst_many ty_sub
        in let fields_fixed = List.map (fun (f, ty) -> (f, do_sub ty)) fields_sorted
        in let* fields = do_params (List.cons sn ctx) fields_fixed
        in let ty : ty = (inferred, Rec fields)
        in Succ (loc, Struct (sn, provs, tys, Some ty))
      | Some (Tup (_, _, dfn_provs, tyvars, tup_tys)) ->
        let* prov_sub = combine_prov "T-TupStruct" provs dfn_provs
        in let* ty_sub = combine_ty "T-TupStruct" tys tyvars
        in let do_sub : ty -> ty = subst_many_prov prov_sub >> subst_many ty_sub
        in let tup_tys = List.map do_sub tup_tys
        in let* tup_tys = do_tys ctx tup_tys
        in let ty : ty = (inferred, Tup tup_tys)
        in Succ (loc, Struct (sn, provs, tys, Some ty))
      | None -> Fail (UnknownStruct (loc, sn)))
    (* structural cases *)
    | Any | BaseTy _ | TyVar _ -> Succ (loc, ty)
    | Ref (prov, omega, ty) ->
      let* ty = do_ty ctx ty
      in Succ (loc, Ref (prov, omega, ty))
    | Fun (evs, provs, tyvars, tys, gamma, ty) ->
      (* should we transform gamma here? maybe not necessary *)
      let* tys = do_tys ctx tys
      in let* ty = do_ty ctx ty
      in let fn : prety = Fun (evs, provs, tyvars, tys, gamma, ty)
      in Succ (loc, fn)
    | Array (ty, n) ->
      let* ty = do_ty ctx ty
      in let array : prety = Array (ty, n)
      in Succ (loc, array)
    | Slice ty ->
      let* ty = do_ty ctx ty
      in let slice : prety = Slice ty
      in Succ (loc, slice)
    | Rec fields ->
      let* fields = do_params ctx fields
      in let record : prety = Rec fields
      in Succ (loc, record)
    | Tup tys ->
      let* tys = do_tys ctx tys
      in let tup : prety = Tup tys
      in Succ (loc, tup)
    | Struct (sn, provs, tys, Some tagged_ty) ->
      let* tys = do_tys ctx tys
      in let* tagged_ty = do_ty ctx tagged_ty
      in Succ (loc, Struct (sn, provs, tys, Some tagged_ty))
    | Uninit ty ->
      let* ty = do_ty ctx ty
      in let uninit : prety = Uninit ty
      in Succ (loc, uninit)
  and do_exprs (ctx : struct_var list) (exprs : expr list) : expr list tc =
    let do_lifted (expr : expr) (exprs : expr list) : expr list tc =
      let* expr = do_expr ctx expr
      in Succ (List.cons expr exprs)
    in foldr do_lifted exprs []
  and do_args (ctx : struct_var list) (args : (field * expr) list) : (field * expr) list tc =
    let do_lifted (arg : field * expr) (so_far : (field * expr) list) : (field * expr) list tc =
      let* expr = do_expr ctx (snd arg)
      in Succ (List.cons (fst arg, expr) so_far)
    in foldr do_lifted args []
  and do_tys (ctx : struct_var list) (tys : ty list) : ty list tc =
    let do_lifted (ty : ty) (tys : ty list) : ty list tc =
      let* ty = do_ty ctx ty
      in Succ (List.cons ty tys)
    in foldr do_lifted tys []
  and do_opt_ty (ctx : struct_var list) (ty : ty option) : ty option tc =
    match ty with
    | Some ty -> let* ty = do_ty ctx ty in Succ (Some ty)
    | None -> Succ None
  and do_params (ctx : struct_var list) (params : (var * ty) list) : (var * ty) list tc =
    let do_lifted (param : var * ty) (so_far : (var * ty) list) : (var * ty) list tc =
      let* ty = do_ty ctx (snd param)
      in Succ (List.cons (fst param, ty) so_far)
    in foldr do_lifted params []
  and do_global_entry (ctx : struct_var list) (entry : global_entry) : global_entry tc =
    match entry with
    | FnDef (fn, evs, provs, tyvars, params, ret_ty, bounds, body) ->
      let* params = do_params ctx params
      in let* ret_ty = do_ty ctx ret_ty
      in let* body = do_expr ctx body
      in Succ (FnDef (fn, evs, provs, tyvars, params, ret_ty, bounds, body))
    | RecStructDef (copyable, sn, provs, tyvars, fields) ->
      let* fields = do_params ctx fields
      in Succ (RecStructDef (copyable, sn, provs, tyvars, fields))
    | TupStructDef (copyable, sn, provs, tyvars, tys) ->
      let* tys = do_tys ctx tys
      in Succ (TupStructDef (copyable, sn, provs, tyvars, tys))
  and do_global_entries (ctx : struct_var list) (entries : global_env) : global_env tc =
    let do_lifted (entry : global_entry) (entries : global_env) : global_env tc =
      let* entry = do_global_entry ctx entry
      in Succ (List.cons entry entries)
    in foldr do_lifted entries []
  in do_global_entries [] sigma

(* produces an error if the loans in the given type are found in the parameter list *)
let find_refs_to_params (ell : loan_env) (ty : ty) (params : (var * ty) list) : unit tc =
  let place_in_params (pi : place) : bool = List.mem_assoc (root_of pi) params
  in let rec impl (ty : ty) : unit tc =
    match snd ty with
    | Any | BaseTy _ | TyVar _ -> Succ ()
    | Ref (prov, _, ty) ->
      let loans = loan_env_lookup ell prov
      in let borrow_loans = loans |> List.map snd |> List.filter_map place_expr_to_place
      in let param_loans = borrow_loans |> List.filter place_in_params
      in if is_empty param_loans then impl ty
      else Fail (NoReferenceToParameter (List.hd param_loans))
    | Fun _ -> Succ ()
    | Array (ty, _) | Slice ty -> impl ty
    | Rec fields -> fields |> List.map snd |> for_each_rev impl
    | Tup tys -> for_each_rev impl tys
    | Struct (_, _, _, Some ty) -> impl ty
    | Struct _ | Uninit _ -> Succ ()
  in impl ty

let wf_global_env (sigma : global_env) : unit tc =
  let* sigma = struct_to_tagged (List.cons drop sigma)
  in let valid_global_entry (entry : global_entry) : unit tc =
    match entry with
    (* WF-FunctionDef*)
    | FnDef (_, evs, provs, tyvars, params, ret_ty, bounds, body) ->
      let not_in_provs (prov : prov) : bool =
        provs |> List.map snd |> List.mem (snd prov) |> not
      in let free_provs = (* this lets us infer provenances not bound in letprov *)
         free_provs body |> List.filter not_in_provs
      in let delta : tyvar_env = (evs, List.append provs free_provs, tyvars)
      in let ell = (List.map (fun p -> (snd p, [])) free_provs, (List.map snd provs, []))
      in let ell = List.fold_left (fun ell (prov1, prov2) -> loan_env_add_abs_sub ell prov1 prov2)
                                  ell bounds
      in let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gamma = List.fold_left var_include_fold [] params
      in let* (output_ty, ellPrime, gammaPrime) = type_check sigma delta ell gamma body
      in (match valid_type sigma delta ellPrime gammaPrime output_ty with
      | Succ () ->
        (* find_refs_to_params corresponds to the return type validity: WF-ReturnRef *)
        let* () = find_refs_to_params ellPrime output_ty params
        in let* _ = subtype Combine ellPrime output_ty ret_ty
        in Succ ()
      (* this is caused by a provenance being killed by its loans dropping out of scope *)
      (* in other words: references to temporaries cause an InvalidReturnType *)
      | Fail (InvalidProv prov) -> Fail (InvalidReturnType (output_ty, prov))
      | Fail err -> Fail err)
    (* T-RecordStructDef *)
    | RecStructDef (_, name, provs, tyvars, fields) ->
      let delta : tyvar_env = ([], provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let* () = valid_copy_impl sigma (unwrap (global_env_find_struct sigma name))
      in let* () = valid_types sigma delta ell empty_gamma (List.map snd fields)
      in let find_dup (pair : field * ty)
                      (acc : (field * ty) list * ((field * ty) * (field * ty)) option) =
        let (acc_lst, acc_opt) = acc
        in if List.mem_assoc (fst pair) acc_lst then
          (acc_lst, Some (pair, (fst pair, List.assoc (fst pair) acc_lst)))
        else (List.cons pair acc_lst, acc_opt)
      in (match List.fold_right find_dup fields ([], None) with
          | (_, None) -> Succ ()
          | (_, Some (p1, p2)) -> Fail (DuplicateFieldsInStructDef (name, p1, p2)))
    (* T-TupleStructDef *)
    | TupStructDef (_, name, provs, tyvars, tys) ->
      let delta : tyvar_env = ([], provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let* () = valid_copy_impl sigma (unwrap (global_env_find_struct sigma name))
      in let* () = valid_types sigma delta ell empty_gamma tys
      in Succ ()
  in for_each sigma valid_global_entry
