open Oxide.Edsl
open Oxide.Borrowck
open Oxide.Typeck
open Oxide.Meta
open Oxide.Syntax
open Oxide.Util

type node_id = int [@@deriving show]

let opt_or_else o1 f = match o1 with Some _ -> o1 | None -> f ()

let rec children (_, e) =
  match e with
  | Prim _ | Borrow _ -> []
  | Let (_, _, e1, e2) -> [ e1; e2 ]
  | Seq (e1, e2) -> [ e1; e2 ]
  | Assign (_, e) -> [ e ]
  | App (_, _, _, _, args) -> args
  | Branch (e1, e2, e3) -> [ e1; e2; e3 ]
  | _ -> raise (Failure (Format.sprintf "children: %s" (show_preexpr e)))

let find_loc (l : source_loc) (e : expr) : preexpr =
  let rec aux ((l', _) as e) =
    if l = l' then Some e
    else
      List.fold_left
        (fun opt arg -> opt_or_else opt (fun _ -> aux arg))
        None (children e)
  in
  aux e |> Option.get |> fun (_, e) -> e

let fmt_owned (o : owned) : string =
  match o with Shared -> "shrd" | Unique -> "uniq"

let fmt_place ((_, (x, path)) : place_expr) : string =
  List.fold_left
    (fun acc part ->
      match part with
      | Field f -> Format.sprintf "%s.%s" acc f
      | Index i -> Format.sprintf "%s[%d]" acc i
      | Deref -> Format.sprintf "(*%s)" acc)
    x path

let rec fmt_ty ((_, tau) : ty) : string =
  match tau with
  | BaseTy base -> (
    match base with Bool -> "bool" | U32 -> "u32" | Unit -> "unit" )
  | Ref ((_, p), o, tau) ->
    Format.sprintf "&%s %s %s" p (fmt_owned o) (fmt_ty tau)

let rec fmt_expr ((_, e) : expr) : string =
  match e with
  | Prim v -> (
    match v with
    | Unit -> "()"
    | Num n -> Format.sprintf "%d" n
    | True -> "true"
    | False -> "false" )
  | Borrow ((_, prov), o, p) ->
    Format.sprintf "&%s %s %s" prov (fmt_owned o) (fmt_place p)
  | Let (x, tau, e1, e2) ->
    Format.sprintf "let %s : %s = %s; %s" x (fmt_ty tau) (fmt_expr e1)
      (fmt_expr e2)
  | Seq (e1, e2) -> Format.sprintf "%s; %s" (fmt_expr e1) (fmt_expr e2)
  | Assign (p, e) -> Format.sprintf "%s = %s" (fmt_place p) (fmt_expr e)
  | App (f, _, _, _, args) ->
    Format.sprintf "%s(%s)" (fmt_expr f)
      (String.concat ", " (List.map fmt_expr args))
  | Move p -> fmt_place p
  | Fn f -> f
  | Branch (e1, e2, e3) ->
    Format.sprintf "if %s { %s } else { %s }" (fmt_expr e1) (fmt_expr e2)
      (fmt_expr e3)
  | _ -> raise (Failure (Format.sprintf "fmt_expr: %s" (show_preexpr e)))

module SliceEnv = struct
  type slice = source_loc list [@@deriving show]

  type t = (preplace_expr * slice) list [@@deriving show]

  let global_expr = ref unit

  let make (body : expr) : t =
    global_expr := body;
    []

  let fmt (t : t) : string =
    Format.sprintf "[%s]"
      (String.concat ", "
         (List.map
            (fun (p, s) ->
              let s =
                String.concat ", "
                  (List.map
                     (fun loc -> fmt_expr (loc, find_loc loc !global_expr))
                     s)
              in
              Format.sprintf "%s: {%s}" (fmt_place (static, p)) s)
            t))

  let lookup (t : t) ((_, p) : place_expr) : slice =
    List.find_opt (fun (p', _) -> p = p') t
    |> Option.map (fun (_, slice) -> slice)
    |> Option.value ~default:[]

  let insert (t : t) ((_, p) : place_expr) (s : slice) : t =
    match List.find_opt (fun (p', _) -> p = p') t with
    | Some (_, s') -> replace_assoc t p (list_union s s')
    | None -> (p, s) :: t

  let minus (l : t) (r : t) : t =
    List.map
      (fun (p, s_l) ->
        let s_r = lookup r (static, p) in
        (p, List.filter (fun loc -> not (List.mem loc s_r)) s_l))
      l

  let expr_deps (t : t) ((loc, e) : expr) : slice =
    let transitive =
      match e with
      | Prim _ -> []
      | Move p -> lookup t p
      | Borrow (_, _, p) -> lookup t p
      | _ -> raise (Failure (Format.sprintf "expr_deps: %s" (show_preexpr e)))
    in
    uniq_cons loc transitive

  let places (t : t) : preplace_expr list = List.map (fun (p, _) -> p) t
end

let type_check (slice_env : SliceEnv.t) (sigma : global_env) (delta : tyvar_env)
    (gamma : var_env) (expr : expr) : (ty * var_env * SliceEnv.t) tc =
  let rec tc (slice_env : SliceEnv.t) (delta : tyvar_env) (gamma : var_env)
      (expr : expr) : (ty * var_env * SliceEnv.t) tc =
    (* Format.printf "tc: %s\n" (fmt_expr expr); *)
    match snd expr with
    (* T-Unit, T-u32, T-True, T-False *)
    | Prim prim -> Succ (type_of prim, gamma, slice_env)
    (* binary operations *)
    | BinOp (op, e1, e2) -> (
      match binop_to_types op with
      | Some lhs_ty, Some rhs_ty, out_ty ->
        let* t1, gamma1, slice_env1 = tc slice_env delta gamma e1 in
        if ty_eq t1 lhs_ty then
          let* t2, gamma2, slice_env2 = tc slice_env1 delta gamma1 e2 in
          if ty_eq t2 rhs_ty then
            let* gammaFinal, _ = unify (fst expr) delta gamma2 t1 t2 in
            Succ (out_ty, gammaFinal, slice_env2)
          else TypeMismatch (rhs_ty, t2) |> fail
        else TypeMismatch (lhs_ty, t1) |> fail
      | None, None, out_ty ->
        let* t1, gamma1, slice_env1 = tc slice_env delta gamma e1 in
        let* t2, gamma2, slice_env2 = tc slice_env1 delta gamma1 e2 in
        let* gammaFinal, _ = unify (fst expr) delta gamma2 t1 t2 in
        Succ (out_ty, gammaFinal, slice_env2)
      | _ -> failwith "T-BinOp: unreachable" )
    (* T-Move and T-Copy *)
    | Move phi -> (
      (* we compute an initial type to determine whether we're in Move or Copy *)
      let* computed_ty = compute_ty delta gamma phi in
      let* copy = copyable sigma computed_ty in
      let omega =
        if copy then Shared else Unique
        (* but we recompute the type with the right context to do permissions checking *)
      in
      let* ty = compute_ty_in omega delta gamma phi in
      match ownership_safe sigma delta gamma omega phi with
      | Succ [ (Unique, pi) ] ->
        let* gammaPrime =
          match place_expr_to_place pi with
          | Some pi ->
            let* noncopy = noncopyable sigma ty in
            if is_init ty then
              if noncopy then
                let* gammaPrime = var_env_uninit gamma ty pi in
                Succ gammaPrime
              else Succ gamma
            else PartiallyMoved (pi, ty) |> fail
          | None ->
            let* copy = copyable sigma ty in
            if copy then Succ gamma else failwith "T-Move: unreachable"
        in
        Succ (ty, gammaPrime, slice_env)
      | Succ _ ->
        if copy then Succ (ty, gamma, slice_env)
        else failwith "T-Copy: unreachable"
      | Fail err -> Fail err )
    (* T-Borrow *)
    | Borrow (prov, omega, pi) ->
      let* loans = ownership_safe sigma delta gamma omega pi in
      let* ty = compute_ty_in omega delta gamma pi in
      if tyvar_env_prov_mem delta prov then
        CannotBorrowIntoAbstractProvenance prov |> fail
      else if prov |> loan_env_lookup gamma |> non_empty then
        CannotBorrowIntoInUseProvenance prov |> fail
      else
        let* updated_gamma = loan_env_prov_update prov loans gamma in
        Succ ((inferred, Ref (prov, omega, ty)), updated_gamma, slice_env)
      (* T-Seq *)
    | Seq (e1, e2) ->
      let* _, gamma1, slice_env1 = tc slice_env delta gamma e1 in
      let still_used_provs = used_provs gamma1 in
      let* gamma1Prime = clear_unused_provenances still_used_provs gamma1 in
      tc slice_env1 delta gamma1Prime e2
    (* T-Branch *)
    | Branch (e1, e2, e3) -> (
      match tc slice_env delta gamma e1 with
      | Succ ((_, BaseTy Bool), gamma1, slice_env1) ->
        let* ty2, gamma2, slice_env2 = tc slice_env1 delta gamma1 e2 in
        let* ty3, gamma3, slice_env3 = tc slice_env2 delta gamma1 e3 in
        let gammaPrime = union gamma2 gamma3 in
        let* gammaFinal, tyFinal = unify (fst expr) delta gammaPrime ty2 ty3 in
        let* () = valid_type sigma delta gammaFinal tyFinal in

        let deps = SliceEnv.expr_deps slice_env3 e1 in
        let slice_env3prime =
          List.fold_left
            (fun se p ->
              let p = (static, p) in
              SliceEnv.insert se p (list_union (SliceEnv.lookup se p) deps))
            slice_env3
            (SliceEnv.places (SliceEnv.minus slice_env3 slice_env1))
        in

        Succ (tyFinal, gammaFinal, slice_env3prime)
      | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy Bool), found) |> fail
      | Fail err -> Fail err )
    (* T-Let *)
    | Let (var, ann_ty, e1, e2) ->
      let* ty1, gamma1, slice_env1 = tc slice_env delta gamma e1 in
      let* () = valid_type sigma delta gamma1 ty1 in
      let* gamma1Prime = subtype Combine delta gamma1 ty1 ann_ty in
      let* ann_ty = flow_closed_envs_forward ty1 ann_ty in
      let gamma1Prime = var_env_include gamma1Prime var ann_ty in
      let still_used = used_provs gamma1Prime in
      let* gamma1Prime = gamma1Prime |> clear_unused_provenances still_used in
      let slice_env1Prime =
        SliceEnv.insert slice_env1 (Oxide.Edsl.var var)
          (SliceEnv.expr_deps slice_env1 e1)
      in
      let* ty2, gamma2, slice_env2 = tc slice_env1Prime delta gamma1Prime e2 in
      let* gamma2Prime = var |> var_to_place |> var_env_uninit gamma2 ty2 in
      let still_used =
        List.concat [ used_provs gamma2Prime; provs_used_in_ty ty2 ]
      in
      let* gamma2Prime =
        gamma2Prime |> clear_unused_provenances still_used >>= (succ >> shift)
      in
      let* () = ty_valid_before_after sigma delta ty2 gamma2 gamma2Prime in

      Succ (ty2, gamma2Prime, slice_env2)
    (* T-Assign and T-AssignDeref *)
    | Assign (phi, e) -> (
      let gamma = kill_loans_for phi gamma in
      let* loans = ownership_safe sigma delta gamma Unique phi in
      let* ty_old = compute_ty_in Unique delta gamma phi in
      let* ty_update, gamma1, slice_env1 = tc slice_env delta gamma e in
      let* gammaPrime = subtype Override delta gamma1 ty_update ty_old in

      let deps = SliceEnv.expr_deps slice_env1 e in
      let mutated = phi :: List.map (fun (_, p) -> p) loans in
      let slice_env2 =
        List.fold_left
          (fun acc p -> SliceEnv.insert acc p deps)
          slice_env1 mutated
      in

      match place_expr_to_place phi with
      (* T-Assign *)
      | Some pi ->
        let* gammaPrime = gammaPrime |> var_env_type_update pi ty_update in
        Succ ((inferred, BaseTy Unit), gammaPrime, slice_env2)
      (* T-AssignDeref *)
      | None -> Succ ((inferred, BaseTy Unit), gammaPrime, slice_env2)
      (* T-Function *) )
    | Fn fn -> (
      match global_env_find_fn sigma fn with
      | Some (_, evs, provs, tyvars, params, ret_ty, bounds, _) ->
        let fn_ty : ty =
          ( inferred,
            Fun (evs, provs, tyvars, List.map snd params, Env [], ret_ty, bounds)
          )
        in
        Succ (fn_ty, gamma, slice_env)
      | None -> (
        match gamma |> stack_to_bindings |> List.assoc_opt fn with
        (* T-Move for a closure *)
        | Some (_, Fun _) -> (
          match
            ownership_safe sigma delta gamma Unique (fst expr, (fn, []))
          with
          | Succ [ (Unique, _) ] ->
            let* ty = compute_ty_in Unique delta gamma (fst expr, (fn, [])) in
            let* closure_copyable = copyable sigma ty in
            if closure_copyable then Succ (ty, gamma, slice_env)
            else
              let* gammaPrime =
                gamma |> var_env_type_update (fst expr, (fn, [])) (uninit ty)
              in
              Succ (ty, gammaPrime, slice_env)
          | Succ _ -> failwith "T-Move as T-Function: unreachable"
          | Fail err -> Fail err )
        | Some ((_, Uninit (_, Fun _)) as uninit_fn_ty) ->
          MovedFunction (expr, uninit_fn_ty) |> fail
        | Some (_, Ref (_, omega, (_, Fun _))) -> (
          match
            ownership_safe sigma delta gamma omega (fst expr, (fn, [ Deref ]))
          with
          | Succ _ ->
            let* ty =
              compute_ty_in omega delta gamma (fst expr, (fn, [ Deref ]))
            in
            Succ (ty, gamma, slice_env)
          | Fail err -> Fail err )
        | Some ty -> TypeMismatchFunction ty |> fail
        | None -> UnknownFunction (fst expr, fn) |> fail (* T-App *) ) )
    | App (fn, envs, new_provs, new_tys, args) -> (
      match tc slice_env delta gamma fn with
      | Succ
          ( (_, Fun (evs, provs, tyvars, params, _, ret_ty, bounds)),
            gammaF,
            slice_env1 ) -> (
        let* arg_tys, gammaN, slice_env2 =
          tc_many slice_env1 delta gammaF args
        in
        let* evaled_envs = map (eval_env_of gammaF) envs in
        let* env_sub = combine_evs "T-App" evaled_envs evs in
        let* () = check_qualifiers sigma env_sub in
        let* prov_sub = combine_prov "T-App" new_provs provs in
        let* ty_sub = combine_ty "T-App" new_tys tyvars in
        let do_sub : ty -> ty =
          subst_many ty_sub >> subst_many_prov prov_sub
          >> subst_many_env_var env_sub
        in
        let new_params = List.map do_sub params in
        let* ty_pairs = combine_tys "T-App" new_params arg_tys in
        let instantiated_bounds = subst_many_prov_in_bounds prov_sub bounds in
        let* gammaPrime = check_bounds delta gammaN instantiated_bounds in
        let types_mismatch ((expected, found) : ty * ty) : bool tc =
          match subtype Combine delta gammaPrime found expected with
          | Succ _ -> Succ false
          | Fail (UnificationFailed _) -> Succ true
          | Fail err -> Fail err
        in
        let* type_mismatches = find types_mismatch ty_pairs in
        match type_mismatches with
        | None ->
          let new_ret_ty = do_sub ret_ty in
          let* () = valid_type sigma delta gammaPrime new_ret_ty in

          let rec mut_provs (_, ty) =
            match ty with
            | Ref (rho, omega, ty) -> (
              match omega with Shared -> [] | Unique -> rho :: mut_provs ty )
            | _ -> []
          in

          let arg_deps =
            List.map (SliceEnv.expr_deps slice_env2) args
            |> List.fold_left list_union []
          in

          (* Format.printf "before env: %s\n" (SliceEnv.fmt slice_env2);
             Format.printf "args: `%s`\n" (String.concat ", " (List.map fmt_expr args)); *)
          let slice_env3 =
            List.fold_left
              (fun acc tau ->
                List.fold_left
                  (fun acc rho ->
                    Option.value ~default:acc
                      (Option.map
                         (fun loans ->
                           List.fold_left
                             (fun acc (_, p) -> SliceEnv.insert acc p arg_deps)
                             acc loans)
                         (loan_env_lookup_opt gammaPrime rho)))
                  acc (mut_provs tau))
              slice_env2 arg_tys
          in

          (* Format.printf "after env: %s\n" (SliceEnv.fmt slice_env3); *)
          Succ (new_ret_ty, gammaPrime, slice_env3)
        | Some (expected, found) -> TypeMismatch (expected, found) |> fail )
      | Succ (((_, Uninit (_, Fun _)) as uninit_ty), _, _) ->
        MovedFunction (fn, uninit_ty) |> fail
      | Succ (found, _, _) -> TypeMismatchFunction found |> fail
      | Fail err -> Fail err )
  and tc_many (slice_env : SliceEnv.t) (delta : tyvar_env) (gamma : var_env)
      (exprs : expr list) : (ty list * var_env * SliceEnv.t) tc =
    let tc_next (e : expr)
        ((curr_tys, curr_gamma, slice_env) : ty list * var_env * SliceEnv.t) =
      let* ty, gammaPrime, slice_env1 = tc slice_env delta curr_gamma e in
      Succ (List.cons ty curr_tys, gammaPrime, slice_env1)
    in
    foldr tc_next exprs ([], gamma, slice_env)
  in
  let* out_ty, out_gamma, out_slice_env = tc slice_env delta gamma expr in
  let* () = valid_type sigma delta out_gamma out_ty in
  (out_ty, out_gamma, out_slice_env) |> succ

let main () =
  let foo =
    let open Oxide.Edsl in
    fn "foo" [] [(loc (), p1)] [] [x @: ~&p1 uniq u32] unit_ty []
    (~*(var x) <== num 1 >> unit)
    
    [@ocamlformat "disable"]
  in
  let body : expr =
    let open Oxide.Edsl in
    letexp x u32 (num 0)
    ((var x) <== num 1 >> 
    (letexp y (~&p1 uniq u32) (borrow p2 uniq (var x))   
    (cond (tru) (~*(var y) <== num 2) unit >> 
     app (~@ "foo") [] [p1] [] [move (var y)])))
    
    
    [@ocamlformat "disable"]
  in
  let main = fn "main" [] [] [] [] unit_ty [] body in
  let sigma = [ main; foo ] in

  let (FnDef (_, evs, provs, tyvars, params, _ret_ty, bounds, body)) = main in

  let not_in_provs (prov : prov) : bool = provs |> contains prov |> not in
  let free_provs =
    (* this lets us infer letprovs for unbound provenances *)
    free_provs body |> List.filter not_in_provs
    |> List.sort_uniq (fun (_, p1) (_, p2) -> String.compare p1 p2)
  in
  let delta =
    empty_delta |> tyvar_env_add_env_vars evs |> tyvar_env_add_provs provs
    |> tyvar_env_add_ty_vars tyvars
  in
  let* delta =
    foldl
      (fun delta (prov1, prov2) -> tyvar_env_add_abs_sub delta prov1 prov2)
      delta bounds
  in
  let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
    var_env_include gamma (fst pair) (snd pair)
  in
  let gamma =
    params
    |> List.fold_left var_include_fold empty_gamma
    |> loan_env_include_all free_provs []
  in

  (* let* _, gamma = type_check sigma delta gamma body in *)
  Format.printf "%s\n" (fmt_expr body);
  let* _, _, slice_env =
    type_check (SliceEnv.make body) sigma delta gamma body
  in
  Format.printf "%s\n" (SliceEnv.fmt slice_env);

  (* Format.printf "Slice: %a@." SliceEnv.pp slice_env; *)
  Succ ()

let () =
  match main () with
  | Succ _ -> ()
  | Fail err -> Format.printf "Error: %a@." pp_tc_error err
