open Oxide.Typeck
open Oxide.Meta
open Oxide.Syntax
open Oxide.Util
open Oxide.Edsl

type node_id = int [@@deriving show]

let opt_or_else o1 f = match o1 with Some _ -> o1 | None -> f ()

let find_loc (l : source_loc) (e : expr) : preexpr =
  let rec aux (l', e) =
    if l = l' then Some e
    else
      match e with
      | Prim _ | Borrow _ -> None
      | Let (_, _, e1, e2) -> opt_or_else (aux e1) (fun _ -> aux e2)
      | Seq (e1, e2) -> opt_or_else (aux e1) (fun _ -> aux e2)
      | Assign (_, e) -> aux e
      | _ -> raise (Failure (Format.sprintf "find_loc: %s" (show_preexpr e)))
  in
  aux e |> Option.get

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

let global_expr = ref unit

module SliceEnv = struct
  type slice = source_loc list [@@deriving show]

  type t = (place_expr * slice) list [@@deriving show]

  let empty : t = []

  let fmt (t : t) : string =
    String.concat ", "
      (List.map
         (fun (p, s) ->
           let s =
             String.concat ", "
               (List.map
                  (fun loc -> fmt_expr (loc, find_loc loc !global_expr))
                  s)
           in
           Format.sprintf "%s: {%s}" (fmt_place p) s)
         t)

  let lookup (t : t) ((_, p) : place_expr) : slice =
    List.find_opt (fun ((_, p'), _) -> p = p') t
    |> Option.map (fun (_, slice) -> slice)
    |> Option.value ~default:[]

  let insert (t : t) ((_, p) as pexp : place_expr) (s : slice) : t =
    match List.find_opt (fun ((_, p'), _) -> p = p') t with
    | Some (_, s') -> replace_assoc t pexp (list_union s s')
    | None -> (pexp, s) :: t

  let expr_deps (t : t) ((loc, e) : expr) : slice =
    let transitive =
      match e with
      | Prim _ -> []
      | Move p -> lookup t p
      | Borrow (_, _, p) -> lookup t p
      | _ -> raise (Failure (Format.sprintf "expr_deps: %s" (show_preexpr e)))
    in
    uniq_cons loc transitive

  let rec compute (env : t) ((loc, e) : expr) : t =
    match e with
    | Prim _ | Borrow (_, _, _) -> env
    | Let (x, _tau, e1, e2) ->
        let env = compute env e1 in
        let env = insert env (var x) (expr_deps env e1) in
        compute env e2
    | Seq (e1, e2) ->
        let env = compute env e1 in
        compute env e2
    | Assign (p, e) ->
        let env = compute env e in
        insert env p (expr_deps env e)
    | _ -> raise (Failure (Format.sprintf "slice: %s" (show_preexpr e)))
end

let main () =
  let body : expr =
    letexp x u32 (num 0)
      (letexp y (~&p1 uniq u32)
         (borrow p2 uniq (var x))
         (~*(var y) <== num 1 >> unit))
  in
  global_expr := body;
  let main = fn "main" [] [] [] [] unit_ty [] body in
  let sigma = [ main ] in

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
  let* tau, venv = type_check sigma delta gamma body in

  Format.printf "%s\n" (fmt_expr body);
  let slice_env = SliceEnv.compute SliceEnv.empty body in
  Format.printf "%s\n" (SliceEnv.fmt slice_env);

  (* Format.printf "Slice: %a@." SliceEnv.pp slice_env; *)
  Succ ()

let () =
  match main () with
  | Succ _ -> ()
  | Fail err -> Format.printf "Error: %a@." pp_tc_error err
