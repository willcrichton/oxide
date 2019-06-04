open Syntax
open Meta

let omega_safe (ell : loan_env) (gamma : place_env) (omega : owned) (pi : place_expr) : (ty * loans) option =
  failwith "unimplemented"
  (* if is_safe ell gamma omega pi then Some (List.assoc pi gamma)
   * else None *)

let unify (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env * ty = failwith "unimplemented"

let intersect (envs1 : loan_env * place_env) (envs2 : loan_env * place_env) : loan_env * place_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in failwith "unimplemented"

let valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env) (ty : ty) : () tc =
  failwith "unimplemented"

let type_of (prim : prim) : ty =
  match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
               (expr : expr) : (ty * loan_env * place_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
             (expr : expr) : (ty * loan_env * place_env) tc =
    match snd expr with
    | Prim prim -> (type_of prim, ell, gamma)
    | Move pi ->
      (match omega_safe ell gamma Unique pi with
       | Some (ty, _) -> Succ (ty, ell, if noncopyable ty then place_env_subtract gamma pi else gamma)
       | None -> Fail (SafetyErr (fst expr, Unique, pi)))
    | Borrow (prov, omega, pi) ->
      (match omega_safe ell gamma omega pi with
       | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
       | None -> Fail (SafetyErr (fst expr, omega, pi)))
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e1 with
       | Some (BaseTy U32, ell1, gamma1) ->
         (match omega_safe ell1 gamma1 omega pi with
          | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
          | None -> Fail (SafetyErr (fst expr, omega, pi)))
       | Some (found, _, _) -> Fail (TypeMismatch (fst e, BaseTy U32, found))
       | Fail err -> Fail err)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Some (BaseTy U32, ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Some (BaseTy U32, ell2, gamma2) ->
            (match omega_safe ell2 gamma2 omega pi with
             | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
             | None -> Fail (SafetyErr (fst expr, omega, pi)))
          | Some (found, _, _) -> Fail (TypeMismatch (fst e2, BaseTy U32, found))
          | Fail err -> Fail err)
       | Some (found, _, _) -> Fail (TypeMismatch (fst e1, BaseTy U32, found))
       | Fail err -> Fail err)
    | Idx (pi, e) ->
      (match tc delta ell gamma e with
       | Some (BaseTy U32, ell1, gamma1) ->
         (match omega_safe ell1 gamma1 Shrd pi with
          | Some (Array (ty, _), loans) ->
            if copyable ty then Succ (ty, loan_env_include ell prov loans, gamma)
            else Fail (CannotMove (fst expr, pi))
          | Some (found, _, _) -> Fail (TypeMisMatch (fst expr, Array (TyVar -1, -1), found))
          | None -> Fail (SafetyErr (fst expr, omega, pi)))
       | Some (found, _, _) -> Fail (TypeMismatch (fst e, BaseTy U32, found))
       | Fail err -> Fail err)
    | Seq (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (_, ell1, gamma1) -> tc delta ell1 gamma1 e2
       | Fail err -> Fail err)
    | Branch (e1, e2, e3) ->
      (match tc delta ell gamma e1 with
       | Succ (BaseTy Bool, ell1, gamma1) ->
         (match (tc delta ell1 gamma1 e2, tc delta ell1 gamma1 e3) with
          | (Succ (ty2, ell2, gamma2), Succ (ty3, ell3, gamma3)) ->
            (let (ellPrime, gammaPrime) = intersect (ell2, gamma2) (ell3, gamm3)
             in let (ellFinal, tyFinal) = unify ellPrime ty2 ty3
             in match valid_type sigma delta ellFinal gammaPrime tyFinal with
             | Succ () -> (tyFinal, ellFinal, gammaPrime)
             | Fail err -> Fail err)
          | (Fail err, _) | (_, Fail err) -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e1, BaseTy Bool, found))
       | Fail err -> Fail err)
    | LetProv (new_provars, e) ->
      let (provars, tyvars) = delta
      in tc (List.append new_provars provars, tyvars) ell gamma e
  | _ -> failwith "unimplemented"
  in tc delta ell gamma expr
