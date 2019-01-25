type var = int [@@deriving show]
type ty_var = int [@@deriving show]
type rgn_var = int [@@deriving show]
type loan_id = int [@@deriving show]

type muta = Imm | Mut [@@deriving show]
type place =
  | Var of var
  | Deref of place
  | FieldProj of place * string
  | IndexProj of place * int
  [@@deriving show]

type frac =
  | Num of int
  | Div of frac * frac
  | Add of frac * frac
  [@@deriving show]
type rgn_atom =
  | RgnVar of rgn_var
  | Loan of loan_id * frac * place
  [@@deriving show]
type rgn = rgn_atom list [@@deriving show]

type kind = Star | Rgn [@@deriving show]
type base_ty = Bool | U32 | Unit [@@deriving show]
type ty =
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of rgn * muta * ty
  | Fun of rgn_var list * ty_var list * ty list * ty
  | Array of ty * int
  | Tup of ty list
  [@@deriving show]

type global_env = () (* TODO: actual global environment definition *)
type tyvar_env = rgn_var list * ty_var list
type var_env = (place * (frac * ty)) list [@@deriving show]

let var_env_lookup (gamma : var_env) (pi : place) : (frac * ty) = List.assoc pi gamma

let rec add_frac (f1 : frac) (f2 : frac) =
  match (f1, f2) with
  | (Num n1, Num n2) -> Num (n1 + n2)
  | (Add (n1, n2), f2) -> add_frac (add_frac n1 n2) f2
  | (f1, Add (n1, n2)) -> add_frac f1 (add_frac n1 n2)
  | (Div (n1, d1), Div (n2, d2)) -> Div (add_frac n1 n2, mult_frac d1 d2)
  | (Div (n1, d1), Num n) -> Div (add_frac n1 (mult_frac d1 (Num n)), d1)
  | (Num n, Div (n1, d1)) -> Div (add_frac n1 (mult_frac d1 (Num n)), d1)
and mult_frac (f1 : frac) (f2 : frac)  =
  match (f1, f2)  with
  | (Num n1, Num  n2) -> Num (n1 * n2)
  | (Add (n1, n2), f2) -> mult_frac (add_frac n1 n2) f2
  | (f1, Add (n1, n2)) -> mult_frac f1 (add_frac n1 n2)
  | (Div (n1, d1), Div (n2, d2)) -> Div (mult_frac n1 d2, mult_frac d1 n2)
  | (Div (n1, d1), Num n) -> Div (mult_frac n1 (Num n), d1)
  | (Num n, Div (n1, d1)) -> Div (mult_frac n1 (Num n), d1)

let rec gcd a b =
  match (a mod b) with
  | 0 -> b
  | r -> gcd b r

let rec normalize (frac : frac) : frac =
  match frac with
  | Num x -> Num x
  | Add (f1, f2) -> normalize (add_frac f1 f2)
  | Div (Num n, Num d) ->
      let gcd = gcd n d
      in Div (Num (n / gcd), Num (d / gcd))
  | Div (f1, f2) -> normalize (mult_frac f1 (Div (Num 1, f2)))

let make_loan (gamma : var_env) (mu : muta) (from_pi : place) : var_env =
  let (curr_frac, tau) = var_env_lookup gamma from_pi
  in let base_gamma = List.remove_assoc from_pi gamma
  in match mu with
     | Imm -> List.cons (from_pi, (normalize (Div (curr_frac, Num 2)), tau)) base_gamma
     | Mut -> List.cons (from_pi, (Num 0, tau)) base_gamma

let return_loan (gamma : var_env) (frac : frac) (from_pi : place) : var_env =
  let (curr_frac, tau) = var_env_lookup gamma from_pi
  in let base_gamma = List.remove_assoc from_pi gamma
  in List.cons (from_pi, (normalize (Add (curr_frac, frac)), tau)) base_gamma

let frac_to_muta (frac : frac) : muta =
  match frac with
  | Num 1 -> Mut
  | _ -> Imm

let rec walk (change : var_env -> frac -> place -> var_env) (gamma : var_env) (tau : ty) : var_env =
  match tau with
  | Ref (rgns, _, inner_tau) ->
      let work (gamma : var_env) (rgn : rgn_atom) : var_env =
        match rgn with
        | RgnVar _ -> gamma
        | Loan (_, frac, from_pi) -> change gamma frac from_pi
      in walk change (List.fold_left work gamma rgns) inner_tau
  | Array (inner_tau, _) -> walk change gamma inner_tau
  | Tup taus -> List.fold_left (walk change) gamma taus
  | _ -> gamma

let incl (gamma : var_env) (tau : ty) : var_env =
  walk (fun gamma -> fun frac -> make_loan gamma (frac_to_muta frac)) gamma tau

let excl (gamma : var_env) (pi : place) : var_env =
  let (_, tau) = var_env_lookup gamma pi
  in walk return_loan (List.remove_assoc pi gamma) tau

let main =
  let env1 = [(Var 1, (Num 1, BaseTy U32))]
  in let ref_ty = Ref ([Loan (1, Div (Num 1, Num 2), Var 1)], Imm, BaseTy U32)
  in let env2 = incl env1 ref_ty
  in let env3 = excl (List.cons (Var 2, (Num 1, ref_ty)) env2) (Var 2)
  in begin
    Format.printf "%a@." pp_var_env env1;
    Format.printf "%a@." pp_var_env env2;
    Format.printf "%a@." pp_var_env env3;
  end
