open Syntax

val flow_closed_envs_forward : ty -> ty -> ty tc

val type_of : prim -> ty

val ty_valid_before_after : global_env -> tyvar_env -> ty -> var_env -> var_env -> unit tc

val eval_env_of : var_env -> env -> env tc

val valid_prov : tyvar_env -> var_env -> prov -> unit tc

val valid_type :
  global_env -> tyvar_env -> var_env ->
  ty -> unit tc

val valid_types :
  global_env -> tyvar_env -> var_env ->
  ty list -> unit tc

val wf_global_env : global_env -> unit tc

val valid_var_env :
  global_env -> tyvar_env ->
  var_env -> unit tc

val valid_envs :
  global_env -> tyvar_env -> var_env -> unit tc

val type_check :
  global_env -> tyvar_env -> var_env ->
  expr -> (ty * var_env) tc
