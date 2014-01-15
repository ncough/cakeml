(*Generated by Lem from typeSoundInvariants.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory libTheory astTheory semanticPrimitivesTheory smallStepTheory typeSystemTheory;

val _ = numLib.prefer_num();



val _ = new_theory "typeSoundInvariants"

(*open import Pervasives*)
(*open import Lib*)
(*open import Ast*)
(*open import SemanticPrimitives*)
(*open import SmallStep*)
(*open import TypeSystem*)

(* Store typing *)
val _ = type_abbrev( "tenvS" , ``: (num, t) env``);

(* Constructor type environments keyed by constructor namd and type *)
val _ = type_abbrev( "tenvCT" , ``: (( conN id # tid_or_exn), ( tvarN list # t list)) env``);

(*val same_module : id conN -> tid_or_exn -> bool*)
 val _ = Define `
 (same_module (Short x) _ = T)
/\
(same_module (Long mn1 x) (TypeId (Long mn2 y)) = (mn1 = mn2))
/\
(same_module _ TypeExn = T)
/\
(same_module _ _ = F)`;


(*val tenvC_ok : tenvC -> bool*)
val _ = Define `
 (tenvC_ok tenvC =  
(EVERY (\ (cn,(tvs,ts,tn)) .  same_module cn tn /\ EVERY (check_freevars( 0) tvs) ts) tenvC))`;


(*val tenvCT_ok : tenvCT -> bool*)
val _ = Define `
 (tenvCT_ok tenvCT =  
(
  (*all_distinct (List.map fst tenvCT) &&*)EVERY (\ ((cn,tn),(tvs,ts)) .  same_module cn tn /\ EVERY (check_freevars( 0) tvs) ts) tenvCT))`;


(* Check that a constructor type environment is consistent with a runtime type
 * enviroment, using the full type keyed constructor type environment to ensure
 * that the correct types are used. *)
(*val consistent_con_env : tenvCT -> envC -> tenvC -> bool*)
val _ = Define `
 (consistent_con_env tenvCT envC tenvC =  
(tenvC_ok tenvC /\  
(tenvCT_ok tenvCT /\  
((! cn n t.    
(lookup cn envC = SOME (n, t))
    ==>    
(? tvs ts.      
(lookup cn tenvC = SOME (tvs, ts, t)) /\
      ((lookup (cn,t) tenvCT = SOME (tvs, ts)) /\      
(LENGTH ts = n))))
  /\
  (! cn.    
(lookup cn envC = NONE)
    ==>    
(lookup cn tenvC = NONE))))))`;


(* A value has a type *)
(* The number is how many deBruijn type variables are bound in the context. *)
(*val type_v : nat -> tenvCT -> tenvS -> v -> t -> bool*)

(* A value environment has a corresponding type environment.  Since all of the
 * entries in the environment are values, and values have no free variables,
 * each entry in the environment can be typed in the empty environment (if at
 * all) *)
(*val type_env : tenvCT -> tenvS -> envE -> tenvE -> bool*)

(* The type of the store *)
(*val type_s : tenvCT -> tenvS -> store v -> bool*)

(* An evaluation context has the second type when its hole is filled with a
 * value of the first type. *)
(* The number is how many deBruijn type variables are bound in the context.
 * This is only used for constructor contexts, because the value restriction 
 * ensures that no other contexts can be created under a let binding. *)
(*val type_ctxt : nat -> tenvM -> tenvCT -> tenvC -> tenvS -> tenvE -> ctxt_frame -> t -> t -> bool*)
(*val type_ctxts : nat -> tenvCT -> tenvS -> list ctxt -> t -> t -> bool*)
(*val type_state : nat -> tenvCT -> tenvS -> state -> t -> bool*)
(*val context_invariant : nat -> list ctxt -> nat -> bool*)

(* Type programs without imposing signatures.  This is needed for the type
 * soundness proof *)
(*val type_top_ignore_sig : tenvM -> tenvC -> tenvE -> top -> tenvM -> tenvC -> env varN (nat * t) -> bool*)

val _ = Hol_reln ` (! menv cenv tenv d cenv' tenv'.
(type_d NONE menv cenv tenv d cenv' tenv')
==>
type_top_ignore_sig menv cenv tenv (Tdec d) emp cenv' tenv')

/\ (! menv cenv tenv mn spec ds cenv' tenv'.
 (~ (MEM mn (MAP FST menv)) /\
type_ds (SOME mn) menv cenv tenv ds cenv' tenv')
==>
type_top_ignore_sig menv cenv tenv (Tmod mn spec ds) [(mn,tenv')] (add_mod_prefix mn cenv') emp)`;

 val _ = Define `
 
(tenv_ok Empty = T)
/\
(tenv_ok (Bind_tvar n tenv) = (tenv_ok tenv))
/\
(tenv_ok (Bind_name x tvs t tenv) =  
(check_freevars (tvs + num_tvs tenv) [] t /\ tenv_ok tenv))`;


val _ = Define `
 (tenvM_ok tenvM = (EVERY (\ (mn,tenv) .  tenv_ok (bind_var_list2 tenv Empty)) tenvM))`;


val _ = Hol_reln ` (! tvs cenv senv b.
T
==>
type_v tvs cenv senv (Litv (Bool b)) Tbool)

/\ (! tvs cenv senv n.
T
==>
type_v tvs cenv senv (Litv (IntLit n)) Tint)

/\ (! tvs cenv senv.
T
==>
type_v tvs cenv senv (Litv Unit) Tunit)

/\ (! tvs cenv senv cn vs tvs' tn ts' ts.
(EVERY (check_freevars tvs []) ts' /\
((LENGTH tvs' = LENGTH ts') /\
(type_vs tvs cenv senv vs (MAP (type_subst (ZIP (tvs', ts'))) ts) /\
(lookup (cn, tn) cenv = SOME (tvs',ts)))))
==>
type_v tvs cenv senv (Conv (SOME (cn,tn)) vs) (Tapp ts' (tid_exn_to_tc tn)))

/\ (! tvs cenv senv vs ts.
(type_vs tvs cenv senv vs ts)
==>
type_v tvs cenv senv (Conv NONE vs) (Tapp ts TC_tup))

/\ (! tvs menv tenvC tenvCT senv envC envM env tenv n e t1 t2.
(consistent_con_env tenvCT envC tenvC /\
(tenvM_ok menv /\
(consistent_mod_env senv tenvCT envM menv /\
(type_env tenvCT senv env tenv /\
(check_freevars tvs [] t1 /\
type_e menv tenvC (bind_tenv n( 0) t1 (bind_tvar tvs tenv)) e t2)))))
==>
type_v tvs tenvCT senv (Closure (envM, envC, env) n e) (Tfn t1 t2))

/\ (! tvs menv tenvC tenvCT senv envM envC env funs n t tenv tenv'.
(consistent_con_env tenvCT envC tenvC /\
(tenvM_ok menv /\
(consistent_mod_env senv tenvCT envM menv /\
(type_env tenvCT senv env tenv /\
(type_funs menv tenvC (bind_var_list( 0) tenv' (bind_tvar tvs tenv)) funs tenv' /\
(lookup n tenv' = SOME t))))))
==>
type_v tvs tenvCT senv (Recclosure (envM, envC, env) funs n) t)

/\ (! tvs cenv senv n t.
(check_freevars( 0) [] t /\
(lookup n senv = SOME t))
==>
type_v tvs cenv senv (Loc n) (Tref t))

/\ (! tvs cenv senv.
T
==>
type_vs tvs cenv senv [] [])

/\ (! tvs cenv senv v vs t ts.
(type_v tvs cenv senv v t /\
type_vs tvs cenv senv vs ts)
==>
type_vs tvs cenv senv (v::vs) (t::ts))

/\ (! cenv senv.
T
==>
type_env cenv senv emp Empty)

/\ (! cenv senv n v env t tenv tvs.
(type_v tvs cenv senv v t /\
type_env cenv senv env tenv)
==>
type_env cenv senv (bind n v env) (bind_tenv n tvs t tenv))

/\ (! tenvS tenvC.
T
==>
consistent_mod_env tenvS tenvC [] [])

/\ (! tenvS tenvC mn env menv mn' tenv tenvM.
((mn = mn') /\
(~ (MEM mn (MAP FST tenvM)) /\
(type_env tenvC tenvS env (bind_var_list2 tenv Empty) /\
consistent_mod_env tenvS tenvC menv tenvM)))
==>
consistent_mod_env tenvS tenvC ((mn,env)::menv) ((mn',tenv)::tenvM))`;

val _ = Define `
 (type_s cenv senv s =  
(! l. 
    ((? t. lookup l senv = SOME t) <=> (? v. store_lookup l s = SOME v)) /\    
(! t v. ((lookup l senv = SOME t) /\ (store_lookup l s = SOME v)) ==> type_v( 0) cenv senv v t)))`;


val _ = Hol_reln ` (! n.
T
==>
context_invariant n [] n)

/\ (! dec_tvs c env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Craise () ,env) :: c) 0)

/\ (! dec_tvs c pes env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Chandle ()  pes,env) :: c) 0)

/\ (! dec_tvs c op e env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Capp1 op ()  e,env) :: c) 0)

/\ (! dec_tvs c op v env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Capp2 op v () ,env) :: c) 0)

/\ (! dec_tvs c l e env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Clog l ()  e,env) :: c) 0)

/\ (! dec_tvs c e1 e2 env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Cif ()  e1 e2,env) :: c) 0)

/\ (! dec_tvs c pes env err_v.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Cmat ()  pes err_v,env) :: c) 0)

/\ (! dec_tvs c tvs x e env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Clet x ()  e,env) :: c) tvs)

/\ (! dec_tvs c cn vs es tvs env.
(context_invariant dec_tvs c tvs /\
( ~ (tvs =( 0)) ==> EVERY is_value es))
==>
context_invariant dec_tvs ((Ccon cn vs ()  es,env) :: c) tvs)

/\ (! dec_tvs c op env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Cuapp op () ,env) :: c) 0)`;

val _ = Hol_reln ` (! tvs menv all_cenv cenv senv tenv t.
(check_freevars tvs [] t)
 ==>
type_ctxt tvs menv all_cenv cenv senv tenv (Craise () ) Texn t)

/\ (! tvs menv all_cenv cenv senv tenv pes t.
(! ((p,e) :: LIST_TO_SET pes). ? tenv'.
   ALL_DISTINCT (pat_bindings p []) /\   
(type_p (num_tvs tenv) cenv p Texn tenv' /\
   type_e menv cenv (bind_var_list( 0) tenv' tenv) e t))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Chandle ()  pes) t t)

/\ (! tvs menv all_cenv cenv senv tenv uop t1 t2.
(check_freevars tvs [] t1 /\
(check_freevars tvs [] t2 /\
type_uop uop t1 t2))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Cuapp uop () ) t1 t2)

/\ (! tvs menv all_cenv cenv senv tenv e op t1 t2 t3.
(check_freevars tvs [] t1 /\
(check_freevars tvs [] t3 /\
(type_e menv cenv tenv e t2 /\
type_op op t1 t2 t3)))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Capp1 op ()  e) t1 t3)

/\ (! tvs menv all_cenv cenv senv tenv op v t1 t2 t3.
(check_freevars tvs [] t2 /\
(check_freevars tvs [] t3 /\
(type_v( 0) all_cenv senv v t1 /\
type_op op t1 t2 t3)))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Capp2 op v () ) t2 t3)

/\ (! tvs menv all_cenv cenv senv tenv op e.
(type_e menv cenv tenv e Tbool)
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Clog op ()  e) Tbool Tbool)

/\ (! tvs menv all_cenv cenv senv tenv e1 e2 t.
(type_e menv cenv tenv e1 t /\
type_e menv cenv tenv e2 t)
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Cif ()  e1 e2) Tbool t)

/\ (! tvs menv all_cenv cenv senv tenv t1 t2 pes err_v.
(((pes = []) ==> (check_freevars tvs [] t1 /\ check_freevars( 0) [] t2)) /\
((! ((p,e) :: LIST_TO_SET pes) . ? tenv'.
   ALL_DISTINCT (pat_bindings p []) /\   
(type_p tvs cenv p t1 tenv' /\
   type_e menv cenv (bind_var_list( 0) tenv' tenv) e t2)) /\
type_v( 0) all_cenv senv err_v Texn))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Cmat ()  pes err_v) t1 t2)

/\ (! tvs menv all_cenv cenv senv tenv e t1 t2 n.
(check_freevars tvs [] t1 /\
type_e menv cenv (bind_tenv n tvs t1 tenv) e t2)
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Clet n ()  e) t1 t2)

/\ (! tvs menv all_cenv cenv senv tenv cn vs es ts1 ts2 t tn ts' tvs'.
(EVERY (check_freevars tvs []) ts' /\
((LENGTH tvs' = LENGTH ts') /\
(type_vs tvs all_cenv senv (REVERSE vs)
        (MAP (type_subst (ZIP (tvs', ts'))) ts1) /\
(type_es menv cenv (bind_tvar tvs tenv) es (MAP (type_subst (ZIP (tvs', ts'))) ts2) /\
(lookup cn cenv = SOME (tvs', ((ts1++[t])++ts2), tn))))))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Ccon (SOME cn) vs ()  es) (type_subst (ZIP (tvs', ts')) t)
          (Tapp ts' (tid_exn_to_tc tn)))

/\ (! tvs menv all_cenv cenv senv tenv vs es t ts1 ts2.
(check_freevars tvs [] t /\
(type_vs tvs all_cenv senv (REVERSE vs) ts1 /\
type_es menv cenv (bind_tvar tvs tenv) es ts2))
==>
type_ctxt tvs menv all_cenv cenv senv tenv (Ccon NONE vs ()  es) t (Tapp ((ts1++[t])++ts2) TC_tup))`;

val _ = Define `
 (poly_context cs =  
 ((case cs of
      (Ccon cn vs ()  es,env) :: cs => EVERY is_value es
    | (Clet x ()  e,env) :: cs => T
    | [] => T
    | _ => F
  )))`;


val _ = Define `
 (is_ccon c =  
 ((case c of
      Ccon cn vs ()  es => T
    | _ => F
  )))`;


val _ = Hol_reln ` (! tvs tenvC senv t.
(check_freevars tvs [] t)
==>
type_ctxts tvs tenvC senv [] t t)

/\ (! tvs tenvM tenvC tenvCT senv c envM envC env cs tenv t1 t2 t3.
(type_env tenvCT senv env tenv /\
(consistent_con_env tenvCT envC tenvC /\
(tenvM_ok tenvM /\
(consistent_mod_env senv tenvCT envM tenvM /\
(type_ctxt tvs tenvM tenvCT tenvC senv tenv c t1 t2 /\
type_ctxts (if is_ccon c /\ poly_context cs then tvs else  0) tenvCT senv cs t2 t3)))))
==>
type_ctxts tvs tenvCT senv ((c,(envM,envC,env))::cs) t1 t3)`;

val _ = Hol_reln ` (! dec_tvs tenvM tenvC tenvCT senv envM envC s env e c t1 t2 tenv tvs.
(context_invariant dec_tvs c tvs /\
(consistent_con_env tenvCT envC tenvC /\
(tenvM_ok tenvM /\
(consistent_mod_env senv tenvCT envM tenvM /\
(type_ctxts tvs tenvCT senv c t1 t2 /\
(type_env tenvCT senv env tenv /\
(type_s tenvCT senv s /\
(type_e tenvM tenvC (bind_tvar tvs tenv) e t1 /\
(( ~ (tvs =( 0))) ==> is_value e)))))))))
==>
type_state dec_tvs tenvCT senv ((envM, envC, env), s, Exp e, c) t2)

/\ (! dec_tvs tenvCT senv envM envC s env v c t1 t2 tvs.
(context_invariant dec_tvs c tvs /\
(type_ctxts tvs tenvCT senv c t1 t2 /\
(type_s tenvCT senv s /\
type_v tvs tenvCT senv v t1)))
==>
type_state dec_tvs tenvCT senv ((envM, envC, env), s, Val v, c) t2)`;
val _ = export_theory()

