open alistTheory preamble wordLangTheory wordSemTheory wordPropsTheory
     word_simpProofTheory word_cseTheory whileTheory word_allocProofTheory;

val _ = new_theory "word_cseProof";

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

fun lt tac thm = (tac [thm]);
val option_case_eq = TypeBase.case_eq_of ``:'a option``;
val list_case_eq = TypeBase.case_eq_of ``:'a list``;
val wl_case_eq = TypeBase.case_eq_of ``:'a word_loc``;
val addr_case_eq = TypeBase.case_eq_of ``:'a addr``;

(* option_seq *)
val option_seq_def = Define `
  (option_seq [] = SOME []) /\
  (option_seq (x::xs) =
    case (x, option_seq xs) of
      | SOME e, SOME l => SOME (e::l)
      | _ => NONE)`;

val option_seq_mono = Q.store_thm("option_seq_mono",
  `∀Q l res P.
    option_seq (MAP P l) = SOME res ∧
    (!e. MEM e l ⇒ !r. (P e = SOME r) ⇒ (Q e = SOME r)) ⇒ 
    option_seq (MAP Q l) = SOME res`,
  Induct_on `l` >> rw [option_seq_def, option_case_eq]
  >> first_x_assum irule >> metis_tac []);

val option_seq_eq = Q.store_thm("option_seq_eq",
  `∀Q l P.
    (∀e. MEM e l ⇒ P e = Q e) ⇒ 
    option_seq (MAP P l) = option_seq (MAP Q l)`,
  Induct_on `l`
  >- rw [option_seq_def, option_case_eq]
  >-
  (rw [] >> Cases_on `Q h`
  >> rw [option_seq_def] >> every_case_tac
  >> first_x_assum (qspecl_then [`Q`, `P`] assume_tac) >> rfs []));

val option_seq_append = Q.store_thm("option_seq_append",
  `∀l1 l2 v.
  option_seq (l1 ⧺ [SOME v]) = SOME l2 ⇔
  ∃l3. option_seq (l1) = SOME l3 ∧ l2 = (l3 ++ [v])`,
  Induct>>fs[option_seq_def,option_case_eq]>>
  rw[]>>EQ_TAC>>rw[]);

(* MIN_SET *)
val min_in_thm = Q.store_thm("min_in",
  `!s. s <> {} ==> (MIN_SET s) IN s`,
  rw [MIN_SET_DEF]
  >> qspecl_then [`s`, `s`] assume_tac LEAST_ELIM
  >> Cases_on `s` >> fs[]);

val min_only_thm = Q.store_thm("min_only",
  `!x. MIN_SET {x} = x`,
  rw[] >> `MIN_SET {x} IN {x}` by fs[min_in_thm] >> fs[]);

val min_delete_thm = Q.store_thm("min_delete",
  `!x s. s DELETE x <> {} ==>
    MIN_SET (s DELETE x) <> x`,
  rw [MIN_SET_DEF]
  >> qspecl_then [`\y. y <> x`, `s DELETE x`] assume_tac LEAST_ELIM
  >> Cases_on `s` >> fs[]
  >> Cases_on `x = x'` >> fs []
  >> Cases_on `t` >> fs[]);

val min_insert_thm = Q.store_thm("min_insert",
  `!x s. MIN_SET (x INSERT s) <> x ==>
    MIN_SET (x INSERT s) = MIN_SET s`,
  rw []
  >> `(MIN_SET (x INSERT s)) IN (x INSERT s)` by fs [min_in_thm]
  >> `(MIN_SET (x INSERT s)) IN s` by (CCONTR_TAC >> fs [INSERT_DEF])
  >> fs [MIN_SET_DEF]
  >> qspecl_then [`\y. $LEAST (x INSERT s) = y`, `s`] assume_tac LEAST_ELIM
  >> sg `!n. (!m. m < n ==> ~s m) /\ s n ==> $LEAST (x INSERT s) = n`
  >- (rw[] >> Cases_on `n < $LEAST (x INSERT s)`
      >> Cases_on `$LEAST (x INSERT s) < n`
      >> qspecl_then [`x INSERT s`] assume_tac LESS_LEAST
      >> res_tac >> fs[IN_DEF])
  >> fs[IN_DEF] >> res_tac);

(* alookup *)
val alookup_none_zip = Q.store_thm("alookup_none_zip",
  `∀f s x. LENGTH f = LENGTH s ⇒
    (~MEM x f ⇔ ALOOKUP (ZIP (f, s)) x = NONE)`,
  fs [ALOOKUP_NONE, MAP_ZIP]);

(*
 * Wrappers fpr value node properties with default values
 *)
val held_def = Define `
  held n nums =
    case lookup n nums.vnodes of
      | SOME n => domain n.held
      | NONE => {}`;

val uses_def = Define `
  uses n nums =
    case lookup n nums.vnodes of
      | SOME node => domain node.uses
      | NONE => {}`; 

val operands_def = Define `
  operands n nums =
    case lookup n nums.vnodes of
      | SOME node => node.operands
      | NONE => []`;

val label_def = Define `
  label n nums =
    case lookup n nums.vnodes of
      | SOME node => node.label
      | NONE => VUnknown`;

val valid_def = Define `
  (valid (VN n) nums = (n ∈ domain nums.vnodes)) ∧
  (valid (VConst w) nums = T)`;

(*
 * From a set of vars, get an arbitrary one from the state
 * Used when selecting a random var from an equivalent set
 *)
val get_any_def = Define `
  get_any t s = 
    if t = {} then NONE else get_var (MIN_SET t) s`;

val eval_label_def = Define `
  (eval_label (VOp op) ws =
    OPTION_MAP Word (OPTION_BIND (the_words (MAP SOME ws)) (word_op op))) ∧
  (eval_label label ws = NONE)`;

(*
 * A value number can be evaluated either by accessing a var in its
 * held set or through a recursive DAG walk, evaluating the label.
 * Both of this methods should agree.
 *)
val eval_vn_def = tDefine "eval_vn" `
  (eval_vn (VConst w) nums s = SOME (Word w)) ∧
  (eval_vn (VN n) nums s =
    let
      ops = operands n nums;
      lbl = label n nums;
      any = get_any (held n nums) s;
      rec = if ∃op. MEM (VN op) ops ∧ n ≤ op then NONE
            else option_seq (MAP (\v. eval_vn v nums s) ops)
    in
      case OPTION_BIND rec (eval_label lbl) of NONE => any | x => x)`
  (WF_REL_TAC `measure (\(v, n, s). case v of (VN n) => SUC n | _ => 0)`
  >> rw [] >> CASE_TAC >> fs []
  >> first_x_assum (qspecl_then [`n'`] mp_tac) >> rw []);

val eval_vn_ind = (#1 o #2 o hd o DB.find) "eval_vn_ind"

val eval_exp_def = Define `
  eval_exp lbl vns nums s =
    OPTION_BIND (option_seq (MAP (\v. eval_vn v nums s) vns))
      (eval_label lbl)`;

val eval_vnode_def = Define `
  eval_vnode n nums s = eval_exp (label n nums) (operands n nums) nums s`;

val eval_var_def = Define `
  eval_var var nums s =
    do
      vn <- get_num var nums;
      eval_vn vn nums s
    od`;

(*
 * wf numbering properties
 * 1) get_num should reflect the held sets
 * 2) vnodes should represent a DAG
 *)
val wf_nums_def = Define `
  wf_nums nums ⇔ 
    (∀vn var. get_num var nums = SOME (VN vn) ⇔ var ∈ held vn nums) ∧
    (∀vn. nums.next ≤ vn ⇒ vn ∉ domain nums.vnodes) ∧
    (∀vn op. MEM (VN op) (operands vn nums) ⇔ vn ∈ uses op nums) ∧
    (∀vn op. MEM (VN op) (operands vn nums) ⇒ op < vn) ∧
    (∀vn. uses vn nums ⊆ domain nums.vnodes)`;

(*
 * state relationship
 * 1) eval_var should imply get_var
 * 2) if in the graph, it should have a value
 *)
val cse_state_rel_def = Define `
  cse_state_rel nums s ⇔
    (∀res var.
      eval_var var nums s = SOME res ⇒ get_var var s = SOME res) ∧
    (∀var.
      IS_SOME (get_num var nums) ⇒ IS_SOME (get_var var s))`;

(*
 * Merge prior properties with locals_rel
 * Using locals_rel for proof reuse
 *)
val cse_state_locals_rel_def = Define `
  cse_state_locals_rel nums st loc ⇔
    wf_nums nums ∧
    cse_state_rel nums st ∧
    (∀k. lookup k st.locals = lookup k loc)`;

val cse_state_locals_rel_thm = Q.prove(`
  ∀temp nums st loc.
  cse_state_locals_rel nums st loc ⇒
  locals_rel temp st.locals loc`,
  fs [cse_state_locals_rel_def, locals_rel_def]);

val dag_thm = Q.prove(`
  ∀vn1 vn2 nums.
  wf_nums nums ∧ MEM (VN vn2) (operands vn1 nums) ⇒ vn2 < vn1`,
  rw [wf_nums_def]);

(* equal nums implies equal vars *)
val eq_nums_eq_vars = Q.prove(`
  ∀nums s var1 var2 vn.
  wf_nums nums ∧ cse_state_rel nums s ∧
  get_num var1 nums = SOME vn ∧ get_num var2 nums = SOME vn ⇒
  ∃v. get_var var1 s = SOME v ∧ get_var var2 s = SOME v`,
  rw [cse_state_rel_def, eval_var_def] >> res_tac
  >> Cases_on `vn` >> fs [eval_vn_def]
  >> every_case_tac 
    >- (fs [] >> drule_all dag_thm >> rw [])
    >- fs []
    >- (`var1 ∈ held n nums` by metis_tac [wf_nums_def]
       >> Cases_on `held n nums = {}` >- fs []
       >> metis_tac [get_any_def, IS_SOME_EXISTS, IS_SOME_DEF, min_in_thm,
           wf_nums_def])
    >- fs []);

(* get_any should return the same value for all vars in held *)
val get_any_get_var_thm = Q.prove(`
  ∀vn nums s var.
  wf_nums nums ∧ cse_state_rel nums s ∧
  get_num var nums = SOME (VN vn) ⇒
  get_any (held vn nums) s = get_var var s`,
  rw[get_any_def] >- rfs[wf_nums_def]
  >> imp_res_tac min_in_thm
  >> metis_tac [eq_nums_eq_vars, IS_SOME_EXISTS, cse_state_rel_def,
      wf_nums_def]);

(* eval_vnode should return the same value as all vars in held *)
val eval_vnode_get_var_thm = Q.prove(`
  ∀nums s vn var res.
  wf_nums nums ∧ cse_state_rel nums s ∧
  get_num var nums = SOME (VN vn) ∧
  eval_vnode vn nums s = SOME res ⇒
  get_var var s = SOME res`,
  rw [eval_vnode_def, cse_state_rel_def, eval_exp_def]
  >> first_x_assum irule
  >> fs [eval_var_def, eval_vn_def]
  >> CASE_TAC >> fs []
  >> drule_all dag_thm >> fs []);

(* eval_vnode and get_any should agree *)
val eval_vnode_get_any_thm = Q.store_thm("eval_vnode_get_any",
  `∀vn nums s res1 res2.
    wf_nums nums ∧ cse_state_rel nums s ∧
    eval_vnode vn nums s = SOME res1 ∧
    get_any (held vn nums) s = SOME res2 ⇒
    res1 = res2`,
  rw []
  >> Cases_on `?v. v IN held vn nums` >> fs []
  >-
  (`get_num v nums = SOME (VN vn)` by metis_tac [wf_nums_def, INSERT_DEF]
  >> drule_all get_any_get_var_thm >> rw []
  >> drule_all eval_vnode_get_var_thm >> rw [] >> fs [])
  >-
  (Cases_on `held vn nums` >> fs [get_any_def]
  >> first_x_assum (qspec_then `x` assume_tac)
  >> fs [INSERT_DEF]));

(* a successful get_any implies a successful eval_vn *)
val get_any_eval_vn_thm = Q.store_thm("get_any_eval_vn",
  `∀vnum nums s res vn.
    wf_nums nums ∧ cse_state_rel nums s ∧ vnum = VN vn ∧
    get_any (held vn nums) s = SOME res ⇒
    eval_vn vnum nums s = SOME res`,
  rw [eval_vn_def] >> CASE_TAC
  >> assume_tac eval_vnode_get_any_thm
  >> fs [eval_vnode_def, eval_exp_def]
  >> metis_tac []);

(* a successful eval_vnode implies a successful eval_vn *)
val eval_vnode_eval_vn_thm = Q.store_thm("eval_vnode_eval_vn",
  `∀vnum nums s res vn.
    wf_nums nums ∧ cse_state_rel nums s ∧ vnum = VN vn ∧
    eval_vnode vn nums s = SOME res ⇒
    eval_vn vnum nums s = SOME res`,
  rw [eval_vn_def, eval_vnode_def, eval_exp_def]
  >- (drule_all dag_thm >> fs [])
  >- (CASE_TAC >> fs [] >> fs [] >> rfs []));

val eval_vn_thm = Q.store_thm ("eval_vn_thm",
  `∀vn nums s res w.
    wf_nums nums ∧ cse_state_rel nums s ⇒
    eval_vn (VConst w) nums s = SOME (Word w) ∧
    (eval_vn (VN vn) nums s = SOME res ⇔
      get_any (held vn nums) s = SOME res ∨
      eval_vnode vn nums s = SOME res)`,
  rw []
  >- fs [eval_vn_def]
  >- (EQ_TAC >> rw []
    >- (fs [eval_vn_def] >> every_case_tac >> fs [eval_vnode_def,eval_exp_def])
    >- metis_tac [get_any_eval_vn_thm]
    >- metis_tac [eval_vnode_eval_vn_thm]));

val option_seq_eq_vnum =
  INST_TYPE [``:'a`` |-> ``:'a vnumber``, ``:'b`` |-> ``:'a word_loc``]
    option_seq_eq;

val eval_vn_locals_thm = Q.store_thm("eval_vn_locals",
  `∀s vn nums ns res.
    wf_nums nums ∧ cse_state_rel nums s ∧
    s.locals = ns.locals ⇒
    eval_vn vn nums s = eval_vn vn nums ns`,
  gen_tac >> recInduct eval_vn_ind >> rw [eval_vn_def]
  >- (drule_all dag_thm >> rw [])
  >-
  (every_case_tac
  >- fs [get_any_def, get_var_def]
  >> fs []
  >> qspecl_then [`\v. eval_vn v nums s'`,
                  `operands n nums`,
                  `\v. eval_vn v nums s`] assume_tac option_seq_eq_vnum
  >> rfs [] >> fs []));

val eval_var_locals_thm = Q.store_thm("eval_var_locals",
  `∀s var nums ns res.
    wf_nums nums ∧ cse_state_rel nums s ∧
    s.locals = ns.locals ⇒
    eval_var var nums s = eval_var var nums ns`,
  rw [eval_var_def]
  >> Cases_on `get_num var nums` >> fs []
  >> metis_tac [eval_vn_locals_thm]);

(* initial vnumbering properties *)
val wf_initial_vn_thm = Q.store_thm("wf_initial_vn",
  `wf_nums initial_vn`,
  fs [initial_vn_def, wf_nums_def]
  >> fs [held_def, uses_def, operands_def]
  >> fs [lookup_def, get_num_def]);

val state_initial_vn_thm = Q.store_thm("state_initial_vn",
  `∀s. cse_state_rel initial_vn s`,
  fs [initial_vn_def, cse_state_rel_def]
  >> fs [get_num_def, eval_var_def, lookup_def]);

val locals_initial_vn_thm = Q.store_thm("locals_initial_vn",
  `∀s. cse_state_locals_rel initial_vn s s.locals`,
  fs [cse_state_locals_rel_def]
  >> fs [wf_initial_vn_thm, state_initial_vn_thm]);

(* get_any thms *)
val get_any_delete_thm = Q.store_thm("get_any_delete",
  `∀var x s res nums vn.
    cse_state_rel nums s ∧ wf_nums nums ∧ 
    get_any (held vn nums DELETE var) (set_var var x s) = SOME res ⇒ 
    get_any (held vn nums) s = SOME res`,
  rw [get_any_def, get_var_set_var_thm, min_delete_thm]
  >> `held vn nums <> {}` by metis_tac [EMPTY_DELETE]
  >> `MIN_SET (held vn nums DELETE var) IN held vn nums` by
       metis_tac [DELETE_SUBSET, SUBSET_DEF, min_in_thm]
  >> `MIN_SET (held vn nums) IN held vn nums` by metis_tac [min_in_thm]
  >> metis_tac [cse_state_rel_def, wf_nums_def, eq_nums_eq_vars]);

val get_any_insert_thm = Q.store_thm("get_any_insert",
  `∀vn var res1 res2 nums s.
    wf_nums nums ∧ cse_state_rel nums s ∧
    eval_vn (VN vn) nums s = SOME res1 ∧
    get_any (var INSERT held vn nums) (set_var var res1 s) = SOME res2 ⇒
    res1 = res2`,
  rw [eval_vn_thm, get_any_def, get_var_set_var_thm, min_insert_thm]
  >> drule get_any_eval_vn_thm >> disch_then drule >> rw []
  >> pop_assum (qspecl_then [`res2`, `vn`] assume_tac)
  >> Cases_on `held vn nums <> {}`
  >- fs [get_any_def]
  >- metis_tac [min_only_thm]);

val held_vnodes_thm = Q.prove(`
  ∀vn n1 n2.
  n1.vnodes = n2.vnodes ⇒
  held vn n1 = held vn n2`,
  rw [held_def] >> every_case_tac >> rfs []);

val get_num_valid_thm = Q.prove(`
  ∀var nums vn.
  wf_nums nums ∧ get_num var nums = SOME vn ⇒
  valid vn nums`,
  rw [wf_nums_def] >> Cases_on `vn`
  >> fs [valid_def, held_def]
  >> res_tac >>  every_case_tac  
  >> fs [domain_lookup]);

(* delete_held thms *)
val uses_delete_held_thm = Q.store_thm("uses_delete_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = delete_held var vn1 n1.vnodes ⇒
    uses vn2 n2 = uses vn2 n1`,
  rw [delete_held_def, uses_def]
  >> Cases_on `vn1 = vn2` >> rw []
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val operands_delete_held_thm = Q.store_thm("operands_delete_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = delete_held var vn1 n1.vnodes ⇒
    operands vn2 n2 = operands vn2 n1`,
  rw [delete_held_def, operands_def]
  >> Cases_on `vn1 = vn2` >> rw []
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val label_delete_held_thm = Q.store_thm("label_delete_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = delete_held var vn1 n1.vnodes ⇒
    label vn2 n2 = label vn2 n1`,
  rw [delete_held_def, label_def]
  >> Cases_on `vn1 = vn2` >> rw []
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val delete_held_thm = Q.store_thm("delete_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = delete_held var vn1 n1.vnodes ⇒
    held vn2 n2 =
      if vn1 = vn2 then held vn2 n1 DELETE var
      else held vn2 n1`,
  rw [delete_held_def, held_def]
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val absorption_delete_held_thm = Q.store_thm("absorption_delete_held",
  `∀vn var nums.
    wf_nums nums /\ get_num var nums <> SOME (VN vn) ==>
    held vn nums DELETE var = held vn nums`,
  rw []
  >> `var ∉ held vn nums` by metis_tac [wf_nums_def]
  >> metis_tac [DELETE_NON_ELEMENT]);

(* insert_held thms *)
val uses_insert_held_thm = Q.store_thm("uses_insert_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = insert_held var vn1 n1.vnodes ⇒
    uses vn2 n2 = uses vn2 n1`,
  rw [insert_held_def, uses_def]
  >> Cases_on `vn1 = vn2` >> rw []
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val operands_insert_held_thm = Q.store_thm("operands_insert_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = insert_held var vn1 n1.vnodes ⇒
    operands vn2 n2 = operands vn2 n1`,
  rw [insert_held_def, operands_def]
  >> Cases_on `vn1 = vn2` >> rw []
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val label_insert_held_thm = Q.store_thm("label_insert_held",
  `∀vn1 vn2 n1 n2 var.
    n2.vnodes = insert_held var vn1 n1.vnodes ⇒
    label vn2 n2 = label vn2 n1`,
  rw [insert_held_def, label_def]
  >> Cases_on `vn1 = vn2` >> rw []
  >> every_case_tac >> rfs [lookup_insert] >> rw []);

val insert_held_thm = Q.store_thm("insert_held",
  `∀vn1 vn2 n1 n2 var.
    vn1 ∈ domain n1.vnodes ⇒
    n2.vnodes = insert_held var vn1 n1.vnodes ⇒
    held vn2 n2 =
      if vn1 = vn2 then var INSERT held vn2 n1
      else held vn2 n1`,
  rw [insert_held_def, held_def]
  >> every_case_tac >> fs [domain_lookup]
  >> rfs [lookup_insert] >> rw []);

val absorption_insert_held_thm = Q.store_thm("absorption_insert_held",
  `∀vn var nums.
    wf_nums nums /\ get_num var nums = SOME (VN vn) ==>
    var INSERT held vn nums = held vn nums`,
  rw []
  >> `var ∈ held vn nums` by metis_tac [wf_nums_def]
  >> metis_tac [ABSORPTION]);

(* unassign_num thms *)
val get_num_unassign_thm = Q.store_thm("get_num_unassign",
  `∀var1 var2 nums.
    get_num var1 (unassign_num var2 nums) =
    if var1 = var2 then NONE else get_num var1 nums`,
  rpt gen_tac
  >> fs [unassign_num_def, get_num_def]
  >> every_case_tac >> fs [lookup_delete]);

val held_unassign_thm = Q.store_thm("held_unassign",
  `∀var vn nums.
    wf_nums nums ⇒
    held vn (unassign_num var nums) = held vn nums DELETE var`,
  rw [unassign_num_def] >> every_case_tac
  >- fs [absorption_delete_held_thm, held_vnodes_thm, vnumbering_component_equality]
  >- fs [absorption_delete_held_thm, held_vnodes_thm, vnumbering_component_equality]
  >-
  (`(nums with <| vnums updated_by delete var;
                  vnodes updated_by delete_held var n|>).vnodes =
     delete_held var n nums.vnodes` by fs[]
  >> drule_then (lt simp) delete_held_thm 
  >> CASE_TAC >> fs [absorption_delete_held_thm]));

val uses_unassign_thm = Q.store_thm("uses_unassign",
  `∀var vn nums.
    uses vn (unassign_num var nums) = uses vn nums`,
  rw [unassign_num_def] >> every_case_tac
  >- fs [vnumbering_component_equality, uses_def]
  >- fs [vnumbering_component_equality, uses_def]
  >> irule uses_delete_held_thm >> rw [] >> metis_tac []);

val operands_unassign_thm = Q.store_thm("operands_unassign",
  `∀var vn nums.
    operands vn (unassign_num var nums) = operands vn nums`,
  rw [unassign_num_def] >> every_case_tac
  >- fs [vnumbering_component_equality, operands_def]
  >- fs [vnumbering_component_equality, operands_def]
  >> irule operands_delete_held_thm >> rw [] >> metis_tac []);

val label_unassign_thm = Q.store_thm("label_unassign",
  `∀var vn nums.  
    label vn (unassign_num var nums) = label vn nums`,
  rw [unassign_num_def] >> every_case_tac
  >- fs [vnumbering_component_equality, label_def]
  >- fs [vnumbering_component_equality, label_def]
  >> irule label_delete_held_thm >> rw [] >> metis_tac []);

val domain_unassign_thm = Q.store_thm("domain_unassign",
  `∀var nums.
    domain (unassign_num var nums).vnodes = domain nums.vnodes`,
  rw [unassign_num_def] >> every_case_tac
  >> fs [delete_held_def] >> CASE_TAC
  >> metis_tac [domain_insert, domain_lookup, ABSORPTION]);

val valid_unassign_thm = Q.store_thm("valid_unassign",
  `∀var (vn:α vnumber) (nums:α vnumbering).
    valid vn (unassign_num var nums) = valid vn nums`,
  Cases_on `vn` >> fs [valid_def, domain_unassign_thm]);

val wf_unassign_thm = Q.store_thm("wf_unassign",
  `∀var nums.
    wf_nums nums ⇒ wf_nums (unassign_num var nums)`,
  (rpt strip_tac) >> rw [wf_nums_def]
  >- 
  (fs [get_num_unassign_thm, held_unassign_thm]
  >> metis_tac [wf_nums_def])
  >-
  (fs [domain_unassign_thm, unassign_num_def]
  >> every_case_tac
  >> fs [vnumbering_component_equality, delete_held_def]
  >> metis_tac [wf_nums_def])
  >-
  (fs [operands_unassign_thm, uses_unassign_thm]
  >> metis_tac [wf_nums_def])
  >-
  (fs [operands_unassign_thm, uses_unassign_thm]
  >> metis_tac [wf_nums_def])
  >-
  (fs [uses_unassign_thm, domain_unassign_thm, valid_def]
  >> metis_tac [wf_nums_def]));

val eval_vn_unassign_thm = Q.store_thm("eval_vn_unassign",
  `∀var x vn nums s ns res.
    cse_state_rel nums s ∧ wf_nums nums ∧
    eval_vn vn (unassign_num var nums) (set_var var x s) = SOME res ⇒
    eval_vn vn nums s = SOME res`,
  gen_tac >> gen_tac >> recInduct eval_vn_ind >> rw []
  >- fs [eval_vn_def]
  >-
  (simp [eval_vn_thm] >> fs [eval_vn_def, label_unassign_thm]
  >> fs [operands_unassign_thm, option_case_eq]
  >- metis_tac [held_unassign_thm, get_any_delete_thm]
  >- metis_tac [held_unassign_thm, get_any_delete_thm]
  >-
  (drule option_seq_mono >> rw []
  >> pop_assum (qspecl_then [`\v. eval_vn v nums s`] assume_tac)
  >> rfs [eval_vnode_def,eval_exp_def])));

val eval_var_unassign_thm = Q.store_thm("eval_var_unassign",
  `∀var1 var2 nums s ns res.
    cse_state_rel nums s ∧ wf_nums nums ∧
    eval_var var1 (unassign_num var2 nums) (set_var var2 x s) = SOME res ⇒
    var1 <> var2 ∧ eval_var var1 nums s = SOME res`,
  rw [eval_var_def, get_num_unassign_thm]
  >> metis_tac [eval_vn_unassign_thm]);

val state_unassign_thm = Q.store_thm("state_unassign",
  `∀var nums s x.
    wf_nums nums ∧ cse_state_rel nums s ⇒
    cse_state_rel (unassign_num var nums) (set_var var x s)`,
  (rpt strip_tac) >> rw [cse_state_rel_def]
  >-
  (fs [get_var_set_var_thm]
  >> metis_tac [eval_var_unassign_thm, cse_state_rel_def])
  >-
  (fs [get_num_unassign_thm, get_var_set_var_thm]
  >> metis_tac [cse_state_rel_def, IS_SOME_DEF]))

(* assign_num thms *)
val get_num_assign_thm = Q.store_thm("get_num_assign",
  `∀var1 var2 vn nums.
    get_num var1 (assign_num var2 vn nums) =
    if var1 = var2 then SOME vn else get_num var1 nums`,
  rpt gen_tac >> Cases_on `vn` >> rw [assign_num_def]
  >> fs [get_num_def, lookup_insert]
  >> metis_tac [get_num_def, get_num_unassign_thm]);

val held_assign_thm = Q.store_thm("held_assign",
  `∀var vn vnum nums.
    wf_nums nums ∧ valid vnum nums ⇒
    held vn (assign_num var vnum nums) =
    if vnum = VN vn then var INSERT held vn nums
    else held vn nums DELETE var`,
  (rpt gen_tac) >> Cases_on `vnum`
  >-
  (rw [assign_num_def]
  >> `(unassign_num var nums with vnums updated_by insert var (VConst c))
        .vnodes = (unassign_num var nums).vnodes` by fs[]
  >> drule held_vnodes_thm >> rw [held_unassign_thm])
  >-
  (simp [assign_num_def]
  >> `(unassign_num var nums with <| vnums updated_by insert var (VN n);
                  vnodes updated_by insert_held var n|>).vnodes =
                  insert_held var n (unassign_num var nums).vnodes` by fs[]
  >> strip_tac
  >> `n ∈ domain (unassign_num var nums).vnodes` by
       fs [valid_def, domain_unassign_thm]
  >> drule insert_held_thm >> disch_then drule
  >> rw [held_unassign_thm] >> Cases_on `var IN held n nums`
  >- fs [INSERT_DELETE, ABSORPTION]
  >- fs [DELETE_NON_ELEMENT]));

val uses_assign_thm = Q.store_thm("uses_assign",
  `∀var vnum vn nums.
    uses vn (assign_num var vnum nums) = uses vn nums`,
  rpt gen_tac >> Cases_on `vnum` >> fs [assign_num_def, uses_def]
  >- metis_tac [uses_def, uses_unassign_thm]
  >> fs [insert_held_def] >> CASE_TAC
  >- metis_tac [uses_def, uses_unassign_thm]
  >> fs [lookup_insert] >> Cases_on `vn = n` >> fs []
  >- (qspecl_then [`var`, `n`, `nums`] assume_tac uses_unassign_thm
     >> rfs [uses_def])
  >> metis_tac [uses_def, uses_unassign_thm]);

val operands_assign_thm = Q.store_thm("operands_assign",
  `∀var vnum vn nums.
    operands vn (assign_num var vnum nums) = operands vn nums`,
  rpt gen_tac >> Cases_on `vnum` >> fs [assign_num_def, operands_def]
  >- metis_tac [operands_def, operands_unassign_thm]
  >> fs [insert_held_def] >> CASE_TAC
  >- metis_tac [operands_def, operands_unassign_thm]
  >> fs [lookup_insert] >> Cases_on `vn = n` >> fs []
  >- (qspecl_then [`var`, `n`, `nums`] assume_tac operands_unassign_thm
     >> rfs [operands_def])
  >- metis_tac [operands_def, operands_unassign_thm]);

val label_assign_thm = Q.store_thm("label_assign",
  `∀var vnum vn nums.  
    label vn (assign_num var vnum nums) = label vn nums`,
  rpt gen_tac >> Cases_on `vnum` >> fs [assign_num_def, label_def]
  >- metis_tac [label_def, label_unassign_thm]
  >> fs [insert_held_def] >> CASE_TAC
  >- metis_tac [label_def, label_unassign_thm]
  >> fs [lookup_insert] >> Cases_on `vn = n` >> fs []
  >- (qspecl_then [`var`, `vn`, `nums`] assume_tac label_unassign_thm
     >> rfs [label_def])
  >- metis_tac [label_def, label_unassign_thm]);

val domain_assign_thm = Q.store_thm("domain_assign",
  `∀var vnum vn nums.
    domain (assign_num var vnum nums).vnodes = domain nums.vnodes`,
  Cases_on `vnum` >> rw [assign_num_def]
  >- fs [domain_unassign_thm]
  >> fs [vnumbering_component_equality, insert_held_def]
  >> every_case_tac
  >> metis_tac [ABSORPTION, domain_lookup, domain_insert, domain_unassign_thm]);

val valid_assign_thm = Q.store_thm("valid_assign",
  `∀var vnum (vn:α vnumber) (nums:α vnumbering).
    valid vn (assign_num var vnum nums) = valid vn nums`,
  Cases_on `vn` >> fs [valid_def, domain_assign_thm]);

val wf_assign_thm = Q.store_thm("wf_assign",
  `∀var vnum nums.
    wf_nums nums ∧ valid vnum nums ⇒
    wf_nums (assign_num var vnum nums)`,
  (rpt strip_tac) >> rw [wf_nums_def]
  >- 
  (Cases_on `vnum = VN vn` >> fs [get_num_assign_thm, held_assign_thm]
  >> CASE_TAC >> metis_tac [wf_nums_def])
  >-
  (Cases_on `vnum` >> fs [domain_assign_thm, assign_num_def]
  >> metis_tac [wf_unassign_thm, wf_nums_def, domain_unassign_thm])
  >-
  (fs [operands_assign_thm, uses_assign_thm]
  >> metis_tac [wf_nums_def])
  >-
  (fs [operands_assign_thm, uses_assign_thm]
  >> metis_tac [wf_nums_def])
  >-
  (fs [uses_assign_thm, domain_assign_thm, valid_def]
  >> metis_tac [wf_nums_def]));

val eval_vn_valid_thm = Q.store_thm("eval_vn_valid",
  `∀vnum nums s res.
    eval_vn vnum nums s = SOME res ⇒
    valid vnum nums`,
  rw [] >> Cases_on `vnum`
  >> fs [valid_def, eval_vn_def, get_any_def, held_def, label_def]
  >> every_case_tac >> fs [domain_lookup, eval_label_def]);

val eval_vn_assign_thm = Q.store_thm("eval_vn_assign",
  `∀vnum1 res1 var vnum2 nums s res2.
    cse_state_rel nums s ∧ wf_nums nums ∧ eval_vn vnum1 nums s = SOME res1 ⇒
    eval_vn vnum2 (assign_num var vnum1 nums) (set_var var res1 s) = SOME res2 ⇒
    eval_vn vnum2 nums s = SOME res2`,
  gen_tac >> gen_tac >> gen_tac 
  >> recInduct eval_vn_ind >> rw []
    >- fs [eval_vn_def]
    >-
    (simp [eval_vn_thm]
    >> fs [eval_vn_def, label_assign_thm, operands_assign_thm]
    >> drule_all_then assume_tac eval_vn_valid_thm 
    >> drule_all_then (lt fs) held_assign_thm
    >> fs [option_case_eq]
      >-
      (Cases_on `vnum1 = VN vn`
      >> metis_tac [get_any_insert_thm, eval_vn_thm, get_any_delete_thm])
      >-
      (Cases_on `vnum1 = VN vn`
      >> metis_tac [get_any_insert_thm, eval_vn_thm, get_any_delete_thm])
      >-
      (drule option_seq_mono >> rw []
      >> pop_assum (qspecl_then [`\v. eval_vn v nums s`] assume_tac)
      >> rfs [eval_vnode_def,eval_exp_def])));

val eval_var_assign_thm = Q.store_thm("eval_var_assign",
  `∀var1 var2 res1 res2 vnum nums s.
    wf_nums nums ∧ cse_state_rel nums s ∧ eval_vn vnum nums s = SOME res1 ⇒
    eval_var var1 (assign_num var2 vnum nums) (set_var var2 res1 s) = SOME res2 ⇒
    if var1 = var2 then res1 = res2
    else eval_var var1 nums s = SOME res2`,
  rw [eval_var_def, get_num_assign_thm]
  >> drule_all_then (lt fs) eval_vn_assign_thm);

val state_assign_thm = Q.store_thm("state_assign",
  `∀var vnum nums s res.
    wf_nums nums ∧ cse_state_rel nums s ∧
    eval_vn vnum nums s = SOME res ⇒
    cse_state_rel (assign_num var vnum nums) (set_var var res s)`,
  (rpt strip_tac) >> rw [cse_state_rel_def]
  >-
  (fs [get_var_set_var_thm]
  >> metis_tac [eval_var_assign_thm, cse_state_rel_def])
  >-
  (fs [get_num_assign_thm, get_var_set_var_thm] >>  rw []
  >> fs [cse_state_rel_def, eval_var_def]));

(* add_empty_vnode *)
val get_num_not_next_thm = Q.prove(`
  ∀var nums.
  wf_nums nums ⇒ get_num var nums <> SOME (VN nums.next)`,
  rw [wf_nums_def] >> fs [held_def] >> CASE_TAC >- fs []
  >> qpat_x_assum `∀vn. nums.next ≤ vn ⇒ _` (qspec_then `nums.next` assume_tac)
  >> fs [domain_lookup]);

val get_num_add_empty_vnode_thm = Q.prove(`
  ∀ops lbl var nums.
  get_num var (add_empty_vnode lbl ops nums) = get_num var nums`,
  Induct >- fs [add_empty_vnode_def, add_uses_def, get_num_def]
  >-
  (Cases_on `h`
  >> fs [add_empty_vnode_def, add_uses_def, get_num_def]
  >> rpt gen_tac
  >> pop_assum (qspecl_then [`var`,
       `nums with vnodes updated_by insert_use nums.next n`] assume_tac)
  >> fs []));

val held_add_uses_thm = Q.prove (`
  ∀ops vn1 vn2 nums.
  held vn1 (add_uses vn2 ops nums) = held vn1 nums`,
  Induct >- fs [add_uses_def]
  >> Cases_on `h` >- fs [add_uses_def]
  >> rw [] >> fs [held_def, add_uses_def, insert_use_def]
  >> CASE_TAC >> fs [lookup_insert] >> CASE_TAC >> fs []);

val held_add_empty_vnode_thm = Q.prove(`
  ∀ops lbl vn nums.
  wf_nums nums ⇒
  held vn (add_empty_vnode lbl ops nums) = held vn nums`,
  rw [add_empty_vnode_def, held_def, lookup_insert, wf_nums_def]
  >- (CASE_TAC >> metis_tac [LESS_EQ_REFL, domain_lookup, NOT_NONE_SOME])
  >- fs [GSYM held_def, held_add_uses_thm]);

val next_add_empty_vnode_thm = Q.prove(`
  ∀ops nums.
  (add_empty_vnode lbl ops nums).next = SUC (nums.next)`,
  Induct >- fs [add_empty_vnode_def, add_uses_def]
  >> Cases_on `h` >> fs [add_empty_vnode_def, add_uses_def]
  >> gen_tac
  >> pop_assum (qspec_then
       `nums with vnodes updated_by insert_use nums.next n` assume_tac)
  >> fs []);

val domain_add_empty_vnode_thm = Q.prove(`
  ∀ops nums.
  domain (add_empty_vnode lbl ops nums).vnodes = 
  nums.next INSERT domain nums.vnodes`,
  Induct >- fs [add_empty_vnode_def, add_uses_def]
  >> Cases_on `h` >> fs [add_empty_vnode_def, add_uses_def]
  >> gen_tac
  >> pop_assum (qspec_then
       `nums with vnodes updated_by insert_use nums.next n` assume_tac)
  >> fs [insert_use_def] >> CASE_TAC
  >> metis_tac [domain_insert, domain_lookup, ABSORPTION]);

val operands_add_uses_thm = Q.prove(`
  ∀(ops :α vnumber list) (nums :α vnumbering) n vn.
  operands vn (add_uses n ops nums) = operands vn nums`,
  Induct >- fs [add_uses_def]
  >> Cases_on `h` >- fs [add_uses_def]
  >> fs [add_uses_def, operands_def, insert_use_def] >> rw []
  >> CASE_TAC >> fs [lookup_insert]
  >> CASE_TAC >> fs []);

val operands_add_empty_vnode_thm = Q.prove(`
  ∀ops nums.
  operands vn (add_empty_vnode lbl ops nums) =
    if vn = nums.next then ops
    else operands vn nums`,
  rw [add_empty_vnode_def, operands_def, lookup_insert]
  >> metis_tac [operands_def, operands_add_uses_thm]);

val label_add_uses_thm = Q.prove(`
  ∀(ops :α vnumber list) (nums :α vnumbering) n vn.
  label vn (add_uses n ops nums) = label vn nums`,
  Induct >- fs [add_uses_def]
  >> Cases_on `h` >- fs [add_uses_def]
  >> fs [add_uses_def, label_def, insert_use_def] >> rw []
  >> CASE_TAC >> fs [lookup_insert]
  >> CASE_TAC >> fs []);

val label_add_empty_vnode_thm = Q.prove(`
  ∀ops nums.
  label vn (add_empty_vnode lbl ops nums) =
    if vn = nums.next then lbl
    else label vn nums`,
  rw [add_empty_vnode_def, label_def, lookup_insert]
  >> metis_tac [label_def, label_add_uses_thm]);

val valid_insert_use_thm = Q.prove(`
  ∀v nums vn1 vn2.
  valid v (nums with vnodes updated_by insert_use vn1 vn2) ⇔
  valid v nums`,
  Cases_on `v` >> rw [valid_def, insert_use_def]
  >> CASE_TAC >> fs [] >> EQ_TAC >> rw [] >> metis_tac [domain_lookup]);

val uses_add_uses_thm = Q.prove(`
  ∀(ops :α vnumber list) (nums :α vnumbering) n vn.
  EVERY (\l. valid l nums) ops ⇒
  uses vn (add_uses n ops nums) =
    if MEM (VN vn) ops then n INSERT uses vn nums
    else uses vn nums`,
  Induct >- fs [add_uses_def]
  >> Cases_on `h` >- fs [add_uses_def]
  >> rw []
    >- 
    (fs [add_uses_def, valid_insert_use_thm]
    >> CASE_TAC >> simp [uses_def, insert_use_def]
    >> CASE_TAC >> fs [lookup_insert, valid_def, domain_lookup])
  >> fs [add_uses_def, valid_insert_use_thm]
  >> simp [uses_def, insert_use_def]
  >> CASE_TAC >> fs [lookup_insert]
  >> CASE_TAC >> fs []);

val uses_add_empty_vnode_thm = Q.prove(`
  ∀vn ops nums.
  wf_nums nums ∧ EVERY (\l. valid l nums) ops ⇒
  uses vn (add_empty_vnode lbl ops nums) =
    if MEM (VN vn) ops then nums.next INSERT uses vn nums
    else uses vn nums`,
  rw [add_empty_vnode_def, uses_def, lookup_insert]
    >-
    (Cases_on `wf_nums nums` >> fs []
    >> qspecl_then [`$~ o (\l. valid l nums)`, `ops`] assume_tac
         (INST_TYPE [``:α`` |-> ``:α vnumber``] EXISTS_MEM)
    >> fs [] >> qexists_tac `VN nums.next` >> fs [valid_def]
    >> metis_tac [wf_nums_def, LESS_EQ_REFL, domain_lookup, NOT_NONE_SOME])
    >-
    (CASE_TAC
    >> metis_tac [wf_nums_def, LESS_EQ_REFL, domain_lookup, NOT_NONE_SOME])
  >> metis_tac [uses_add_uses_thm, uses_def]);

val wf_add_empty_vnode_thm = Q.prove(`
  ∀lbl ops nums.
  wf_nums nums ∧ EVERY (\p. valid p nums) ops ⇒
  wf_nums (add_empty_vnode lbl ops nums)`,
  rw []
  >> `nums.next ∉ domain nums.vnodes` by metis_tac [wf_nums_def, LESS_EQ_REFL,
       domain_lookup, NOT_NONE_SOME]
  >> rw [wf_nums_def]
  >- metis_tac [wf_nums_def, get_num_add_empty_vnode_thm,
       held_add_empty_vnode_thm]
  >- fs [next_add_empty_vnode_thm, domain_add_empty_vnode_thm, wf_nums_def]
  >-
  (fs [operands_add_empty_vnode_thm, uses_add_empty_vnode_thm]
  >> every_case_tac >> fs [] >> metis_tac [wf_nums_def, SUBSET_DEF])
  >-  
  (fs [operands_add_empty_vnode_thm]
  >> reverse (Cases_on `vn = nums.next`) >- metis_tac [wf_nums_def]
  >> qspecl_then [`\p. valid p nums`, `ops`] assume_tac
       (INST_TYPE [``:α`` |-> ``:α vnumber``] EVERY_MEM)
  >> fs [] >> res_tac >> fs [valid_def, wf_nums_def]
  >> CCONTR_TAC >> `nums.next ≤ op` by  fs []
  >> metis_tac []) 
  >-
  (fs [uses_add_empty_vnode_thm, domain_add_empty_vnode_thm]
  >> CASE_TAC >> fs [wf_nums_def, SUBSET_DEF] >> metis_tac []));

val eval_vn_add_empty_vnode_thm = Q.prove(`
  ∀nums ops lbl vn nnums st.
  wf_nums nums ∧ cse_state_rel nums st ∧
  EVERY (\p. valid p nums) ops ∧
  add_empty_vnode lbl ops nums = nnums ⇒
  eval_vn vn nnums st = 
    if vn = VN nums.next then eval_exp lbl ops nums st
    else eval_vn vn nums st`,
  ntac 3 gen_tac>>
  recInduct eval_vn_ind>>rw []
  >- (fs [eval_vn_def])
  >- (
    fs [eval_vn_def,operands_add_empty_vnode_thm,label_add_empty_vnode_thm]>>
    fs [held_add_empty_vnode_thm]>>
    full_case_tac
    >- (fs []>>imp_res_tac EVERY_MEM>>metis_tac [valid_def,wf_nums_def])
    >- (
      `nums.next ∉ domain nums.vnodes` by metis_tac [LESS_EQ_REFL,wf_nums_def]>>
      fs [held_def]>>full_case_tac>>fs [domain_lookup,get_any_def]>>
      `(MAP (λv. eval_vn v (add_empty_vnode lbl ops nums) s) ops) =
        (MAP (λv. eval_vn v nums s) ops)` by (
        rw [MAP_EQ_f]>>imp_res_tac EVERY_MEM>>
        metis_tac [valid_def,wf_nums_def,LESS_EQ_REFL])>>
      fs[eval_exp_def]>>full_case_tac>>fs []))
  >- (
    fs [eval_vn_def,operands_add_empty_vnode_thm,label_add_empty_vnode_thm]>>
    fs [held_add_empty_vnode_thm]>>
    `nums.next ∉ domain nums.vnodes` by metis_tac [LESS_EQ_REFL,wf_nums_def]>>
    full_case_tac>>rfs[]>>fs[]>>
    `(MAP (λv. eval_vn v (add_empty_vnode lbl ops nums) s) (operands n nums)) =
        (MAP (λv. eval_vn v nums s) (operands n nums ))` by (
      rw [MAP_EQ_f]>>fs[wf_nums_def]>>
      metis_tac[SUBSET_DEF, LESS_IMP_LESS_OR_EQ, NOT_LESS_EQUAL])>>
    fs []));

val state_add_empty_vnode_thm = Q.prove(`
  ∀nums st lbl ops.
  wf_nums nums ∧ cse_state_rel nums st ∧
  EVERY (\p. valid p nums) ops ⇒
  cse_state_rel (add_empty_vnode lbl ops nums) st`,
  rpt gen_tac>>strip_tac>>rw[cse_state_rel_def]
  >- (
    fs[eval_var_def,get_num_add_empty_vnode_thm]>>
    `vn <> VN nums.next` by metis_tac[get_num_not_next_thm]>>
    drule eval_vn_add_empty_vnode_thm>>fs[]>>
    disch_then drule_all>>rw[]>>
    fs[cse_state_rel_def,eval_var_def])
  >- metis_tac[get_num_add_empty_vnode_thm,cse_state_rel_def]);

(* add_vnode *)
val wf_add_vnode_thm = Q.prove(`
  ∀lbl dst ops nums.
  wf_nums nums ∧ EVERY (\p. valid p nums) ops ⇒
  wf_nums (add_vnode lbl dst ops nums)`,
  rw [add_vnode_def] >> match_mp_tac wf_assign_thm
  >> fs [valid_def, domain_add_empty_vnode_thm]
  >> metis_tac [wf_add_empty_vnode_thm]);

val eval_vns_valid_thm = Q.prove(`
  ∀ops nums st x.
  option_seq (MAP (λv. eval_vn v nums st) ops) = SOME x ⇒
  EVERY (λp. valid p nums) ops`,
  Induct >> rw [option_seq_def, option_case_eq]
  >> metis_tac [eval_vn_valid_thm]);

val eval_var_add_vnode_thm = Q.prove(`
  ∀nums ops lbl var st dst x res.
  wf_nums nums ∧ cse_state_rel nums st ∧
  eval_exp lbl ops nums st = SOME x ∧
  eval_var var (add_vnode lbl dst ops nums) (set_var dst x st) = SOME res ⇒
  if var = dst then res = x
  else eval_var var nums st = SOME res`,
  rpt gen_tac>>strip_tac>>fs[add_vnode_def,eval_var_def]>>
  `EVERY (λp. valid p nums) ops` by
    (fs[eval_exp_def]>>metis_tac[eval_vns_valid_thm])>>
  drule eval_vn_add_empty_vnode_thm>>
  rpt (disch_then drule)>>fs[]>>strip_tac>>
  drule_all_then (qspec_then `lbl` assume_tac) state_add_empty_vnode_thm>>
  drule_all_then (qspec_then `lbl` assume_tac) wf_add_empty_vnode_thm>>
  `eval_vn (VN nums.next) (add_empty_vnode lbl ops nums) st = SOME x` by
    metis_tac[]>>
  drule_all eval_vn_assign_thm>>strip_tac>>rfs[]>>
  fs[get_num_assign_thm,get_num_add_empty_vnode_thm]>>
  full_case_tac>-rfs []
  >-metis_tac[get_num_not_next_thm]);

val eval_vn_add_vnode_unknown_thm = Q.prove(`
  ∀dst x vn nums st.
  wf_nums nums ∧ cse_state_rel nums st ∧
  get_num dst nums = NONE ∧ get_var dst st = SOME x ⇒ 
  eval_vn vn (add_vnode VUnknown dst [] nums) st =
  if vn = VN nums.next then SOME x
  else eval_vn vn nums st`,
  ntac 2 gen_tac>>recInduct eval_vn_ind>>CONJ_TAC
  >- (rw[eval_vn_def])
  >- (
    ntac 2 (rpt gen_tac>>strip_tac)>>fs[add_vnode_def]>>
    `EVERY (λp. valid (p :α vnumber) nums) []` by fs[]>>
    drule eval_vn_add_empty_vnode_thm>>
    ntac 2 (disch_then drule)>>simp[]>>
    disch_then (qspec_then `VUnknown` assume_tac)>>
    drule_all_then (qspec_then `VUnknown` assume_tac) wf_add_empty_vnode_thm>>
    drule_all_then (qspec_then `VUnknown` assume_tac) state_add_empty_vnode_thm>>
    simp[eval_vn_def]>>
    fs[label_assign_thm,operands_assign_thm,operands_add_empty_vnode_thm]>>
    fs[valid_def,domain_add_empty_vnode_thm,held_assign_thm]>>
    fs[label_add_empty_vnode_thm,held_add_empty_vnode_thm]>>
    full_case_tac
    >- ((* eval on nums.next *)
      fs[eval_label_def,option_seq_def,held_def]>>CASE_TAC>>
      fs[get_any_def,min_only_thm]>>
      metis_tac[wf_nums_def,LESS_EQ_REFL,NOT_NONE_SOME,domain_lookup])
    >- (
      CASE_TAC>-(fs[]>>drule_all dag_thm>>fs[])>>fs[]>>
      qabbrev_tac `nnums = add_empty_vnode VUnknown [] nums`>>
      `MAP (λv. eval_vn v (assign_num dst (VN nums.next) nnums) s)
          (operands n nums) = MAP (λv. eval_vn v nums s) (operands n nums)` by (
        rw [MAP_EQ_f]>>fs[wf_nums_def]>>
        metis_tac[SUBSET_DEF, LESS_IMP_LESS_OR_EQ, NOT_LESS_EQUAL])>>
      fs[]>>full_case_tac>>
      `dst ∉ held n nums` by metis_tac [wf_nums_def, NOT_NONE_SOME]>>
      fs [DELETE_NON_ELEMENT])));

val state_add_vnode_thm = Q.prove(`
  ∀nums lbl dst ops x st.
  wf_nums nums ∧ cse_state_rel nums st ∧
  eval_exp lbl ops nums st = SOME x ⇒
  cse_state_rel (add_vnode lbl dst ops nums) (set_var dst x st)`,
  rpt gen_tac>>strip_tac>>rw[cse_state_rel_def,get_var_set_var_thm]
  >- (full_case_tac>>metis_tac[eval_var_add_vnode_thm,cse_state_rel_def])
  >- (
    full_case_tac>>
    fs [get_num_assign_thm,get_num_add_empty_vnode_thm,add_vnode_def]>>
    metis_tac[cse_state_rel_def]));

val valid_add_vnode_thm = Q.prove(`
  ∀vn lbl dst ops nums.
  valid vn nums ⇒
  valid vn (add_vnode lbl dst ops nums)`,
  rw [] >> fs [add_vnode_def] >> Cases_on `vn`
  >> fs [valid_def, domain_assign_thm, domain_add_empty_vnode_thm]);

(* get_or_assign_num *)
val get_or_assign_num_thm = Q.prove(`
  ∀var nums vn nnums.
  get_or_assign_num var nums = (vn, nnums) ⇒
  get_num var nnums = SOME vn`,
  rpt gen_tac>>fs[get_or_assign_num_def]>>full_case_tac>>
  rw[add_vnode_def]>>fs[get_num_assign_thm,get_num_add_empty_vnode_thm]);

val wf_get_or_assign_thm = Q.prove(`
  ∀var nums vn nnums.  
  wf_nums nums ⇒
  get_or_assign_num var nums = (vn, nnums) ⇒
  wf_nums nnums`,
  rpt gen_tac>>fs[get_or_assign_num_def]>>full_case_tac>>
  rw[]>>fs[wf_add_vnode_thm]);

val state_get_or_assign_thm = Q.prove(`
  ∀var nums st vn nnums.  
  wf_nums nums ∧ cse_state_rel nums st ∧ IS_SOME(get_var var st) ∧
  get_or_assign_num var nums = (vn, nnums) ⇒
  cse_state_rel nnums st`,
  rpt gen_tac>>fs[get_or_assign_num_def]>>full_case_tac>>
  strip_tac>>rw[cse_state_rel_def]
  >- (
    fs[eval_var_def,IS_SOME_EXISTS]>>drule_all eval_vn_add_vnode_unknown_thm>>
    disch_then (qspec_then `vn` mp_tac)>>full_case_tac>>strip_tac>>
    fs[add_vnode_def,get_num_assign_thm,get_num_add_empty_vnode_thm]>>
    Cases_on `var=var'`>>fs[]
    >- (metis_tac [get_num_not_next_thm])
    >- (fs[cse_state_rel_def,eval_var_def]>>metis_tac[]))
  >- (
    fs[add_vnode_def,get_num_assign_thm,get_num_add_empty_vnode_thm]>>
    Cases_on `var=var'`>>fs[]>>metis_tac[cse_state_rel_def]));

(* get_or_assign_nums *)
val get_num_get_or_assign_nums_thm = Q.prove(`
  ∀vars vns nnums vn nums var.
  get_or_assign_nums vars nums = (vns, nnums) ∧
  get_num var nums = SOME vn ⇒
  get_num var nnums = SOME vn`,
  Induct>>fs[get_or_assign_nums_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>
  first_x_assum irule>>qexists_tac `nums1`>>qexists_tac `vns'`>>
  fs[get_or_assign_num_def]>>Cases_on `get_num h nums`>>fs[]>>
  rw [add_vnode_def,get_num_assign_thm,get_num_add_empty_vnode_thm]>>fs[]);

val get_or_assign_nums_thm = Q.prove(`
  ∀vars nums vns nnums.
  get_or_assign_nums vars nums = (vns, nnums) ⇒
  EVERY (\(v,vn). get_num v nnums = SOME vn) (ZIP (vars, vns))`,
  Induct>>fs[get_or_assign_nums_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>
  drule get_or_assign_num_thm>>rw[]>>
  metis_tac [get_num_get_or_assign_nums_thm]);

val wf_get_or_assign_nums_thm = Q.prove(`
  ∀vars nums vns nnums.
  wf_nums nums ∧ get_or_assign_nums vars nums = (vns, nnums) ⇒
  wf_nums nnums`,
  Induct>>fs[get_or_assign_nums_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>
  metis_tac[wf_get_or_assign_thm]);

val valid_get_or_assign_nums_thm = Q.prove(`
  ∀vars nums vns nnums.
  wf_nums nums ∧ get_or_assign_nums vars nums = (vns, nnums) ⇒
  EVERY (\v. valid v nnums) vns`,
  Induct>>fs[get_or_assign_nums_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>rw[]
  >- (
    irule get_num_valid_thm
    >- (metis_tac[wf_get_or_assign_nums_thm, wf_get_or_assign_thm])
    >- (drule get_or_assign_num_thm>>metis_tac[get_num_get_or_assign_nums_thm]))
  >- (
    first_x_assum irule>>
    metis_tac[wf_get_or_assign_nums_thm, wf_get_or_assign_thm]));

val state_get_or_assign_nums_thm = Q.prove(`
  ∀vars nums vns nnums st.
  wf_nums nums ∧ cse_state_rel nums st ∧
  EVERY (\v. IS_SOME(get_var v st)) vars ∧
  get_or_assign_nums vars nums = (vns, nnums) ⇒
  cse_state_rel nnums st`,
  Induct>>fs[get_or_assign_nums_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>
  metis_tac[state_get_or_assign_thm,wf_get_or_assign_thm]);

val the_words_get_or_assign_nums_thm = Q.prove(`
  ∀vars ws nums st nnums vns.
  wf_nums nums ∧ cse_state_rel nums st ∧
  get_or_assign_nums vars nums = (vns,nnums) ∧
  the_words (MAP (λv. get_var v st) vars) = SOME ws ⇒
  option_seq (MAP (λv. eval_vn v nnums st) vns) = SOME (MAP Word ws)`,
  Induct>>
  fs[option_seq_def,the_words_def,get_or_assign_nums_def,option_case_eq]>>rw[]>>
  Cases_on `v5`>>fs[option_case_eq]>>rpt (pairarg_tac>>fs[])>>rw[]>>
  fs[option_seq_def,option_case_eq]>>
  drule_all wf_get_or_assign_thm>>strip_tac>>
  `cse_state_rel nums1 st` by
    metis_tac[state_get_or_assign_thm,IS_SOME_EXISTS]>>
  drule_all wf_get_or_assign_nums_thm>>strip_tac>>
  `cse_state_rel nnums st` by
    metis_tac[state_get_or_assign_nums_thm,the_words_EVERY_IS_SOME,EVERY_MAP]>>
  strip_tac
  >- (
    drule_all get_or_assign_num_thm>>strip_tac>>
    drule_all get_num_get_or_assign_nums_thm>>strip_tac>>
    Cases_on `vn`
    >- (fs[eval_var_def,cse_state_rel_def]>>res_tac>>fs[eval_vn_def])
    >- (irule get_any_eval_vn_thm>>fs[]>>metis_tac[get_any_get_var_thm]))
  >- (first_x_assum irule>>metis_tac[]));

(* find_exp thms *)
val all_const_the_words_thm = Q.prove(`
  ∀vns cs ws x nums st.
  option_seq (MAP (λv. eval_vn v nums st) vns) = SOME x ∧
  the_words (MAP SOME x) = SOME ws ∧
  all_const vns = SOME cs ⇒
  cs = ws`,
  Induct>>fs[option_seq_def,all_const_def,option_case_eq]>>rw[]>>
  reverse(Cases_on `h`)>-fs[option_case_eq,all_const_def]>>
  fs[all_const_def,option_case_eq,the_words_def]>>
  Cases_on `e`>>fs[option_case_eq]>>rw[]
  >- fs[eval_vn_def]
  >- metis_tac[]);

val find_exp_eval_vn_thm = Q.prove(`
  ∀st lbl vns nums vn res.
  wf_nums nums ∧ cse_state_rel nums st ∧
  find_exp lbl vns nums = SOME vn ∧
  eval_exp lbl vns nums st = SOME res ⇒
  eval_vn vn nums st = SOME res`,
  rw[find_exp_def]>>Cases_on `attempt_fold lbl vns`
  >- (
    fs[eval_exp_def,eval_vn_def,attempt_match_def,list_case_eq]>>
    `MEM x [x]` by fs[]>>
    `compare_exp lbl vns nums x` by metis_tac[MEM_FILTER]>>
    rw[eval_vn_def]>-(fs[]>>drule_all dag_thm>>rw[])>>
    fs[compare_exp_def,operands_def,label_def]>>
    Cases_on `lookup x nums.vnodes`>>fs[])
  >- (
    fs[attempt_fold_def]>>rw[]>>Cases_on `lbl`>>
    fs[eval_exp_def,fold_def,eval_label_def,eval_vn_def]>>
    drule_all all_const_the_words_thm>>rw[]>>fs[]));

val gen_prog_thm = Q.prove(`
  ∀nums st res dst vn nprog rloc loc.
  cse_state_locals_rel nums st loc ∧
  eval_vn vn nums st = SOME res ∧
  gen_prog dst vn nums = SOME nprog ⇒
  ∃rloc.
  evaluate (nprog,st with locals := loc) = (NONE,st with locals := rloc) ∧
  ∀v. lookup v rloc = if v = dst then SOME res else lookup v st.locals`,
  rw[gen_prog_def]
  >- (
    fs[evaluate_def]>>qexists_tac `loc`>>Cases_on `st`>>
    fs[state_locals_fupd,cse_state_locals_rel_def,locals_rel_def]>>
    fs[cse_state_rel_def,eval_var_def,get_var_def,cse_state_locals_rel_def]>>
    res_tac>>metis_tac[])
  >- (
    Cases_on `vn`
    >- (
      fs[gen_move_def,eval_vn_def]>>
      rw[evaluate_def,inst_def,assign_def,option_case_eq,word_exp_def]>>
      fs[set_var_def]>>qexists_tac `insert dst (Word c) loc`>>
      fs[set_var_def,lookup_insert,cse_state_locals_rel_def])
    >- (
      fs [gen_move_def,option_case_eq,list_case_eq]>>
      PairCases_on `v2`>>fs[]>>
      rw[evaluate_def,inst_def,assign_def,option_case_eq,word_exp_def]>>
      fs[get_vars_def,set_vars_def,option_case_eq,get_var_def]>>
      qexists_tac `insert dst res loc`>>fs[cse_state_locals_rel_def]>>
      rw[lookup_insert]>>qexists_tac `[res]`>>rw[alist_insert_def]>>
      `MEM (v20,()) (toAList node.held)` by fs[]>>
      fs[MEM_toAList,cse_state_rel_def,eval_var_def,wf_nums_def]>>
      res_tac>>rfs[held_def,domain_lookup]>>metis_tac[get_var_def])));

val gen_prog_cases_thm = Q.prove(`
  ∀dst vn nums nprog.
  gen_prog dst vn nums = SOME nprog ⇒
  nprog = Skip ∨
  ∃w. nprog = Inst (Const dst w) ∨
  ∃s. nprog = Move 0 [(dst,s)]`,
  rw[gen_prog_def]>>Cases_on `vn`>>fs[gen_move_def]>>
  every_case_tac>>fs[]>>rw[]);

(* cse_move thms *)
val wf_assign_nums_thm = Q.store_thm("wf_assign_nums",
  `∀vns nums.
    wf_nums nums ∧ (!v vn. MEM (v, SOME vn) vns ⇒ valid vn nums) ⇒ 
    wf_nums (assign_nums vns nums)`,
  Induct >> rw [assign_nums_def]
  >> Cases_on `h` >> Cases_on `r` >> fs [assign_nums_def]
  >- metis_tac [valid_unassign_thm, wf_unassign_thm]
  >- metis_tac [valid_assign_thm, wf_assign_thm]);

val get_moves_valid_thm = Q.store_thm("get_moves_valid",
  `∀(moves : (num, num) alist) nums.
    wf_nums nums ⇒
    (∀v vn. MEM (v, SOME vn) (get_moves moves nums) ⇒ valid vn nums)`,
  Induct >> rw [get_moves_def, get_nums_def]
  >-
  (Cases_on `vn` >> fs [valid_def]
  >> `SND h ∈ held n nums` by metis_tac [wf_nums_def] >> fs [held_def]
  >> Cases_on `lookup n nums.vnodes` >> fs [domain_lookup])
  >- metis_tac [get_moves_def, get_nums_def]);

val get_num_assign_nums_thm = Q.store_thm("get_num_assign_nums",
  `∀vns var nums.
    ALL_DISTINCT (MAP FST vns) ⇒
    get_num var (assign_nums vns nums) =
    case ALOOKUP vns var of
      | SOME vn => vn
      | NONE => get_num var nums`,
  Induct >> rw [assign_nums_def]
  >> Cases_on `h`
  >> rename1 `¬MEM (FST (var2,vnum)) _`
  >> Cases_on `vnum`
    >-
    (fs [assign_nums_def, get_num_unassign_thm] >> CASE_TAC
      >- metis_tac [option_case_eq, ALOOKUP_NONE]
      >- (CASE_TAC >> fs []))
    >-
    (fs [assign_nums_def, get_num_assign_thm] >> CASE_TAC
      >- metis_tac [option_case_eq, ALOOKUP_NONE]
      >- (CASE_TAC >> fs [])));

val alookup_moves_some_thm = Q.store_thm("alookup_moves_some",
  `∀(moves : (num, num) alist) var dst nums.
    ALOOKUP moves var = SOME dst ⇒
    ALOOKUP (get_moves moves nums) var = SOME (get_num dst nums)`,
  Induct >> rw [get_moves_def, get_nums_def]
  >> Cases_on `h` >> fs []
  >> metis_tac [get_moves_def, get_nums_def, get_num_def]);

val alookup_moves_none_thm = Q.store_thm("alookup_moves_none",
  `∀(moves : (num, num) alist) var nums.
    ALOOKUP moves var = NONE ⇒
    ALOOKUP (get_moves moves nums) var = NONE`,
  Induct >> rw [get_moves_def, get_nums_def]
  >> Cases_on `h` >> fs []
  >> metis_tac [get_moves_def, get_nums_def, get_num_def]);

val distinct_moves_thm = Q.store_thm("distinct_moves",
  `∀moves nums.
    ALL_DISTINCT (MAP FST moves) ⇒
    ALL_DISTINCT (MAP FST (get_moves moves nums))`,
  fs [get_moves_def, get_nums_def]
  >> metis_tac [MAP_ZIP, LENGTH_MAP]);

val get_num_moves_thm = Q.store_thm("get_num_moves",
  `∀moves var nums.
    ALL_DISTINCT (MAP FST moves) ⇒
    get_num var (assign_nums (get_moves moves nums) nums) =
    case ALOOKUP moves var of
      | SOME src => get_num src nums
      | NONE => get_num var nums`,
  rw [get_num_assign_nums_thm, distinct_moves_thm]
  >> every_case_tac
  >- (drule alookup_moves_some_thm >> disch_then (lt fs))
  >- (drule alookup_moves_none_thm >> disch_then (lt fs))
  >- (drule alookup_moves_some_thm >> disch_then (lt fs)));

val operands_assign_nums_thm = Q.store_thm("operands_assign_nums",
  `∀vns vn nums.
    operands vn (assign_nums vns nums) = operands vn nums`,
  Induct >> rw [assign_nums_def]
  >> Cases_on `h` >> fs [assign_nums_def]
  >> rename1 `_ vn (_ ((var2,vnum)::vns) _) = _`
  >> Cases_on `vnum`
  >- fs [assign_nums_def, operands_unassign_thm]
  >- fs [assign_nums_def, operands_assign_thm]);

val label_assign_nums_thm = Q.store_thm("label_assign_nums",
  `∀vns vn nums.
    label vn (assign_nums vns nums) = label vn nums`,
  Induct >> rw [assign_nums_def]
  >> Cases_on `h` >> fs [assign_nums_def]
  >> rename1 `_ vn (_ ((var2,vnum)::vns) _) = _`
  >> Cases_on `vnum`
  >- fs [assign_nums_def, label_unassign_thm]
  >- fs [assign_nums_def, label_assign_thm]);

val held_moves_thm = Q.store_thm("held_moves",
  `∀moves nums vn var.
    wf_nums nums ∧ 
    ALL_DISTINCT (MAP FST moves) ∧
    var IN held vn (assign_nums (get_moves moves nums) nums) ⇒ 
    case ALOOKUP moves var of
      | SOME orig => orig IN held vn nums
      | NONE => var IN held vn nums`,
  rw []
  >> qspec_then `moves` drule get_moves_valid_thm >> rw []
  >> drule_all_then assume_tac wf_assign_nums_thm
  >> `get_num var (assign_nums (get_moves moves nums) nums) = SOME (VN vn)` by
       metis_tac [wf_nums_def]
  >> rfs [get_num_moves_thm] >> CASE_TAC
  >- rfs [wf_nums_def]
  >- rfs [wf_nums_def]);

val get_any_assign_nums_thm = Q.store_thm("get_any_assign_nums",
  `∀moves nums nnums vn vals s res.
    wf_nums nums ∧ cse_state_rel nums s ∧ ALL_DISTINCT (MAP FST moves) ∧
    get_vars (MAP SND moves) s = SOME vals ∧
    assign_nums (get_moves moves nums) nums = nnums ∧
    get_any (held vn nnums) (set_vars (MAP FST moves) vals s) = SOME res ⇒
    get_any (held vn nums) s = SOME res`,
  rw [] >> fs [get_any_def]
  >> drule_all_then assume_tac min_in_thm
  >> drule_all held_moves_thm
  >> CASE_TAC
  >-
  (`?ns. set_vars (MAP FST moves) vals s = ns` by fs []
  >> drule_all set_vars_move_NONE
  >> Cases_on `held vn nums = {}` >> fs []
  >> `MIN_SET (held vn nums) IN (held vn nums)` by metis_tac [min_in_thm]
  >> metis_tac [wf_nums_def, cse_state_rel_def, min_in_thm, eq_nums_eq_vars])
  >-
  (`?ns. set_vars (MAP FST moves) vals s = ns` by fs []
  >> drule_all set_vars_move_SOME
  >> Cases_on `held vn nums = {}` >> fs []
  >> `MIN_SET (held vn nums) IN (held vn nums)` by metis_tac [min_in_thm]
  >> metis_tac [wf_nums_def, cse_state_rel_def, min_in_thm, eq_nums_eq_vars]));

val eval_vn_assign_nums_thm = Q.store_thm("eval_vn_assign_nums",
  `∀moves vals vn nums s vns ns res nnums.
    wf_nums nums ∧ cse_state_rel nums s ∧ ALL_DISTINCT (MAP FST moves) ∧
    get_vars (MAP SND moves) s = SOME vals ∧
    assign_nums (get_moves moves nums) nums = nnums ∧
    eval_vn vn nnums (set_vars (MAP FST moves) vals s) = SOME res ⇒
    eval_vn vn nums s = SOME res`,
  gen_tac >> gen_tac >> recInduct eval_vn_ind >> rw []
  >- fs [eval_vn_def]
  >-
  (simp [eval_vn_thm] >> fs [eval_vn_def]
  >> fs [label_assign_nums_thm, operands_assign_nums_thm]
  >> fs [option_case_eq]
  >-
  (drule get_any_assign_nums_thm
  >> rpt (disch_then drule) >> simp [])
  >-
  (drule get_any_assign_nums_thm
  >> rpt (disch_then drule) >> simp [])
  >-
  (drule option_seq_mono >> rw []
  >> pop_assum (qspecl_then [`\v. eval_vn v nums s`] assume_tac)
  >> rfs [eval_vnode_def,eval_exp_def])));

val eval_var_assign_nums_thm = Q.store_thm("eval_var_assign_nums",
  `∀moves vals var nums s res nnums.
    wf_nums nums ∧ cse_state_rel nums s ∧ ALL_DISTINCT (MAP FST moves) ∧
    get_vars (MAP SND moves) s = SOME vals ∧
    assign_nums (get_moves moves nums) nums = nnums ∧
    eval_var var nnums (set_vars (MAP FST moves) vals s) = SOME res ⇒
    case ALOOKUP moves var of
      | SOME src => eval_var src nums s = SOME res
      | NONE => eval_var var nums s = SOME res`,
  rw [eval_var_def]
  >> drule_all_then (lt fs) get_num_moves_thm
  >> CASE_TAC >> fs []
  >> metis_tac [eval_vn_assign_nums_thm]);

val alookup_get_var_thm = Q.store_thm("alookup_get_var_thm",
  `∀moves s vals v var src.
    get_vars (MAP SND moves) s = SOME vals ∧
    ALOOKUP (ZIP (MAP FST moves, vals)) var = SOME v ∧
    ALOOKUP moves var = SOME src ⇒
    get_var src s = SOME v`,
  Induct >> rw [get_vars_def]
  >> Cases_on `h` >> fs []
  >> every_case_tac >> rw []
  >> fs [] >> metis_tac []);

val state_moves_thm = Q.store_thm("state_moves",
  `∀moves vals nums nnums s.
    wf_nums nums ∧ cse_state_rel nums s ∧ ALL_DISTINCT (MAP FST moves) ∧
    get_vars (MAP SND moves) s = SOME vals ∧
    assign_nums (get_moves moves nums) nums = nnums ⇒
    cse_state_rel nnums (set_vars (MAP FST moves) vals s)`,
  (rpt strip_tac) >> rw [cse_state_rel_def]
  >-
  (drule eval_var_assign_nums_thm >> rpt (disch_then drule)
  >> simp [] >> disch_then drule >> rw []
  >> fs [get_var_def, set_vars_def]
  >> `LENGTH moves = LENGTH vals` by metis_tac [LENGTH_MAP,
       get_vars_length_lemma]
  >> fs [lookup_alist_insert] >> CASE_TAC
  >-
  (`~MEM var (MAP FST moves)` by metis_tac [alookup_none_zip, LENGTH_MAP]
  >> `ALOOKUP moves var = NONE` by metis_tac [ALOOKUP_NONE]
  >> fs [] >> metis_tac [get_var_def, cse_state_rel_def])
  >-
  (`MEM var (MAP FST moves)` by metis_tac
       [alookup_none_zip, LENGTH_MAP, NOT_NONE_SOME]
  >> `ALOOKUP moves var <> NONE` by metis_tac [ALOOKUP_NONE]
  >> Cases_on `ALOOKUP moves var` >> fs []
  >> drule_all alookup_get_var_thm
  >> `get_var x' s = SOME res` by metis_tac [cse_state_rel_def]
  >> fs []))
  >-
  (drule get_num_moves_thm >> disch_then (lt fs)
  >> `?ns. set_vars (MAP FST moves) vals s = ns` by fs []
  >> every_case_tac
  >- (drule_all set_vars_move_NONE >> metis_tac [cse_state_rel_def])
  >- (drule_all set_vars_move_SOME >> metis_tac [cse_state_rel_def])));

val redun_move_get_vars = Q.prove(`
  ∀moves acc nums st loc.
  cse_state_locals_rel nums st loc ∧
  IS_SOME(get_vars (MAP SND acc) st) ∧
  IS_SOME(get_vars (MAP SND moves) st) ⇒
  IS_SOME(get_vars (MAP SND (redun_move moves acc nums))
    (st with locals := loc))`,
  Induct >> fs [get_vars_def, redun_move_def]
  >- (
    rw [IS_SOME_EXISTS]
    >> drule cse_state_locals_rel_thm >> strip_tac
    >> qexists_tac `x`
    >> irule locals_rel_get_vars >> fs []
    >> qexists_tac `SUC(list_max (MAP SND acc))`
    >> irule EVERY_MONOTONIC
    >> qexists_tac `λx. x ≤ list_max (MAP SND acc)`
    >> fs [list_max_max])
  >- (
    rpt gen_tac >> PairCases_on `h` >> fs []
    >> rpt (TOP_CASE_TAC >- fs [])
    >> simp [redun_move_def] >> CASE_TAC >> strip_tac
    >> first_x_assum irule
    >> fs [get_vars_def, IS_SOME_EXISTS]
    >> metis_tac []));

val redun_move_distinct = Q.prove(`
  ∀moves nums acc.
  ALL_DISTINCT ((MAP FST moves) ++ (MAP FST acc)) ⇒
  ALL_DISTINCT (MAP FST (redun_move moves acc nums))`,
  Induct >> fs [redun_move_def]
  >> rpt gen_tac >> PairCases_on `h`
  >> simp [redun_move_def] >> CASE_TAC
  >> rpt strip_tac
  >> first_x_assum irule >> fs [ALL_DISTINCT_APPEND]);

val redun_move_alookup_thm = Q.prove(`
  ∀moves nums k v acc.
  ALL_DISTINCT ((MAP FST moves) ++ (MAP FST acc)) ∧
  ALOOKUP (redun_move moves acc nums) k = SOME v ⇒
  ALOOKUP (moves ++ acc) k = SOME v`,
  Induct >> rw [redun_move_def]
  >> PairCases_on `h`
  >> fs [redun_move_def]
  >> qpat_x_assum `_ = SOME v` mp_tac >> TOP_CASE_TAC
  >-
  (strip_tac >> res_tac >> CASE_TAC >> rw []
  >> `~MEM h0 (MAP FST (moves ++ acc))` by metis_tac [MEM_APPEND, MAP_APPEND]
  >> metis_tac [ALOOKUP_NONE, NOT_NONE_SOME, MEM_APPEND])
  >-
  (pop_assum (K ALL_TAC) >> strip_tac >> res_tac
  >> rfs [ALL_DISTINCT_APPEND, ALOOKUP_APPEND]
  >> CASE_TAC >- fs [] >> CASE_TAC >> fs []
  >> `~MEM h0 (MAP FST (moves ++ acc))` by metis_tac [MEM_APPEND, MAP_APPEND]
  >> metis_tac [ALOOKUP_NONE, NOT_NONE_SOME, MEM_APPEND]));

val redun_move_mem_acc_thm = Q.prove(`
  ∀moves k acc nums.
   ~MEM k (MAP FST (redun_move moves acc nums)) ⇒
   ~MEM k (MAP FST acc)`,
  Induct >- rw [redun_move_def]
  >> rpt gen_tac >> PairCases_on `h` >> fs [redun_move_def]
  >> CASE_TAC >> rw [] >> res_tac >> fs []);

val redun_move_missing_thm = Q.prove(`
  ∀moves nums dst src acc.
  ALL_DISTINCT ((MAP FST moves) ++ (MAP FST acc)) ∧
  ALOOKUP moves dst = SOME src ∧
  ~MEM dst (MAP FST (redun_move moves acc nums)) ⇒
  IS_SOME (get_num dst nums) ∧ get_num dst nums = get_num src nums`,
  Induct >- rw []
  >> rpt gen_tac >> PairCases_on `h` >> fs [redun_move_def]
  >> reverse(CASE_TAC) >- (rw [] >> res_tac >> rfs [ALL_DISTINCT_APPEND])
  >> CASE_TAC >> strip_tac
  >> drule redun_move_mem_acc_thm >> rw []);

val get_var_set_vars_thm = Q.prove(`
  ∀dst src st k.
  LENGTH dst = LENGTH src ⇒
  get_var k (set_vars dst src st) = 
    case ALOOKUP (ZIP (dst, src)) k of
      | SOME v => SOME v
      | NONE => get_var k st`,
  fs [get_var_def, set_vars_def, lookup_alist_insert]);

val alookup_get_vars_thm = Q.prove(
  `∀moves s vals v var.
    get_vars (MAP SND moves) s = SOME vals ∧
    ALOOKUP (ZIP (MAP FST moves, vals)) var = SOME v ⇒
    ∃src. ALOOKUP moves var = SOME src ∧
          get_var src s = SOME v`,
  Induct >> rw [get_vars_def]
  >- (Cases_on `vals` >> fs [])
  >> every_case_tac >> fs []
  >> rw [] >> PairCases_on `h` >> fs [] >> CASE_TAC >> fs []);

val redun_move_get_var_thm = Q.prove(`
  ∀moves nums st loc vars vars' k.
  ALL_DISTINCT (MAP FST moves) ∧
  cse_state_locals_rel nums st loc ∧
  get_vars (MAP SND moves) st = SOME vars ∧
  get_vars (MAP SND (redun_move moves [] nums))
    (st with locals := loc ) = SOME vars' ⇒
  get_var k (set_vars (MAP FST moves) vars st) =
  get_var k (set_vars (MAP FST (redun_move moves [] nums)) vars'
    (st with locals := loc))`,
  rw [] >> qabbrev_tac `nmoves = redun_move moves [] nums`
  >> `LENGTH moves = LENGTH vars` by metis_tac [LENGTH_MAP,
       get_vars_length_lemma]
  >> `LENGTH nmoves = LENGTH vars'` by metis_tac [LENGTH_MAP,
       get_vars_length_lemma]
  >> fs [get_var_set_vars_thm] >> every_case_tac
  >- fs [cse_state_locals_rel_def, get_var_def]
  >-
  (drule_all alookup_get_vars_thm >> rw []
  >> qspecl_then [`moves`, `nums`, `k`, `src`, `[]`] assume_tac
      redun_move_alookup_thm
  >> rfs []
  >> `MEM k (MAP FST moves)` by metis_tac [ALOOKUP_NONE, NOT_NONE_SOME]
  >> metis_tac [alookup_none_zip, LENGTH_MAP, NOT_NONE_SOME])
  >-
  (drule_all alookup_get_vars_thm >> rw []
  >> `MEM k (MAP FST moves)` by metis_tac [ALOOKUP_NONE, NOT_NONE_SOME]
  >> `~MEM k (MAP FST nmoves)` by metis_tac [alookup_none_zip, LENGTH_MAP,
      get_vars_length_lemma]
  >> unabbrev_all_tac
  >> `ALL_DISTINCT (MAP FST moves ++ MAP FST ([] : (num, num) alist))` by fs []
  >> drule_all redun_move_missing_thm >> rw [IS_SOME_EXISTS]
  >> fs [cse_state_locals_rel_def, get_var_def, locals_rel_def]
  >> metis_tac [eq_nums_eq_vars, get_var_def])
  >-
  (dxrule_all alookup_get_vars_thm >> rw []
  >> dxrule_all alookup_get_vars_thm >> rw []
  >> qspecl_then [`moves`, `nums`, `k`, `src`, `[]`] assume_tac
      redun_move_alookup_thm
  >> rfs [cse_state_locals_rel_def, get_var_def] >> fs []));

(* evaluate thms *)
val evaluate_cse_move_thm = Q.prove(`
  ∀moves pri nums st loc.
  cse_state_locals_rel nums st loc ⇒
  let (res,rst) = evaluate(Move pri moves,st) in
  if (res = SOME Error) then T else
  let
    (nprog, nnums) = cse_move pri moves nums;
    (res', rcst) = evaluate (nprog, st with locals := loc)
  in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧
    case res of
      | SOME _ => rst.locals = rcst.locals
      | _ => cse_state_locals_rel nnums rst rcst.locals`,
  rw [] >> rpt (pairarg_tac >> fs [])
  >> fs [cse_move_def] >> rw []
  >> Cases_on `res = SOME Error` >> fs []
  >> fs [evaluate_def]
  >> qpat_x_assum `_ = (res,rst)` mp_tac
  >> CASE_TAC >- fs []
  >> reverse(CASE_TAC) >- fs []
  >> strip_tac
  >> drule redun_move_get_vars
  >> disch_then (qspecl_then [`moves`, `[]`] mp_tac)
  >> impl_tac >- fs [get_vars_def]
  >> strip_tac
  >> qspecl_then [`moves`, `nums`, `[]`] mp_tac redun_move_distinct
  >> impl_tac >- fs [] >> strip_tac
  >> fs [IS_SOME_EXISTS] >> fs []
  >> rw [cse_state_locals_rel_def]
  >- fs [word_state_eq_rel_def, set_vars_def, cse_state_locals_rel_def]
  >- fs[set_vars_def]
  >- metis_tac [get_moves_valid_thm, wf_assign_nums_thm, cse_state_locals_rel_def]
  >- metis_tac [state_moves_thm, cse_state_locals_rel_def]
  >- metis_tac [redun_move_get_var_thm, get_var_def]);

val evaluate_cse_assign_thm = Q.prove(`
  ∀dst exp nums st loc.
  cse_state_locals_rel nums st loc ⇒
  let (res,rst) = evaluate(Assign dst exp,st) in
  if (res = SOME Error) then T else
  let
    (nprog, nnums) = cse_assign dst exp nums;
    (res', rcst) = evaluate (nprog, st with locals := loc)
  in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧
    case res of
      | SOME _ => rst.locals = rcst.locals
      | _ => cse_state_locals_rel nnums rst rcst.locals`,
  rw [] >> rpt (pairarg_tac >> fs [])
  >> fs [cse_assign_def] >> rw []
  >> Cases_on `res = SOME Error` >> fs []
  >> fs [evaluate_def]
  >> qpat_x_assum `_ = (res,rst)` mp_tac
  >> CASE_TAC >- fs []
  >> `word_exp (st with locals := loc) exp = SOME x` by (
    imp_res_tac cse_state_locals_rel_thm
    >> irule locals_rel_word_exp >> fs []
    >> qexists_tac `SUC(max_var (Assign dst exp))`
    >> qspec_then `Assign dst exp` assume_tac max_var_max
    >> fs [every_var_def] >> irule every_var_exp_mono
    >> HINT_EXISTS_TAC >> fs[])
  >> fs [cse_state_locals_rel_def]
  >> rw []
    >- fs [word_state_eq_rel_def, state_component_equality, set_var_def]
    >- fs [set_var_def]
    >- rw [wf_unassign_thm, state_unassign_thm, lookup_insert, set_var_def]);

val evaluate_cse_binop_thm = Q.prove(`
  ∀bop r1 r2 ri nums st loc .
  cse_state_locals_rel nums st loc ⇒
  let (res,rst) = evaluate(Inst (Arith (Binop bop r1 r2 ri)), st) in
  if (res = SOME Error) then T else
  let
    (nprog, nnums) = cse_binop bop r1 r2 ri nums;
    (res', rcst) = evaluate (nprog, st with locals := loc)
  in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧
    case res of
      | SOME _ => rst.locals = rcst.locals
      | _ => cse_state_locals_rel nnums rst rcst.locals`,
  rw[]>>rpt (pairarg_tac>>fs[])>>
  fs[cse_binop_def]>>rpt (pairarg_tac>>fs[])>>
  qpat_x_assum `A=(nprog,nnums)` mp_tac>>
  TOP_CASE_TAC
  >- ((* no redundancy found *)
    rw []>>Cases_on `res = SOME Error` >>fs [cse_state_locals_rel_def]>>
    qpat_x_assum `A=(res,rst)` assume_tac>>
    drule locals_rel_evaluate_thm>>disch_then drule>>
    disch_then (qspecl_then [`loc`,
      `SUC(max_var(Inst (Arith (Binop bop r1 r2 ri))))`] mp_tac)>>
    qspec_then `Inst (Arith (Binop bop r1 r2 ri))` assume_tac max_var_max>>
    impl_tac>-(
      fs [locals_rel_def]>>irule every_var_mono>>
      HINT_EXISTS_TAC>>fs[])>>
    strip_tac>>rw[]>-(fs[])>-(fs[word_state_eq_rel_def]>>rw[])>>
    Cases_on `res`>>fs[]>>rw[]
    >- ((* wf_nums *)
      Cases_on `ri`>>fs[]>>rw[]>>irule wf_add_vnode_thm
      >- (metis_tac [wf_get_or_assign_nums_thm])
      >- (fs [] >> metis_tac [valid_get_or_assign_nums_thm,valid_def])
      >- (metis_tac [wf_get_or_assign_nums_thm])
      >- (fs [] >> metis_tac [valid_get_or_assign_nums_thm,valid_def]))
    >- ((* cse_state *)
      Cases_on `ri`
      >- ( 
        fs[evaluate_def,inst_def,assign_def,option_case_eq]>>rw[]>>
        irule state_add_vnode_thm
        >- metis_tac [wf_get_or_assign_nums_thm]
        >- (
          fs[word_exp_def,option_case_eq]>>
          drule the_words_get_or_assign_nums_thm>>
          disch_then drule>>disch_then (qspec_then `[r2;n']` mp_tac)>>
          rw[get_var_def,eval_exp_def,eval_label_def,MAP_MAP_o,the_words_thm]>>
          rfs[]>>fs[])
        >- (
          irule state_get_or_assign_nums_thm>>HINT_EXISTS_TAC>>
          qexists_tac `[r2;n']`>>HINT_EXISTS_TAC>>
          fs[word_exp_def,option_case_eq]>>
          imp_res_tac the_words_EVERY_IS_SOME>>fs[get_var_def]))
      >- (
        fs [evaluate_def,inst_def,assign_def,option_case_eq]>>rw[]>>
        irule state_add_vnode_thm
        >- metis_tac [wf_get_or_assign_nums_thm]
        >- (
          drule the_words_get_or_assign_nums_thm>>
          disch_then drule>>
          disch_then (qspec_then `[r2]` mp_tac)>>
          rw [eval_exp_def, eval_label_def, MAP_MAP_o, the_words_thm]>>
          fs [get_or_assign_nums_def]>>rpt (pairarg_tac >> fs [])>>rw []>>
          fs [option_seq_def, the_words_def, word_exp_def,option_case_eq]>>
          Cases_on `v5` >> fs [get_var_def]>>
          res_tac >> fs [] >> simp [eval_vn_def, the_words_def])
        >- (
          irule state_get_or_assign_nums_thm>>HINT_EXISTS_TAC>>
          qexists_tac `[r2]`>>qexists_tac `vn`>>
          fs[word_exp_def,option_case_eq]>>
          imp_res_tac the_words_EVERY_IS_SOME>>
          fs[get_var_def])))
      >- ((* locals_rel *)
        fs[evaluate_def,inst_def,assign_def,option_case_eq]>>rw[]>>
        fs[state_component_equality,locals_rel_def,set_var_def]>>
        rw[lookup_insert]>>pop_assum (qspec_then `k` assume_tac)>>
        fs [max_var_def,max_var_inst_def]>>Cases_on `ri` >> fs [MAX_DEF]))
  >- ((* redundancy found *)
    rw[]>>Cases_on `res = SOME Error` >>fs [cse_state_locals_rel_def]>>
    qpat_x_assum `A=(res,rst)` assume_tac>>
    drule locals_rel_evaluate_thm>>disch_then drule>>
    disch_then (qspecl_then [`loc`,
      `SUC(max_var(Inst (Arith (Binop bop r1 r2 ri))))`] mp_tac)>>
    qspec_then `Inst (Arith (Binop bop r1 r2 ri))` assume_tac max_var_max>>
    impl_tac>-(
      fs [locals_rel_def]>>irule every_var_mono>>
      HINT_EXISTS_TAC>>fs[])>>
    strip_tac>>
    Cases_on `res`>>fs [redun_exp_def]
    >- (
      Cases_on `ri`
      >- (
        fs [evaluate_def,inst_def,assign_def,option_case_eq,word_exp_def]>>
        `eval_exp (VOp bop) vns nnums' st = SOME (Word z)` by (
          fs [eval_exp_def]>>qexists_tac `MAP Word ws`>>rw[]>>
          fs[eval_label_def, MAP_MAP_o, the_words_thm]>>
          irule the_words_get_or_assign_nums_thm>>HINT_EXISTS_TAC>>
          qexists_tac `[r2;n']`>>fs[get_var_def]>>rfs[])>>
        `cse_state_rel nnums' st` by (
          irule state_get_or_assign_nums_thm>>
          HINT_EXISTS_TAC>>fs []>>qexists_tac `[r2; n']`>>
          fs[get_var_def]>>imp_res_tac the_words_EVERY_IS_SOME>>fs[])>>
        `wf_nums nnums'` by metis_tac [wf_get_or_assign_nums_thm]>>
        drule_all find_exp_eval_vn_thm>>strip_tac>>
        mp_tac gen_prog_thm>>fs[cse_state_locals_rel_def]>>
        disch_then drule_all>>strip_tac>>fs[]>>
        rw[set_var_def, lookup_insert]
        >- fs [word_state_eq_rel_def]
        >- metis_tac [wf_assign_thm, eval_vn_valid_thm]
        >- metis_tac [state_assign_thm, eval_vn_valid_thm,set_var_def])
      >- (
        fs [evaluate_def,inst_def,assign_def,option_case_eq,word_exp_def]>>
        `eval_exp (VOp bop) vns nnums' st = SOME (Word z)` by (
          fs[eval_exp_def]>>qexists_tac `MAP Word ws`>>rw[]>>
          fs[eval_label_def, MAP_MAP_o, the_words_thm]>>
          fs[option_seq_append,eval_vn_def,the_words_def,option_case_eq]>>
          Cases_on `v5`>>fs[]>>qexists_tac `[Word c']`>>rw[]>>
          drule the_words_get_or_assign_nums_thm>>
          rpt(disch_then drule)>>
          simp [the_words_def,option_case_eq,get_var_def])>>
       `cse_state_rel nnums' st` by (
          irule state_get_or_assign_nums_thm>>
          HINT_EXISTS_TAC>>fs []>>qexists_tac `[r2]`>>
          fs[get_var_def]>>imp_res_tac the_words_EVERY_IS_SOME>>fs[])>>
        `wf_nums nnums'` by metis_tac [wf_get_or_assign_nums_thm]>>
        drule_all find_exp_eval_vn_thm>>strip_tac>>
        mp_tac gen_prog_thm>>fs[cse_state_locals_rel_def]>>
        disch_then drule_all>>strip_tac>>fs[]>>
        rw[set_var_def, lookup_insert]
        >- fs [word_state_eq_rel_def]
        >- metis_tac [wf_assign_thm, eval_vn_valid_thm]
        >- metis_tac [state_assign_thm, eval_vn_valid_thm,set_var_def]))
    >- (fs [evaluate_def,inst_def,assign_def,option_case_eq,word_exp_def])));

val cse_locals_rel_word_exp = Q.prove(`
  ∀exp  st nums w loc.
  word_exp st exp = SOME w ∧
  cse_state_locals_rel nums st loc ⇒
  word_exp (st with locals := loc) exp = SOME w`,
  cheat);

val cse_locals_rel_get_vars = Q.prove(`
  ∀ls vs.
  (∀k. lookup k st.locals = lookup k loc) ⇒
  get_vars ls (st with locals := loc) = get_vars ls st`,
  cheat);

val evaluate_cse_inst_thm = Q.prove(`
  ∀i nums st loc .
  cse_state_locals_rel nums st loc ⇒
  let (res,rst) = evaluate(Inst i, st) in
  if (res = SOME Error) then T else
  let
    (nprog, nnums) = cse_inst i nums;
    (res', rcst) = evaluate (nprog,st with locals := loc)
  in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧
    case res of
      | SOME _ => rst.locals = rcst.locals
      | _ => cse_state_locals_rel nnums rst rcst.locals`,
  rw[]>>rpt (pairarg_tac>>fs[])>>
  Cases_on `i`>>fs[cse_inst_def]>>rw[]
  >- ((* Skip *)
    fs[evaluate_def,option_case_eq,inst_def]>>rw[]>>fs[word_state_eq_rel_def])
  >- ((* Const *)
    fs[evaluate_def,option_case_eq,inst_def,assign_def,word_exp_def]>>rw[]
    >- fs[word_state_eq_rel_def,set_var_def]
    >- fs[set_var_def]
    >- (
      fs[cse_state_locals_rel_def,wf_assign_thm,valid_def]>>
      fs[state_assign_thm,eval_vn_def,lookup_insert,valid_def,set_var_def]))
  >- ((* Arith *)
    Cases_on `a`>>fs[cse_arith_def]>>rw[]
    >- ((* Binop *)
      drule evaluate_cse_binop_thm>>fs[]>>
      disch_then (qspecl_then [`b`, `n`, `n0`, `r`] assume_tac)>>
      rpt (pairarg_tac>>fs[])>>rw[]>>fs[]>>metis_tac[])
    >- ((* Shift *)
      cheat
    )>>
    (* Rest *)
    Cases_on `res = SOME Error`>>
    fs[evaluate_def,inst_def,option_case_eq,list_case_eq,wl_case_eq]>>
    rw[]>>rfs[cse_locals_rel_get_vars,cse_state_locals_rel_def]>>
    fs[state_unassign_thm,wf_unassign_thm]>>
    fs[word_state_eq_rel_def, set_var_def,lookup_insert])
  >- ((* Mem *)
    cheat
    ) 
  >- ((* FP *)
    cheat));

val cse_state_locals_rel_eq_thm = Q.prove(`
  ∀nums (s:(α, β) wordSem$state) (ns:(α, β) wordSem$state) loc.
  s.locals = ns.locals ⇒
  (cse_state_locals_rel nums s loc ⇔ cse_state_locals_rel nums ns loc)`,
  rw [cse_state_locals_rel_def] >> EQ_TAC >> strip_tac
    >- 
    (drule_all (INST_TYPE [``:γ`` |-> ``:β``] eval_var_locals_thm)
    >> rw [cse_state_rel_def]
      >- metis_tac [get_var_def, cse_state_rel_def]
      >- metis_tac [cse_state_rel_def, get_var_def])
    >-
    (drule (INST_TYPE [``:γ`` |-> ``:β``] eval_var_locals_thm)
    >> disch_then drule >> rw [cse_state_rel_def]
      >- metis_tac [get_var_def, cse_state_rel_def]
      >- metis_tac [cse_state_rel_def, get_var_def]));

val evaluate_cse_loop = Q.store_thm("evaluate_cse_loop", `
  ∀prog nums st loc.
  cse_state_locals_rel nums st loc ⇒
  let (res,rst) = evaluate(prog,st) in
  if (res = SOME Error) then T else
  let
    (nprog, nnums) = cse_loop prog nums;
    (res', rcst) = evaluate (nprog, st with locals := loc)
  in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧
    rst.permute = rcst.permute ∧
    case res of
      | SOME _ => rst.locals = rcst.locals
      | _ => cse_state_locals_rel nnums rst rcst.locals`,
  recInduct cse_loop_ind>>rpt conj_tac
  >- (mp_tac evaluate_cse_move_thm>>fs[cse_loop_def])
  >- (mp_tac evaluate_cse_assign_thm>>fs[cse_loop_def]) 
  >- (mp_tac evaluate_cse_inst_thm>>fs[cse_loop_def])

  >- ((* Get *)
    rw[]>>rpt (pairarg_tac>>fs[])>>
    fs[cse_loop_def,cse_get_def]>>rw[]>>
    fs[evaluate_def,cse_state_locals_rel_def]>>
    every_case_tac>>fs[]>>rw[wf_unassign_thm,state_unassign_thm]>>
    fs[word_state_eq_rel_def,set_var_def,lookup_insert])

  >- ((* LocValue *)
    rw[]>>rpt (pairarg_tac>>fs[])>>fs[cse_loop_def]>>rw[]>>
    fs[evaluate_def,cse_state_locals_rel_def]>>
    every_case_tac>>fs[]>>rw[wf_unassign_thm,state_unassign_thm]>>
    fs[word_state_eq_rel_def,set_var_def,lookup_insert])

  >- ((* MustTerminate *)
    rw[]>>rpt (pairarg_tac>>fs[])>>fs[cse_loop_def]>>rw[]>>
    fs[evaluate_def]>>rpt (pairarg_tac >> fs [])>>
    `st.locals = (st with <|clock := MustTerminate_limit (:'a);
      termdep := st.termdep − 1|>).locals` by fs []>>
    `cse_state_locals_rel nums (st with <| clock := MustTerminate_limit (:α);
      termdep := st.termdep − 1|>) loc` by
      metis_tac [cse_state_locals_rel_eq_thm]>>
    first_x_assum drule>>rpt (pairarg_tac>>fs[])>>strip_tac>>rw[]
    >-(every_case_tac>>fs[])>>
    qpat_x_assum `_ = (res,rst)` mp_tac>>
    CASE_TAC>>fs[]>>CASE_TAC>>fs[]>>
    every_case_tac>>fs[]>>rw[]
    >- fs [word_state_eq_rel_def]
    >- fs [state_component_equality]
    >- (
      `rst'.locals = (rst' with <| clock := st.clock; termdep :=
        st.termdep|>).locals` by fs []>>
      drule cse_state_locals_rel_eq_thm>>rw[]>>metis_tac[])
    >- fs [word_state_eq_rel_def])

  >- ((* Seq *)
    rw[cse_loop_def]>>rpt (pairarg_tac>>fs[])>>rw[]>>
    fs[evaluate_def]>>rpt (pairarg_tac>>fs[])>>
    first_x_assum drule>>rpt (pairarg_tac>>fs[])>>
    strip_tac>>fs[]>>rw[]>>
    reverse(Cases_on `res''`)>-(fs[]>>rw[])>>
    qabbrev_tac `rloc = s1.locals`>>
    `s1 = rst' with locals := rloc` by
      fs[state_component_equality,word_state_eq_rel_def]>>fs[]>>
    first_x_assum drule>>rpt (pairarg_tac>>fs[]))

  >- ((* If *)
    rw[cse_loop_def]>>rpt (pairarg_tac>>fs[])>>rw[]>>
    Cases_on `res = SOME Error` >> fs[evaluate_def]>>
    `get_var lhs (st with locals := loc) = get_var lhs st` by
      fs [cse_state_locals_rel_def,get_var_def]>>
    `get_var_imm rhs (st with locals := loc) = get_var_imm rhs st` by (
      Cases_on`rhs`>>fs[cse_state_locals_rel_def,get_var_def,get_var_imm_def])>>
    fs[option_case_eq,wl_case_eq]>>fs[]>>rfs[]>>
    Cases_on `word_cmp cmp x y`>>fs[]
    >- (
      first_x_assum drule>>rpt (pairarg_tac>>fs[])>>strip_tac>>
      rw[merge_vnums_def]>>Cases_on `res`>>
      fs[cse_state_locals_rel_def,wf_initial_vn_thm,state_initial_vn_thm])
    >- (
      qpat_x_assum `∀st' loc'. _ ⇒ A (evalauate(p2,st'))` drule>>
      rpt (pairarg_tac >> fs[])>>strip_tac>>
      rw[merge_vnums_def]>>Cases_on `res`>>
      fs[cse_state_locals_rel_def,wf_initial_vn_thm,state_initial_vn_thm]))

  (* Call *)
  >- (cheat)

  (* Alloc *)
  >- (
    rw[cse_loop_def]>>rpt (pairarg_tac>>fs[])>>rw[]>>
    Cases_on `res = SOME Error`>>fs[]>>
    qpat_x_assum `_ = (res,rst)` assume_tac>>
    drule locals_rel_evaluate_thm>>
    disch_then (qspecl_then [`loc`, `temp`] mp_tac)>>
    impl_tac>-(cheat)>>strip_tac>>
    fs[word_state_eq_rel_def,state_component_equality]>>
    Cases_on `res` >> rw[]
    >- (
      fs[cse_state_locals_rel_def,wf_initial_vn_thm,state_initial_vn_thm]>>
      cheat)
    >- fs[])

  (* FFI *)
  >- (cheat)
  (* Skip *)
  >- (rw [cse_loop_def, evaluate_def, word_state_eq_rel_def])
  (* Set, Raise, Return, Tick *)
  >> cheat);

(* evaluation sematics are preserved by the pass *)
val evaluate_cse = Q.store_thm("evaluate_cse", `
  ∀prog st.
  let (res,rst) = evaluate(prog,st) in
  if (res = SOME Error) then T else
  let
    (res', rcst) = evaluate (cse prog, st)
  in
    res = res' ∧ 
    word_state_eq_rel rst rcst ∧
    case res of
      | SOME _ => rst.locals = rcst.locals
      | _ => T`,
  fs [cse_def] >> rpt gen_tac
  >> qspec_then `st` assume_tac locals_initial_vn_thm
  >> drule_then (qspec_then `prog` assume_tac) evaluate_cse_loop >> fs[]
  >> rpt (pairarg_tac >> fs []) >> rw[]
  >> Cases_on `st`
  >> fs [state_locals_fupd]
  >> every_case_tac >> fs []);

val cse_loop_wf_cutsets_thm = Q.store_thm("cse_loop_wf_cutsets",
  `∀p nums np nnums.
    wf_cutsets p ∧
    cse_loop p nums = (np, nnums) ⇒
    wf_cutsets np`,
  recInduct cse_loop_ind >> rpt conj_tac
  >> fs [wf_cutsets_def, cse_loop_def]
  (* Move *)
  >- fs [cse_move_def, wf_cutsets_def]
  (* Assign *)
  >- fs [cse_assign_def, wf_cutsets_def]
  (* Inst *)
  >- (
    rw[]>>Cases_on `i`>>fs[cse_inst_def]
    >- rw [wf_cutsets_def]
    >- rw [wf_cutsets_def]
    >- (
      Cases_on `a`>>fs[cse_arith_def,cse_binop_def]
      >- (
        rpt(pairarg_tac>>fs[])>>
        every_case_tac>>rw[]>>rw[wf_cutsets_def]>>
        fs[redun_exp_def]>>imp_res_tac gen_prog_cases_thm>>
        rw[wf_cutsets_def])
      >> rw [wf_cutsets_def])
    >- (Cases_on `m`>>fs[cse_mem_def]>>rw[wf_cutsets_def])
    >- (Cases_on `f`>>fs[cse_fp_def]>>rw[wf_cutsets_def]))
  (* Get *)
  >- fs [cse_get_def, wf_cutsets_def]
  (* Must Terminate *)
  >- (rw [] >> pairarg_tac >> fs [] >> rw [wf_cutsets_def])
  (* Seq *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [wf_cutsets_def])
  (* If *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [wf_cutsets_def])
  (* Call *)
  >-
  (rw [] >> Cases_on `ret` >> fs []
    >- rw [wf_cutsets_def]
    >-
    (PairCases_on `x`
    >> Cases_on `handler` >> fs []
    >> rpt (pairarg_tac >> fs [])
    >> rw [wf_cutsets_def])));

val cse_wf_cutsets = Q.store_thm("cse_wf_cutsets", `
  ∀p. wf_cutsets p ⇒ wf_cutsets (cse p)`,
  metis_tac [FST, PAIR, cse_def, cse_loop_wf_cutsets_thm]);

val cse_loop_distinct_tar_reg_thm = Q.prove(`
  ∀p nums np nnums.
    every_inst distinct_tar_reg p ∧
    cse_loop p nums = (np, nnums) ⇒
    every_inst distinct_tar_reg np`,
  recInduct cse_loop_ind >> rpt conj_tac
  >> fs [every_inst_def, cse_loop_def]
  (* Move *)
  >- fs [cse_move_def, every_inst_def]
  (* Assign *)
  >- fs [cse_assign_def, every_inst_def]
  >- ((* Inst *)
    rw[]>>Cases_on `i`>>fs[cse_inst_def]
    >- rw [every_inst_def]
    >- rw [every_inst_def]
    >- (
      Cases_on `a`>> fs [cse_arith_def,cse_binop_def]
      >- (
        rpt(pairarg_tac>>fs[])>>
        every_case_tac>>rw[]>>rw[every_inst_def]>>
        fs[redun_exp_def]>>imp_res_tac gen_prog_cases_thm>>
        rw[every_inst_def,distinct_tar_reg_def])
      >> rw [every_inst_def])
    >- (Cases_on `m` >> fs [cse_mem_def] >> rw [every_inst_def])
    >- (Cases_on `f` >> fs [cse_fp_def] >> rw [every_inst_def]))
  (* Get *)
  >- fs [cse_get_def, every_inst_def]
  (* Must Terminate *)
  >- (rw [] >> pairarg_tac >> fs [] >> rw [every_inst_def])
  (* Seq *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [every_inst_def])
  (* If *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [every_inst_def])
  >- (* Call *)
  (rw []
  >> qpat_x_assum `_ = (np,nnums)` mp_tac
  >> TOP_CASE_TAC >- metis_tac [every_inst_def]
  >> PairCases_on `x` >> fs []
  >> CASE_TAC >> rpt (pairarg_tac >> fs [])
  >> rw [] >> rw [every_inst_def]));

val cse_distinct_tar_reg = Q.store_thm("cse_distinct_tar_reg", `
  ∀p. every_inst distinct_tar_reg p ⇒ every_inst distinct_tar_reg (cse p)`,
  metis_tac [FST, PAIR, cse_loop_distinct_tar_reg_thm, cse_def]);

val cse_loop_extract_labels_thm = Q.prove(`
  ∀p nums np nnums.
    cse_loop p nums = (np, nnums) ⇒
    extract_labels p = extract_labels np`,
  recInduct cse_loop_ind >> rpt conj_tac
  >> fs [extract_labels_def, cse_loop_def]
  (* Move *)
  >- fs [cse_move_def, extract_labels_def]
  (* Assign *)
  >- fs [cse_assign_def, extract_labels_def]
  >- ((* Inst *)
    rw[]>>Cases_on `i`>>fs[cse_inst_def]
    >- rw [extract_labels_def]
    >- rw [extract_labels_def]
    >- (
      Cases_on `a`>> fs [cse_arith_def,cse_binop_def]
      >- (
        rpt(pairarg_tac>>fs[])>>
        every_case_tac>>rw[]>>rw[extract_labels_def]>>
        fs[redun_exp_def]>>imp_res_tac gen_prog_cases_thm>>
        rw[extract_labels_def])
      >> rw [extract_labels_def]
      )
    >- (Cases_on `m`>>fs[cse_mem_def]>>rw[extract_labels_def])
    >- (Cases_on `f`>>fs[cse_fp_def]>>rw[extract_labels_def]))
  (* Get *)
  >- fs [cse_get_def, extract_labels_def]
  (* Must Terminate *)
  >- (rw [] >> pairarg_tac >> fs [] >> rw [extract_labels_def])
  (* Seq *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [extract_labels_def])
  (* If *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [extract_labels_def])
  >- (* Call *)
  (rw []
  >> qpat_x_assum `_ = (np,nnums)` mp_tac
  >> TOP_CASE_TAC >- (rw [] >> rw [extract_labels_def])
  >> PairCases_on `x` >> fs []
  >> CASE_TAC >> rpt (pairarg_tac >> fs [])
  >> rw [] >> rw [extract_labels_def]));

val cse_extract_labels_thm = Q.store_thm("cse_extract_labels", `
  ∀p. extract_labels p = extract_labels (cse p)`,
  metis_tac [FST, PAIR, cse_loop_extract_labels_thm, cse_def]);

val cse_loop_flat_exp_conventions_thm = Q.prove(`
  ∀p nums np nnums.
    flat_exp_conventions p ∧
    cse_loop p nums = (np, nnums) ⇒
    flat_exp_conventions np`,
  recInduct cse_loop_ind >> rpt conj_tac
  >> fs [flat_exp_conventions_def, cse_loop_def]
  (* Move *)
  >- fs [cse_move_def, flat_exp_conventions_def]
  >- ((* Inst *)
    rw[]>>Cases_on `i`>>fs[cse_inst_def]
    >- rw [flat_exp_conventions_def]
    >- rw [flat_exp_conventions_def]
    >- (
      Cases_on `a`>> fs [cse_arith_def,cse_binop_def]
      >- (
        rpt(pairarg_tac>>fs[])>>
        every_case_tac>>rw[]>>rw[flat_exp_conventions_def]>>
        fs[redun_exp_def]>>imp_res_tac gen_prog_cases_thm>>
        rw[flat_exp_conventions_def])
      >> rw [flat_exp_conventions_def])
    >- (Cases_on `m`>>fs[cse_mem_def]>>rw[flat_exp_conventions_def])
    >- (Cases_on `f`>>fs[cse_fp_def]>>rw[flat_exp_conventions_def]))
  (* Get *)
  >- fs [cse_get_def, flat_exp_conventions_def]
  (* Must Terminate *)
  >- (rw [] >> pairarg_tac >> fs [] >> rw [flat_exp_conventions_def])
  (* Seq *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [flat_exp_conventions_def])
  (* If *)
  >- (rw [] >> rpt (pairarg_tac >> fs []) >> rw [flat_exp_conventions_def])
  >- (* Call *)
  (rw []
  >> qpat_x_assum `_ = (np,nnums)` mp_tac
  >> TOP_CASE_TAC >- (rw [] >> rw [flat_exp_conventions_def])
  >> PairCases_on `x` >> fs []
  >> CASE_TAC >> rpt (pairarg_tac >> fs [])
  >> rw [] >> rw [flat_exp_conventions_def]));

val cse_flat_exp_conventions = Q.store_thm("cse_flat_exp_conventions", `
  ∀p. flat_exp_conventions p ⇒ flat_exp_conventions (cse p)`,
  metis_tac [FST, PAIR, cse_loop_flat_exp_conventions_thm, cse_def]);

val cse_loop_pre_alloc_conventions_thm = Q.prove(`
  ∀p nums np nnums.
    pre_alloc_conventions p ∧
    cse_loop p nums = (np, nnums) ⇒
    pre_alloc_conventions np`,
  recInduct cse_loop_ind >> rw [cse_loop_def] >> fs []
  (* Move *)
  >-
  (fs [cse_move_def] >> rw [pre_alloc_conventions_def]
  >> fs [call_arg_convention_def, every_stack_var_def])
  (* Assign *)
  >- fs [cse_assign_def]
  >- ((* Inst *)
    rw[]>>Cases_on `i`>>fs[cse_inst_def]
    >- (
      Cases_on `a`>>fs[cse_arith_def,cse_binop_def]>>
      rpt(pairarg_tac>>fs[])>>
      every_case_tac>>rw[]>>rw[]>>
      fs[redun_exp_def]>>imp_res_tac gen_prog_cases_thm>>
      rw[pre_alloc_conventions_def,every_stack_var_def,
        call_arg_convention_def,inst_arg_convention_def])
    >- (Cases_on `m`>>fs[cse_mem_def]>>rw[])
    >- (Cases_on `f`>>fs[cse_fp_def]>>rw[]))
  (* Get *)
  >- fs [cse_get_def]
  (* Must Terminate *)
  >- 
  (pairarg_tac >> fs [] >> rw []
  >> fs [pre_alloc_conventions_def]
  >> fs [every_stack_var_def, call_arg_convention_def])
  (* Seq *)
  >-
  (rpt (pairarg_tac >> fs []) >> rw []
  >> fs [pre_alloc_conventions_def]
  >> fs [every_stack_var_def, call_arg_convention_def])
  (* If *)
  >-
  (rpt (pairarg_tac >> fs []) >> rw []
  >> fs [pre_alloc_conventions_def]
  >> fs [every_stack_var_def, call_arg_convention_def])
  >- (* Call *)
  (qpat_x_assum `_ = (np,nnums)` mp_tac
  >> TOP_CASE_TAC >- (rw [] >> fs [])
  >> PairCases_on `x` >> fs []
  >> CASE_TAC >> rpt (pairarg_tac >> fs [])
  >> rw [] >> fs [pre_alloc_conventions_def]
  >> fs [every_stack_var_def, call_arg_convention_def]));

val cse_pre_alloc_conventions = Q.store_thm("cse_pre_alloc_conventions", `
  ∀p. pre_alloc_conventions p ⇒ pre_alloc_conventions (cse p)`,
  metis_tac [FST, PAIR, cse_loop_pre_alloc_conventions_thm, cse_def]);

val cse_loop_full_inst_ok_less_thm = Q.prove(`
  ∀p nums c np nnums.
    full_inst_ok_less c p ∧
    cse_loop p nums = (np, nnums) ⇒
    full_inst_ok_less c np`,
  recInduct cse_loop_ind >> rw [cse_loop_def] >> fs []
  (* Move *)
  >- (fs [cse_move_def] >> rw [] >> fs [full_inst_ok_less_def])
  (* Assign *)
  >- fs [cse_assign_def]
  >- ((* Inst *)
    rw[]>>Cases_on `i`>>fs[cse_inst_def]
    >- (
      Cases_on `a`>> fs [cse_arith_def,cse_binop_def]>>
      rpt(pairarg_tac>>fs[])>>
      every_case_tac>>rw[]>>rw[]>>
      fs[redun_exp_def]>>imp_res_tac gen_prog_cases_thm>>
      rw[full_inst_ok_less_def,inst_ok_less_def])
    >- (Cases_on `m`>>fs[cse_mem_def]>>rw[])
    >- (Cases_on `f`>>fs[cse_fp_def]>>rw[]))
  (* Get *)
  >- fs [cse_get_def]
  (* Must Terminate *)
  >- 
  (pairarg_tac >> fs [] >> rw []
  >> fs [full_inst_ok_less_def])
  (* Seq *)
  >-
  (rpt (pairarg_tac >> fs []) >> rw []
  >> fs [full_inst_ok_less_def])
  (* If *)
  >-
  (rpt (pairarg_tac >> fs []) >> rw []
  >> fs [full_inst_ok_less_def])
  >- (* Call *)
  (qpat_x_assum `_ = (np,nnums)` mp_tac
  >> TOP_CASE_TAC >- (rw [] >> fs [])
  >> PairCases_on `x` >> fs []
  >> CASE_TAC >> rpt (pairarg_tac >> fs [])
  >> rw [] >> fs [full_inst_ok_less_def]));

val cse_full_inst_ok_less = Q.store_thm("cse_full_inst_ok_less", `
  ∀c p. full_inst_ok_less c p ⇒ full_inst_ok_less c (cse p)`,
  metis_tac [FST, PAIR, cse_loop_full_inst_ok_less_thm, cse_def]);

val _ = export_theory();
