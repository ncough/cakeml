open preamble readerTheory ml_monadBaseTheory
     holKernelTheory holKernelProofTheory
     holSyntaxTheory holSyntaxExtraTheory

val _ = new_theory"readerProof";

(* case_eq theorems *)

val case_eqs =
    [ { case_def = exc_case_def, nchotomy = exc_nchotomy }
    , { case_def = hol_exn_case_def, nchotomy = hol_exn_nchotomy }
    , { case_def = holSyntaxTheory.term_case_def
      , nchotomy = holSyntaxTheory.term_nchotomy }
    , { case_def = optionTheory.option_case_def
      , nchotomy = optionTheory.option_nchotomy }
    , { case_def = listTheory.list_case_def
      , nchotomy = listTheory.list_nchotomy }
    , { case_def = holSyntaxTheory.update_case_def
      , nchotomy = holSyntaxTheory.update_nchotomy }
    , { case_def = readerTheory.state_case_def
      , nchotomy = readerTheory.state_nchotomy }
    , { case_def = holSyntaxTheory.type_case_def
      , nchotomy = holSyntaxTheory.type_nchotomy }
    , { case_def = sumTheory.sum_case_def
      , nchotomy = sumTheory.sum_CASES } ]

val case_eq_thms = save_thm ("case_eq_thms",
  LIST_CONJ (pair_case_eq::map prove_case_eq_thm case_eqs));

(* ------------------------------------------------------------------------- *)
(* Reader does not raise Clash                                               *)
(* ------------------------------------------------------------------------- *)

(* TODO where? comes from translation of Candle kernel *)
val find_axiom_not_clash = Q.store_thm("find_axiom_not_clash[simp]",
  `find_axiom (a,b) c <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ rw [find_axiom_def, st_ex_bind_def, raise_Fail_def, st_ex_return_def]
  \\ every_case_tac  \\ fs [get_the_axioms_def]);

val pop_not_clash = Q.store_thm("pop_not_clash[simp]",
  `pop x y ≠ (Failure (Clash tm),refs)`,
  EVAL_TAC \\ rw[] \\ EVAL_TAC);

val peek_not_clash = Q.store_thm("peek_not_clash[simp]",
  `peek x y <> (Failure (Clash tm),refs)`,
  EVAL_TAC \\ rw [] \\ EVAL_TAC);

val getNum_not_clash = Q.store_thm("getNum_not_clash[simp]",
  `getNum x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getVar_not_clash = Q.store_thm("getVar_not_clash[simp]",
  `getVar x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getTerm_not_clash = Q.store_thm("getTerm_not_clash[simp]",
  `getTerm x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getThm_not_clash = Q.store_thm("getThm_not_clash[simp]",
  `getThm x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getType_not_clash = Q.store_thm("getType_not_clash[simp]",
  `getType x y <> (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getName_not_clash = Q.store_thm("getName_not_clash[simp]",
  `getName x y <> (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC
  \\ fs [st_ex_return_def] \\ CASE_TAC \\ fs []);

val getConst_not_clash = Q.store_thm("getConst_not_clash[simp]",
  `getConst x y <> (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getList_not_clash = Q.store_thm("getList_not_clash[simp]",
  `getList x y <> (Failure (Clash tm),refs)`,
  Cases_on `x` \\ EVAL_TAC);

val getTypeOp_not_clash = Q.store_thm("getTypeOp_not_clash[simp]",
  `getTypeOp a b <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ EVAL_TAC);

val getPair_not_clash = Q.store_thm("getPair_not_clash[simp]",
  `getPair a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC
  \\ Cases_on `t` \\ EVAL_TAC \\ Cases_on `t'` \\ EVAL_TAC);

val getCns_not_clash = Q.store_thm("getCns_not_clash[simp]",
  `getCns a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs []);

val getNvs_not_clash = Q.store_thm("getNvs_not_clash[simp]",
  `getNvs a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs [] \\ EVAL_TAC
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [getPair_not_clash, getName_not_clash, getVar_not_clash]);

val getTms_not_clash = Q.store_thm("getTms_not_clash[simp]",
  `getTms a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC
  \\ every_case_tac \\ fs [] \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [getPair_not_clash, getName_not_clash, getVar_not_clash, getTerm_not_clash]);

val getTys_not_clash = Q.store_thm("getTys_not_clash[simp]",
  `getTys a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC
  \\ every_case_tac \\ fs [] \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [getName_not_clash, getType_not_clash, getPair_not_clash]);

val BETA_CONV_not_clash = Q.store_thm("BETA_CONV_not_clash[simp]",
  `BETA_CONV t s <> (Failure (Clash tm),r)`,
  Cases_on `t` \\ strip_tac
  \\ fs [BETA_CONV_def, handle_Fail_def, raise_Fail_def, st_ex_bind_def,
         st_ex_return_def, dest_comb_def, dest_abs_def, BETA_def, UNCURRY,
         case_eq_thms]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []);

val readLine_not_clash = Q.store_thm("readLine_not_clash[simp]",
  `readLine x y z ≠ (Failure (Clash tm),refs)`,
  strip_tac \\
  fs[readLine_def,st_ex_bind_def,st_ex_return_def,raise_Fail_def,
     handle_Clash_def,handle_Fail_def,case_eq_thms,bool_case_eq,UNCURRY,
     COND_RATOR] \\ rw []
  \\ every_case_tac \\ fs [map_not_clash_thm]);

val readLines_not_clash = Q.store_thm("readLines_not_clash[simp]",
  `∀ls x y tm refs. readLines ls x y ≠ (Failure (Clash tm),refs)`,
  recInduct readLines_ind
  \\ rw[]
  \\ rw[Once readLines_def]
  \\ CASE_TAC \\ fs[st_ex_return_def]
  \\ simp[st_ex_bind_def, handle_Fail_def, raise_Fail_def]
  \\ every_case_tac \\ fs [] \\ rw []);

(* ------------------------------------------------------------------------- *)
(* Refinement invariants                                                     *)
(* ------------------------------------------------------------------------- *)

(* Refinement invariant for objects *)
val OBJ_def = tDefine "OBJ" `
  (OBJ defs (List xs)     <=> EVERY (OBJ defs) xs) /\
  (OBJ defs (Type ty)     <=> TYPE defs ty) /\
  (OBJ defs (Var (n, ty)) <=> TERM defs (Var n ty) /\ TYPE defs ty) /\
  (OBJ defs (Term tm)     <=> TERM defs tm) /\
  (OBJ defs (Thm thm)     <=> THM defs thm) /\
  (OBJ defs _             <=> T)`
  (WF_REL_TAC `measure (object_size o SND)`
   \\ Induct \\ rw [object_size_def]
   \\ res_tac \\ fs []);

val OBJ_APPEND_EXTEND = Q.store_thm("OBJ_APPEND_EXTEND",
  `!defs obj d.
     STATE (ds ++ defs) refs /\
     (!th. THM defs th ==> THM (ds ++ defs) th) /\
     OBJ defs obj
     ==>
     OBJ (ds++defs) obj`,
  recInduct (theorem"OBJ_ind") \\ rw [] \\ fs [OBJ_def, EVERY_MEM]
  \\ metis_tac [TERM_APPEND_EXTEND, TYPE_APPEND_EXTEND]);

val READER_STATE_def = Define `
  READER_STATE defs st <=>
    EVERY (THM defs) st.thms /\
    EVERY (OBJ defs) st.stack /\
    (!n obj. lookup (Num n) st.dict = SOME obj ==> OBJ defs obj)`

val READER_STATE_EXTEND = Q.store_thm("READER_STATE_EXTEND",
  `READER_STATE defs st /\
   THM defs th
   ==>
   READER_STATE defs (st with thms := th::st.thms)`,
   rw [READER_STATE_def]);

val READER_STATE_APPEND_EXTEND = Q.store_thm("READER_STATE_APPEND_EXTEND",
  `STATE (ds++defs) refs /\
   READER_STATE defs st /\
   (!th. THM defs th ==> THM (ds++defs) th)
   ==>
   READER_STATE (ds++defs) st`,
  rw [READER_STATE_def] \\ metis_tac [OBJ_APPEND_EXTEND, EVERY_MEM]);

val READER_STATE_CONS_EXTEND = save_thm ("READER_STATE_CONS_EXTEND",
  READER_STATE_APPEND_EXTEND
  |> Q.INST [`ds`|->`[d]`]
  |> SIMP_RULE(srw_ss())[]);

(* ------------------------------------------------------------------------- *)
(* Kernel function support theorems (TODO: move)                             *)
(* ------------------------------------------------------------------------- *)

val first_EVERY = Q.store_thm("first_EVERY",
  `!Q xs x. EVERY P xs /\ first Q xs = SOME x ==> P x`,
  recInduct first_ind \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [first_def]
  \\ CASE_TAC \\ fs [] \\ rw [] \\ fs []);

val axiom_lemma = Q.store_thm("axiom_lemma",
  `!upd.
     axexts_of_upd upd <> []
     ==>
     axexts_of_upd upd = axexts_of_upd upd ++ conexts_of_upd upd`,
  Induct \\ rw [] \\ EVAL_TAC);

val axioms_lemma1 = Q.store_thm("axioms_lemma1",
  `!ctx tm ts.
     MEM tm ts /\
     MEM ts (MAP axexts_of_upd ctx)
     ==>
     MEM ts (MAP (\upd. axexts_of_upd upd ++ conexts_of_upd upd) ctx)`,
  Induct \\ rw []
  >-
   (Cases_on `axexts_of_upd h = []` >- fs []
    \\ metis_tac [axiom_lemma])
  \\ metis_tac []);

(* TODO move to holKernelProof *)
val get_the_axioms_thm = Q.store_thm("get_the_axioms_thm",
  `STATE defs refs /\
   get_the_axioms refs = (res, refs')
   ==>
   refs = refs' /\
   !axs. res = Success axs ==> EVERY (THM defs) axs`,
  rw [get_the_axioms_def, STATE_def]
  \\ fs [EVERY_MAP, lift_tm_def, CONTEXT_def, EVERY_MEM, MEM_MAP] \\ rw []
  \\ fs [THM_def]
  \\ match_mp_tac (last (CONJUNCTS proves_rules))
  \\ conj_tac >- metis_tac [extends_theory_ok, init_theory_ok]
  \\ EVAL_TAC
  \\ fs [MEM_FLAT]
  \\ metis_tac [axioms_lemma1]);

(* TODO move to holKernelProof *)
val find_axiom_thm = Q.store_thm("find_axiom_thm",
  `STATE defs refs /\
   EVERY (TERM defs) ls /\
   TERM defs tm /\
   find_axiom (ls, tm) refs = (res, refs')
   ==>
   refs = refs' /\ !thm. res = Success thm ==> THM defs thm`,
  fs [find_axiom_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ fs [case_eq_thms, PULL_EXISTS] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac get_the_axioms_thm \\ fs [] \\ rveq
  \\ qmatch_asmsub_abbrev_tac `first P`
  \\ Q.ISPECL_THEN [`THM defs`, `P`] mp_tac (GEN_ALL first_EVERY)
  \\ disch_then drule \\ rw []);

val assoc_thm = Q.store_thm("assoc_thm",
  `!s l refs res refs'.
     assoc s l refs = (res, refs')
     ==>
     refs = refs' /\
     !t. res = Success t ==> ALOOKUP l s = SOME t`,
   Induct_on `l` \\ once_rewrite_tac [assoc_def]
   \\ fs [raise_Fail_def, st_ex_return_def]
   \\ Cases \\ fs [] \\ rw [] \\ fs []
   \\ first_x_assum drule
   \\ TRY (disch_then drule) \\ rw []);

(* TODO holKernelProof - move, or already exists? *)
val assoc_state_thm = Q.store_thm("assoc_state_thm",
  `!s l refs res refs'. assoc s l refs = (res, refs') ==> refs = refs'`,
   Induct_on `l` \\ rw [] \\ pop_assum mp_tac
   \\ once_rewrite_tac [assoc_def] \\ fs [raise_Fail_def, st_ex_return_def]
   \\ CASE_TAC \\ fs []
   \\ fs [bool_case_eq, COND_RATOR]
   \\ rw [] \\ fs [] \\ metis_tac []);

(* TODO holKernelProof - move, or already exists? *)
val assoc_ty_thm = Q.store_thm("assoc_ty_thm",
  `!s l refs res refs'.
     EVERY (TYPE defs o SND) l /\
     assoc s l refs = (res, refs')
     ==>
     !ty. res = Success ty ==> TYPE defs ty`,
  Induct_on `l` \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [assoc_def] \\ fs [raise_Fail_def, st_ex_return_def]
  \\ CASE_TAC \\ fs [bool_case_eq, COND_RATOR] \\ rw [] \\ fs []
  \\ metis_tac []);

(* TODO holKernelProof - move, or already exists? *)
val type_of_thm = Q.store_thm("type_of_thm",
  `!tm refs res refs'.
     STATE defs refs /\
     TERM defs tm /\
     type_of tm refs = (res, refs')
     ==>
     refs = refs' /\
     !ty. res = Success ty ==> TYPE defs ty /\ welltyped tm`,
  Induct
  \\ once_rewrite_tac [type_of_def]
  \\ fs [st_ex_return_def, st_ex_bind_def, raise_Fail_def, dest_type_def]
  >-
   (rw [TERM_def, TYPE_def, holSyntaxTheory.term_ok_def]
    \\ fs [holSyntaxTheory.has_type_def])
  >-
   (rw [TERM_def, TYPE_def, holSyntaxTheory.term_ok_def]
    \\ fs [holSyntaxTheory.has_type_def])
  \\ fs [case_eq_thms, PULL_EXISTS, PULL_FORALL] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY
   (first_x_assum drule
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ rw [TYPE_def, holSyntaxTheory.type_ok_def]
    \\ NO_TAC)
  \\ fs [mk_fun_ty_def, mk_type_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ fs [try_def, otherwise_def, get_type_arity_def, st_ex_bind_def, raise_Fail_def]
  \\ fs [get_the_type_constants_def]
  \\ fs [case_eq_thms] \\ rw []
  \\ fs [bool_case_eq, COND_RATOR] \\ rw []
  \\ last_x_assum drule
  \\ fs [TERM_def, holSyntaxTheory.term_ok_def]
  \\ fs [TYPE_def, holSyntaxTheory.type_ok_def] \\ rw []
  \\ TRY
   (Q.ISPECL_THEN [`strlit"fun"`,`r.the_type_constants`] mp_tac assoc_thm
    \\ disch_then drule \\ fs [] \\ rw []
    \\ fs [STATE_def, CONTEXT_def]
    \\ rfs [] \\ NO_TAC)
  \\ fs [EQ_SYM_EQ]
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac `Tyapp z w`
  \\ disch_then (qspec_then `Tyapp z w` mp_tac)
  \\ rw [holSyntaxTheory.type_ok_def, Abbr`z`, Abbr`w`]);

(* TODO holKernelProof - move, or already exists? *)
val mk_comb_thm = Q.store_thm("mk_comb_thm",
  `STATE defs refs /\
   TERM defs f /\
   TERM defs a /\
   mk_comb (f, a) refs = (res, refs')
   ==>
   refs = refs' /\ !fa. res = Success fa ==> TERM defs fa`,
  rw [mk_comb_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ fs [case_eq_thms] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac type_of_thm \\ fs [] \\ rfs []
  \\ fs [TERM_def, holSyntaxTheory.term_ok_def, TYPE_def, holSyntaxTheory.type_ok_def]
  \\ rpt (qpat_x_assum `!x._` kall_tac)
  \\ sg `typeof a = h`
  >- metis_tac [type_of_has_type, TERM_def,TYPE_def]
  \\ fs []
  \\ qexists_tac `h'`
  \\ match_mp_tac holSyntaxExtraTheory.WELLTYPED_LEMMA
  \\ metis_tac [type_of_has_type, TERM_def,TYPE_def])

(* TODO holKernelProof - move, or already exists? *)
val get_const_type_thm = Q.store_thm("get_const_type_thm",
  `STATE defs refs /\
   get_const_type n refs = (res, refs')
   ==>
   refs = refs' /\ !ty. res = Success ty ==> TYPE defs ty`,
  rw [get_const_type_def, st_ex_bind_def, st_ex_return_def, get_the_term_constants_def]
  \\ imp_res_tac the_term_constants_TYPE \\ fs [ELIM_UNCURRY, GSYM o_DEF]
  \\ metis_tac [assoc_state_thm, assoc_ty_thm]);

(* TODO holKernelProof - move, or already exists? *)
val tymatch_thm = Q.store_thm("tymatch_thm",
  `!tys1 tys2 sids.
     EVERY (TYPE defs) tys1 /\
     EVERY (TYPE defs) tys2 /\
     EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) (FST sids) /\
     tymatch tys1 tys2 sids = SOME (tys, _)
     ==>
     EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) tys`,
  recInduct holSyntaxExtraTheory.tymatch_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [holSyntaxExtraTheory.tymatch_def] \\ fs [] \\ rw [] \\ fs []
  \\ fs [UNCURRY, case_eq_thms, bool_case_eq]
  \\ PairCases_on `sids` \\ fs []
  \\ fs [TYPE_def, holSyntaxTheory.type_ok_def]
  \\ fs [GSYM TYPE_def] \\ rfs []
  \\ metis_tac []);

(* TODO holKernelProof - move, or already exists? *)
val match_type_thm = Q.store_thm("match_type_thm",
  `TYPE defs ty1 /\
   TYPE defs ty2 /\
   match_type ty1 ty2 = SOME tys
   ==>
   EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) tys`,
  rw [holSyntaxExtraTheory.match_type_def]
  \\ PairCases_on `z` \\ fs []
  \\ imp_res_tac tymatch_thm \\ rfs []);

(* TODO proven elsewhere *)
val TERM_Comb = Q.store_thm("TERM_Comb",
  `TERM defs (Comb a b) ==> TERM defs a /\ TERM defs b`,
  rw [TERM_def, term_ok_def]);

val TERM_Abs = Q.store_thm("TERM_Abs",
  `TERM defs (Abs v e) ==> TERM defs v /\ TERM defs e`,
  rw [TERM_def] \\ fs [term_ok_def]);

(* ------------------------------------------------------------------------- *)
(* Reader operations preserve invariants                                     *)
(* ------------------------------------------------------------------------- *)

val next_line_thm = Q.store_thm("next_line_thm",
  `READER_STATE defs s ==> READER_STATE defs (next_line s)`,
  rw [READER_STATE_def, next_line_def]);

val getNum_thm = Q.store_thm("getNum_thm",
  `getNum obj refs = (res, refs') ==> refs = refs'`,
   Cases_on `obj` \\ rw [getNum_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getName_thm = Q.store_thm("getName_thm",
  `getName obj refs = (res, refs') ==> refs = refs'`,
   Cases_on `obj` \\ rw [getName_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getList_thm = Q.store_thm("getList_thm",
  `OBJ defs obj /\
   getList obj refs = (res, refs')
   ==>
   refs = refs' /\ !ls. res = Success ls ==> EVERY (OBJ defs) ls`,
   Cases_on `obj` \\ rw [getList_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ metis_tac [OBJ_def]);

val getTypeOp_thm = Q.store_thm("getTypeOp_thm",
  `getTypeOp obj refs = (res, refs') ==> refs = refs'`,
   Cases_on `obj` \\ rw [getTypeOp_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getType_thm = Q.store_thm("getType_thm",
  `OBJ defs obj /\
   getType obj refs = (res, refs')
   ==>
   refs = refs' /\ !ty. res = Success ty ==> TYPE defs ty`,
   Cases_on `obj` \\ rw [getType_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]);

val map_getType_thm = Q.store_thm("map_getType_thm",
  `!xs refs res refs'.
     EVERY (OBJ defs) xs /\
     map getType xs refs = (res, refs')
     ==>
     refs = refs' /\ !tys. res = Success tys ==> EVERY (TYPE defs) tys`,
  Induct \\ once_rewrite_tac [map_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ rw [case_eq_thms] \\ fs []
  \\ imp_res_tac getType_thm \\ fs []
  \\ first_x_assum drule \\ rw []);

val getConst_thm = Q.store_thm("getConst_thm",
  `getConst obj refs = (res, refs') ==> refs = refs'`,
   Cases_on `obj` \\ rw [getConst_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getVar_thm = Q.store_thm("getVar_thm",
  `OBJ defs obj /\
   getVar obj refs = (res, refs')
   ==>
   refs = refs' /\
   !n ty. res = Success (n, ty) ==> TERM defs (Var n ty) /\ TYPE defs ty`,
   Cases_on `obj` \\ rw [getVar_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]);

val getTerm_thm = Q.store_thm("getTerm_thm",
  `OBJ defs obj /\
   getTerm obj refs = (res, refs')
   ==>
   refs = refs' /\ !tm. res = Success tm ==> TERM defs tm`,
   Cases_on `obj` \\ rw [getTerm_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ fs [OBJ_def]);

val map_getTerm_thm = Q.store_thm("map_getTerm_thm",
  `!xs refs res refs'.
     EVERY (OBJ defs) xs /\
     map getTerm xs refs = (res, refs')
     ==>
     refs = refs' /\ !tms. res = Success tms ==> EVERY (TERM defs) tms`,
  Induct \\ once_rewrite_tac [map_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ rw [case_eq_thms] \\ fs []
  \\ imp_res_tac getTerm_thm \\ fs []
  \\ first_x_assum drule \\ rw []);

val getThm_thm = Q.store_thm("getThm_thm",
  `OBJ defs obj /\
   getThm obj refs = (res, refs')
   ==>
   refs = refs' /\ !thm. res = Success thm ==> THM defs thm`,
   Cases_on `obj` \\ rw [getThm_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]);

val pop_thm = Q.store_thm("pop_thm",
  `READER_STATE defs st /\
   pop st refs = (res, refs')
   ==>
   refs = refs' /\
   !a st'. res = Success (a, st') ==> OBJ defs a /\ READER_STATE defs st'`,
   rw [pop_def, raise_Fail_def, st_ex_return_def]
   \\ every_case_tac \\ fs [READER_STATE_def, state_component_equality]
   \\ rw [] \\ metis_tac []);

val peek_thm = Q.store_thm("peek_thm",
  `READER_STATE defs st /\
   peek st refs = (res, refs')
   ==>
   refs = refs' /\ !obj. res = Success obj ==> OBJ defs obj`,
   rw [peek_def, raise_Fail_def, st_ex_return_def]
   \\ every_case_tac \\ fs []
   \\ fs [READER_STATE_def]);

val push_thm = Q.store_thm("push_thm",
  `READER_STATE defs st /\
   OBJ defs obj
   ==>
   READER_STATE defs (push obj st)`,
  rw [push_def, READER_STATE_def]);

val push_push_thm = Q.store_thm("push_push_thm",
  `READER_STATE defs st /\
   OBJ defs obj1 /\
   OBJ defs obj2
   ==>
   READER_STATE defs (push obj1 (push obj2 st))`,
  rw [push_def, READER_STATE_def]);

val insert_dict_thm = Q.store_thm("insert_dict_thm",
  `READER_STATE defs st /\
   OBJ defs obj
   ==>
   READER_STATE defs (insert_dict (Num n) obj st)`,
  rw [insert_dict_def, READER_STATE_def]
  \\ fs [bool_case_eq, lookup_insert]
  \\ metis_tac []);

val delete_dict_thm = Q.store_thm("delete_dict_thm",
  `READER_STATE defs st
   ==>
   READER_STATE defs (delete_dict (Num n) st)`,
  rw [delete_dict_def, READER_STATE_def]
  \\ fs [lookup_delete] \\ metis_tac []);

val getPair_thm = Q.store_thm("getPair_thm",
  `OBJ defs obj /\
   getPair obj refs = (res, refs')
   ==>
   refs = refs' /\ !a b. res = Success (a, b) ==> OBJ defs a /\ OBJ defs b`,
  Cases_on `obj` \\ rw [getPair_def, st_ex_return_def, raise_Fail_def] \\ fs []
  \\ Cases_on `l` \\ fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ rfs []
  \\ every_case_tac \\ fs []
  \\ Cases_on `t` \\ fs [getPair_def, st_ex_return_def, raise_Fail_def]
  \\ rename1 `x::y::z`
  \\ Cases_on `z` \\ fs [getPair_def, st_ex_return_def, raise_Fail_def]
  \\ fs [OBJ_def]);

val getTys_thm = Q.store_thm("getTys_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getTys obj refs = (res, refs')
   ==>
   refs = refs' /\ !t ty. res = Success (t, ty) ==> TYPE defs t /\ TYPE defs ty`,
  Cases_on `obj`
  \\ fs [getTys_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ TRY (fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ NO_TAC)
  \\ TRY (PairCases_on `a`) \\ fs []
  \\ map_every imp_res_tac [getPair_thm, getType_thm, getName_thm] \\ fs [] \\ rw []
  \\ metis_tac [mk_vartype_thm, STATE_def]);

val map_getTys_thm = Q.store_thm("map_getTys_thm",
  `!xs refs res refs'.
     STATE defs refs /\
     EVERY (OBJ defs) xs /\
     map getTys xs refs = (res, refs')
     ==>
     refs = refs' /\
     !tys.
       res = Success tys
       ==>
       EVERY (\(ty1,ty2). TYPE defs ty1 /\ TYPE defs ty2) tys`,
  Induct \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [map_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ imp_res_tac getTys_thm
  \\ first_x_assum drule \\ fs []
  \\ rename1 `_ ==> _ z` \\ PairCases_on `z` \\ rw []);

val getTms_thm = Q.store_thm("getTms_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getTms obj refs = (res, refs')
   ==>
   refs = refs' /\
   !tm var. res = Success (tm, var) ==> TERM defs tm /\ TERM defs var`,
  Cases_on `obj`
  \\ fs [getTms_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ TRY (fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ NO_TAC)
  \\ TRY (PairCases_on `a`) \\ fs []
  \\ map_every imp_res_tac [getPair_thm, getTerm_thm, getVar_thm] \\ fs []
  \\ TRY (rename1 `getVar _ _ = (_ v,_)` \\ PairCases_on `v`)
  \\ TRY (metis_tac [])
  \\ irule mk_var_thm >- (asm_exists_tac \\ fs [])
  \\ map_every imp_res_tac [getPair_thm, getTerm_thm, getVar_thm] \\ fs []);

val map_getTms_thm = Q.store_thm("map_getTms_thm",
  `!xs refs res refs'.
     STATE defs refs /\
     EVERY (OBJ defs) xs /\
     map getTms xs refs = (res, refs')
     ==>
     refs = refs' /\
     !tmvs.
       res = Success tmvs
       ==>
       EVERY (\(tm1,tm2). TERM defs tm1 /\ TERM defs tm2) tmvs`,
  Induct \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [map_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ imp_res_tac getTms_thm
  \\ first_x_assum drule \\ fs []
  \\ rename1 `_ ==> _ z` \\ PairCases_on `z` \\ rw []);

val getNvs_thm = Q.store_thm("getNvs_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getNvs obj refs = (res, refs')
   ==>
   refs = refs' /\
   !tm1 tm2. res = Success (tm1, tm2) ==> TERM defs tm1 /\ TERM defs tm2`,
  Cases_on `obj`
  \\ fs [getNvs_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ TRY (fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ NO_TAC)
  \\ TRY (PairCases_on `a`) \\ fs []
  \\ map_every imp_res_tac [getPair_thm, getName_thm, getVar_thm] \\ fs []
  \\ TRY (rename1 `getVar _ _ = (_ v,_)` \\ PairCases_on `v`)
  \\ TRY (metis_tac [])
  \\ irule mk_var_thm
  \\ TRY (asm_exists_tac \\ fs [])
  \\ map_every imp_res_tac [getPair_thm, getName_thm, getVar_thm] \\ fs []);

val map_getNvs_thm = Q.store_thm("map_getNvs_thm",
  `!xs refs res refs'.
     STATE defs refs /\
     EVERY (OBJ defs) xs /\
     map getNvs xs refs = (res, refs')
     ==>
     refs = refs' /\
     !ts. res = Success ts ==> EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) ts`,
  Induct \\ once_rewrite_tac [map_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ rw [case_eq_thms] \\ fs []
  \\ imp_res_tac getNvs_thm \\ fs []
  \\ rename1 `_ tm /\ EVERY _ tms`
  \\ PairCases_on `tm`
  \\ first_x_assum drule \\ rw []);

val getCns_thm = Q.store_thm("getCns_thm",
  `STATE defs refs /\
   TERM defs tm /\
   getCns (tm, _) refs = (res, refs')
   ==>
   refs = refs' /\ !a. res = Success a ==> OBJ defs a`,
  rw [getCns_def, st_ex_bind_def, st_ex_return_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [dest_var_thm, OBJ_def]);

val map_getCns_thm = Q.store_thm("map_getCns_thm",
  `!xs refs res refs'.
     STATE defs refs /\
     EVERY (TERM defs o FST) xs /\
     map getCns xs refs = (res, refs')
     ==>
     refs = refs' /\ !xs. res = Success xs ==> EVERY (OBJ defs) xs`,
  Induct \\ once_rewrite_tac [map_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ Cases \\ fs []
  \\ rw [case_eq_thms] \\ fs []
  \\ imp_res_tac getCns_thm \\ fs []
  \\ first_x_assum drule \\ rw []);

(* imp_res_tac is not useful when the monadic functions are too deep *)
fun drule_or_nil thm =
  (drule (GEN_ALL thm) \\ rpt (disch_then drule \\ fs []) \\ rw []) ORELSE
  (qexists_tac `[]` \\ fs [] \\ metis_tac [])

(* TODO clean *)
val BETA_CONV_thm = Q.store_thm("BETA_CONV_thm",
  `STATE defs refs /\
   TERM defs tm /\
   BETA_CONV tm refs = (res, refs')
   ==>
   refs = refs' /\
   !thm. res = Success thm ==> THM defs thm`,
  Cases_on `tm`
  \\ rw [BETA_CONV_def, handle_Fail_def, raise_Fail_def, st_ex_bind_def,
        st_ex_return_def, case_eq_thms, UNCURRY, dest_comb_def, dest_abs_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (metis_tac [BETA_thm])
  \\ imp_res_tac TERM_Comb \\ fs []
  \\ imp_res_tac TERM_Abs \\ fs []
  \\ qmatch_asmsub_abbrev_tac `BETA tm1 refs`
  \\ qpat_x_assum `TERM defs tm1` assume_tac
  \\ drule_or_nil BETA_thm
  \\ qmatch_asmsub_abbrev_tac `mk_comb (a, b)`
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then (mp_tac o Q.SPECL [`b`,`a`] o (CONV_RULE (RESORT_FORALL_CONV rev))) \\ fs [] \\ rw []
  \\ drule_or_nil BETA_thm
  \\ `EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) [(t0,b)]` by fs []
  \\ drule_or_nil INST_thm);

(* ------------------------------------------------------------------------- *)
(* Reader preserves invariants                                               *)
(* ------------------------------------------------------------------------- *)

val readLine_thm = Q.store_thm("readLine_thm",
  `STATE defs refs /\
   READER_STATE defs st /\
   readLine line st refs = (res, refs')
   ==>
   ?ds.
     STATE (ds ++ defs) refs' /\
     !st'. res = Success st' ==> READER_STATE (ds ++ defs) st'`,
  fs [readLine_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ IF_CASES_TAC \\ fs []
  >- (* version *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ fs []
    \\ metis_tac [pop_thm, getNum_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* absTerm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (rename1 `mk_var v1` \\ Cases_on `v1` \\ fs [mk_var_def])
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getVar_thm, mk_abs_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* absThm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (rename1 `mk_var v1` \\ Cases_on `v1` \\ fs [mk_var_def])
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm, getVar_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [ABS_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* appTerm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getVar_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [mk_comb_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* appThm *)
   (fs [case_eq_thms] \\ rw  []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms]
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [MK_COMB_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* assume *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [ASSUME_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* axiom *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getList_thm, map_getTerm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def]) \\ rw []
    \\ metis_tac [find_axiom_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* betaConv *)
   (fs [case_eq_thms, handle_Fail_def] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, BETA_CONV_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* cons *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* const *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* constTerm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getType_thm, getConst_thm, match_type_thm, get_const_type_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [mk_const_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* deductAntysim *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [DEDUCT_ANTISYM_RULE_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* def *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, peek_thm, getNum_thm] \\ fs []
    \\ fs [insert_dict_thm]
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineConst *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getName_thm, type_of_thm] \\ fs []
    \\ res_tac \\ fs [] \\ rveq
    \\ imp_res_tac type_of_thm \\ fs [] \\ rveq
    \\ TRY (* For a new definition added to defs *)
     (drule (GEN_ALL mk_var_thm)
      \\ disch_then (qspecl_then [`n`,`ty`] mp_tac) \\ rw []
      \\ drule (GEN_ALL mk_eq_thm)
      \\ disch_then (qspec_then `tm` mp_tac)
      \\ rpt (disch_then drule \\ fs []) \\ rw []
      \\ drule (GEN_ALL new_basic_definition_thm)
      \\ disch_then drule \\ fs [] \\ rw []
      \\ qexists_tac `[d]` \\ rw []
      \\ `OBJ (d::defs) (Thm th)` by rw [OBJ_def])
    \\ TRY
      (irule push_push_thm \\ simp [OBJ_def]
       \\ irule READER_STATE_CONS_EXTEND \\ fs []
       \\ asm_exists_tac \\ fs [])
    \\ qexists_tac `[]` \\ fs []
    \\ drule (GEN_ALL mk_var_thm)
    \\ disch_then (qspecl_then [`n`,`ty`] mp_tac) \\ rw []
    \\ drule (GEN_ALL mk_eq_thm)
    \\ disch_then (qspec_then `tm` mp_tac)
    \\ rpt (disch_then drule \\ fs []) \\ rw []
    \\ drule (GEN_ALL new_basic_definition_thm)
    \\ disch_then drule \\ fs [] \\ rw [])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineConstList *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every drule_or_nil
      [pop_thm, getThm_thm, pop_thm, getList_thm, map_getNvs_thm, INST_thm]
    \\ TRY
     (drule_or_nil new_specification_thm
      \\ drule (GEN_ALL TERM_CONS_EXTEND) \\ rw []
      \\ `EVERY (TERM (d::defs) o FST) ls'` by fs [EVERY_MEM, ELIM_UNCURRY]
      \\ Q.ISPEC_THEN `ls'` mp_tac (Q.INST [`defs`|->`d::defs`] map_getCns_thm)
      \\ disch_then drule \\ rw [])
    \\ TRY
     (qexists_tac `[]` \\ fs []
      \\ drule (GEN_ALL new_specification_thm)
      \\ disch_then drule \\ fs []
      \\ rw []
      \\ NO_TAC)
    \\ qexists_tac `[d]` \\ fs []
    \\ irule push_push_thm \\ fs [OBJ_def] >- metis_tac []
    \\ irule READER_STATE_CONS_EXTEND \\ fs []
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineTypeOp *)
   (fs [case_eq_thms] \\ rw []
    \\ rpt (CHANGED_TAC (TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []))
    \\ map_every drule_or_nil [pop_thm, getThm_thm, pop_thm, getList_thm, pop_thm]
    \\ imp_res_tac getName_thm \\ fs [] \\ rveq
    \\ drule_or_nil pop_thm
    \\ TRY (qexists_tac `[]` \\ fs [] \\ metis_tac [])
    \\ drule_or_nil pop_thm
    \\ TRY
     (drule (GEN_ALL new_basic_type_definition_thm)
      \\ disch_then (qspec_then `nm` drule)
      \\ disch_then (qspecl_then [`rep`,`abs`] mp_tac) \\ rw [])
    \\ TRY (`TERM (ds ++ defs) (concl th1)` by metis_tac [concl_thm])
    \\ drule_or_nil dest_eq_thm
    \\ drule (GEN_ALL ABS_thm)
    \\ disch_then (qspec_then `th1` mp_tac)
    \\ rpt (disch_then drule) \\ rw []
    \\ qspec_then `th2` mp_tac (GEN_ALL SYM_thm)
    \\ rpt (disch_then drule) \\ rw []
    \\ TRY (`TERM (ds ++ defs) (concl th2')` by metis_tac [concl_thm])
    \\ drule_or_nil dest_eq_thm
    \\ drule_or_nil dest_comb_thm
    \\ drule_or_nil ABS_thm
    \\ qexists_tac `ds` \\ fs []
    \\ irule push_push_thm \\ fs [OBJ_def]
    \\ irule push_push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule READER_STATE_APPEND_EXTEND \\ fs []
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* eqMp *)
   (fs [case_eq_thms, handle_Fail_def] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm]
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [EQ_MP_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* hdTl *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* nil *)
   (fs [case_eq_thms] \\ rw [] \\ fs []
    \\ qexists_tac `[]` \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* opType *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm, getTypeOp_thm, map_getType_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [mk_type_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* pop *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ imp_res_tac pop_thm \\ fs []
    \\ qexists_tac `[]` \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* pragma *)
   (fs [case_eq_thms, handle_Fail_def] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ imp_res_tac pop_thm \\ fs [bool_case_eq, COND_RATOR]
    \\ imp_res_tac getName_thm
    \\ qexists_tac `[]` \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* proveHyp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [PROVE_HYP_thm, pop_thm, getThm_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* ref *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getNum_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ metis_tac [READER_STATE_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* refl *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, REFL_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* remove *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getNum_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ metis_tac [READER_STATE_def, delete_dict_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* subst *)
   (fs [case_eq_thms, handle_Clash_def] \\ rw []
    \\ rpt (CHANGED_TAC
      (TRY (pairarg_tac \\ fs [])
       \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []))
    \\ map_every drule_or_nil [pop_thm, getThm_thm]
    \\ map_every drule_or_nil [pop_thm, getPair_thm]
    \\ qpat_x_assum `_ _ tys` assume_tac
    \\ map_every drule_or_nil [getList_thm, map_getTys_thm, INST_TYPE_thm]
    \\ qpat_x_assum `_ _ tms` assume_tac
    \\ map_every drule_or_nil [getList_thm, map_getTms_thm, INST_thm]
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* sym *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [SYM_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* thm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getList_thm, getThm_thm, map_getTerm_thm] \\ fs []
    \\ metis_tac [ALPHA_THM_thm, READER_STATE_EXTEND])
  \\ IF_CASES_TAC \\ fs []
  >- (* trans *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [TRANS_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* typeOp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* var *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm, getType_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ fs [TYPE_def, TERM_def, holSyntaxTheory.term_ok_def]
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >-
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ drule_or_nil pop_thm
    \\ drule_or_nil getVar_thm
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ rename1 `mk_var v1` \\ PairCases_on `v1` \\ fs [mk_var_def, TERM_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* varType *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs []
    \\ fs [OBJ_def, STATE_def]
    \\ irule mk_vartype_thm
    \\ metis_tac [STATE_def, CONTEXT_def])
     (* digits *)
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ qexists_tac `[]` \\ fs [] \\ rw []
  \\ irule push_thm \\ fs [OBJ_def]);

val readLines_thm = Q.store_thm("readLines_thm",
  `!lines st res refs refs' defs.
     STATE defs refs /\
     READER_STATE defs st /\
     readLines lines st refs = (res, refs')
     ==>
     ?ds.
       STATE (ds ++ defs) refs' /\
       !st' n. res = Success (st', n) ==> READER_STATE (ds ++ defs) st'`,
  recInduct readLines_ind \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [readLines_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ CASE_TAC \\ fs []
  >- (rw [] \\ qexists_tac `[]` \\ fs [])
  \\ fs [case_eq_thms, PULL_EXISTS, handle_Fail_def, raise_Fail_def]
  \\ rw [] \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ drule (GEN_ALL readLine_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ first_x_assum drule
  >- (fs [next_line_def, READER_STATE_def] \\ metis_tac [])
  \\ imp_res_tac next_line_thm
  \\ disch_then drule \\ rw []
  \\ asm_exists_tac \\ fs []);

(* ------------------------------------------------------------------------- *)
(* Ok to use custom cotext/state                                             *)
(* ------------------------------------------------------------------------- *)

(* TODO move -- ml_kernel/ somewhere? *)
val init_refs_def = Define `
  init_refs =
    <| the_type_constants := init_type_constants
     ; the_term_constants := init_term_constants
     ; the_axioms         := init_axioms
     ; the_context        := init_context |>`;

val set_reader_ctxt_ok = Q.store_thm("set_reader_ctxt_ok",
  `set_reader_ctxt () init_refs = (res, refs)
   ==>
   res = Success () /\
   ?defs. STATE defs refs`,
  rw [set_reader_ctxt_def, st_ex_bind_def, st_ex_return_def,
      set_the_type_constants_def, set_the_term_constants_def,
      set_the_context_def, set_the_axioms_def, get_the_context_def,
      init_refs_def, reader_tys_def, reader_const_def, reader_axs_def]
  \\ EVAL_TAC \\ rw [Once RTC_CASES1, updates_cases] \\ EVAL_TAC
  \\ cheat (* TODO update STATE_def *)
  );

val readLines_init_state_thm = Q.store_thm("readLines_init_state_thm",
  `set_reader_ctxt () init_refs = (r, ax_refs) /\
   readLines lines init_state ax_refs = (res, refs)
   ==>
   ?defs.
     STATE defs refs /\
     !st n . res = Success (st, n) ==> READER_STATE defs st`,
  strip_tac
  \\ imp_res_tac set_reader_ctxt_ok
  \\ sg `READER_STATE defs init_state`
  >- fs [init_state_def, READER_STATE_def, lookup_def]
  \\ metis_tac [readLines_thm]);

(* ------------------------------------------------------------------------- *)
(* Program specification (shared)                                            *)
(* ------------------------------------------------------------------------- *)

val process_line_def = Define`
  process_line st refs ln =
    if invalid_line ln then (INL st, refs) else
    case readLine (fix_fun_typ (str_prefix ln)) st refs
    of (Success st, refs) => (INL st, refs)
     | (Failure (Fail s), refs) => (INR s, refs)`;

val process_lines_def = Define`
  (process_lines fd st refs fs [] =
    STDIO (add_stdout (fastForwardFD fs fd) (msg_success (lines_read st))) *
    HOL_STORE refs) ∧
  (process_lines fd st refs fs (ln::ls) =
   case process_line st refs ln of
   | (INL st,refs) =>
       process_lines fd (next_line st) refs (lineForwardFD fs fd) ls
   | (INR e,refs)  =>
       STDIO (add_stderr (lineForwardFD fs fd) (line_Fail st e)) *
       HOL_STORE refs)`;

val read_file_def = Define`
  read_file fs refs fnm =
    (if inFS_fname fs (File fnm) then
       (case readLines (all_lines fs (File fnm)) init_state refs of
        | (Success (_,n), refs) => (add_stdout fs (msg_success n), refs)
        | (Failure (Fail e), refs) => (add_stderr fs e, refs))
     else (add_stderr fs (msg_bad_name fnm), refs))`;

val set_reader_ctxt_no_exc = Q.store_thm("set_reader_ctxt_no_exc[simp]",
  `set_reader_ctxt () refs <> (Failure err, refs')`,
  rw [set_reader_ctxt_def, st_ex_bind_def, st_ex_return_def,
      get_the_context_def, set_the_term_constants_def,
      set_the_type_constants_def, set_the_context_def, set_the_axioms_def]);

val reader_main_def = Define `
   reader_main fs refs cl =
       case cl of
         [fnm] => FST (read_file fs (SND (set_reader_ctxt () refs)) fnm)
       | _ => add_stderr fs msg_usage`;

val _ = export_theory();
