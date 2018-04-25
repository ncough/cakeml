open Parse preamble wordLangTheory asmTheory sptreeTheory listTheory
     pred_setTheory;

val _ = new_theory "word_cse";

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

(* Value number assigned to vars *)
val _ = Datatype `
  vnumber = VConst ('a word)
          | VN num`;

(*
 * Supported operations, used as labels on graph nodes.
 * Non-deterministic operations are marked as unknown
 *)
val _ = Datatype `
  vop = VOp binop
      | VUnknown`;

(*
 * Graph nodes. Represents a non-constant value.
 * Uses are other nodes that make use of this value.
 * Held stores all vars known to hold this value.
 *)
val _ = Datatype `
  vnode = <| label : vop ;
             operands : ('a vnumber) list ;
             uses : unit spt ;
             held : unit spt |>`;

(*
 * Numbering state.
 * Holds the next value number and all nodes.
 * Also holds a mapping from vars to their assigned numbers.
 *)
val _ = Datatype `
  vnumbering = <| vnums : ('a vnumber) spt ;
                  vnodes : ('a vnode) spt ;
                  next : num |>`;

val initial_vn_def = Define `
  initial_vn = <| vnums := LN ; vnodes := LN ; next := 0 |>`;

(* value node operations *)
val delete_held_def = Define `
  delete_held var n vnodes =
    case lookup n vnodes of
      | SOME node => insert n (node with held updated_by (delete var)) vnodes
      | NONE => vnodes`;

val insert_held_def = Define `
  insert_held var n vnodes =
    case lookup n vnodes of
      | SOME node => insert n (node with held updated_by (insert var ())) vnodes
      | NONE => vnodes`;

val insert_use_def = Define `
  insert_use use n vnodes =
    case lookup n vnodes of
      | SOME node => insert n (node with uses updated_by (insert use ())) vnodes
      | NONE => vnodes`;

(* value number operations *)
val get_num_def = Define `
  get_num var nums = lookup var nums.vnums`;

val get_nums_def = Define `
  get_nums vars nums = MAP (\v. get_num v nums) vars`;

val unassign_num_def = Define `
  unassign_num var nums =
    case get_num var nums of
      | SOME (VN v) =>
          nums with <| vnums updated_by (delete var) ;
                       vnodes updated_by (delete_held var v) |>
      | _ => nums with vnums updated_by (delete var)`;

val assign_num_def = Define `
  (assign_num var (VN v) nums =
    (unassign_num var nums) with
      <| vnums updated_by (insert var (VN v)) ;
         vnodes updated_by (insert_held var v) |>) ∧
  (assign_num var (VConst w) nums =
    (unassign_num var nums) with
      vnums updated_by (insert var (VConst w)))`;

val assign_nums_def = Define `
  (assign_nums ((var, NONE)::vns) nums = 
    (assign_nums vns (unassign_num var nums))) ∧
  (assign_nums ((var, SOME vn)::vns) nums = 
    (assign_nums vns (assign_num var vn nums))) ∧
  (assign_nums [] nums = nums)`;

(*
 * Move
 * Track values through a move and remove any moves known to not
 * modify state, eg. dst and src have same VN
 *)
val get_moves_def = Define `
  get_moves (moves : (num,num) alist) nums =
    ZIP (MAP FST moves, get_nums (MAP SND moves) nums)`;

val redun_move_def = Define `
  (redun_move [] acc nums = acc) ∧
  (redun_move ((dst, src)::xs) acc nums = 
    let
      vn1 = get_num dst nums;
      vn2 = get_num src nums
    in
      if IS_SOME(vn1) ∧ vn1 = vn2 then redun_move xs acc nums
      else redun_move xs ((dst,src)::acc) nums)`;

val cse_move_def = Define `
  cse_move pri moves nums : (α prog # α vnumbering) =
    let
      nmoves = redun_move moves [] nums;
      nnums = assign_nums (get_moves moves nums) nums
    in
      (Move pri nmoves, nnums)`;

(*
 * Inst
 *)
val all_const_def = Define `
  (all_const ((VConst w)::xs) =
    case all_const xs of
      | SOME ws => SOME (w::ws)
      | NONE => NONE) ∧
  (all_const xs = NONE)`;

(*
 * Constant folding
 * If all operands are known for a deterministic op, carry it out now
 * TODO: Identities may allow for folds over non-constants, eg. a = b, a - b = 0
 *)
val fold_def = Define `
  (fold (VOp op) ws = word_op op ws) ∧
  (fold label ws = NONE)`;

val attempt_fold_def = Define `
  attempt_fold label vnums =
    do
      cs <- all_const vnums;
      r <- fold label cs;
      SOME (VConst r)
    od`;

(*
 * Expression matching
 * Lookup an expressions operands, if they are known intersect their uses
 * and match on the result.
 *
 * TODO: Identities
 *)
val compare_exp_def = Define `
  compare_exp lbl vns nums can =
    case lookup can nums.vnodes of
      | NONE => F
      | SOME n => n.label <> VUnknown ∧ n.label = lbl ∧ n.operands = vns`;

val inter_uses_def = Define `
  (inter_uses [VN n] nums =
    case lookup n nums.vnodes of
      | SOME node => node.uses
      | NONE => LN) ∧
  (inter_uses (VN n::xs) nums =
    case lookup n nums.vnodes of
      | SOME node => inter node.uses (inter_uses xs nums)
      | NONE => LN) ∧ 
  (inter_uses (vn :α vnumber list) (nums :α vnumbering) = LN)`;

val attempt_match_def = Define`
  attempt_match lbl vns (nums :α vnumbering) :α vnumber option =
    let
      uses = MAP FST (toAList (inter_uses vns nums));
      f = compare_exp lbl vns nums;
    in 
      case FILTER f uses of
        | [x] => SOME (VN x)
        | _ => NONE`;

val find_exp_def = Define `
  find_exp label vns nums =
    OPTION_CHOICE (attempt_fold label vns) (attempt_match label vns nums)`;

(*
 * Generate either a move, const or skip depending on the situation
 *)
val gen_move_def = Define `
  (gen_move dst ((VN n) : α vnumber) (nums : α vnumbering) =
    case lookup n nums.vnodes of
      | SOME node =>
          (case toAList node.held of
            | ((i,p)::t) => SOME (Move 0 [(dst,i)])
            | _ => NONE)
      | NONE => NONE) ∧
  (gen_move dst (VConst w) nums = SOME (Inst (Const dst w)))`;

val gen_prog_def = Define `
  gen_prog dst vn nums =
    if get_num dst nums = SOME vn then SOME (Skip)
    else gen_move dst vn nums`;

(* Attempt to match/fold the expression and generate a replacement prog *)
val redun_exp_def = Define `
  redun_exp label dst vns nums =
    do
      vn <- find_exp label vns nums;
      prog <- gen_prog dst vn nums;
      SOME (prog, assign_num dst vn nums)
    od`;

(*
 * Add a new node to the graph
 * The node is added with its uses and operands. These won't be modified again.
 *)
val add_uses_def = Define `
  (add_uses use (((VN vn) :α vnumber)::vns) (nums : α vnumbering) =
    add_uses use vns (nums with vnodes updated_by (insert_use use vn))) ∧
  (add_uses use (x::vns) nums = add_uses use vns nums) ∧
  (add_uses use [] nums = nums)`;

val add_empty_vnode_def = Define `
  add_empty_vnode lbl ops nums =
    let
      n = <| label := lbl ; operands := ops ; uses := LN ; held := LN |>;
      nnums = add_uses nums.next ops nums;
    in
      nnums with <| vnodes updated_by insert nums.next n ;
                    next updated_by SUC |>`

val add_vnode_def = Define `
  add_vnode lbl var ops nums =
    assign_num var (VN nums.next) (add_empty_vnode lbl ops nums)`;

val get_or_assign_num_def = Define `
  get_or_assign_num var nums =
    case get_num var nums of
      | SOME vn => (vn, nums)
      | NONE => (VN nums.next, add_vnode VUnknown var [] nums)`

val get_or_assign_nums_def = Define `
  (get_or_assign_nums (v::vs) nums =
    let
      (vn,nums1) = get_or_assign_num v nums;
      (vns,nums2) = get_or_assign_nums vs nums1
    in 
      (vn::vns,nums2)) ∧
  (get_or_assign_nums [] nums = ([],nums))`;

val cse_binop_def = Define `
  cse_binop op r1 r2 ri nums =
    let
      lbl = VOp op;
      orig = Inst (Arith (Binop op r1 r2 ri));
      (vns,nnums) = case ri of
        | Reg r3 => get_or_assign_nums [r2; r3] nums
        | Imm w => let (vn,n) = get_or_assign_nums [r2] nums in (vn ++ [VConst w], n)
    in
      case redun_exp lbl r1 vns nnums of
        | SOME res => res
        | NONE => (orig, add_vnode lbl r1 vns nnums)`;

(*
 * arith instructions
 *)
val cse_arith_def = Define `
  (cse_arith (Binop bop r1 r2 ri) nums = cse_binop bop r1 r2 ri nums) /\
  (cse_arith (Shift s r1 r2 n) nums =
    (Inst (Arith (Shift s r1 r2 n)), unassign_num r1 nums)) /\
  (cse_arith (Div r1 r2 r3) nums =
    (Inst (Arith (Div r1 r2 r3)), unassign_num r1 nums)) /\
  (cse_arith (LongMul r1 r2 r3 r4) nums =
    (Inst (Arith (LongMul r1 r2 r3 r4)), unassign_num r2 (unassign_num r1 nums))) /\
  (cse_arith (LongDiv r1 r2 r3 r4 r5) nums =
    (Inst (Arith (LongDiv r1 r2 r3 r4 r5)), unassign_num r1 (unassign_num r2 nums))) /\
  (cse_arith (AddCarry r1 r2 r3 r4) nums =
    (Inst (Arith (AddCarry r1 r2 r3 r4)), unassign_num r4 (unassign_num r1 nums))) /\
  (cse_arith (AddOverflow r1 r2 r3 r4) nums =
    (Inst (Arith (AddOverflow r1 r2 r3 r4)), unassign_num r4 (unassign_num r1 nums))) /\
  (cse_arith (SubOverflow r1 r2 r3 r4) nums =
    (Inst (Arith (SubOverflow r1 r2 r3 r4)), unassign_num r4 (unassign_num r1 nums)))`;

(*
 * floating point instructions
 *)
val cse_fp_def = Define `
  (cse_fp (FPLess r f1 f2) (nums : 'a vnumbering) =
    (Inst (FP (FPLess r f1 f2)), unassign_num r nums)) ∧
  (cse_fp (FPLessEqual r f1 f2) nums =
    (Inst (FP (FPLessEqual r f1 f2)), unassign_num r nums)) ∧
  (cse_fp (FPEqual r f1 f2) nums =
    (Inst (FP (FPEqual r f1 f2)), unassign_num r nums)) ∧
  (cse_fp (FPMovToReg r1 r2 d) (nums : 'a vnumbering) =
    (Inst (FP (FPMovToReg r1 r2 d)),
      if dimindex(:'a) = 64 then unassign_num r1 nums
      else unassign_num r2 (unassign_num r1 nums))) ∧
  (cse_fp fp (nums :α vnumbering) = (Inst (FP fp) :α prog, nums))`;

(*
 * memory instructions
 *)
val cse_mem_def = Define `
  (cse_mem Load r a nums = (Inst (Mem Load r a), unassign_num r nums)) /\
  (cse_mem Load8 r a nums = (Inst (Mem Load8 r a), unassign_num r nums)) /\
  (cse_mem memop r a (nums :α vnumbering) =
    (Inst (Mem memop r a) :α prog, nums))`;

val cse_inst_def = Define `
  (cse_inst asm$Skip nums = (Inst (Skip), nums)) ∧
  (cse_inst (Const dst w) nums =
    (Inst (Const dst w), assign_num dst (VConst w) nums)) ∧
  (cse_inst (Arith a) nums = cse_arith a nums) ∧
  (cse_inst (FP fp) nums = cse_fp fp nums) ∧
  (cse_inst (Mem memop r a) nums = cse_mem memop r a nums)`;

(*
 * manage modifications to vnums due to assigns
 * there should be none after inst sel, so just maintain correctness
 *)
val cse_assign_def = Define `
  cse_assign dst exp (nums :α vnumbering) =
    (wordLang$Assign dst exp :α prog, unassign_num dst nums)`;

val cse_get_def = Define `
  cse_get dst name (nums :α vnumbering) =
    (Get dst name :α prog, unassign_num dst nums)`;

(* logic for merging vnums at a join *)
(* TODO: actually perform a merge of some sort *)
(* TODO: Pruning of value graph *)
val merge_vnums_def = Define `
  merge_vnums (vnums1 :α vnumbering) (vnums2 :α vnumbering) :α vnumbering =
    initial_vn`;

val cse_loop_def = Define `
  (* operations updating state *)
  (cse_loop (Move pri moves) nums = cse_move pri moves nums) /\
  (cse_loop (Assign dst exp) nums = cse_assign dst exp nums) /\
  (cse_loop (Inst i) nums = cse_inst i nums) ∧
  (cse_loop (Get dst name) nums = cse_get dst name nums) /\
  (cse_loop (LocValue dst n) nums = (LocValue dst n, unassign_num dst nums)) /\
  (* control flow *)
  (cse_loop (MustTerminate p) nums =
    let (pn, numsn) = cse_loop p nums in
      (MustTerminate pn, numsn)) /\
  (cse_loop (Seq p1 p2) nums =
    let
      (p1n, nums1) = cse_loop p1 nums;
      (p2n, nums2) = cse_loop p2 nums1
    in
      (Seq p1n p2n, nums2)) /\
  (* TODO: optimisations over comparisons *)
  (cse_loop (wordLang$If cmp lhs rhs p1 p2) nums =
    let (p1n, nums1) = cse_loop p1 nums in
    let (p2n, nums2) = cse_loop p2 nums in
    (wordLang$If cmp lhs rhs p1n p2n, merge_vnums nums1 nums2)) /\
  (* GC / Calls - reset nums *)
  (cse_loop (Call ret dest args handler) nums =
    case ret of
      | NONE => (Call ret dest args handler, initial_vn)
      | SOME (n, names, ret_handler, l1, l2) =>
        (if handler = NONE then
           (let (ret_handlern, _) = cse_loop ret_handler initial_vn in
           (Call (SOME (n, names, ret_handlern, l1, l2)) dest args handler, initial_vn))
         else
           (Call ret dest args handler, initial_vn))) /\
  (cse_loop (Alloc n names) nums = (Alloc n names, initial_vn)) /\
  (cse_loop (FFI x0 x1 x2 x3 x4 names) nums = (FFI x0 x1 x2 x3 x4 names, initial_vn)) /\
  (* other instructions are ignored *)
  (* TODO: potential opts for memory operations *)
  (cse_loop (p : 'a prog) (nums : 'a vnumbering)  =  (p, nums))`;

val cse_def = Define `
  cse (p : 'a prog) = FST (cse_loop p (initial_vn : 'a vnumbering))`;

val _ = export_theory();
