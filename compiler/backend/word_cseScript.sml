open Parse preamble wordLangTheory asmTheory sptreeTheory listTheory
     pred_setTheory;

open jsonLangTheory presLangTheory;

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
  wideop = High
         | Low`

val _ = Datatype `
  vop = VOp binop
      | VShift shift num
      | VDiv
      | VLongMul wideop
      | VLongDiv wideop
      | VAddCarry wideop
      | VAddOverflow wideop
      | VSubOverflow wideop
      | VLoad num
      | VLoad8 num
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
  vnumbering = <| globals : ('a vnumber) spt ;
                  locals : ('a vnumber) spt ;
                  vnodes : ('a vnode) spt ;
                  memnum : num ;
                  next : num |>`;

val _ = Datatype `
  event = RedunMove
        | Merge
        | GCPrune
        | Init
        | Unassign
        | Assign 
        | RedunIf
        | RedunGet ('a prog)
        | RedunMem ('a prog)
        | RedunArith ('a prog)`;

val log_event_def = Define `
  (log_event RedunMove = empty_ffi (strlit "redun move")) ∧
  (log_event Merge = empty_ffi (strlit "merge")) ∧
  (log_event GCPrune = empty_ffi (strlit "gcprune")) ∧
  (log_event Init = empty_ffi (strlit "init")) ∧
  (log_event Unassign = empty_ffi (strlit "unassign")) ∧
  (log_event Assign = empty_ffi (strlit "assign")) ∧
  (log_event RedunIf = empty_ffi (strlit "redun if")) ∧

  (log_event (RedunGet Skip) = empty_ffi (strlit "redun get skip")) ∧
  (log_event (RedunGet (Inst _)) = empty_ffi (strlit "redun get const")) ∧
  (log_event (RedunGet (Move _ _)) = empty_ffi (strlit "redun get copy")) ∧
  (log_event (RedunGet p) = empty_ffi (strlit "redun get unknown")) ∧ 

  (log_event (RedunMem Skip) = empty_ffi (strlit "redun mem skip")) ∧
  (log_event (RedunMem (Inst _)) = empty_ffi (strlit "redun mem const")) ∧
  (log_event (RedunMem (Move _ _)) = empty_ffi (strlit "redun mem copy")) ∧
  (log_event (RedunMem p) = empty_ffi (strlit "redun mem unknown")) ∧

  (log_event (RedunArith Skip) = empty_ffi (strlit "redun skip")) ∧
  (log_event (RedunArith (Inst _)) = empty_ffi (strlit "redun const")) ∧
  (log_event (RedunArith (Move _ _)) = empty_ffi (strlit "redun copy")) ∧
  (log_event (RedunArith p) = empty_ffi (strlit "redun unknown"))`;

val initial_vn_def = Define `
  initial_vn =
    <| globals := LN ; locals := LN ; vnodes := LN ; next := 0 ; memnum := 0 |>`;

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
  get_num var nums = lookup var nums.locals`;

val get_nums_def = Define `
  get_nums vars nums = MAP (\v. get_num v nums) vars`;

val unassign_num_def = Define `
  unassign_num var (nums :'a vnumbering) =
    case get_num var nums of
      | SOME (VN v) =>
          let _ = log_event (Unassign :'a event) in
          nums with <| locals updated_by (delete var) ;
                       vnodes updated_by (delete_held var v) |>
      | SOME (VConst w) =>
          let _ = log_event (Unassign :'a event) in
          nums with locals updated_by (delete var)
      | NONE => nums`;

val assign_num_def = Define `
  (assign_num var (VN v) (nums :'a vnumbering) =
    let _ = log_event (Assign :'a event) in
    (unassign_num var nums) with
      <| locals updated_by (insert var (VN v)) ;
         vnodes updated_by (insert_held var v) |>) ∧
  (assign_num var (VConst w) nums =
    let _ = log_event (Assign :'a event) in
    (unassign_num var nums) with
      locals updated_by (insert var (VConst w)))`;

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
  (redun_move ((dst, src)::xs) acc (nums : 'a vnumbering) = 
    let
      vn1 = get_num dst nums;
      vn2 = get_num src nums
    in
      if IS_SOME(vn1) ∧ vn1 = vn2 then
        (let _ = (log_event (RedunMove : 'a event)) in redun_move xs acc nums)
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
  (fold (VShift sh n) [w] = word_sh sh w n) ∧
  (fold VDiv [w1; w2] = if w2 ≠ 0w then SOME(w1 / w2) else NONE) ∧
  (fold (VLongMul wide) [w1; w2] =
    let r = w2n w1 * w2n w2 in
    case wide of
      | High => SOME (n2w (r DIV dimword(:'a)))
      | Low => SOME (n2w r)) ∧
  (fold (VLongDiv wide) [w1; w2; w3] =
    let n = w2n w1 * dimword (:'a) + w2n w2 in
    let d = w2n w3 in
    if d = 0 then NONE else
    let q = n DIV d in
    if q >= dimword(:'a) then NONE else
      case wide of
        | High => SOME (n2w (n MOD d))
        | Low => SOME (n2w q)) ∧
  (fold (VAddCarry wide) [w1; w2; w3] =
    let res = w2n w1 + w2n w2 + if w3 = 0w then 0 else 1 in
      case wide of
        | High => SOME (n2w res)
        | Low => SOME (if dimword(:'a) ≤ res then (1w:'a word) else 0w)) ∧
  (fold (VAddOverflow wide) [w1; w2] =
    case wide of
      | High => SOME (w1 + w2)
      | Low => SOME (if w2i (w1 + w2) ≠ w2i w1 + w2i w2 then 1w else 0w)) ∧
  (fold (VSubOverflow wide) [w1; w2] =
    case wide of
      | High => SOME (w1 - w2)
      | Low => SOME (if w2i (w1 - w2) ≠ w2i w1 - w2i w2 then 1w else 0w)) ∧
  (fold label ws = NONE)`;

val attempt_fold_def = Define `
  attempt_fold label nums =
    do
      cs <- all_const nums;
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
val pick_source_def = Define `
  pick_source n nums =
    case lookup n nums.vnodes of
      | SOME node =>
          (case toAList node.held of
            | ((i,p)::t) => SOME i
            | _ => NONE)
      | NONE => NONE`;

val gen_move_def = Define `
  (gen_move dst ((VN n) : α vnumber) (nums : α vnumbering) =
    case pick_source n nums of
      | SOME i => SOME (Move 0 [(dst,i)])
      | NONE => NONE) ∧
  (gen_move dst (VConst w) nums = SOME (Inst (Const dst w)))`;

val gen_wide_move_def = Define `
  (gen_wide_move dst1 dst2 (VN n1) (VN n2) nums =
    case (pick_source n1 nums, pick_source n2 nums) of
      | SOME i1, SOME i2 => SOME (Move 0 [(dst1,i1);(dst2,i2)])
      | _, _ => NONE) ∧
  (gen_wide_move dst1 dst2 (VConst c) (VN n) nums =
    case (gen_move dst2 (VN n) nums, gen_move dst1 (VConst c) nums) of
      | SOME p1, SOME p2 => SOME (Seq p1 p2)
      | _, _ => NONE) ∧
  (gen_wide_move dst1 dst2 vn1 vn2 nums =
    case (gen_move dst1 vn1 nums, gen_move dst2 vn2 nums) of
      | SOME p1, SOME p2 => SOME (Seq p1 p2)
      | _, _ => NONE)`;

val gen_prog_def = Define `
  gen_prog dst vn nums =
    if get_num dst nums = SOME vn then SOME (Skip)
    else gen_move dst vn nums`;

val gen_wide_prog_def = Define `
  gen_wide_prog dst1 dst2 vn1 vn2 nums =
    if dst1 = dst2 then gen_prog dst2 vn2 nums
    else gen_wide_move dst1 dst2 vn1 vn2 nums`;

(* Attempt to match/fold the expression and generate a replacement prog *)
val redun_exp_def = Define `
  redun_exp label dst vns nums =
    case find_exp label vns nums of
      | SOME vn => SOME(gen_prog dst vn nums, assign_num dst vn nums)
      | NONE => NONE`

val redun_wide_exp_def = Define `
  redun_wide_exp lbl dst1 dst2 vns nums =
    let
      dsts = do
               vn1 <- find_exp (lbl High) vns nums;
               vn2 <- find_exp (lbl Low) vns nums;
               SOME(vn1,vn2)
             od
    in
      case dsts of
        | SOME (vn1, vn2) =>
            SOME(gen_wide_prog dst1 dst2 vn1 vn2 nums,
            assign_num dst2 vn2 (assign_num dst1 vn1 nums))
        | NONE => NONE`;
 
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

val add_wide_vnode_def = Define `
  add_wide_vnode lbl var1 var2 ops nums =
    let
      lbl1 = add_empty_vnode (lbl High) ops nums;
      lbl2 = add_empty_vnode (lbl Low) ops lbl1;
      l = [(var1, SOME (VN nums.next)); (var2, SOME (VN lbl1.next))]
    in
      assign_nums l lbl2`;

(*
 * Given a var, either find it in nums or create an Unknown VN to represent it
 * Modified flag in the result represents whether any where created
 *)
val get_or_assign_num_def = Define `
  get_or_assign_num var nums =
    case get_num var nums of
      | SOME vn => (vn,nums,F)
      | NONE => (VN nums.next,add_vnode VUnknown var [] nums,T)`

val get_or_assign_nums_def = Define `
  (get_or_assign_nums (v::vs) nums =
    let
      (vn,nums1,m1) = get_or_assign_num v nums;
      (vns,nums2,m2) = get_or_assign_nums vs nums1
    in 
      (vn::vns,nums2,m1 ∨ m2)) ∧
  (get_or_assign_nums [] nums = ([],nums,F))`;

(*
 * Functions that take an expression in lbl,dsts,args form and
 * either matches it with another in nums to produce a new prog or
 * inserts the new expression into the graph
 *)
val cse_exp_def = Define `
  cse_exp lbl dst args nums =
    let (vns,nnums,modified) = get_or_assign_nums args nums in
    if modified then (NONE, add_vnode lbl dst vns nnums)
    else case redun_exp lbl dst vns nnums of
      | SOME n => n
      | NONE => (NONE, add_vnode lbl dst vns nnums)`;

val cse_const_exp_def = Define `
  cse_const_exp lbl dst args c nums =
    let
      (vns1,nnums,modified) = get_or_assign_nums args nums;
      vns = (vns1 ++ [VConst c])
    in
      if modified then (NONE, add_vnode lbl dst vns nnums)
      else case redun_exp lbl dst vns nnums of
        | SOME n => n
        | NONE => (NONE, add_vnode lbl dst vns nnums)`;

val cse_wide_exp_def = Define `
  cse_wide_exp (lbl:wideop -> vop) dst1 dst2 args nums =
    let
      (vns,nnums,modified) = get_or_assign_nums args nums;
      fnums = add_wide_vnode lbl dst1 dst2 vns nnums
    in
      if modified then (NONE,fnums)
      else case redun_wide_exp lbl dst1 dst2 vns nums of
        | SOME n => n
        | NONE => (NONE,fnums)`;

(*
 * arith instructions
 *)
val cse_arith_def = Define `
  (cse_arith (Binop op r1 r2 (Reg r)) nums = cse_exp (VOp op) r1 [r2;r] nums) ∧
  (cse_arith (Shift s r1 r2 n) nums = cse_exp (VShift s n) r1 [r2] nums) ∧
  (cse_arith (Div r1 r2 r3) nums = cse_exp VDiv r1 [r2;r3] nums) ∧

  (cse_arith (Binop op r1 r2 (Imm c)) nums =
    cse_const_exp (VOp op) r1 [r2] c nums) ∧

  (cse_arith (LongMul r1 r2 r3 r4) nums =
    cse_wide_exp VLongMul r1 r2 [r3;r4] nums) ∧
  (cse_arith (LongDiv r1 r2 r3 r4 r5) nums =
    cse_wide_exp VLongDiv r2 r1 [r3;r4;r5] nums) ∧
  (cse_arith (AddCarry r1 r2 r3 r4) nums =
    cse_wide_exp VAddCarry r1 r4 [r2;r3;r4] nums) ∧
  (cse_arith (AddOverflow r1 r2 r3 r4) nums =
    cse_wide_exp VAddOverflow r1 r4 [r2;r3] nums) ∧
  (cse_arith (SubOverflow r1 r2 r3 r4) nums =
    cse_wide_exp VSubOverflow r1 r4 [r2;r3] nums)`;

(*
 * floating point instructions
 *)
val cse_fp_def = Define `
  (cse_fp (FPLess r f1 f2) nums = (NONE, unassign_num r nums)) ∧
  (cse_fp (FPLessEqual r f1 f2) nums = (NONE, unassign_num r nums)) ∧
  (cse_fp (FPEqual r f1 f2) nums = (NONE, unassign_num r nums)) ∧
  (cse_fp (FPMovToReg r1 r2 d) (nums : 'a vnumbering) =
    (NONE,
      if dimindex(:'a) = 64 then unassign_num r1 nums
      else unassign_num r2 (unassign_num r1 nums))) ∧
  (cse_fp fp (nums :α vnumbering) = (NONE :α prog option, nums))`;

(*
 * memory instructions
 *)
val cse_mem_def = Define `
  (cse_mem Load r1 (Addr r2 w) nums =
    cse_const_exp (VLoad nums.memnum) r1 [r2] w nums) ∧
  (cse_mem Load8 r1 (Addr r2 w) nums =
    cse_const_exp (VLoad8 nums.memnum) r1 [r2] w nums) ∧
  (cse_mem memop r a nums = (NONE, nums with memnum updated_by SUC))`;

val cse_inst_def = Define `
  (cse_inst Skip nums = (Inst (asm$Skip), nums)) ∧
  (cse_inst (Const dst w) nums =
    (Inst (Const dst w), assign_num dst (VConst w) nums)) ∧
  (cse_inst (Arith a) nums =
    let (np,nnums) = cse_arith a nums in
      case np of
        | SOME p => let _ = log_event (RedunArith p) in (p, nnums)
        | NONE => (Inst (Arith a), nnums)) ∧
  (cse_inst (FP fp) nums =
    let (np,nnums) = cse_fp fp nums in
      ((case np of SOME p => p | NONE => Inst (FP fp)), nnums)) ∧
  (cse_inst (Mem memop r a) nums =
    let (np,nnums) = cse_mem memop r a nums in
      case np of
        | SOME p => let _ = log_event (RedunMem p) in (p, nnums)
        | NONE => (Inst (Mem memop r a), nnums))`;

(* logic for merging vnums at a join *)
(* TODO: actually perform a merge of some sort *)
(* TODO: Pruning of value graph *)
val merge_vnums_def = Define `
  merge_vnums (nums1 :α vnumbering) (nums2 :α vnumbering) :α vnumbering =
    let _ = log_event (Merge :α event) in initial_vn`;

val gc_prune_def = Define `
  gc_prune (nums :α vnumbering) :α vnumbering = 
    let _ = log_event (GCPrune :α event) in initial_vn`;

val fold_cmp_def = Define `
  (fold_cmp cmp lhs (Reg rhs) nums =
    case (get_num lhs nums, get_num rhs nums) of
      | SOME (VConst w1), SOME (VConst w2) => SOME (word_cmp cmp w1 w2)
      | SOME (VN vn1), SOME (VN vn2) =>
          if vn1 <> vn2 then NONE else
            (case cmp of
              | Equal => SOME T
              | Less => SOME F
              | Lower => SOME F 
              | Test => SOME F
              | NotEqual => SOME F
              | NotLess => SOME T
              | NotLower => SOME T 
              | NotTest => SOME T)
      | p1, p2 => NONE) ∧
  (fold_cmp cmp lhs (Imm rhs) nums =
    case get_num lhs nums of
      | SOME (VConst w1) => SOME (word_cmp cmp w1 rhs)
      | p1 => NONE)`;

val name2num_def = Define `
  (name2num NextFree   = 0) ∧
  (name2num EndOfHeap  = 1) ∧
  (name2num TriggerGC  = 2) ∧
  (name2num HeapLength = 3) ∧
  (name2num ProgStart  = 4) ∧
  (name2num BitmapBase = 5) ∧
  (name2num CurrHeap   = 6) ∧
  (name2num OtherHeap  = 7) ∧
  (name2num AllocSize  = 8) ∧
  (name2num Globals    = 9) ∧
  (name2num Handler    = 10) ∧
  (name2num GenStart   = 11) ∧
  (name2num (Temp w)   = 12 + (w2n w))`;

val cse_get_def = Define `
  cse_get dst name nums =
    let
      en = name2num name;
    in
      case lookup en nums.globals of
        | SOME vn => 
            (case gen_prog dst vn nums of
              | SOME p => let _ = log_event (RedunGet p) in (p, assign_num dst vn nums)
              | NONE => (Get dst name, assign_num dst vn nums))
        | NONE => (Get dst name, (add_vnode VUnknown dst [] nums) with globals
        updated_by (insert en (VN nums.next)))`;

val cse_set_def = Define `
  cse_set name src (nums : α vnumbering) : α prog # α vnumbering =
    let
      en = name2num name;
    in
      case get_num src nums of
        | SOME vn => (Set name (Var src), nums with globals updated_by (insert en vn))
        | NONE => (Set name (Var src), (add_vnode VUnknown src [] nums) with
        globals updated_by (insert en (VN nums.next)))`;

val cse_loop_def = Define `
  (* optimised operations *)
  (cse_loop (Move pri moves) nums = cse_move pri moves nums) ∧
  (cse_loop (Inst i) nums = cse_inst i nums) ∧
  (cse_loop (Get dst name) nums = cse_get dst name nums) ∧
  (cse_loop (Set name (Var src)) nums = cse_set name src nums) ∧ 

  (* control flow *)
  (cse_loop (MustTerminate p) nums =
    let (pn, numsn) = cse_loop p nums in (MustTerminate pn, numsn)) ∧
  (cse_loop (Seq p1 p2) nums =
    let
      (p1n, nums1) = cse_loop p1 nums;
      (p2n, nums2) = cse_loop p2 nums1
    in
      (Seq p1n p2n, nums2)) ∧
  (cse_loop ((If cmp lhs rhs p1 p2) : 'a prog) (nums : 'a vnumbering) =
    case fold_cmp cmp lhs rhs nums of
      | SOME b =>
          let _ = log_event (RedunIf : 'a event) in
          if b then cse_loop p1 nums else cse_loop p2 nums
      | NONE =>
          let
            (p1n, nums1) = cse_loop p1 nums;
            (p2n, nums2) = cse_loop p2 nums;
          in
            (If cmp lhs rhs p1n p2n, merge_vnums nums1 nums2)) ∧

  (* GC / Calls - reset nums *)
  (cse_loop (Call ret dest args handler) nums =
    case ret of
      | NONE => (Call ret dest args handler, gc_prune nums)
      | SOME (n, names, ret_handler, l1, l2) =>
        (if handler = NONE then
           (let (ret_handlern, _) = cse_loop ret_handler initial_vn in
           (Call (SOME (n, names, ret_handlern, l1, l2)) dest args handler,
             gc_prune nums))
         else
           (Call ret dest args handler, gc_prune nums))) ∧
  (cse_loop (Alloc n names) nums = (Alloc n names, gc_prune nums)) ∧
  (cse_loop (FFI x0 x1 x2 x3 x4 names) nums =
    (FFI x0 x1 x2 x3 x4 names, gc_prune nums)) ∧

  (* other instructions are ignored *)
  (cse_loop (Assign dst exp) nums = (Assign dst exp, unassign_num dst nums)) ∧
  (cse_loop (LocValue dst n) nums = (LocValue dst n, unassign_num dst nums)) ∧
  (cse_loop (Set name exp) nums = (Set name exp, nums)) ∧ 
  (cse_loop (p :'a prog) (nums :'a vnumbering)  =  (p, nums))`;

val cse_def = Define `
  cse (p :'a prog) =
    let _ = log_event (Init : 'a event) in
    FST (cse_loop p (initial_vn :'a vnumbering))`;

val _ = export_theory();
