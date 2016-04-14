structure arm8bilInstructionLib :> arm8bilInstructionLib =
struct

open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open proofTools arithTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
open arm8stepbilLib;


(* **************************************** *)
(* INSTRUCTION LIFTER *)
(* **************************************** *)
(* Theorem to simplifying boolean cast *)
val bool_cast_simpl_tm = prove (``!e.(case if e then Reg1 (1w :word1) else Reg1 (0w :word1)
       of Reg1 v11 => Reg Bit1
        | Reg8 v12 => Reg Bit8
        | Reg16 v13 => Reg Bit16
        | Reg32 v14 => Reg Bit32
        | Reg64 v15 => Reg Bit64) = Reg Bit1``,
       (RW_TAC (srw_ss()) []));
(* Theorem to simplifying boolean cast *)
val bool_cast_simpl2_tm = prove (``!e.(case bool2b e
       of Reg1 v11 => Reg Bit1
        | Reg8 v12 => Reg Bit8
        | Reg16 v13 => Reg Bit16
        | Reg32 v14 => Reg Bit32
        | Reg64 v15 => Reg Bit64) = Reg Bit1``,
       (RW_TAC (srw_ss()) [bool2b_def]));

val bool_cast_simpl3_tm = prove (``(!v1 . ∃v. Reg1 v1 = bool2b v)``,
 (RW_TAC (srw_ss()) [bool2b_def])
 THEN (EXISTS_TAC ``if v1=1w:word1 then T else F``)
 THEN (RW_TAC (srw_ss()) [])
 THEN (UNDISCH_TAC ``v1 <> 1w:word1``)
 THEN (blastLib.BBLAST_TAC)
);
val bool_cast_simpl4_tm = prove (``(!v1 . (∃v. bool2b v1 = bool2b v))``,
 (RW_TAC (srw_ss()) [bool2b_def])
 THENL [
    (EXISTS_TAC ``T``) THEN (RW_TAC (srw_ss()) []),
    (EXISTS_TAC ``F``) THEN (RW_TAC (srw_ss()) [])
 ]);


(* To use a normal form, we prefer to express casts as bool2b x *)
(* instead of if x then v1 else v2 *)
fun ABBREV_NEW_ENV n (asl, g) =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
	val (x,_) = dest_imp g
	val (s,_) = dest_eq x
	val (f, [s,n]) = strip_comb s
        (* eval tac was simplifying too much *)
        val thm_rev = (SIMP_CONV (srw_ss()) [] ``^s.environ``)
	val nenv = (snd o dest_eq o concl) thm_rev
       in
	(* I must ensure that the same simplification is applied to the env *)
	   ((SIMP_TAC (srw_ss()) []) THEN
	   (Q.ABBREV_TAC `^var_name=^nenv`)) (asl,g)
    end;





fun PROCESS_ONE_ASSIGNMENT certs n =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
	val th_just = (List.nth (certs, n-1))
	val th1 = SPEC ``^var_name`` th_just
	val th2 = if is_forall (concl th1) then SPEC ``s:arm8_state`` th1 else th1
    in
	(ABBREV_NEW_ENV n)
	THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
	THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	THEN (ASSUME_TAC th2)
	THEN (REV_FULL_SIMP_TAC (srw_ss()) [Abbr `^var_name`])
	(* bool type simplification *)
	THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
	THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
	THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
	THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
    end;

val sim_invariant_def = Define `sim_invariant s env =
   (env "" = (NoType,Unknown)) ∧
   (env "R0" = (Reg Bit64,Int (Reg64 (s.REG 0w)))) ∧
   (env "R1" = (Reg Bit64,Int (Reg64 (s.REG 1w)))) ∧
   (env "R2" = (Reg Bit64,Int (Reg64 (s.REG 2w)))) ∧
   (env "R3" = (Reg Bit64,Int (Reg64 (s.REG 3w)))) ∧
   (env "R30" = (Reg Bit64,Int (Reg64 (s.REG 30w)))) ∧
   (env "ProcState_C" = (Reg Bit1,Int (bool2b s.PSTATE.C))) ∧
   (env "ProcState_N" = (Reg Bit1,Int (bool2b s.PSTATE.N))) ∧
   (env "ProcState_V" = (Reg Bit1,Int (bool2b s.PSTATE.V))) ∧
   (env "ProcState_Z" = (Reg Bit1,Int (bool2b s.PSTATE.Z))) ∧
   (env "arm8_state_PC" = (Reg Bit64,Int (Reg64 s.PC))) ∧
   (env "arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 s.SP_EL0))) ∧
   (∃v. env "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R2" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R3" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
   (∃v. env "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃v. env "tmp_arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 v))) ∧
   (∃m.
      (env "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
      ∀a. m (Reg64 a) = Reg8 (s.MEM a)) /\
   ¬s.SCTLR_EL1.E0E ∧ (s.PSTATE.EL = 0w) ∧ (s.exception = NoException) /\
   (Aligned (s.SP_EL0,8)) /\
   ¬s.SCTLR_EL1.SA0
      `;

fun tc_gen_goal p certs step pc_value fault_wt_mem_cnd =
      let val goal = ``
        (^(list_mk_conj (hyp step))) ==>
        (s.PC = ^pc_value) ==>
        (sim_invariant s env) ==>
       (?n. ((INDEX_FIND 0 (\(x:bil_block_t). x.label = (Address (Reg64 (s.PC)))) prog) =
               SOME(n, <| label:= (Address (Reg64 (s.PC)));
                  statements:= ^p|>))) ==>
        (NextStateARM8 s = SOME s1) ==>
        (bil_exec_step_n <|
          pco:= SOME <| label:= (Address (Reg64 (s.PC))); index:= 0 |>;
          environ:= env ;
          termcode:= Unknown ;
          debug:=d1;
          execs:=e1;
          pi:=prog
          |> ^(numSyntax.term_of_int ((List.length certs)+1)) = bs1) ==>
        (((sim_invariant s1 bs1.environ) /\
         (!a. ^fault_wt_mem_cnd a ==> (s.MEM a = s1.MEM a))) \/
         (bs1.pco = NONE))
        ``
      in
	  goal
      end;

(* prevent >>>~ to become >>> *)
(* HOL_Interactive.toggle_quietdec(); *)
val myss = simpLib.remove_ssfrags (srw_ss()) ["word shift"];
(* HOL_Interactive.toggle_quietdec(); *)

fun tc_one_instruction inst =
    let val code = arm8AssemblerLib.arm8_code inst;
	val instr = (hd code);
	val (p, certs, [step]) = tc_stmt_arm8_hex instr;
	val goal = tc_gen_goal p certs step ``0w:word64`` ``\x:word64.T``;
	val thm = prove(``^goal``,
			(DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction *)
			THEN (MAP_EVERY (PROCESS_ONE_ASSIGNMENT certs) (List.tabulate (List.length certs, fn x => x+1)))
			(* Computation completed *)
			THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
			THEN DISCH_TAC
			(* use the step theorem *)
			THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [] (DISCH_ALL step))))
			THEN (FULL_SIMP_TAC (srw_ss()) [])
			THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
		       );
    in
	thm
    end;


(* Try to speed up the computation *)
val single_step_assign_64_thm = prove( ``
!pc_value env past_steps var e v lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assign var e)) ==>
((LENGTH l) > (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(var <> "") ==>
(?v.((env var) = (Reg Bit64, Int (Reg64 (v))))) ==>
((bil_eval_exp e env) = Int (Reg64 v)) ==>
(?n. ((INDEX_FIND 0 (\(x:bil_block_t). x.label = lbl) prog) =
			SOME(n, <| label:= (Address (Reg64 pc_value));
				 statements:= l|>))
) ==>
(
 (bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i|>;
     pi :=prog;
     environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
   n) = 
(bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i + 1|>;
     pi := prog;
     environ :=
       (λc.
          if var = c then (Reg Bit64,Int (Reg64 v))
          else env c); termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
)
``,
       (REPEAT STRIP_TAC)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [bil_exec_step_def, bil_get_program_block_info_by_label_def])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [])
);


val single_step_assign_1_thm = prove( ``
!pc_value env past_steps var e v lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assign var e)) ==>
((LENGTH l) > (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(var <> "") ==>
(?v.((env var) = (Reg Bit1, Int (bool2b (v))))) ==>
((bil_eval_exp e env) = Int (bool2b v)) ==>
(?n. ((INDEX_FIND 0 (\(x:bil_block_t). x.label = lbl) prog) =
			SOME(n, <| label:= (Address (Reg64 pc_value));
				 statements:= l|>))
) ==>
(
 (bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i|>;
     pi := prog;
     environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
   n) = 
(bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i + 1|>;
     pi := prog;
     environ :=
       (λc.
          if var = c then (Reg Bit1,Int (bool2b v))
          else env c); termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
)
``,
       (REPEAT STRIP_TAC)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [bil_exec_step_def, bil_get_program_block_info_by_label_def])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (arith_ss) [bool_cast_simpl2_tm])
);


val single_step_assign_mem64_thm = prove( ``
!pc_value env past_steps (vname:string) exp hm lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assign "arm8_state_MEM"
     (* (Store (Den "arm8_state_MEM") ba bv (Const (Reg1 0w)) Bit64) *)
     exp
)) ==>
((LENGTH l) > (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(?v.((env "arm8_state_MEM") = (MemByte Bit64,v))) ==>
(∃m.
   (* ((bil_eval_exp (Store (Den "arm8_state_MEM") ba bv (Const (Reg1 0w)) Bit64) env) = (Mem Bit64 m)) ∧ *)
   ((bil_eval_exp exp env) = (Mem Bit64 m)) ∧
   ∀a. m (Reg64 a) = Reg8 (hm a)) ==>
(?n. ((INDEX_FIND 0 (\(x:bil_block_t). x.label = lbl) prog) =
			SOME(n, <| label:= (Address (Reg64 pc_value));
				 statements:= l|>))
) ==>
(?m.
(
 (bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i|>;
     pi := prog;
     environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
   n) = 
(bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i + 1|>;
     pi := prog;
     environ :=
       (λc.
          if "arm8_state_MEM" = c then (MemByte Bit64,Mem Bit64 m)
          else env c); termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
) /\
(∀a. m (Reg64 a) = Reg8 (hm a))
)
``,
       (REPEAT STRIP_TAC)
       THEN (EXISTS_TAC ``m:bil_int_t -> bil_int_t``)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq o fst o dest_conj) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [bil_exec_step_def, bil_get_program_block_info_by_label_def])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
);



val static_jmp_thm = prove( ``
!pc_value1 pc_value2 env past_steps lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Jmp (Const (Reg64 pc_value2)))) ==>
((LENGTH l) = (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(?n. ((INDEX_FIND 0 (\(x:bil_block_t). x.label = lbl) prog) =
			SOME(n, <| label:= (Address (Reg64 pc_value1));
				 statements:= l|>))
) ==>
(
 (bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i|>;
     pi :=prog;
     environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
   n) = 
(bil_exec_step_n
   <|pco := SOME <|label := Address (Reg64 pc_value2); index := 0|>;
     pi := prog;
     environ :=env; termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
)
``,
       (REPEAT STRIP_TAC)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [bil_exec_step_def, bil_get_program_block_info_by_label_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [])
);


val assert_step_thm = prove( ``
!pc_value env past_steps e v lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assert e)) ==>
((LENGTH l) > (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
((bil_eval_exp e env) = Int (bool2b v)) ==>
(?n. ((INDEX_FIND 0 (\(x:bil_block_t). x.label = lbl) prog) =
			SOME(n, <| label:= (Address (Reg64 pc_value));
				 statements:= l|>))
) ==>
((v ==>
    (
     (bil_exec_step_n
       <|pco := SOME <|label := lbl; index := i|>;
         pi := prog;
         environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
       n) = 
    (bil_exec_step_n
       <|pco := SOME <|label := lbl; index := i + 1|>;
         pi := prog;
         environ := env; termcode := Unknown; debug := d1;
         execs := past_steps + 1|> (n-1))
    ))
  /\
  (~v ==>
     ((bil_exec_step_n
       <|pco := SOME <|label := lbl; index := i|>;
         pi := prog;
         environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
       n).pco = NONE))
)
``,
       (REPEAT STRIP_TAC)
       THENL [
           (fn (asl,g) =>
        let val rx = (snd o dest_eq) g in
            (Q.ABBREV_TAC `s2=^rx`)(asl,g)
        end)
           THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
           THEN (FULL_SIMP_TAC (arith_ss) [])
           THEN (FULL_SIMP_TAC (srw_ss()) [bil_exec_step_def, bil_get_program_block_info_by_label_def])
           THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])
           THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
           THEN (FULL_SIMP_TAC (arith_ss) [])
           THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
           THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``]),
           ALL_TAC]
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [bil_exec_step_def, bil_get_program_block_info_by_label_def])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])
       THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
);



fun ONE_EXEC2 certs prog pc_value i =

(fn (asl,curr_goal) =>
let val exec_term = (fst o dest_eq o fst o dest_imp) curr_goal;
    val (_, [state, steps]) = strip_comb exec_term;
    val (_, [("pco", pco), _,  ("environ", env), tc, db, ("execs", ex)]) = TypeBase.dest_record state;
    val lbl = (optionSyntax.dest_some) pco;
    val (_, [("label", lbl), ("index", index)]) = TypeBase.dest_record lbl;
    val sts = prog;
    val (sts1, _) = listSyntax.dest_list sts;
    val statement = List.nth(sts1, i-1);
    val (operator, [vname, exp]) = strip_comb statement;
    val th_just = (List.nth (certs, i-1));
    val th_just1 = SPEC env th_just;
    val th_just2 = if is_forall (concl th_just1)
		   then SPEC ``s:arm8_state`` th_just1
		   else th_just1;
    val th_just3 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def] th_just2);
    (* For constant PC *)
    val th_just3Bis = REWRITE_RULE [ASSUME ``s.PC = ^pc_value``] th_just3;
    val th_just4 = (UNDISCH_ALL th_just3Bis);
    val (single_assign_th, value) =
        (* standard case that is when we are not assigning a memory *)
        if (is_eq o concl) th_just4
        then
            let val value = (hd o snd o strip_comb o hd o snd o strip_comb o snd o dest_eq o concl) th_just4;
            in if (type_of value) = ``:word64``
               then (single_step_assign_64_thm, value)
               else (single_step_assign_1_thm, value)
            end
        else
          let val value = (snd o dest_comb o snd o dest_eq o snd o dest_forall o snd o dest_conj o snd o dest_exists o concl) th_just4;
              val value = ``\a.^value``;
  	      (* we extract the type of the write *)
	            val store_value_eq = (fst o dest_conj o snd o dest_exists o concl) th_just4;
              val store_exp = (hd o snd o strip_comb o fst o dest_eq) store_value_eq;
              val store_type = (hd o rev o snd o strip_comb) store_exp;
          in
              if store_type = ``Bit64`` then (single_step_assign_mem64_thm, value)
              else (single_step_assign_mem64_thm, value)
          end;
    val th1 = SPECL [pc_value, env, ex, vname, exp, value, lbl, steps] single_assign_th;
    val th2 = (SPECL [sts, numSyntax.mk_numeral(Arbnum.fromInt (i-1))]) th1;
    val lbl_not_empty_thm = prove(``^((fst o dest_imp o concl) th2)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_minus_i_not_zero_thm = prove(``^((fst o dest_imp o snd o dest_imp o concl) th2)``, (FULL_SIMP_TAC (arith_ss) []));
    (* val simp2 = (SIMP_RULE (srw_ss()) [] th2); *)
    val hd_thm = prove (``(EL ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1))) ^sts = Assign ^vname ^exp)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_thm = prove (``(LENGTH ^sts > ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1)))+1)``, (FULL_SIMP_TAC (srw_ss()) []));
    val th3 = (MP (MP (MP (MP th2 lbl_not_empty_thm) length_minus_i_not_zero_thm) hd_thm) length_thm);
    (* For constant PC *)
    val th3Bis = REWRITE_RULE [ASSUME ``s.PC = ^pc_value``] th3;
    val th4 = UNDISCH_ALL th3Bis;
in
    (
     (* We prove the big theorem and we use it for the substitution *)
     (SUBGOAL_THEN (concl th4) (fn thm =>
           (* we are probably handling a memory update *)
           if ((is_exists o concl) thm) then
               ((CHOOSE_TAC thm)
	            	THEN (FULL_SIMP_TAC (srw_ss()) [])
                (* we should not remove the additional assumption *)
                (* that guarantee constraint the content of the memory *)
                THEN (PAT_ASSUM ``bil_exec_step_n a b = c`` (fn thm => ALL_TAC))
	             )
            else ((REWRITE_TAC [thm])
                 THEN (SIMP_TAC (srw_ss()) []))
     ))
     THENL [
          (fn (asl,goal) =>
                (MAP_EVERY (fn tm => if List.exists (fn tm1 => tm1 = tm) asl
                                     then ALL_TAC
                                     (* This is probably a memory *)
                                     else if (is_exists tm) then
                                        (SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                         THENL [
                                          (FULL_SIMP_TAC (srw_ss()) []),
                                          ALL_TAC
                                        ]
                                     else ALL_TAC
        	     ) (hyp th_just4)
          )(asl,goal))
          (* need to substitute the s.PC = 0 everywhere *)
          (* THEN (REV_FULL_SIMP_TAC (bool_ss) []) *)
          (* There is a problem with nested updates of the environment. *)
          (* We can not use simp tac, but only rewrite *)
          (* Also we should avoid to rempove the ipothesis itself *)
          THEN (PAT_ASSUM ``s.PC=^pc_value`` (fn thm =>
                   (RULE_ASSUM_TAC (REWRITE_RULE [thm]))
                   THEN (ASSUME_TAC thm)))
          THEN (ASSUME_TAC th_just4)
          THEN (fn (asl,goal) =>
               (MAP_EVERY (fn tm =>
                              (* The hypotesis is in the assumptions *)
                              if List.exists (fn tm1 => tm1 = tm) asl then ALL_TAC
                              (* this is the assumption justified by the expression certificate *)
                              else if tm = (concl th_just4) then ALL_TAC
                              (* "tmp_arm8_state_PC" ≠ "" *)
                              else if (is_neq tm) andalso ((snd o dest_eq o dest_neg) tm = ``""``) then
                                   (ASSUME_TAC (prove(tm, FULL_SIMP_TAC (srw_ss()) [])))
                              (* it is an existential quantifier, we try to solve this using the assumptions *)
                              else if (is_exists tm) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) [
                                    					    bool_cast_simpl3_tm,
                                                  bool_cast_simpl4_tm]), ALL_TAC])
                              (* env" "" = (NoType,Unknown) *)
                              else if (is_eq tm) andalso ((snd o dest_eq)tm = ``(NoType,Unknown)``) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) []), ALL_TAC])
                              else (print_term tm;
                                    ALL_TAC))
                    (hyp th4)
          )(asl,goal))
          THEN (ACCEPT_TAC th4)
          ,
          ALL_TAC]
    )
    (asl, curr_goal)
end
)

;

fun ONE_EXEC_JMP certs prog pc_value i =

(fn (asl,curr_goal) => (
let val exec_term = (fst o dest_eq o fst o dest_imp) curr_goal;
    val (_, [state, steps]) = strip_comb exec_term;
    val (_, [("pco", pco), _,  ("environ", env), tc, db, ("execs", ex)]) = TypeBase.dest_record state;
    val lbl = (optionSyntax.dest_some) pco;
    val (_, [("label", lbl), ("index", index)]) = TypeBase.dest_record lbl;val (sts1, _) = listSyntax.dest_list prog;
    val sts = prog;
    val (sts1, _) = listSyntax.dest_list sts;
    val statement = List.nth(sts1, i-1);
    val (operation, [addr_exp]) = strip_comb statement;
    val (_, [addr]) = strip_comb addr_exp;
    val (_, [addr_w]) = strip_comb addr;
    val th1 = SPECL [pc_value, addr_w, env, ex, lbl, steps] static_jmp_thm;
    val th2 = (SPECL [sts, numSyntax.mk_numeral(Arbnum.fromInt (i-1))]) th1;
    val lbl_not_empty_thm = prove(``^((fst o dest_imp o concl) th2)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_minus_i_not_zero_thm = prove(``^((fst o dest_imp o snd o dest_imp o concl) th2)``, (FULL_SIMP_TAC (arith_ss) []));
    val hd_thm = prove (``(EL ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1))) ^sts = Jmp (Const (Reg64 (^addr_w))))``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_thm = prove (``(LENGTH ^sts = ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1)))+1)``, (FULL_SIMP_TAC (srw_ss()) []));
    val th3 = (MP (MP (MP (MP th2 lbl_not_empty_thm) length_minus_i_not_zero_thm) hd_thm) length_thm);
    (* For constant PC *)
    val th3Bis = REWRITE_RULE [ASSUME ``s.PC = ^pc_value``] th3;
    val th4 = UNDISCH_ALL th3Bis;
in
    (
     (* We prove the big theorem and we use it for the substitution *)
     (SUBGOAL_THEN (concl th4) (fn thm =>
           ((REWRITE_TAC [thm]) THEN (SIMP_TAC (srw_ss()) []))
     ))
     THENL [
          (* need to substitute the s.PC = 0 everywhere *)
          (PAT_ASSUM ``s.PC=^pc_value`` (fn thm =>
                   (RULE_ASSUM_TAC (REWRITE_RULE [thm]))
                   THEN (ASSUME_TAC thm)))
          THEN (fn (asl,goal) =>
               (MAP_EVERY (fn tm =>
                              (* The hypotesis is in the assumptions *)
                              if List.exists (fn tm1 => tm1 = tm) asl then ALL_TAC
                              (* "tmp_arm8_state_PC" ≠ "" *)
                              else if (is_neq tm) andalso ((snd o dest_eq o dest_neg) tm = ``""``) then
                                   (ASSUME_TAC (prove(tm, FULL_SIMP_TAC (srw_ss()) [])))
                              (* it is an existential quantifier, we try to solve this using the assumptions *)
                              else if (is_exists tm) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) [
                                    					    bool_cast_simpl3_tm,
                                                  bool_cast_simpl4_tm]), ALL_TAC])
                              (* env" "" = (NoType,Unknown) *)
                              else if (is_eq tm) andalso ((snd o dest_eq)tm = ``(NoType,Unknown)``) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) []), ALL_TAC])
                              else (print_term tm;
                                    ALL_TAC))
                    (hyp th4)
          )(asl,goal))
          THEN (ACCEPT_TAC th4)
          ,
          ALL_TAC]
    )
end

)(asl,curr_goal))

;

fun ONE_EXEC_ASSERT certs prog pc_value i =

(fn (asl,curr_goal) =>
let val exec_term = (fst o dest_eq o fst o dest_imp) curr_goal;
    val (_, [state, steps]) = strip_comb exec_term;
    val (_, [("pco", pco), _,  ("environ", env), tc, db, ("execs", ex)]) = TypeBase.dest_record state;
    val lbl = (optionSyntax.dest_some) pco;
    val (_, [("label", lbl), ("index", index)]) = TypeBase.dest_record lbl;
    val sts = prog;
    val (sts1, _) = listSyntax.dest_list sts;
    val statement = List.nth(sts1, i-1);
    val (operator, [exp]) = strip_comb statement;
    val th_just = (List.nth (certs, i-1));
    val th_just1 = SPEC env th_just;
    val th_just2 = if is_forall (concl th_just1)
		   then SPEC ``s:arm8_state`` th_just1
		   else th_just1;
    val th_just3 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def] th_just2);
    (* For constant PC *)
    val th_just3Bis = REWRITE_RULE [ASSUME ``s.PC = ^pc_value``] th_just3;
    val th_just4 = (UNDISCH_ALL th_just3Bis);
    val value = (hd o snd o strip_comb o hd o snd o strip_comb o snd o dest_eq o concl) th_just4;
    val th1 = SPECL [pc_value, env, ex, exp, value, lbl, steps] assert_step_thm;
    val th2 = (SPECL [sts, numSyntax.mk_numeral(Arbnum.fromInt (i-1))]) th1;
    val lbl_not_empty_thm = prove(``^((fst o dest_imp o concl) th2)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_minus_i_not_zero_thm = prove(``^((fst o dest_imp o snd o dest_imp o concl) th2)``, (FULL_SIMP_TAC (arith_ss) []));
    (* val simp2 = (SIMP_RULE (srw_ss()) [] th2); *)
    val hd_thm = prove (``(EL ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1))) ^sts = Assert ^exp)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_thm = prove (``(LENGTH ^sts > ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1)))+1)``, (FULL_SIMP_TAC (srw_ss()) []));
    val th3 = (MP (MP (MP (MP th2 lbl_not_empty_thm) length_minus_i_not_zero_thm) hd_thm) length_thm);
    (* For constant PC *)
    val th3Bis = REWRITE_RULE [ASSUME ``s.PC = ^pc_value``] th3;
    val th4 = UNDISCH_ALL th3Bis;
in
    (
     (* We prove the big theorem and we use it for the substitution *)
     (SUBGOAL_THEN (concl th4) (fn thm =>
         (ASSUME_TAC thm)
         THEN (Q.ABBREV_TAC `assert_cnd = ^value`)
         THEN (Cases_on `assert_cnd`)
         THENL [
            (FULL_SIMP_TAC (srw_ss()) []),
            (FULL_SIMP_TAC (srw_ss()) [])
       			THEN (RW_TAC (srw_ss()) [])
            THEN (FULL_SIMP_TAC (srw_ss()) [])
         ]
     ))
     THENL [
          (fn (asl,goal) =>
                (MAP_EVERY (fn tm => if List.exists (fn tm1 => tm1 = tm) asl
                                     then ALL_TAC
                                     (* This is probably a memory *)
                                     else if (is_exists tm) then
                                        (SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                         THENL [
                                          (FULL_SIMP_TAC (srw_ss()) []),
                                          ALL_TAC
                                        ]
                                     else ALL_TAC
        	     ) (hyp th_just4)
          )(asl,goal))
          (* need to substitute the s.PC = 0 everywhere *)
          (* THEN (REV_FULL_SIMP_TAC (bool_ss) []) *)
          (* There is a problem with nested updates of the environment. *)
          (* We can not use simp tac, but only rewrite *)
          (* Also we should avoid to rempove the ipothesis itself *)
          THEN (PAT_ASSUM ``s.PC=^pc_value`` (fn thm =>
                   (RULE_ASSUM_TAC (REWRITE_RULE [thm]))
                   THEN (ASSUME_TAC thm)))
          THEN (ASSUME_TAC th_just4)
          THEN (fn (asl,goal) =>
               (MAP_EVERY (fn tm =>
                              (* The hypotesis is in the assumptions *)
                              if List.exists (fn tm1 => tm1 = tm) asl then ALL_TAC
                              (* this is the assumption justified by the expression certificate *)
                              else if tm = (concl th_just4) then ALL_TAC
                              (* "tmp_arm8_state_PC" ≠ "" *)
                              else if (is_neq tm) andalso ((snd o dest_eq o dest_neg) tm = ``""``) then
                                   (ASSUME_TAC (prove(tm, FULL_SIMP_TAC (srw_ss()) [])))
                              (* it is an existential quantifier, we try to solve this using the assumptions *)
                              else if (is_exists tm) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) [
                                    					    bool_cast_simpl3_tm,
                                                  bool_cast_simpl4_tm]), ALL_TAC])
                              (* env" "" = (NoType,Unknown) *)
                              else if (is_eq tm) andalso ((snd o dest_eq)tm = ``(NoType,Unknown)``) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) []), ALL_TAC])
                              else (print_term tm;
                                    ALL_TAC))
                    (hyp th4)
          )(asl,goal))
          THEN (ACCEPT_TAC th4)
          ,
          ALL_TAC]
    )
    (asl, curr_goal)
end
)

;



fun ONE_EXEC_MAIN certs prog pc_value i =

(fn (asl,curr_goal) => (
let  val (sts1, _) = listSyntax.dest_list prog;
     val statement = List.nth(sts1, i-1);
     val (operation, _) = strip_comb statement;
in
  if (operation = ``Assign``) then (ONE_EXEC2 certs prog pc_value i)
  else if (operation = ``Assert``) then (ONE_EXEC_ASSERT certs prog pc_value i)
  else (ONE_EXEC_JMP certs prog pc_value i)
end
)(asl,curr_goal))

;



fun does_match tm pat =
    let val _ = match_term pat tm in true end
    handle _ => false;

val align_conversion_thm = prove(``!x y. Aligned(x,y) = ((x && ((n2w y) - 1w)) = 0w:word64)``, cheat);

fun extract_upds byte_val upds =
    if is_cond byte_val then
      let val (cnd, v, others) = dest_cond byte_val;
          val addr = (fst o dest_eq) cnd;
      in addr::(extract_upds others upds) end
    else upds;


fun generate_assert step fault_wt_mem =
  let val s1 = (optionSyntax.dest_some o snd o dest_eq o concl) step;
      val byte_val = (snd o dest_eq o concl o EVAL) ``^s1.MEM(a)``;
      val upds = extract_upds byte_val [];
      val side_conds_wt_mem = List.map (fn tm=> (snd o dest_eq o concl o EVAL) ``~((^fault_wt_mem) ^tm)``) upds;
  in if side_conds_wt_mem = [] then (false, [], [])
     else
      let val side_cond_wt_mem = list_mk_conj side_conds_wt_mem;
          val (bexp_wt_assert, _,  cert_wt_assert) = tc_exp_arm8  side_cond_wt_mem;
      in (true, [``Assert ^bexp_wt_assert``], [cert_wt_assert]) end
  end;

fun tc_one_instruction2_by_bin instr pc_value fault_wt_mem =
    let val (p, certs, [step]) = tc_stmt_arm8_hex instr;
  val (sts, sts_ty) = listSyntax.dest_list p;
  (* manually add the memory fault *)
  val (memory_check_needed, assert_stm, assert_cert) = generate_assert step fault_wt_mem;
  val sts = List.concat [assert_stm, sts];
  val certs = List.concat [assert_cert, certs];
  (* manually add the final jump *)
  val sts = List.concat [sts, [``Jmp (Const (Reg64 (^pc_value+4w)))``]];
  val p = listSyntax.mk_list(sts,sts_ty);
	val goal = tc_gen_goal p certs step pc_value fault_wt_mem;
	val thm = prove(``^goal``,
      (REWRITE_TAC [sim_invariant_def])
			THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction, plus 1 since the fixed jump has no certificate *)
			THEN (MAP_EVERY (ONE_EXEC_MAIN certs p pc_value) (List.tabulate ((List.length certs) + 1, fn x => x+1)))
			(* Computation completed *)
			THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
			THEN DISCH_TAC
			(* use the step theorem *)
			THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [ASSUME ``s.PC=^pc_value``] (DISCH_ALL step))))
			THEN (FULL_SIMP_TAC (srw_ss()) [])
      (* Manually abbreviate the memory condition *)
      THEN (Q.ABBREV_TAC `mem_cond = ^((snd o dest_eq o concl o EVAL) ``∀a. (\x.x<+0x100000w:word64) a ⇒ (s.MEM a = s1.MEM a)``)`)
			THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
      (* other part of the invariant: basically show that the code does not mess up with other stuff *)
      THEN (fn (asl,g) =>
        if (does_match g ``Aligned(x,y)``) then
             ((REPEAT (PAT_ASSUM ``Aligned(x,y)`` (fn thm=> (ASSUME_TAC thm) THEN (UNDISCH_TAC (concl thm)))))
              THEN (REWRITE_TAC [align_conversion_thm])
              THEN (blastLib.BBLAST_TAC))
              (asl,g)
        else ALL_TAC(asl,g)
      )
      (* now we manage the memory condition using the assumption of the assertion *)
      THEN (UNABBREV_ALL_TAC)
      THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (FULL_SIMP_TAC (srw_ss()) [])
    );
    in
	thm
    end;

fun tc_one_instruction2 inst pc_value fault_wt_mem =
    let val code = arm8AssemblerLib.arm8_code inst ;
      	val instr = (hd code);
    in
	tc_one_instruction2_by_bin instr pc_value fault_wt_mem
    end;

(* ------------------------------------------------------------------------- *)
end
