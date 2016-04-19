HOL_Interactive.toggle_quietdec();
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
open arm8bilInstructionLib;
HOL_Interactive.toggle_quietdec();

  


fun PAT_UNDISCH pat thm =
    List.foldl (fn (tm,thm) =>
         (let val _ =  match_term pat tm in thm end)
         handle _ => (DISCH tm thm))
    (UNDISCH_ALL thm) ((hyp o UNDISCH_ALL) thm);

fun normalize_thm thm = 
    (* fix the invariant: *)
    let (* First step: reorder the assumptions so we have pc=v as first *)
        (* and the we use that to simplify the statement *)
        val th1_1 = PAT_UNDISCH ``s.PC = v`` thm;
        val pc_value = (List.hd (hyp th1_1));
        (* I do not rewrite the pc in bil_exec_step_n *)
        val th1_1 = PAT_UNDISCH ``(bil_exec_step_n a b) = c`` thm;
        val th1_2 = REWRITE_RULE [ASSUME pc_value] th1_1;
        val th1_3 = DISCH_ALL th1_2;
        (* Check that the pc is aligned *)
        val th_tmp = prove (``Aligned (^((snd o dest_eq) pc_value),4)``, SIMP_TAC (srw_ss()) [Aligned_def, Align_def]);
        val th1_4 = SIMP_RULE (srw_ss()) [th_tmp] th1_3;
    in  
        th1_4
    end;

fun get_term_from_ass_path pat thm =
    let val th1_1 = PAT_UNDISCH pat thm;
    in (List.hd (hyp th1_1))
    end;

fun extract_code thm =
    let val hs = ((hyp o UNDISCH_ALL) thm)
        val ex = List.filter (fn tm => is_exists tm) hs
    in List.hd ex end;
        


fun extract_side_cond thm = 
    let val th1 =  List.foldl (fn (tm,thm) =>
            (let val cs = strip_conj tm in
                if List.exists (fn tm1 => tm1 = ``(s.exception = NoException)``) cs then thm
                else (DISCH tm thm)
            end)
             handle _ => (DISCH tm thm))
          (UNDISCH_ALL thm) ((hyp o UNDISCH_ALL) thm);
    in List.hd (hyp th1) end;
    
fun extract_mem_cnd tm =
 list_mk_conj (List.filter (fn tm =>
    let val _ = match_term ``s.MEM a = v`` tm in true end
    handle _ => false) (strip_conj tm));

fun extract_other_cnd tm =
 let val other = (List.filter (fn tm =>
    let val _ = match_term ``s.MEM a = v`` tm in false end
    handle _ =>
      if       tm = ``¬s.SCTLR_EL1.E0E`` orelse tm = ``(s.PSTATE.EL = 0w)``
        orelse tm = ``(s.exception = NoException)`` orelse tm = ``¬s.SCTLR_EL1.SA0``
      then false
      else true
 ) (strip_conj tm))
 in if other = [] then ``T`` else list_mk_conj other end;


fun generate_sim_goal thms =
    let val thms_norm = List.map normalize_thm thms;
        val goal = `` (sim_invariant s env) /\
                      (NextStateARM8 s = SOME s1)
                   ``;
       val cnd_PC = List.foldl (fn (thm,cnd) => ``^cnd \/ ^(get_term_from_ass_path ``s.PC = v`` thm)``) ``F`` thms_norm;
       val cnd_PC = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) [] cnd_PC);
       val goal = ``^goal /\ ^cnd_PC``;
       val goal = List.foldl (fn (thm,cnd) =>
              ``^cnd /\ ^(extract_code thm) /\ ^(extract_mem_cnd (extract_side_cond thm))``) goal thms_norm;
       val side_end_cond = List.foldl (fn (thm,cnd) =>
              ``^cnd /\ ^(extract_mem_cnd (extract_side_cond thm))``) ``T`` thms_norm;
      val side_end_cond_1 = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) []   ``(\s.^side_end_cond) s1``);
      val goal = ``^goal ==>
           ?k. (
           (bil_exec_step_n
                 <|pco := SOME <|label := Address (Reg64 s.PC); index := 0|>;
                   pi := prog; environ := env; termcode := Unknown; debug := d1;
                   execs := e1|> k =
               bs1) ==>
           (((sim_invariant s1 bs1.environ) /\ ^side_end_cond_1)
            \/ (bs1.pco = NONE))
           )``;
   in goal end;
  


(* missing *)
(* sim_invariant_def *)
(* does_match *)
(* align_conversion_thm *)
(* Do we really nead to solve the aligned or we can generate the assertion? *)

fun PROVE_SIM_TAC i =
        fn (asl,goal) => (
        let val thm = (List.nth(thms_norm, i)) in
            (FULL_SIMP_TAC (srw_ss()) [])
            THEN (EXISTS_TAC (
                 List.nth((snd o strip_comb o fst o dest_eq)
                          (get_term_from_ass_path ``a = bs1:stepstate`` thm),
                          1)
            ))
            THEN (SUBGOAL_THEN (extract_other_cnd (extract_side_cond thm))
                 (fn thm => ASSUME_TAC thm))
            THENL [(REV_FULL_SIMP_TAC (srw_ss()) [sim_invariant_def])
                 THEN (RW_TAC (srw_ss()) [])
                 (* this is a copy paste *)
                 THEN (fn (asl,g) =>
                   if (does_match g ``Aligned(x,y)``) then
                        ((REPEAT (PAT_ASSUM ``Aligned(x,y)`` (fn thm=> (ASSUME_TAC thm) THEN (UNDISCH_TAC (concl thm)))))
                         THEN (REWRITE_TAC [align_conversion_thm])
                         THEN (blastLib.BBLAST_TAC))
                         (asl,g)
                   else (ALL_TAC)(asl,g)
                 ),
                 ALL_TAC
            ]
            THEN (REPEAT DISCH_TAC)
            THEN (ASSUME_TAC thm)
            THEN (REV_FULL_SIMP_TAC (srw_ss()) [sim_invariant_def])
            (* memory part *)
            THEN (fn (asl,goal)  => (
              let val mem_cnds = (strip_conj o fst o dest_disj) goal;
                  val addrs = List.map (fn tm => ((fn x => List.nth(x,1)) o snd o strip_comb o fst o dest_eq) tm) mem_cnds;
              in  
                  MAP_EVERY (fn tm => PAT_ASSUM ``!a:word64.(p==>q)`` (fn thm =>
                      ASSUME_TAC (SPEC tm thm)
                      THEN (ASSUME_TAC ((blastLib.BBLAST_PROVE o fst o dest_imp o concl o (SPEC tm)) thm))
                      THEN (ASSUME_TAC thm)
                  )) addrs
              end
            )(asl,goal))
            THEN (FULL_SIMP_TAC (srw_ss()) [])
         end
         )(asl,goal);


(*    0:   d10103ff        sub     sp, sp, #0x40 *)
val main1 = tc_one_instruction2_by_bin "d10103ff" ``0w:word64`` ``\x.x<+0x100000w:word64``;
(*    4:   f9000fe0        str     x0, [sp,#24] *)
val main2 = tc_one_instruction2_by_bin "f9000fe0" ``4w:word64`` ``\x.x<+0x100000w:word64``;
val main3 = tc_one_instruction2_by_bin "f9000be1" ``8w:word64`` ``\x.x<+0x100000w:word64``;

val thms = [main1, main2, main3];

val goal = generate_sim_goal thms;

prove (``^goal``,
      (REPEAT STRIP_TAC)
      (* One case for each value of the PC *)
      THENL [
          PROVE_SIM_TAC 0,
          PROVE_SIM_TAC 1,
          PROVE_SIM_TAC 2
      ]
);





(*   2c:   7900001f        strh    wzr, [x0] *)
val inst = `MOV X1, #1`;
val code = arm8AssemblerLib.arm8_code `MOV X1, #1`;
val instr = (hd code);
val instr = "d10103ff";
val instr = "f9000fe0";
val instr = "f9000be1";

val pc_value = ``0w:word64``;
(* 2.11 seconds *)
  val fault_wt_mem = ``\x.x<+0x100000w:word64``;
  val (p, certs, [step]) = tc_stmt_arm8_hex instr;
  val (sts, sts_ty) = listSyntax.dest_list p;
  (* manually add the memory fault *)
  val (memory_check_needed, assert_stm, assert_cert) = generate_assert step fault_wt_mem;
  val sts = List.concat [[``Assert ^bexp_wt_assert``], sts];
  val certs = List.concat [[cert_wt_assert], certs];

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


      THEN (ONE_EXEC_ASSERT certs p pc_value 1)

      THEN (ONE_EXEC_MAIN certs p pc_value 2)
      THEN (ONE_EXEC_MAIN certs p pc_value 3)
      THEN (ONE_EXEC_MAIN certs p pc_value 4)
      THEN (ONE_EXEC_MAIN certs p pc_value 5)
      
      THEN (ONE_EXEC_MAIN certs p pc_value 6)
      THEN (ONE_EXEC_MAIN certs p pc_value 7)



val i = 1;
val prog = p;
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Address (Reg64 0w); index := 0|>;
     pi := prog; environ := env; termcode := Unknown; debug := d1;
     execs := e1|> 7 =
 bs1) ⇒
((bs1.environ "" = (NoType,Unknown)) ∧
 (bs1.environ "R0" = (Reg Bit64,Int (Reg64 (s1.REG 0w)))) ∧
 (bs1.environ "R1" = (Reg Bit64,Int (Reg64 (s1.REG 1w)))) ∧
 (bs1.environ "R2" = (Reg Bit64,Int (Reg64 (s1.REG 2w)))) ∧
 (bs1.environ "R3" = (Reg Bit64,Int (Reg64 (s1.REG 3w)))) ∧
 (bs1.environ "R30" = (Reg Bit64,Int (Reg64 (s1.REG 30w)))) ∧
 (bs1.environ "ProcState_C" = (Reg Bit1,Int (bool2b s1.PSTATE.C))) ∧
 (bs1.environ "ProcState_N" = (Reg Bit1,Int (bool2b s1.PSTATE.N))) ∧
 (bs1.environ "ProcState_V" = (Reg Bit1,Int (bool2b s1.PSTATE.V))) ∧
 (bs1.environ "ProcState_Z" = (Reg Bit1,Int (bool2b s1.PSTATE.Z))) ∧
 (bs1.environ "arm8_state_PC" = (Reg Bit64,Int (Reg64 s1.PC))) ∧
 (bs1.environ "arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 s1.SP_EL0))) ∧
 (∃v. bs1.environ "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R2" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R3" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
 (∃v. bs1.environ "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃v. bs1.environ "tmp_arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 v))) ∧
 (∃m.
    (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
    ∀a. m (Reg64 a) = Reg8 (s1.MEM a)) ∧ ¬s1.SCTLR_EL1.E0E ∧
 (s1.PSTATE.EL = 0w) ∧ (s1.exception = NoException) ∧
 Aligned (s1.SP_EL0,8) ∧ ¬s1.SCTLR_EL1.SA0) ∧
(∀a. a <₊ 0x100000w ⇒ (s.MEM a = s1.MEM a)) ∨ (bs1.pco = NONE)
``;
