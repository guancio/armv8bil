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
open mainLib;
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
        orelse tm = ``¬s.TCR_EL1.TBI0`` orelse tm = ``¬s.TCR_EL1.TBI1``
      then false
      else true
 ) (strip_conj tm))
 in if other = [] then ``T`` else list_mk_conj other end;


fun generate_sim_goal thms =
    let val thms_norm = List.map normalize_thm thms;
        val goal = `` (sim_invariant s env pco) /\
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
                 <|pco := pco;
                   pi := prog; environ := env; termcode := Unknown; debug := d1;
                   execs := e1|> k =
               bs1) ==>
           (((sim_invariant s1 bs1.environ bs1.pco) /\ ^side_end_cond_1)
            \/ (bs1.pco = NONE))
           )``;
   in goal end;
  


(* missing *)
(* sim_invariant_def *)
(* does_match *)
(* align_conversion_thm *)
(* Do we really nead to solve the aligned or we can generate the assertion? *)

fun PROVE_SIM_TAC thm =
        fn (asl,goal) => (
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
              let (* val mem_cnds = (strip_conj o fst o dest_disj) goal; *)
                  val mem_cnds = strip_conj goal;
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
         )(asl,goal);




val instructions2 = [
"d10103ff","f9000fe0","f9000be1","f90007e2","b90007e3","b9003bff","14000009"
];
val pcs2 = snd (List.foldl (fn (code, (pc, pcs)) =>
  ((snd o dest_eq o concl o EVAL) ``^pc+4w``, List.concat[pcs, [pc]])
) (``0w:word64``, []) instructions2);
val ops2 = ListPair.zip (instructions2, pcs2);
val ids2 = List.tabulate ((List.length ops2), (fn x=> x));

val instructions = [
"d10103ff","f9000fe0","f9000be1","f90007e2","b90007e3","b9003bff","14000009",
"b9803be0","d37ff800","f94007e1","8b000020","7900001f","b9403be0","11000400",
"b9003be0","b94007e0","531f7801","b9403be0","6b00003f","54fffe8c","b94007e0",
"51000400","b9003fe0","14000043","b9803fe0","d37ff800","f9400fe1","8b000020",
"79400000","53003c00","f90017e0","f9001bff","b94007e0","51000400","b9003be0",
"1400002a","b9803be0","d37ff800","f9400be1","8b000020","79400000","53003c01",
"f94017e0","9b007c20","f9401be1","8b000020","f9001be0","b9403fe1","b9403be0",
"0b000020","93407c00","91000400","d37ff800","f94007e1","8b000020","79400000",
"53003c00","f9401be1","8b000020","f9001be0","b9403fe1","b9403be0","0b000020",
"93407c00","91000400","d37ff800","f94007e1","8b000020","f9401be1","53003c21",
"79000001","f9401be0","d350fc00","f9001be0","b9403be0","51000400","b9003be0",
"b9403be0","6b1f001f","54fffaaa","b9803fe0","d37ff800","f94007e1","8b000020",
"f9401be1","53003c21","79000001","b9403fe0","51000400","b9003fe0","b9403fe0",
"6b1f001f","54fff78a","910103ff","d65f03c0"
];
val pcs = snd (List.foldl (fn (code, (pc, pcs)) =>
  ((snd o dest_eq o concl o EVAL) ``^pc+4w``, List.concat[pcs, [pc]])
) (``0w:word64``, []) instructions);
val ops = ListPair.zip (instructions, pcs);
val ids = List.tabulate ((List.length ops), (fn x=> x));

print "*****START*************\n*****START*************\n*****START*************\n";
List.foldl (fn (id, x) =>
  let val _ = print "******************************\n"
      val (code, pc) = (List.nth(ops, id))
      val _ = print (String.concat ["Lifting instruction: ", code, "\n"])
  in
    (let val thms = [tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``];
         val thm = List.hd thms;
         val goal = generate_sim_goal thms;
         val thm1 = prove (``^goal``,
               (REPEAT STRIP_TAC)
               (* One case for each value of the PC *)
               THEN (PROVE_SIM_TAC thm)
               );
     in (* print_thm thm1 ; *) print "\n" end
     handle _ => print "-------FAILURE-------\n");
     1
  end
) 1 ids;


val instructions = [
"d10103ff","f9000fe0","f9000be1","f90007e2","b90007e3","b9003bff","14000009"
];
val pcs = snd (List.foldl (fn (code, (pc, pcs)) =>
  ((snd o dest_eq o concl o EVAL) ``^pc+4w``, List.concat[pcs, [pc]])
) (``0w:word64``, []) instructions);
val ops = ListPair.zip (instructions, pcs);
val thm = lift_program(ops);

val id = 1;
val id = 28;
val id = 70;
val id = 19;
val id = 0;
val id = (List.length ops)-1;
val x = 1;
val (instr, pc_value) = (List.nth(ops, id));
val thms = [tc_one_instruction2_by_bin (fst (List.nth(ops, id))) (snd (List.nth(ops, id))) ``\x.x<+0x100000w:word64``];

val thm = List.hd thms;
val goal = generate_sim_goal thms;
prove (``^goal``,
      (REPEAT STRIP_TAC)
      (* One case for each value of the PC *)
      THEN (PROVE_SIM_TAC thm)
);





val curr_ops = ops;
print "*****START*************\n*****START*************\n*****START*************\n";
val thms = List.map (fn (code, pc) => tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``) curr_ops;
val goal = generate_sim_goal thms;
val thm1 = prove (``^goal``,
      (REPEAT STRIP_TAC)
      (* One case for each value of the PC *)
      THENL (List.map PROVE_SIM_TAC thms)
);
print_thm thm1;








(*   2c:   7900001f        strh    wzr, [x0] *)
val inst = `MOV X1, #1`;
val code = arm8AssemblerLib.arm8_code `MOV X1, #1`;
val instr = (hd code);
val instr = "d65f03c0";

val pc_value = ``376w:word64``;
(* 2.11 seconds *)
  val fault_wt_mem = ``\x.x<+0x100000w:word64``;
val (p, certs, [step]) = tc_stmt_arm8_hex instr;
  val (sts, sts_ty) = listSyntax.dest_list p;
  (* manually add the memory fault *)
  val (memory_check_needed, assert_stm, assert_cert) = generate_assert step fault_wt_mem;
  val sts = List.concat [assert_stm, sts];
  val certs = List.concat [assert_cert, certs];
  (* other conditions: like memory alignment *)
  val side_cnd = extract_other_cnd_from_step step;
  val (side_check_needed, assert_stm1, assert_cert1) = generate_assert_side side_cnd;
  val sts = List.concat [assert_stm1, sts];
  val certs = List.concat [assert_cert1, certs];
  (* manually add the final jump *)
  val s1 = (optionSyntax.dest_some o snd o dest_eq o concl) step;
  val new_pc_val = (snd o dest_eq o concl o EVAL) ``^s1.PC``;
  (* as usual this can be unchanged *)
  val new_pc_val1 = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [ASSUME ``s.PC = ^pc_value``])) new_pc_val
                    handle _ => new_pc_val;
  val (sts, certs) = if wordsSyntax.is_word_literal new_pc_val1 then
                        let val (b_v1, _, t_v1) = tc_exp_arm8 new_pc_val1
                        in
                          (List.concat [sts, [``Jmp (Const (Reg64 (^new_pc_val1)))``]],
                           List.concat [certs, [t_v1]]) end
                     else if is_cond new_pc_val1 then
                        let val (c,v1,v2) = dest_cond new_pc_val1
                            val (b_c, _, t_c) = tc_exp_arm8 c
                            val (b_v1, _, t_v1) = tc_exp_arm8 v1
                            val (b_v2, _, t_v2) = tc_exp_arm8 v2
                            val ncerts = LIST_CONJ(List.map (UNDISCH_ALL o SPEC_ALL) [t_c, t_v1, t_v2]);
                            val ncerts = ((GEN ``env:environment``) o (GEN ``s:arm8_state``) o DISCH_ALL) ncerts;
                         in (List.concat [sts, [``CJmp ^b_c ^b_v1 ^b_v2``]],
                             List.concat [certs, [ncerts]]) end
                     else
                        let val (b_v1, _, t_v1) = tc_exp_arm8 new_pc_val1
                            val b_v1 = ((snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [r2s_def])) b_v1)
                             handle _ => b_v1;
                            val t_v1 = SIMP_RULE (srw_ss()) [r2s_def] t_v1;
                            in (List.concat [sts, [``Jmp ^b_v1``]],
                              List.concat [certs, [t_v1]]) end
  (* standard section *)
  val p = listSyntax.mk_list(sts,sts_ty);
	val goal = tc_gen_goal p certs step pc_value fault_wt_mem;
	val thm = prove(``^goal``,
      (REWRITE_TAC [sim_invariant_def])
			THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction, plus 1 since the fixed jump has no certificate *)
			THEN (MAP_EVERY (ONE_EXEC_MAIN certs p pc_value) (List.tabulate (List.length certs, fn x => x+1)))
			(* Computation completed *)
			THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
			THEN DISCH_TAC
      (* Prove that every assumption of the step theorem is met *)
      THEN (MAP_EVERY (fn tm =>
              (SUBGOAL_THEN tm ASSUME_TAC)
              THENL [
                (FULL_SIMP_TAC (srw_ss()) [align_conversion_thm, markerTheory.Abbrev_def]),
                (* foced to do a full simp_tac due to the next simplification *)
                (FULL_SIMP_TAC (myss) [])
              ]
            )
            (get_side_step_cnd (hyp step)))
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


      THEN (ONE_EXEC_MAIN certs p pc_value 1)
      THEN (ONE_EXEC_MAIN certs p pc_value 2)
      THEN (ONE_EXEC_MAIN certs p pc_value 3)
      THEN (ONE_EXEC_MAIN certs p pc_value 4)
      THEN (ONE_EXEC_MAIN certs p pc_value 5)
      
      THEN (ONE_EXEC_MAIN certs p pc_value 6)
      THEN (ONE_EXEC_MAIN certs p pc_value 7)


val [th] = arm8thl;


val i = 4;
val prog = p;
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Address (Reg64 376w); index := 3|>;
     pi := prog;
     environ :=
       (λc.
          if "arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 (s.REG 30w)))
          else if "tmp_R30" = c then (Reg Bit64,Int (Reg64 (s.REG 30w)))
          else if "tmp_arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 376w))
          else env c); termcode := Unknown; debug := d1;
     execs := e1 + 1 + 1 + 1|> 1 =
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
 ¬s1.SCTLR_EL1.SA0 ∧ ¬s1.TCR_EL1.TBI0 ∧ ¬s1.TCR_EL1.TBI1 ∧
 (bs1.pco = SOME <|label := Address (Reg64 s1.PC); index := 0|>)) ∧
(∀a. a <₊ 0x100000w ⇒ (s.MEM a = s1.MEM a)) ∨ (bs1.pco = NONE)
``;









******************************
Lifting instruction: 54fffe8c
-------FAILURE-------


******************************
Lifting instruction: 79400000
-------FAILURE-------

******************************
Lifting instruction: 79000001
failed.
-------FAILURE-------

******************************
Lifting instruction: d65f03c0
-------FAILURE-------
