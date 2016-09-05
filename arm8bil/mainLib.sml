structure mainLib :> mainLib =
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
open arm8bilInstructionLib;

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



fun lift_program curr_ops =
    let val thms = List.map (fn (code, pc) => tc_one_instruction2_by_bin code pc ``\x.x<+0x100000w:word64``) curr_ops;
        val goal = generate_sim_goal thms;
        val thm1 = prove (``^goal``,
              (REPEAT STRIP_TAC)
              (* One case for each value of the PC *)
              THENL (List.map PROVE_SIM_TAC thms)
        )
    in
      thm1
    end;

end