val mainPath = "../bilmodel";

(* Load path *)
loadPath := mainPath :: !loadPath;

HOL_Interactive.toggle_quietdec();
open bilTheory;
HOL_Interactive.toggle_quietdec();





(* evaluate with a free environment e *)
val a = ``bil_eval_exp (Plus (Const (Reg8 0x1w)) (Const ((Reg8 0x1w)))) e``;
EVAL a;


val b = ``bil_eval_exp (Plus (Den "x") (Const (Reg32 1w))) (("x" =+ (Reg Bit32,Int (Reg32 8w))) (λv. (NoType,Unknown)))``;
EVAL b;




(* simple program declaring, assining and incrementing a value *)
val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "x" (Reg Bit32));
      Assign "x" (Const (Reg32 8w));
      Assign "x" (Plus (Den "x") (Const (Reg32 1w)))
    ]
    |>;
 b
]:program
``;
val state = ``<|
  pco:= SOME <| label:= (Label "main"); index:= 0 |>;
  environ:= (\v. (NoType,Unknown)) ;
  termcode:= Unknown ;
  debug:=d1;
  execs:=e1;
  pi:=^x
|>``;

val state1 = EVAL ``bil_exec_step (bil_exec_step ^state)``;
val state2 = EVAL ``bil_exec_step ^(snd(dest_eq(concl(state1))))``;








(*
val goal = ``!st'. st' ==> T``;
prove(goal, (FULL_SIMP_TAC (srw_ss()) []));
*)

val xsmallten_def = Define `xsmallten st = !v. (st.environ "x" = (Reg Bit32, Int (Reg32 v))) ==> (v < 10w)` (* ((Reg Bit1) ≠ t) /\  *)
val xgreatzer_def = Define `xgreatzer st = !v. (st.environ "x" = (Reg Bit32, Int (Reg32 v))) ==> (v >  0w)`

val goal = ``
!st.
  (st.pi = ^x)
  /\
  (st.pco = SOME <| label:= (Label "main"); index:= 2 |>)
  /\
  (st.termcode = Unknown)
  /\
  (xsmallten st)
  ==>
  !st'.
    (st' = bil_exec_step st)
    ==>
    (xgreatzer st')
``;


(*
!e x y z rt.
  (?x_1 x_2 y_ z_.
    (bil_eval_exp x e = Mem x_1 x_2)	/\
    (bil_eval_exp y e = Int y_)		/\
    (bil_regtype_int_inf y_ = x_1)	/\
    (bil_eval_exp z e = Int z_)	    	/\
    (bil_sizeof_reg rt ≠ Int 0c)
  )
  ==>
  (?v_. (bil_eval_exp (Load x y z rt) e = Int v_))
``;
*)

prove(``^goal``,
	(REPEAT GEN_TAC)
	THEN (FULL_SIMP_TAC (srw_ss()) [xsmallten_def])
	THEN (REPEAT DISCH_TAC)
	THEN (FULL_SIMP_TAC (srw_ss()) [xgreatzer_def, bil_exec_step_def])
	THEN (REPEAT GEN_TAC)



	THEN (FULL_SIMP_TAC (srw_ss()) [bil_get_program_block_info_by_label_def, listTheory.INDEX_FIND_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [LET_DEF, bil_exec_stmt_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [bil_eval_exp_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [bil_env_read_def])
	THEN (Cases_on `st.environ "x"`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	
	THEN (Cases_on `r`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	THEN (FULL_SIMP_TAC (srw_ss()) [is_env_regular_def, set_env_irregular_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])

	THEN (FULL_SIMP_TAC (srw_ss()) [bil_type_int_inf_def])


	THEN (Cases_on `b' + Reg32 1w`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])

	ALL_TAC
	(Cases_on `q = Reg Bit1`)


	THEN (FULL_SIMP_TAC (srw_ss()) [is_env_regular_def])

	THEN (Cases_on `st.environ "x"`)
	THEN (FULL_SIMP_TAC (srw_ss()) [bil_eval_exp_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [bil_env_read_def])

	THEN (Cases_on `r`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	THEN (FULL_SIMP_TAC (srw_ss()) [set_env_irregular_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [LET_DEF])
	THEN (FULL_SIMP_TAC (srw_ss()) [bil_type_int_inf_def])

	THEN (Cases_on `b' + Reg32 1w`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])


	THENL [
	  ALL_TAC,
	  
	  ALL_TAC THEN (Cases_on `q = Reg Bit32`) THEN (FULL_SIMP_TAC (srw_ss()) [])
	  
	  ,
	  
	  ALL_TAC,
	  ALL_TAC,
	  (Cases_on `q = Reg Bit1`)
	    THEN (FULL_SIMP_TAC (srw_ss()) [])
	    THENL [
	      ALL_TAC,
	      (Cases_on `st.environ "" ≠ (NoType,Unknown)`)
	        THEN (FULL_SIMP_TAC (srw_ss()) [])
		THEN (METIS_TAC [])
	    ]
	]
	
(* /// *)
	THEN (Cases_on `q = Reg Bit1`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
(* /// *)
	THEN (Cases_on `st.environ "" ≠ (NoType,Unknown)`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
(* /// *)
	THEN (METIS_TAC [])







	THEN (Q.ABBREV_TAC `tau = Reg Bit1 ≠ t ∧ (Reg Bit1 = t) /\ (b' = Reg32 v)`)

	THEN (`~tau` by ALL_TAC)
	THENL [
	   (FULL_SIMP_TAC (srw_ss()) [Abbr `tau`])
	   THEN (Cases_on `(Reg Bit1 = t)`)
	   THENL [
	     (FULL_SIMP_TAC (srw_ss()) []),
	     (FULL_SIMP_TAC (srw_ss()) [])
	   ],
	   ALL_TAC]


	THEN (`~tau` by ALL_TAC)
	THENL [
	   (FULL_SIMP_TAC (srw_ss()) [Abbr `tau`])
	   THEN (Cases_on `(Reg Bit1 = t)`)
	   THENL [
	     ALL_TAC,
	     (FULL_SIMP_TAC (srw_ss()) [])
	   ],
	   ALL_TAC]


	THEN (`~tau` by ALL_TAC)
	THENL [
	      ALL_TAC,
	      (FULL_SIMP_TAC (srw_ss()) [])
	]
	THEN (FULL_SIMP_TAC (srw_ss()) [Abbr `tau`])
	THEN (Cases_on `(Reg Bit1 = t)`)
	THENL [
	     (FULL_SIMP_TAC (srw_ss()) []),
	     (FULL_SIMP_TAC (srw_ss()) [])
	]


	THEN (Cases_on `(Reg Bit1 = t)`)
	THENL [
	     (FULL_SIMP_TAC (srw_ss()) []),
	     (FULL_SIMP_TAC (srw_ss()) [])
	]


	THEN (METIS_TAC [])




	THEN (`Reg Bit1 ≠ t ∧ (Reg Bit1 = t) ∧ (b' = Reg32 v) = (b' = Reg32 v) /\ Reg Bit1 ≠ t ∧ (Reg Bit1 = t)` by
	     (METIS_TAC []))
        THEN (FULL_SIMP_TAC (pure_ss) [])
        THEN (FULL_SIMP_TAC (srw_ss()) [])
		

        THEN (REWRITE_TAC [
	  prove(``Reg Bit1 ≠ t ∧ (Reg Bit1 = t) ∧ (b' = Reg32 v) = (b' = Reg32 v) /\ Reg Bit1 ≠ t ∧ (Reg Bit1 = t)``,
	     (METIS_TAC []))
	])
	THEN (RW_TAC (srw_ss()) [])
		

	THEN (`~tau` by (FULL_SIMP_TAC (srw_ss()) [Abbr `tau`]))
	THEN (FULL_SIMP_TAC (srw_ss()) [Abbr `tau`])


---?

	THEN (Cases_on `t = Reg Bit1`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])

(RW_TAC arith_ss [])


---?

	THEN (REPEAT DISCH_TAC)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
---?
	THEN (FULL_SIMP_TAC (bool_ss) [])


	THEN (Cases_on `st.environ "x"`)
	THEN (Cases_on `q`)
	THEN (Cases_on `st.environ "x"`)
);




(*

	(REPEAT GEN_TAC)
	THEN (REPEAT DISCH_TAC)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
	THEN (FULL_SIMP_TAC (srw_ss()) [LET_DEF])

	THEN (Cases_on `rt`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])

	THEN (Cases_on `z_ = 0b`)
	THEN (FULL_SIMP_TAC (srw_ss()) [])
);
*)

