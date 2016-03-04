(* ========================================================================= *)
(* FILE          : arm8bilLib.sml                                            *)
(* DESCRIPTION   : A transcompiler from ARMv8 model to BIL model.            *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

structure arm8bilLib :> arm8bilLib =
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

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Exceptions                                                               *)
(* ------------------------------------------------------------------------- *)
exception NotABoolException;
exception NotANumberException;
exception NotAWordException;
exception UnsupportedWordSizeException;
exception UnsupportedARM8ExpressionException of term;
exception ArgumentException of string;
exception UnsupportedARM8StateField of string;

(* ------------------------------------------------------------------------- *)
(*  Misc tools                                                               *)
(* ------------------------------------------------------------------------- *)

(* Just generalize/specialize the environment *)
val SPEC_ENV = SPEC ``env:environment``;
val GEN_ENV = GEN ``env:environment``;

(* Modus Ponens for binary expressions *)
fun MP_UN      thImp (be1, ae1, thm1) = 
  MP (((SPECL [ae1, be1]) o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1)
;

fun MP_NUM_UN  thImp (be1, ae1, thm1) = 
  MP ((UNDISCH o (SPECL [ae1, be1]) o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1)
;

fun MP_BIN     thImp (be1, ae1, thm1) (be2, ae2, thm2) = 
  MP_CONJ ((SPECL [ae1, ae2, be1, be2] o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2)
;

fun MP_NUM_BIN thImp (be1, ae1, thm1) (be2, ae2, thm2) =
  MP_CONJ ((UNDISCH o UNDISCH o (SPECL [ae1, ae2, be1, be2]) o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2)
;

fun MP_ITE thImp (be1, ae1, thm1) (be2, ae2, thm2) (be3, ae3, thm3) = 
  MP_CONJL (((SPECL [ae1, ae2, ae3, be1, be2, be3]) o SPEC_ENV) thImp) (List.rev [(UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2, (UNDISCH_ALL o SPEC_ALL) thm3])
;

fun MP_NUM_ITE thImp (be1, ae1, thm1) (be2, ae2, thm2) (be3, ae3, thm3) = 
  MP_CONJL ((UNDISCH o UNDISCH o (SPECL [ae1, ae2, ae3, be1, be2, be3]) o SPEC_ENV) thImp) (List.rev [(UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2, (UNDISCH_ALL o SPEC_ALL) thm3])
;

(* This version needs to proove something... this is not good... *)
fun MP_NUM_BIN_OLD thImp (be1, ae1, thm1) (be2, ae2, thm2) =
  let
    val thm1_open  = (concl o UNDISCH_ALL o SPEC_ALL) thm1;
    val thm2_open  = (concl o UNDISCH_ALL o SPEC_ALL) thm2;
    val (c11, c12) = if (boolSyntax.is_imp thm1_open) then (dest_imp thm1_open) else (``^ae1 < dimword (:64)``, thm1_open);
    val (c21, c22) = if (boolSyntax.is_imp thm2_open) then (dest_imp thm2_open) else (``^ae2 < dimword (:64)``, thm2_open);
    val cl = List.concat [
      (CONJUNCTS o UNDISCH_ALL o SPEC_ALL) (tryprove(``^c11 ∧ ^c12``, EVAL_TAC)),
      (CONJUNCTS o UNDISCH_ALL o SPEC_ALL) (tryprove(``^c21 ∧ ^c22``, EVAL_TAC))
    ];
  in
    MP_CONJL ((SPECL [ae1, ae2, be1, be2] o SPEC_ENV) thImp) (List.rev cl)
  end
;

(* ------------------------------------------------------------------------- *)
(*  Type and size utils                                                      *)
(* ------------------------------------------------------------------------- *)
(* Register constructors and corresponding sizes *)
val constructor_size_pairs = [
      (``Reg1  ``, 1 )
    , (``Reg8  ``, 8 )
    , (``Reg16 ``, 16)
    , (``Reg32 ``, 32)
    , (``Reg64 ``, 64)
  ];


val word_size = fn t =>
  if (wordsSyntax.is_word_type (type_of t))
    then
      let
        val nt = eval ``word_len ^t``
      in
              if (nt =  ``1:num``)                 then  1
        else  if (nt =  ``8:num``)                 then  8
        else  if (nt = ``16:num``)                 then  16
        else  if (nt = ``32:num``)                 then  32
        else  if (nt = ``64:num``)                 then  64
        else  if (numSyntax.is_numeral nt = false) then  (say "Working with generic words!?";0)
        else  raise UnsupportedWordSizeException
      end
    else raise NotAWordException
;

val word_type_size = fn t =>
  if (wordsSyntax.is_word_type t)
    then word_size (wordsSyntax.mk_n2w (``0:num``, t))
    else raise ArgumentException("Not a word type")
;

val get_alphatype = fn ty =>
  if (wordsSyntax.is_word_type ty)
    then List.nth (snd(dest_type ty), 1)
    else raise NotAWordException
;

val word_length = fn t =>
  if (wordsSyntax.is_word_type (type_of t))
    then
      let
        val l = eval ``word_len ^t``;
      in
        if (numSyntax.is_numeral l)
          then  numSyntax.int_of_term l
          else  raise UnsupportedWordSizeException
      end
    else raise NotAWordException
;

(* ------------------------------------------------------------------------- *)
(*  Expression tests                                                         *)
(* ------------------------------------------------------------------------- *)
fun is_arm8_app t cmp =
  let
    val dummystate = ``ds:arm8_state``;
    val godeep = fn t => (snd o dest_comb) t;
    val subst1 = fn t => subst [godeep t |-> dummystate] t;
    val subst2 = fn t => (subst [(godeep o fst o dest_comb) t |-> dummystate] o fst o dest_comb) t;
    val subst3 = fn t => (subst [(godeep o godeep) t |-> dummystate]) t;
  in
            (is_comb t)
    andalso (
                  (subst1 t = subst1 cmp)
      handle _ => (subst2 t = subst1 cmp)
      handle _ => (subst3 t = subst3 cmp)
      handle _ => false
    )
  end
;
val is_bool = fn t => (type_of t) = ``:bool``;
val is_num  = fn t => (type_of t) = ``:num``;
val is_reg  = fn t => is_arm8_app t ``s.REG``;
val is_mem  = fn t => is_arm8_app t ``s.MEM``;
val is_boolean  = fn t => (t = ``T``) orelse (t = ``F``);
val is_eq_bool = fn t => (is_comb t) andalso (boolSyntax.is_eq t) andalso (List.nth ((snd o dest_type o type_of o fst o strip_comb) t, 0)) = ``:bool``;
val is_eq_num  = fn t => (is_comb t) andalso (boolSyntax.is_eq t) andalso (List.nth ((snd o dest_type o type_of o fst o strip_comb) t, 0)) = ``:num``;
val is_cond_num  = fn t => (is_cond t) andalso ((is_num  o trd3 o dest_cond) t);
val is_cond_bool = fn t => (is_cond t) andalso ((is_bool o trd3 o dest_cond) t);

val is_neq = fn t => if (boolSyntax.is_neg t)
  then
    boolSyntax.is_eq (List.nth ((snd o strip_comb) t, 0))
  else
    false
;

val is_word_eq = fn t => if (boolSyntax.is_eq t)
  then
    let
      val types = (snd o dest_type o type_of o fst o strip_comb) t
    in
      if (List.length types > 0)
        then
          wordsSyntax.is_word_type (List.nth(types, 0))
        else
          false
    end
  else
    false
;

val is_word_neq = fn t => if (boolSyntax.is_neg t)
  then
    is_word_eq (List.nth ((snd o strip_comb) t, 0))
  else
    false
;

(*
  This function is used to detect carry bit (substructure).
  The main problem of this typical arm8 expression to compute the carry bit
  is that in BIL we cannot handle more than 64 bits, but this expression
  uses exactly 2**64, the smallest unrepresentable-in-BIL natural number.
*)
val is_plus_lt_2exp64 = fn t =>
  if (numSyntax.is_less t)
  then
    let
      val tplus = (List.nth ((snd o strip_comb) t, 0));
      val t2exp = (List.nth ((snd o strip_comb) t, 1));
    in
      (numSyntax.is_plus tplus) andalso ((eval t2exp) = (eval ``(2:num) ** 64``))
    end
  else
    false
;

(*
  Another annoying structure found through the armv8 expressions
  is the MOD 2**64
*)
val is_plus_mod_2exp64 = fn t =>
  if (numSyntax.is_mod t)
  then
    let
      val tplus = (List.nth ((snd o strip_comb) t, 0));
      val t2exp = (List.nth ((snd o strip_comb) t, 1));
    in
      (numSyntax.is_plus tplus) andalso ((eval t2exp) = (eval ``(2:num) ** 64``))
    end
  else
    false
;


(*
  WARNING: NOT SUPPORTED FIELDS
  
  ("MEM",ATy(F64,F8))
  ("branch_hint",OTy(CTy"BranchType"))
  ("exception",CTy"exception")])
*)
val arm8_supported_den = fn a8s => [
      ``^(a8s).PC
      
  ``, ``^(a8s).PSTATE.C
  ``, ``^(a8s).PSTATE.EL
  ``, ``^(a8s).PSTATE.N
  ``, ``^(a8s).PSTATE.SPS
  ``, ``^(a8s).PSTATE.V
  ``, ``^(a8s).PSTATE.Z
      
  ``, ``^(a8s).SP_EL0
  ``, ``^(a8s).SP_EL1
  ``, ``^(a8s).SP_EL2
  ``, ``^(a8s).SP_EL3
      
  ``(*, ``^(a8s).TCR_EL1.TBI0
  ``, ``^(a8s).TCR_EL1.TBI1
  ``, ``^(a8s).TCR_EL1.tcr_el1'rst
      
  ``, ``^(a8s).TCR_EL2.TBI
  ``, ``^(a8s).TCR_EL2.tcr_el2_el3'rst
      
  ``, ``^(a8s).TCR_EL3.TBI
  ``, ``^(a8s).TCR_EL3.tcr_el2_el3'rst
      
  ``, ``^(a8s).SCTLR_EL1.A
  ``, ``^(a8s).SCTLR_EL1.E0E
  ``, ``^(a8s).SCTLR_EL1.EE
  ``, ``^(a8s).SCTLR_EL1.SA
  ``, ``^(a8s).SCTLR_EL1.SA0
  ``, ``^(a8s).SCTLR_EL1.sctlrtype'rst
      
  ``, ``^(a8s).SCTLR_EL2.A
  ``, ``^(a8s).SCTLR_EL2.E0E
  ``, ``^(a8s).SCTLR_EL2.EE
  ``, ``^(a8s).SCTLR_EL2.SA
  ``, ``^(a8s).SCTLR_EL2.SA0
  ``, ``^(a8s).SCTLR_EL2.sctlrtype'rst
      
  ``, ``^(a8s).SCTLR_EL3.A
  ``, ``^(a8s).SCTLR_EL3.E0E
  ``, ``^(a8s).SCTLR_EL3.EE
  ``, ``^(a8s).SCTLR_EL3.SA
  ``, ``^(a8s).SCTLR_EL3.SA0
  ``, ``^(a8s).SCTLR_EL3.sctlrtype'rst
  
  `` *)
];

val is_arm8_den = fn t =>
  let
    val dummystate = ``ds:arm8_state``;
    val godeep = fn t => (snd o dest_comb) t;
    val subst1 = fn t => subst [godeep t |-> dummystate] t;
    val subst2 = fn t => subst [(godeep o godeep) t |-> dummystate] t;
    val st     = fn t => (subst1 t) handle _ => (subst2 t) handle _ => t;
  in
    (List.length o List.filter (fn x => x = st t) o map (fn x => st x)) (arm8_supported_den dummystate) = 1
  end
;

(* ------------------------------------------------------------------------- *)
(*  Raw conversion of several types to BIL model expressions                 *)
(* ------------------------------------------------------------------------- *)
val bil_expr_const_bool = fn t =>
  if  t then ``(Const (Reg1 1w))``
        else ``(Const (Reg1 0w))``;

val bil_expr_bool = fn t =>
        if (t = ``T`` orelse t = ``F``) then ``Const (bool2b ^t)``
  else  raise NotABoolException
;

val bil_expr_const = fn t =>
        if  (is_boolean t) then bil_expr_const_bool (t = ``T``)
  else  if  (is_bool    t) then ``Const (bool2b ^t)``
  else
    let
      val s = word_length t;
    in
            if (s  = 1 ) then ``(Const (Reg1  ^t))``
      else  if (s  = 8 ) then ``(Const (Reg8  ^t))``
      else  if (s  = 16) then ``(Const (Reg16 ^t))``
      else  if (s  = 32) then ``(Const (Reg32 ^t))``
      else  if (s  = 64) then ``(Const (Reg64 ^t))``
      else  if (s <= 8 ) then ``(Const (Reg8  (w2w ^t)))``
      else  if (s <= 16) then ``(Const (Reg16 (w2w ^t)))``
      else  if (s <= 32) then ``(Const (Reg32 (w2w ^t)))``
      else  if (s <= 64) then ``(Const (Reg64 (w2w ^t)))``

      else  ``(Const (Reg64 (w2w ^t)))`` (* Encapsulate a generic α word to maximum size (worst choice?) *)
    end
;

val bil_expr_num = fn t =>
  if (numSyntax.is_numeral t)
    then ``Cast (Const (n2b_64 ^t)) Bit64``
    else raise NotANumberException
;

fun bil_a8e2HOLstring_prefix t prefix =
        if (is_reg t) then
          if (prefix = "")
            then  ``r2s ^((snd o dest_comb) t)``
            else  ``APPEND ^(stringSyntax.fromMLstring prefix) (r2s ^((snd o dest_comb) t))``
  else  stringSyntax.fromMLstring (prefix ^ (opname t))
;

val bil_a8e2HOLstring = fn t => bil_a8e2HOLstring_prefix t "";

val bil_a8e2string = fn t =>
        if (is_reg t) then stringSyntax.fromHOLstring (eval ``r2s ^((snd o dest_comb) t)``)
  else  opname t
;

fun bil_a8e_den_prefix t prefix = ``(Den ^(bil_a8e2HOLstring_prefix t prefix))``;
val bil_a8e_den = fn t => ``(Den ^(bil_a8e2HOLstring t))``;

(* ------------------------------------------------------------------------- *)
(*  Conversion of several types to BIL model values                          *)
(* ------------------------------------------------------------------------- *)
fun bil_value_word_encapsulate t ws =
        if (ws  = 0)  then ``(Int (Reg64 (w2w ^t)))`` (* Encapsulate a generic α word to maximum size (worst choice?) *)
  else  if (ws <= 1)  then ``(Int (Reg1  ^t))``
  else  if (ws <= 8)  then ``(Int (Reg8  ^t))``
  else  if (ws <= 16) then ``(Int (Reg16 ^t))``
  else  if (ws <= 32) then ``(Int (Reg32 ^t))``
  else  if (ws <= 64) then ``(Int (Reg64 ^t))``
  else  raise UnsupportedWordSizeException
;

val bil_value_word = fn t => bil_value_word_encapsulate t (word_size t);

val bil_value_bool = fn t =>
  if (is_bool t)
    then ``(Int (bool2b ^t))``
    else  raise NotABoolException
;

val bil_value_num = fn t =>
  if (is_num t)
    then  ``(Int (n2b_64 ^t))``
    else  raise NotANumberException
;

val bil_value_reg = fn t =>
  if (is_reg t)
    then ``Int (Reg64 t)``
    else  raise ArgumentException "Argument is not a register"
;

val bil_value =
      fn t                             => bil_value_bool t
  handle NotABoolException             => bil_value_num  t
  handle NotANumberException           => bil_value_word t
  handle UnsupportedWordSizeException  => bil_value_reg  t
  handle ArgumentException _           => if (wordsSyntax.is_word_type (type_of t))
                                            then ``Int (w2b ^t)``
                                            else raise NotAWordException
;

(* ------------------------------------------------------------------------- *)
(*  Tactics                                                                  *)
(* ------------------------------------------------------------------------- *)
(* TACTICS *)
val BIL_CONST_TAC = (REPEAT GEN_TAC) THEN EVAL_TAC;
val BIL_OP_FULL_SIMP_TAC = (FULL_SIMP_TAC (srw_ss()) [
      bil_add_def
    , bil_sub_def
    , bil_mul_def
    , bil_div_def
    , bil_sdiv_def
    , bil_mod_def
    , bil_smod_def
    , bil_lsl_def
    , bil_lsr_def
    , bil_asr_def
    , bil_and_def
    , bil_or_def
    , bil_xor_def
    , bil_eq_def
    , bil_neq_def
    , bil_lt_def
    , bil_le_def
    , bil_ult_def
    , bil_ule_def
    , bil_cast_def
    , bil_scast_def
    , bil_hcast_def
    , bil_lcast_def
    , n2b_def
    , n2b_1_def
    , n2b_8_def
    , n2b_16_def
    , n2b_32_def
    , n2b_64_def
    , n2bs_def
    , w2b_def
    , w2bs_def
    , bool2b_def
    , r2s_def
    , word_neq_def
    , wordsTheory.n2w_w2n
    , wordsTheory.word_msb_neg
    , arithmeticTheory.GREATER_DEF
    , arithmeticTheory.GREATER_EQ
    , BIT_DIV_MOD
    , SUM_2EXP_EQ
    , GEN_ALL (SIMP_RULE (arith_ss) [] (SPECL [``63:num``, ``n:num``, ``m:num``] PLUS_MOD_2EXP_EQ))
    , n2w_w2w_concat_0
  ]
);
val BIL_EVAL_ONCE_TAC = ((SIMP_TAC (arith_ss) [Once bil_eval_exp_def]) THEN  BIL_OP_FULL_SIMP_TAC);
val BIL_LSB_TAC =
        (FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_lsb, wordsTheory.word_bit_def])
  THEN  (RW_TAC (srw_ss()) [])
  THEN  (
          (SIMP_TAC (srw_ss()) [Ntimes bil_eval_exp_def 2])
    THEN  BIL_OP_FULL_SIMP_TAC
    THEN  (SIMP_TAC (srw_ss()) [Ntimes bil_eval_exp_def 2])
    THEN  EVAL_TAC
    THEN  (FULL_SIMP_TAC (srw_ss()++WORD_BIT_EQ_ss) [])
  )
;
val BIL_OP_BIT_TAC = (
        (RW_TAC (pure_ss) [])
  THEN  (REPEATN (12, BIL_EVAL_ONCE_TAC))
  THEN  (FULL_SIMP_TAC (arith_ss++WORD_ss++WORD_ARITH_ss++WORD_SHIFT_ss++WORD_EXTRACT_ss) [wordsTheory.word_extract_n2w, wordsTheory.word_and_n2w])
  THEN  EVAL_TAC
  THEN  (ASSUME_TAC (SPECL [``63:num``, ``n:num``, ``m:num``] BITS_LT_2EXP))
  THEN  (FULL_SIMP_TAC (srw_ss()) [MODN_MODM])
  THEN  (FULL_SIMP_TAC (arith_ss) [bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def, bitTheory.BITS_def, EXP2_LT_ALT])
);
val BIL_OP_TAC = (
        BIL_OP_FULL_SIMP_TAC
  THEN  (
          (RW_TAC (srw_ss()) [])
    THEN  (SIMP_TAC (arith_ss) [Once bil_eval_exp_def])
    THEN  (RW_TAC (arith_ss) [])
  )
  THEN  (
          (RW_TAC (srw_ss()) [])
    THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
    THEN  BIL_OP_FULL_SIMP_TAC
    THEN  EVAL_TAC
  )
  THEN  (
          (RW_TAC (srw_ss()) [])
    THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
    THEN  BIL_OP_FULL_SIMP_TAC
    THEN  blastLib.BBLAST_TAC
    THEN  EVAL_TAC
    THEN  WORD_DECIDE_TAC
  )
);
val BIL_DEN_TAC = (SRW_TAC [] [Once bil_eval_exp_def, bil_env_read_def, LET_DEF, r2s_def,
			 bil_sizeof_reg_def, n2b_8_def, n2bs_def, bil_regtype_int_inf_def]);
val BIL_NUMERAL_TAC = (
        (SIMP_TAC (srw_ss()) [Ntimes bil_eval_exp_def 2])
  THEN  BIL_OP_FULL_SIMP_TAC
  THEN  (
            (RW_TAC (pure_ss++WORD_ARITH_ss++WORD_SHIFT_ss++WORD_EXTRACT_ss) [])
      THEN  (REPEAT (BIL_OP_FULL_SIMP_TAC THEN WORD_DECIDE_TAC))
  )
);
val BIL_PLUS_LT_2EXP64_TAC = (
        (REPEAT STRIP_TAC)
  THEN  (REPEATN (13, BIL_EVAL_ONCE_TAC))
  THEN  EVAL_TAC
  THEN  ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS, DIV_PRODMOD_LT_2EXP]))
  THEN  (FULL_SIMP_TAC (pure_ss) [prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC), SPECL [``63:num``, ``n:num``, ``m:num``] SUM_2EXP_EQ])
  THEN  (ASSUME_TAC ((UNDISCH_ALL o CONJ_IMP o (SPECL [``63:num``, ``n:num``, ``m:num``])) DIV_PRODMOD_LT_2EXP))
  THEN  ((FULL_SIMP_TAC (arith_ss) []))
);
val BIL_PLUS_MOD_2EXP64_TAC = (
        (REPEAT STRIP_TAC)
  THEN  (FULL_SIMP_TAC (arith_ss) [])
  THEN  (REPEATN (21, BIL_EVAL_ONCE_TAC))
  THEN  EVAL_TAC
  THEN  (FULL_SIMP_TAC (arith_ss) [MODN_MODM])
  THEN  ((Cases_on `EVEN n`)
    THEN  ((Cases_on `EVEN m`)
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, ODD_MOD2, GSYM arithmeticTheory.ODD_EVEN, Once (GSYM arithmeticTheory.MOD_PLUS)])
      THEN  EVAL_TAC
      THEN  (ASSUME_TAC ((CONJUNCT1 o UNDISCH_ALL o CONJ_IMP o SIMP_RULE (arith_ss) [] o SPECL [``63:num``, ``n:num``, ``m:num``]) RIGHT_SHIFT_SUM_LT_2EXP))
      THEN  (ASSUME_TAC ((CONJUNCT2 o UNDISCH_ALL o CONJ_IMP o SIMP_RULE (arith_ss) [] o SPECL [``63:num``, ``n:num``, ``m:num``]) RIGHT_SHIFT_SUM_LT_2EXP))
      THEN  (ASSUME_TAC ((SIMP_RULE (srw_ss()) [] o SPECL [``63:num``, ``(m DIV 2 + n DIV 2) MOD 9223372036854775808``]) EXP2_LT_ALT2))
      THEN  (ASSUME_TAC ((SIMP_RULE (srw_ss()) [] o SPECL [``63:num``, ``(m DIV 2 + (n DIV 2 + 1)) MOD 9223372036854775808``]) EXP2_LT_ALT2))
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_MOD])
    )
  )
);


(* ------------------------------------------------------------------------- *)
(*  Theorems - basic conversion theorems                                     *)
(* ------------------------------------------------------------------------- *)
(* Generic prove for variables (they MUST be at least declared in the environment) *)
val arm8_to_bil_den_tm = tryprove(
    ``∀ env d dt dv. (env d = (dt, dv)) ==> (bil_eval_exp (Den d) env = dv)``
  , BIL_DEN_TAC
);

(* Generic prove for bil constants *)
val bil_const_tm = tryprove(
    ``∀ env x. bil_eval_exp (Const x) env = Int x``
  , BIL_CONST_TAC
);

(* Generic prove for numbers and booleans *)
val bil_boolean_tm = tryprove(
    ``∀ env x. (bil_eval_exp (Const (bool2b x)) env = Int (bool2b x))``
  , BIL_CONST_TAC
);

val bil_numeral_expressibility_tm = tryprove(
    ``∀ env n. (n < dimword (:64)) = (bil_eval_exp (Cast (Const (n2b_64 n)) Bit64) env = Int (n2b_64 n))``
  , BIL_NUMERAL_TAC
);

val bil_numeral_tm = (GEN_ALL o (GEN ``n:num``) o fst o EQ_IMP_RULE o UNDISCH_ALL o SPEC_ALL) bil_numeral_expressibility_tm;

(* useless... ? *)
val bil_num_tm = tryprove(
    ``∀ env n. (n < dimword (:64)) ==> ((∃ bn. bil_eval_exp (bn) env = Int (n2b_64 n)))``
  , PROVE_TAC [bil_numeral_expressibility_tm]
);

val bil_plus_lt_2exp64_tm = tryprove(
    ``∀ env n m bn bm. (n < dimword (:64)) ==> ((m < dimword (:64)) ==> ((bil_eval_exp (bn) env = Int (n2b_64 n)) ∧ (bil_eval_exp (bm) env = Int (n2b_64 m)) ==> (bil_eval_exp (
      LessThan  (Plus (Div bn (Const 2x))
                      (Plus (Div bm (Const 2x))
                            (Mult (Mod bn (Const 2x))
                                  (Mod bm (Const 2x))
                            )
                      )
                )
                (Const 9223372036854775808x)
    ) env = Int (bool2b (n + m < 18446744073709551616)))))``
  , BIL_PLUS_LT_2EXP64_TAC
);

val bil_plus_mod_2exp64_tm = tryprove(
    ``∀ env n m bn bm. (n < dimword (:64)) ==> ((m < dimword (:64)) ==> ((bil_eval_exp (bn) env = Int (n2b_64 n)) ∧ (bil_eval_exp (bm) env = Int (n2b_64 m)) ==> (bil_eval_exp (
          Plus  (Mult (Const 2x)
                      (Mod  (Plus (Plus (Div bn (Const 2x))
                                        (Div bm (Const 2x))
                                  )
                                  (Mult (Mod bn (Const 2x))
                                        (Mod bm (Const 2x))
                                  )
                            )
                            (Const 9223372036854775808x)
                      )
                )
                (Xor  (Mod  bn (Const 2x))
                      (Mod  bm (Const 2x))
                )
        ) env = Int (n2b_64 ((n + m) MOD 2**64)))))``
  , BIL_PLUS_MOD_2EXP64_TAC
);

val memory_access_2exp64_tm = tryprove(
    ``∀m env y x by bx .
   ((bil_eval_exp by env = Mem Bit64 m) /\
   (bil_eval_exp bx env = Int (Reg64 x))) ==>
   (!a. (m (Reg64 a)) = (Reg8 (y a))) ==>
   ((bil_eval_exp (Load by bx (Const (Reg1 1w)) Bit8) env) = (Int (Reg8 (y x))))``, (RW_TAC (srw_ss()) [])
      THEN  BIL_DEN_TAC
      THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
);

val mem_dword_2exp64_tm = tryprove(
    ``∀m env y x by bx .
   ((bil_eval_exp by env = Mem Bit64 m) /\
   (bil_eval_exp bx env = Int (Reg64 x))) ==>
   (!a. (m (Reg64 a)) = (Reg8 (y a))) ==>
   ((bil_eval_exp (Load by bx (Const (Reg1 0w)) Bit64) env) = (Int (Reg64 (mem_dword y x))))``,
    (RW_TAC (srw_ss()) [])
      THEN (BIL_DEN_TAC)
      (* the memory access get stuck since we do not know the value of the endianness *)
      THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def, n2b_1_def, n2bs_def])
      (* we first open the cast *)
      THEN (SIMP_TAC (srw_ss()) [bil_cast_def])
      (* We apply the + definition so we can show that the memory accesses yield always a byte *)
      THEN (SIMP_TAC (srw_ss()) [bil_add_def])
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      (* we first open the shift *)
      THEN (SIMP_TAC (srw_ss()) [bil_lsl_def, n2b_64_def, n2bs_def])
      (* we first open the or *)
      THEN (SIMP_TAC (srw_ss()) [bil_or_def])
      THEN (SIMP_TAC (srw_ss()) [mem_dword_def])
      THEN (blastLib.BBLAST_TAC)
);

fun nw n s = wordsSyntax.mk_wordii(n, s);

(* Generic theorems for binary expressions *)
val bil_op_tms =
  let
    val bopTuples = [
          (fn s => (fst o strip_comb) ``word_add    ^(nw 0 s)``, fn s => ``Plus              bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_sub    ^(nw 0 s)``, fn s => ``Minus             bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_mul    ^(nw 0 s)``, fn s => ``Mult              bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_div    ^(nw 0 s)``, fn s => ``Div               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_sdiv   ^(nw 0 s)``, fn s => ``SignedDiv         bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_mod    ^(nw 0 s)``, fn s => ``Mod               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_smod   ^(nw 0 s)``, fn s => ``SignedMod         bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsl_bv ^(nw 0 s)``, fn s => ``LeftShift         bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsr_bv ^(nw 0 s)``, fn s => ``RightShift        bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_asr_bv ^(nw 0 s)``, fn s => ``SignedRightShift  bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_and    ^(nw 0 s)``, fn s => ``And               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_or     ^(nw 0 s)``, fn s => ``Or                bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_xor    ^(nw 0 s)``, fn s => ``Xor               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``$=          ^(nw 0 s)``, fn s => ``Equal             bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``$≠          ^(nw 0 s)``, fn s => ``NotEqual          bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lt     ^(nw 0 s)``, fn s => ``SignedLessThan    bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_le     ^(nw 0 s)``, fn s => ``SignedLessOrEqual bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_ls     ^(nw 0 s)``, fn s => ``LessOrEqual       bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lo     ^(nw 0 s)``, fn s => ``LessThan          bx by``, BIL_OP_TAC)
      ];
    val uopTuples = [
          (fn s => (fst o strip_comb) ``word_2comp  ^(nw 0 s)``, fn s => ``ChangeSign        bx``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_1comp  ^(nw 0 s)``, fn s => ``Not               bx``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``w2n         ^(nw 0 s)``, fn s => ``Cast              bx Bit64``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(w2w ^(nw 0 s)):word64``, fn s => ``Cast bx Bit64``, BIL_OP_TAC)
	, (fn s => (fst o strip_comb) ``(sw2sw ^(nw 0 s)):word64``, fn s => ``SignedCast bx Bit64``, (
	   (RW_TAC (srw_ss()) [])
           THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
	   THEN  (RW_TAC (arith_ss) [])
	   THEN BIL_OP_FULL_SIMP_TAC
	   THEN  blastLib.BBLAST_TAC
	   THEN  EVAL_TAC
	   THEN  WORD_DECIDE_TAC
	  ))
        
        (* Some special operator *)
        , (fn s => (fst o strip_comb) ``word_msb    ^(nw 0 s)``, fn s => ``SignedLessThan bx ^(bil_expr_const (nw 0 s))``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsb    ^(nw 0 s)``, fn s => ``Equal (And bx ^(bil_expr_const (nw 1 s))) ^(bil_expr_const (nw 1 s))``, BIL_LSB_TAC)
      ];
    val bopTuplesBool = [
          (fn s => (fst o strip_comb) ``T ∧ T``, fn s => ``And    bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``T ∨ T``, fn s => ``Or     bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``T = T``, fn s => ``Equal  bx by``, BIL_OP_TAC)
      ];
    val uopTuplesBool = [
          (fn s => (fst o strip_comb) ``~T``, fn s => ``Not bx``, BIL_OP_TAC)
(*         , (fn s => (fst o strip_comb) ``¬T``, fn s => ````, BIL_OP_TAC) *)
      ];
    val bopTuplesNum = [
          (fn s => (fst o strip_comb) ``(n:num)   + m``, fn s => ``Plus      bn bm``, BIL_OP_TAC)
(*         , (fn s => (fst o strip_comb) ``(n:num)   - m``, fn s => ``IfThenElse (SignedLessThan bn bm) (Const 0x) (Minus bn bm)``, BIL_OP_TAC) *)
        , (fn s => (fst o strip_comb) ``(n:num)   * m``, fn s => ``Mult         bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num) DIV m``, fn s => ``Div          bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num) MOD m``, fn s => ``Mod          bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)   = m``, fn s => ``Equal        bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)   < m``, fn s => ``LessThan     bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)  <= m``, fn s => ``LessOrEqual  bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)   > m``, fn s => ``LessThan     bm bn``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)  >= m``, fn s => ``LessOrEqual  bm bn``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``BIT (n:num) m``, fn s => ``Equal (Mod (RightShift bm bn) ^(bil_expr_const (nw 2 s))) ^(bil_expr_const (nw 1 s))``, BIL_OP_BIT_TAC)
      ];
    val uopTuplesNum = [
      ];
    val iteTuple = [
        (fn s => (fst o strip_comb) ``if (c:bool) then ^(nw 0 s) else x``, fn s => ``IfThenElse bc bx by``, BIL_OP_TAC)
      ];
    val iteTupleBool = [
        (fn s => (fst o strip_comb) ``if (c:bool) then T else x``, fn s => ``IfThenElse bc bx by``, BIL_OP_TAC)
      ];
    val iteTupleNum = [
          (fn s => (fst o strip_comb) ``if (c:bool) then (n:num) else (m:num)``, fn s => ``IfThenElse bc bn bm``, BIL_OP_TAC)
      ];
    
    (* cartesian product *)
    fun prod bints opTuples =
      let
        fun prod' lst1 lst2 res =
          case lst1 of
              []          => res
            | (br, s)::l1 => prod' l1 lst2 (List.concat [List.map (fn (f, b, tac) => (f s, b s, tac, br)) lst2, res])
      in
        prod' bints opTuples []
      end;
      
    val goalgenerator_uop = fn (auop, bexp, tac, br) =>
      let
        val auopValue = bil_value ``(^auop x)``
      in
        (
            auop, bexp, tac, br
            , ``∀ env x bx. (bil_eval_exp bx env = Int (^br x)) ==> (bil_eval_exp ^bexp env = ^auopValue)``
        )
      end;
      
    val goalgenerator_bop = fn (abop, bexp, tac, br) =>
      let
        val abopValue = bil_value ``(^abop x y)``
      in
        (
            abop, bexp, tac, br
          , ``∀ env x y bx by. (bil_eval_exp bx env = Int (^br x)) ∧ (bil_eval_exp by env = Int (^br y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
      
    val goalgenerator_bop_bool = fn (abop, bexp, tac, _) =>
      let
        val abopValue = bil_value ``(^abop x y)``
      in
        (
            abop, bexp, tac, ``Reg1``
          , ``∀ env x y bx by. (bil_eval_exp bx env = Int (bool2b x)) ∧ (bil_eval_exp by env = Int (bool2b y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
      
    val goalgenerator_uop_bool = fn (abop, bexp, tac, _) =>
      let
        val abopValue = bil_value ``(^abop x)``
      in
        (
            abop, bexp, tac, ``Reg1``
          , ``∀ env x bx. (bil_eval_exp bx env = Int (bool2b x)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
    val goalgenerator_bop_num = fn (abop, bexp, tac, _) =>
      let
        val aexp = ``(^abop n m)``;
        val abopValue = bil_value aexp;
        val concl = if (is_num  aexp)
          then ``((^aexp) < dimword(:64)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
          else ``(bil_eval_exp ^bexp env = ^abopValue)``;
      in
        (
            abop, bexp, tac, ``Reg64``
          , ``∀ env n m bn bm.  (n < dimword(:64))
                            ==> ((m < dimword(:64))
                            ==> ((bil_eval_exp bn env = Int (n2b_64 n)) ∧ (bil_eval_exp bm env = Int (n2b_64 m))
                            ==> (^concl)
                            ))``
        )
      end;
    val goalgenerator_ite = fn (ite, bexp, tac, br) =>
      let
        val abopValue = bil_value ``(^ite c x y)``
      in
        (
            ite, bexp, tac, br
          , ``∀ env c x y bc bx by. (bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bx env = Int (^br x)) ∧ (bil_eval_exp by env = Int (^br y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
    val goalgenerator_ite_bool = fn (ite, bexp, tac, _) =>
      let
        val abopValue = bil_value ``(^ite c x y)``
      in
        (
            ite, bexp, tac, ``Reg1``
          , ``∀ env c x y bc bx by. (bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bx env = Int (bool2b x)) ∧ (bil_eval_exp by env = Int (bool2b y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
    val goalgenerator_ite_num = fn (ite, bexp, tac, _) =>
      let
        val aexp = ``(^ite c n m)``;
        val abopValue = bil_value aexp;
        val concl = ``(bil_eval_exp ^bexp env = ^abopValue)``;
      in
        (
            ite, bexp, tac, ``Reg64``
          , ``∀ env c n m bc bn bm. (n < dimword(:64))
                                ==> ((m < dimword(:64))
                                ==> ((bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bn env = Int (n2b_64 n)) ∧ (bil_eval_exp bm env = Int (n2b_64 m))
                                ==> (^concl)
                                ))``
        )
      end;
      
    val goals = List.concat [
          map goalgenerator_bop       (prod constructor_size_pairs bopTuples)
        , map goalgenerator_uop       (prod constructor_size_pairs uopTuples)
        , map goalgenerator_bop_bool  (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) bopTuplesBool)
        , map goalgenerator_uop_bool  (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) uopTuplesBool)
        , map goalgenerator_bop_num   (prod (List.filter (fn (_, n) => n = 64) constructor_size_pairs) bopTuplesNum)
        , map goalgenerator_ite_num   (prod (List.filter (fn (_, n) => n = 64) constructor_size_pairs) iteTupleNum)
        , map goalgenerator_ite_bool  (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) iteTupleBool)
        , map goalgenerator_ite       (prod constructor_size_pairs iteTuple)
      ];
  in
    (* And now batch proofs... *)
    map (fn (abop, bop, tac, br, g) => (abop, bop, br, tryprove (g, tac))) goals
  end
;

(* This function helps selecting a theorem by operator and size *)
fun select_bil_op_theorem operator size =
  let
    val constr = fst (List.nth (List.filter (fn (_, s) => s = size) constructor_size_pairs, 0))
      handle Subscript => raise UnsupportedWordSizeException
    val (_, _, _, th) = List.nth (List.filter (fn (aop, _, c, _) => (aop = operator) andalso (c = constr)) bil_op_tms, 0)
      handle Subscript => raise UnsupportedARM8ExpressionException operator
  in
    th
  end
;

(* ------------------------------------------------------------------------- *)
(*  Transcompiler of expressions                                             *)
(* ------------------------------------------------------------------------- *)

(* Extract operands in triplets *)
fun extract_operands t =
        if (wordsSyntax.is_n2w t) then (``T``, ``T``, ``T``)
  else  if (is_comb t) then
    let
      val ops = snd(strip_comb t)
      val l = List.length ops (* can't be 0, can it? *)
    in
            if (l = 1) then (List.nth (ops, 0), ``F``, ``F``)
      else  if (l = 2) then (List.nth (ops, 0), List.nth (ops, 1),``F``)
      else  if (l = 3) then (List.nth (ops, 0), List.nth (ops, 1), List.nth (ops, 2))
      else  raise ArgumentException("Too many operands found...")
    end
  else (``F``, ``F``, ``F``)
;

fun extract_fun t =
    if not (is_comb t) then ``T``
    else fst (strip_comb t);

(* Transcompiler arm8 expressions to BIL model expressions *)
fun tc_exp_arm8_prefix ae prefix =
  let
    fun tce ae =
      let
        val (o1, o2, o3) = extract_operands ae;
	val f0 = extract_fun ae;
      in
              if (wordsSyntax.is_n2w ae) then (
                      bil_expr_const ae
                    , ae
                    , GEN_ALL (SPECL [``env:environment``, eval ``w2b ^ae``] bil_const_tm)
                  )
        else  if  (is_boolean ae) then (
                      bil_expr_bool ae
                    , ae
                    , GEN_ALL (SPECL [``env:environment``, ``bool2b ^ae``] bil_const_tm)
                  )
        else  if  (numSyntax.is_numeral ae) then (
                      bil_expr_num ae
                    , ae
                    , GEN_ALL (SPECL [``env:environment``, ae] bil_numeral_tm)
                  )
        else  if  (is_reg ae) then (
                      bil_a8e_den_prefix ae prefix
                    , ae
                    , (GEN_ENV o GENL [``s:arm8_state``, ``w:word5``] o SPECL [if (prefix = "") then ``r2s ^((snd o dest_comb) ae)`` else ``APPEND ^(stringSyntax.fromMLstring prefix) (r2s ^((snd o dest_comb) ae))``, ``Reg Bit64``, ``Int (Reg64 ^ae)``] o SPEC_ENV) arm8_to_bil_den_tm
                  )
        else  if  (is_arm8_den ae) then (
                      bil_a8e_den_prefix ae prefix
                    , ae
                    , (GEN_ENV o GEN ``s:arm8_state`` o SPECL [
                          bil_a8e2HOLstring_prefix ae prefix
                        , eval ``bil_type_val_int_inf ^(bil_value ae)``
                        , ``^(bil_value ae)``
                      ] o SPEC_ENV) arm8_to_bil_den_tm
                  )
        else  if  (is_plus_lt_2exp64 ae)
          then
            let
              val (add1, add2, _) = extract_operands o1;
              val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_BIN bil_plus_lt_2exp64_tm (tce add1) (tce add2));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if  (is_plus_mod_2exp64 ae)
          then
            let
              val (add1, add2, _) = extract_operands o1;
              val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_BIN bil_plus_mod_2exp64_tm (tce add1) (tce add2));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (wordsSyntax.is_word_add    ae)
                  orelse  (wordsSyntax.is_word_sub    ae)
                  orelse  (wordsSyntax.is_word_mul    ae)
                  orelse  (wordsSyntax.is_word_div    ae)
                  orelse  (wordsSyntax.is_word_sdiv   ae)
                  orelse  (wordsSyntax.is_word_mod    ae)
                  orelse  (wordsSyntax.is_word_smod   ae)
                  orelse  (wordsSyntax.is_word_lsl_bv ae)
                  orelse  (wordsSyntax.is_word_lsr_bv ae)
                  orelse  (wordsSyntax.is_word_asr_bv ae)
                  orelse  (wordsSyntax.is_word_and    ae)
                  orelse  (wordsSyntax.is_word_or     ae)
                  orelse  (wordsSyntax.is_word_xor    ae)
                  orelse  (            is_word_eq     ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1) (tce o2));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (boolSyntax.is_disj    ae)
                  orelse  (boolSyntax.is_conj    ae)
                  orelse  (           is_eq_bool ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1) (tce o2));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (boolSyntax.is_neg ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          ( numSyntax.is_plus    ae)
    (*               orelse  ( numSyntax.is_minus   ae) *)
                  orelse  ( numSyntax.is_mult    ae)
                  orelse  ( numSyntax.is_div     ae)
                  orelse  ( numSyntax.is_mod     ae)
                  orelse  ( numSyntax.is_less    ae)
                  orelse  ( numSyntax.is_leq     ae)
                  orelse  ( numSyntax.is_greater ae)
                  orelse  ( numSyntax.is_geq     ae)
                  orelse  ( bitSyntax.is_bit     ae)
                  orelse  (           is_eq_num  ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_BIN (select_bil_op_theorem ((fst o strip_comb) ae) 64) (tce o1) (tce o2));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (is_cond_num     ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_ITE (select_bil_op_theorem ((fst o strip_comb) ae) 64) (tce o1) (tce o2) (tce o3));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (is_cond_bool    ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_ITE (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1) (tce o2) (tce o3));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (boolSyntax.is_cond     ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_ITE (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o2)) (tce o1) (tce o2) (tce o3));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (wordsSyntax.is_word_1comp  ae)
                  orelse  (wordsSyntax.is_word_2comp  ae)
                  orelse  (wordsSyntax.is_word_msb    ae)
                  orelse  (wordsSyntax.is_word_lsb    ae)
                  orelse  (wordsSyntax.is_w2n         ae)
                  orelse  (wordsSyntax.is_w2w         ae)
                  orelse  (wordsSyntax.is_sw2sw       ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1))
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)
            in
              (be, ae, mp)
            end
	(* Memory access *)
	else if is_mem ae then
	    let
	(* temporary lifter for memory. For now we do not support load from updated memory *)
		val tce_o1 = (``(Den "MEM")``, ``^o1.MEM``,
			      (GEN_ENV o GENL [``m:bil_int_t -> bil_int_t``] o SPECL [if (prefix = "") then ``"MEM"`` else ``APPEND ^(stringSyntax.fromMLstring prefix) "MEM"``, ``MemByte Bit64``, ``Mem Bit64 m``] o SPEC_ENV) arm8_to_bil_den_tm)
		val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (SPEC ``m:bil_int_t->bil_int_t`` memory_access_2exp64_tm) tce_o1 (tce o2));
		val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
	    in
		(be, ae, mp)
	    end
	(* Memory access dword based *)
	else if (f0 = ``mem_dword``) then
	    let
		val tce_o1 = (``(Den "MEM")``, o1,
			      (GEN_ENV o GENL [``m:bil_int_t -> bil_int_t``] o SPECL [if (prefix = "") then ``"MEM"`` else ``APPEND ^(stringSyntax.fromMLstring prefix) "MEM"``, ``MemByte Bit64``, ``Mem Bit64 m``] o SPEC_ENV) arm8_to_bil_den_tm);
		val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (SPEC ``m:bil_int_t->bil_int_t`` mem_dword_2exp64_tm) tce_o1 (tce o2));
		val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
	    in
		(be, ae, mp)
	    end
        else  raise UnsupportedARM8ExpressionException ae
      end;
    val (be, _, mp) = tce ae;
  in
    (be, ae, (GEN_ALL o GENL [``env:environment``, ``s:arm8_state``] o DISCH_ALL_REV o DISPOSE_HYP) mp)
  end
;
val tc_exp_arm8 = fn ae => tc_exp_arm8_prefix ae "";

(* ------------------------------------------------------------------------- *)
(*  Some list operations                                                     *)
(* ------------------------------------------------------------------------- *)
fun list_intersect l1 l2 = List.filter (fn e => List.exists (fn x => x = e) l2) l1;
fun list_union l1 l2 = List.concat [l1, l2];
fun list_diff l1 l2 = List.filter (fn e => not (List.exists (fn x => x = e) l2)) l1;
fun list_exclusion l1 l2 = list_diff (list_union l1 l2) (list_intersect l1 l2);
fun list_exclusion_id l1 l2 = (list_diff l1 l2, list_diff l2 l1);
fun list_split lst =
  let
    fun ls lst l1 l2 = case lst of
        []        => (List.rev l1, List.rev l2)
      | (a, b)::l => ls l (a::l1) (b::l2);
  in
    ls lst [] []
  end
;
fun list_uniq lst =
  let
    fun lu lst res = case lst of
        []    =>  res
      | e::l  =>  lu l (if List.exists (fn x => x = e) res then res else e::res)
  in
    lu lst []
  end
;

(* ------------------------------------------------------------------------- *)
(*  Field update extraction of ARMv8 states                                  *)
(* ------------------------------------------------------------------------- *)
val extract_updates = fn upd =>
  let
    fun ex upd lst = if (combinSyntax.is_update_comb upd)
      then
        let
          val index = (snd o dest_comb o fst o dest_comb o fst o dest_comb) upd;
          val expr  = (snd o dest_comb o fst o dest_comb) upd;
        in
          ex ((snd o dest_comb) upd) ((stringSyntax.fromHOLstring (eval ``r2s ^index``), expr)::lst)
        end
      else  lst
  in
    ex upd []
  end
;

fun extract_updates_fg upd findex gexpr =
  let
    fun ex upd findex gexpr lst = if (combinSyntax.is_update_comb upd)
      then
        let
          val index = (snd o dest_comb o fst o dest_comb o fst o dest_comb) upd;
          val expr  = (snd o dest_comb o fst o dest_comb) upd;
        in
          ex ((snd o dest_comb) upd) findex gexpr ((findex index, gexpr expr)::lst)
        end
      else  lst
  in
    ex upd findex gexpr []
  end
;
fun extract_updates upd = extract_updates_fg upd (fn x => x) (fn x => x);

fun extract_arm8_changes a8s =
  let
    fun exreg regupd = extract_updates_fg regupd (fn i => (stringSyntax.fromHOLstring (eval ``r2s ^i``))) (fn x => x);
    fun ex a8s lst = if (is_comb a8s)
      then
        let
          val update = (opname o fst o dest_comb) a8s;
          val entry = (snd o dest_comb o snd o dest_comb o fst o dest_comb) a8s handle _ => a8s;
        in
          if (entry = a8s) then lst
          else
                if  (update = "arm8_state_PSTATE_fupd") then ex ((snd o dest_comb) a8s) (List.concat [(ex entry []), lst])
          else  if  (update = "arm8_state_REG_fupd") then ex ((snd o dest_comb) a8s) (List.concat [(exreg entry), lst])
          else ex ((snd o dest_comb) a8s) ((String.substring (update, 0, String.size update - String.size "_fupd"), entry)::lst)
        end
      else  lst;
  in
    ex a8s []
  end
;

fun extract_arm8_changes_cases (a8s1, a8s2) cond =
  let
    fun exreg regupd = extract_updates_fg regupd (fn i => (stringSyntax.fromHOLstring (eval ``r2s ^i``))) (fn x => x);
    fun exregs entries =
      let
        val er1 = exreg (fst entries);
        val er2 = exreg (snd entries);
        fun aux lst1 lst2 res = case (er1, er2) of
            ((s, e1)::l1, (_, e2)::l2) => aux l1 l2 ((s, ``if ^cond then ^e1 else ^e2``)::res)
          | _ => res;
      in
        aux er1 er2 []
      end;
    fun ex (a8s1, a8s2) lst = if (is_comb a8s1) andalso (is_comb a8s2)
      then
        let
          val updates = ((opname o fst o dest_comb) a8s1, (opname o fst o dest_comb) a8s2);
          val entries = (
              (snd o dest_comb o snd o dest_comb o fst o dest_comb) a8s1 handle _ => a8s1
            , (snd o dest_comb o snd o dest_comb o fst o dest_comb) a8s2 handle _ => a8s2
          );
        in
          if (fst entries = a8s1) orelse (snd entries = a8s2) then lst
          else  if  (fst updates = "arm8_state_PSTATE_fupd") andalso (fst updates = snd updates) 
            then ex ((snd o dest_comb) a8s1, (snd o dest_comb) a8s2)  (List.concat [(ex (fst entries, snd entries) []), lst])
          else  if  (fst updates = "arm8_state_REG_fupd") andalso (fst updates = snd updates)
            then ex ((snd o dest_comb) a8s1, (snd o dest_comb) a8s2)  (List.concat [(exregs entries), lst])
          else  if (fst updates = snd updates)
            then ex
              ((snd o dest_comb) a8s1, (snd o dest_comb) a8s2)
              ((String.substring (fst updates, 0, String.size (fst updates) - String.size "_fupd"), ``if ^cond then ^(fst entries) else ^(snd entries)``)::lst)
          else lst
        end
      else  lst;
  in
    ex (a8s1, a8s2) []
  end
;

fun get_a8s_from_upd a8supd = if (is_comb a8supd)
  then  get_a8s_from_upd ((snd o dest_comb) a8supd)
  else  a8supd
;

(* [[TODO: handle more general cases]] *)
fun rewrite_a8s_branch_upd (a8s1, a8s2) cond =
  let
    val changes = extract_arm8_changes_cases (a8s1, a8s2) cond;
    val a8s = get_a8s_from_upd a8s1;
    fun updfield (str, upd) =
            if  (str = "arm8_state_PC")           then  (fst o dest_comb) ``s with <| PC           := ^upd |>``
      else  if  (str = "arm8_state_branch_hint")  then  (fst o dest_comb) ``s with <| branch_hint  := ^upd |>`` (* still unsupported *)
      else  raise UnsupportedARM8StateField str;
  in
    List.foldl (fn (a,b) => ``^a (^b)``) a8s (List.map updfield changes)
  end
;

(* ------------------------------------------------------------------------- *)
(*  Transcompile instructions to BIL programs                                *)
(* ------------------------------------------------------------------------- *)
fun arm8_supported_fields a8s = (
  List.concat [
      arm8_supported_den a8s
    , List.tabulate(32, fn t => ``^a8s.REG ^(wordsSyntax.mk_wordii (t, 5))``)
  ]
);

val arm8_supported_fields_HOLstr = List.map (fn x => bil_a8e2HOLstring x) (arm8_supported_fields ``a8s:arm8_state``);
val arm8_supported_fields_str = List.map (fn x => (stringSyntax.fromHOLstring o eval o bil_a8e2HOLstring) x) (arm8_supported_fields ``a8s:arm8_state``);

fun bil_copy_a8s_state_stmts_prefix a8s prefix =
  let
    val gen_assign_tmp = 
      List.map (fn t => 
              let
                val be  = bil_expr_const t;
                val str = bil_a8e2HOLstring_prefix t prefix;
              in
                ``Assign ^str ^be``
              end
          ) (arm8_supported_fields a8s);
    val assign_tmp = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_assign_tmp);
  in
    assign_tmp
  end
;

fun bil_full_backup_arm8_vars_tmp bs =
  let
    val a8s = ``a8s:arm8_state``;
    val gen_assign_tmp = 
      List.map (fn t => 
              let
                val strsrc = bil_a8e2HOLstring_prefix t "";
                val strdst = bil_a8e2HOLstring_prefix t "tmp_";
              in
                ``Assign ^strdst (Den ^strsrc)``
              end
          ) (arm8_supported_fields a8s);
    val assign_tmp = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_assign_tmp);
  in
    assign_tmp
  end
;

fun bil_backup_arm8_vars_tmp bs bklst =
  let
    val a8s = ``a8s:arm8_state``;
    val removeme = ``rmme:bool``;
    val gen_assign_tmp = 
      List.map (fn t => 
              let
                val strsrc = eval (bil_a8e2HOLstring_prefix t "");
                val strdst = eval (bil_a8e2HOLstring_prefix t "tmp_");
              in
                if (List.exists (fn x => x = stringSyntax.fromHOLstring strsrc) bklst)
                  then  ``Assign ^strdst (Den ^strsrc)``
                  else  removeme
              end
          ) (arm8_supported_fields a8s);
    val gen_assign_tmp_ch = (List.filter (fn x => not (x = removeme)) gen_assign_tmp);
    val assign_tmp = (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_assign_tmp_ch);
  in
    assign_tmp
  end
;

fun arm8_thms_hypdiff th1 th2 =
  let
    val excl = list_exclusion_id (hyp th1) (hyp th2);
    fun clist lst1 lst2 res = case (lst1, lst2) of
        (c1::l1, c2::l2)  =>  clist l1 l2 ((c1, c2)::res)
      | (_, _)            =>  res;
  in
    if (List.length (fst excl) = List.length (snd excl))
      then clist (fst excl) (snd excl) []
      else []
  end
;

fun contr_pairs_conj1 hd =
  let
    fun hdc hd tms = case hd of
        []          =>  tms
      | (t1, t2)::l =>
          if (eval ``^t1 = ~(^t2)``) = ``T``
            then hdc l (t1::tms)
            else [];
            (* [[]] an exception is better *)
  in
    eval (List.foldr (fn (a, b) => ``^a ∧ ^b``) ``T`` (hdc hd []))
  end
;

fun arm8_branch_thm_join thl = case thl of
    th1::th2::[] =>
      let
        val conds = arm8_thms_hypdiff th1 th2;
        val hyps = list_intersect (hyp th1) (hyp th2);
        val c1 = (optionSyntax.dest_some o snd o dest_comb o concl) th1;
        val c2 = (optionSyntax.dest_some o snd o dest_comb o concl) th2;
        val a8s' = rewrite_a8s_branch_upd (c1, c2) (contr_pairs_conj1 conds);
        val conc = ``(NextStateARM8 s = SOME (^a8s'))``;
        val th = List.foldl (fn (a, b) => ``^a ==> (^b)``) conc hyps;
        val tac = (RW_TAC (pure_ss) []) THENL [FULL_SIMP_TAC (srw_ss()) [th1], FULL_SIMP_TAC (srw_ss()) [th2]];
      in
        [UNDISCH_ALL (tryprove(th, tac))]
      end
  | _ => thl
;

fun supported_accesses a8sch =
  let
    val supp_pairs = List.map (fn x => (x, opname x)) (arm8_supported_den ``s:arm8_state``);
    val (writes, aes) = list_split a8sch;
    fun extract_reads ae res = 
            if (is_reg ae)      then  (stringSyntax.fromHOLstring (eval ``r2s ^((snd o dest_comb) ae)``))::res
      else  if (is_arm8_den ae) then  (opname ae)::res
      else  if (is_comb ae)     then  List.concat (List.map (fn x => extract_reads x []) ((snd o strip_comb) ae))
      else  res;
    val reads  =  List.concat (List.map (fn x => extract_reads x []) aes);
  in
    list_uniq (list_union writes reads)
  end
;

fun tc_stmt_arm8_hex instr =
  let
    val arm8thl = arm8_branch_thm_join (arm8_step_hex instr);
  in
    case arm8thl of
        th::[] =>
          let
            (* Filter only supported changes *)
            val a8sch = List.filter (fn (s, v) => List.exists (fn x => x = s) arm8_supported_fields_str) ((extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) th);
            val certify_assignments = List.map (fn (s, a8e) =>
                let
                  val (bexp, _, thm)  = tc_exp_arm8_prefix a8e "tmp_";
                  val str = stringSyntax.fromMLstring (s);
                in
                  (``Assign ^str ^bexp``, thm)
                end
              ) a8sch;
            val (assign, certs) = list_split certify_assignments;
            val cp_tmp = bil_backup_arm8_vars_tmp ``bs:stepstate`` (supported_accesses a8sch);
            val stmts = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` assign);
          in
            (eval ``^cp_tmp ++ ^stmts``, certs, arm8thl)
          end
      | _    => (``[]``, [], [])
  end
;


(* after this we do not have certification of step *)


fun tc_stmt_arm8_hexlist instrlst =
  let
    fun tci ilist idx res = 
      case ilist of
          []    =>  res
        | i::l  =>
            let
              val (stmts, certs, arm8thl) = tc_stmt_arm8_hex i;
              val changes = (extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) (List.hd arm8thl);
              val branch_hint = (snd o List.hd o List.filter (fn (s, e) => s = "arm8_state_branch_hint")) changes;
              val is_branch_conditional = boolSyntax.is_cond branch_hint;
              val is_branch = is_branch_conditional orelse optionSyntax.is_some branch_hint;
              val (assigns_n_jmp, jmp_certs) = if (is_branch_conditional) then
                  let
                    val cond = (snd o List.hd o List.filter (fn (s, e) => s = "arm8_state_PC")) changes;
                    val (c, t, e) = dest_cond cond;
                    val (bc, _, cert) = tc_exp_arm8 c;
                    val (next_t, next_e) = (eval ``^idx + ^((snd o dest_comb) t)``, eval ``^idx + ^((snd o dest_comb) e)``);
                  in
                    (``^stmts ++ [CJmp ^bc (Address (Reg64 ^next_t)) (Address (Reg64 ^next_e))]``, [cert])
                  end
                else if (is_branch) then
                  let
                    val ae = (snd o List.hd o List.filter (fn (s, e) => s = "arm8_state_PC")) changes;
                    val next_ae = eval ``^idx + ^((snd o dest_comb) ae)``;
                  in
                    (``^stmts ++ [Jmp (Address (Reg64 ^next_ae))]``, [])
                  end
                else  (``^stmts``, []);
            in
              tci l (eval ``^idx + 4w``) ((``<| label := Address (Reg64 ^idx); statements := ^assigns_n_jmp |>``, List.concat [certs, jmp_certs])::res)
            end;
  in
    List.rev (tci instrlst ``0w:bool[64]`` [])
  end
;

(* ------------------------------------------------------------------------- *)
(*  Transcompile instructions to BIL program                                 *)
(* ------------------------------------------------------------------------- *)
val arm8_state_zero = ``<|
    PC          := (0w:bool[64])
  ; REG         := λ(x:bool[5]).(0w:bool[64])
  ; MEM         := λ(x:bool[64]).(0w:bool[8])
  ; PSTATE      := <|N := F; Z := F; C := F; V := F; SPS := F; EL := (0w :word2)|>
  ; SCTLR_EL1   := <|
        A := F; E0E := F; EE := F; SA := F; SA0 := F
      ; sctlrtype'rst := (0w:bool[27])
    |>
  ; SCTLR_EL2   := <|
        A := F; E0E := F; EE := F; SA := F; SA0 := F
      ; sctlrtype'rst := (0w:bool[27])
    |>
  ; SCTLR_EL3   := <|
        A := F; E0E := F; EE := F; SA := F; SA0 := F
      ; sctlrtype'rst := (0w:bool[27])
    |>
  ; SP_EL0 := (0w:bool[64]); SP_EL1 := (0w:bool[64])
  ; SP_EL2 := (0w:bool[64]); SP_EL3 := (0w:bool[64])
  ; TCR_EL1     := <|TBI0 := F; TBI1 := F; tcr_el1'rst := (0w :62 word)|>
  ; TCR_EL2     := <|TBI := F; tcr_el2_el3'rst := (0w :31 word)|>
  ; TCR_EL3     := <|TBI := F; tcr_el2_el3'rst := (0w :31 word)|>
  ; branch_hint := NONE
  ; exception   := NoException
|>``;

fun init_arm8_hex instr = 
  let
    val instrHOL = stringSyntax.fromMLstring instr;
    val pc0 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 8, 2))``;
    val pc1 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 6, 2))``;
    val pc2 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 4, 2))``;
    val pc3 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 2, 2))``;
  in
    eval ``^arm8_state_zero with <| MEM := (0w =+ n2w ^pc0) ((1w =+ n2w ^pc1) ((2w =+ n2w ^pc2) ((3w =+ n2w ^pc3) ^arm8_state_zero.MEM))) |>``
  end
;

val bil_init_declaration_stmts_a8s = fn prefix =>
  let
    val a8s     = arm8_state_zero;
    val bs      = ``bs:stepstate``;
    val gen_decls = 
      List.map (fn t => 
              let
                val bv  = bil_value t;
                val str = bil_a8e2HOLstring_prefix t prefix;
                val bvt = eval ``bil_type_val_int_inf ^bv``;
              in
                ``Declare (Var ^str ^bvt)``
              end
          ) (arm8_supported_fields a8s);
    val decls = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_decls);
  in
    decls
  end
;


(* Generate a BIL State equivalent to an ARMv8 State *)
fun a8s2bs_var_prefix a8s bs prefix =
  let
    fun triple_stv x prefix =
      let
        val v = (eval o bil_value) x;
      in
        ((eval o C bil_a8e2HOLstring_prefix prefix) x, eval ``bil_type_val_int_inf ^v``, v)
      end;
    val env_strings = List.map (fn x => triple_stv x prefix) (List.concat [
        arm8_supported_den a8s
      , List.tabulate(32, fn t => ``^a8s.REG ^(wordsSyntax.mk_wordii (t, 5))``)
    ]);
    val den_updates = List.map (fn (s, t, v) => ``(^s =+ (^t, ^v))``) env_strings;
    
    val mem_updates_list = fn a8s =>
      let
        val mem_upd = fn a8s => List.filter (fn (s, v) => s = bil_a8e2string ``s.MEM``) (extract_arm8_changes a8s);
      in
        ((extract_updates o snd) (List.nth (mem_upd a8s, 0))) handle Subscript => []
      end;
    
    val mem_updates =
      let
        fun mups updlp lst = case updlp of
            []        =>  lst
          | (f, v)::l =>  mups l ((``(Reg64 ^f =+ Reg8 ^v)``)::lst);
        val updl = (mups (mem_updates_list a8s) []);
      in
        List.foldr (fn (a, b) => ``^a (^b)``) ``λ(x:bil_int_t).(Reg8 0w)`` updl
      end;
      
    val mstr = bil_a8e2HOLstring_prefix ``^a8s.MEM`` ""; (* don't change memory name *)
    val mem_update = ``^mstr =+ (MemByte Bit64, Mem Bit64 ^mem_updates)``;
    
    val env = List.foldr (fn (a, b) => ``^a (^b)``) (eval ``^bs.environ``) (mem_update::den_updates);
  in
    ``^bs with <| environ  := ^env |>``
  end
;
fun a8s2bs a8s bs = a8s2bs_var_prefix a8s bs "";

fun a8s2bs_step_program instrl a8s =
  let
    val decl = bil_init_declaration_stmts_a8s "";
    val decl_tmp = bil_init_declaration_stmts_a8s "tmp_";
    val decls = eval ``^decl ++ ^decl_tmp``;
    val (blocks, certs) = list_split (tc_stmt_arm8_hexlist instrl);
    val prog = List.foldr (fn (a, b) => ``^a::^b``) ``[]:program`` blocks;
    val copy_block = bil_copy_a8s_state_stmts_prefix a8s "";
    val last_label = eval ``^(List.nth (blocks, (List.length blocks) - 1)).label``;
    val halt_label = eval ``Address (bil_read_address_label ^last_label + 4x)``;
  in
    (``(  (<| label := Label "Init declaration"; statements := ^decls |>)
        ::(<| label := Label "ARM8 state first copy"; statements := ^copy_block |>)
        ::^prog
       ) ++ [<| label := ^halt_label; statements := [ Halt (Const 0b) ] |>]``, List.concat certs)
  end
;


(* ------------------------------------------------------------------------- *)
(*  ARMv8 State - BIL State Bisimulation                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
end
