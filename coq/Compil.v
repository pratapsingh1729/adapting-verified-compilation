From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.
Require Import Sequences IMP.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** The target language: a stack machine *)

(** Instruction set *)
Inductive instr : Type :=
  | Iconst (n: Z)           (** push the integer [n] *)
  | Ivar (x: ident)         (** push the current value of variable [x] *)
  | Isetvar (x: ident)      (** pop an integer and assign it to variable [x] *)
  | Iadd                    (** pop two integers, push their sum *)
  | Iopp                    (** pop one integer, push its opposite *)
  | Ibranch (d: Z)          (** skip forward or backward [d] instructions *)
  | Ibeq (d1: Z) (d0: Z)    (** pop two integers, skip [d1] instructions if equal, [d0] if not equal *)
  | Ible (d1: Z) (d0: Z)    (** pop two integer, skip [d1] instructions if less or equal, [d0] if greater *)
  | Iinput                  (** read input and push it *)
  | Ioutput                 (** pop an integer and output it *)
  | Ihalt.                  (** stop execution *)


Definition code := list instr.

Definition codelen (c: code) : Z := Z.of_nat (List.length c).

(** Operational semantics *)

Definition stack : Type := list Z.

(** [instr_at C pc = Some i] if [i] is the instruction at position [pc] in [C]. *)
Fixpoint instr_at (C: code) (pc: Z) : option instr :=
  match C with
  | nil => None
  | i :: C' => if pc =? 0 then Some i else instr_at C' (pc - 1)
  end.

(** The compilation scheme *)

(** The code for an arithmetic expression [a] executes in sequence (no branches),
  and deposits the value of [a] at the top of the stack.  
  This is the familiar translation to "reverse Polish notation".
  The only twist here is that the machine has no "subtract" instruction.
  However, it can compute the difference [a - b] by adding [a] and the opposite of [b].
*)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | CONST n => Iconst n :: nil
  | VAR x => Ivar x :: nil
  | PLUS a1 a2  => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iopp :: Iadd :: nil
  end.

(** For Boolean expressions [b], we could produce code that deposits [1] or [0]
  at the top of the stack, depending on whether [b] is true or false.
  The compiled code for [IFTHENELSE] and [WHILE] commands would, then,
  compare this 0/1 value against 0 and branch to the appropriate piece of code.

  However, it is simpler and more efficient to compile a Boolean expression [b]
  to a piece of code that directly jumps [d1] or [d0] instructions forward,
  depending on whether [b] is true or false.  The actual value of [b] is
  never computed as an integer, and the stack is unchanged.
*)

Fixpoint compile_bexp (b: bexp) (d1: Z) (d0: Z) : code :=
  match b with
  | TRUE => if d1 =? 0 then nil else Ibranch d1 :: nil
  | FALSE => if d0 =? 0 then nil else Ibranch d0 :: nil
  | EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Ibeq d1 d0 :: nil
  | LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Ible d1 d0 :: nil
  | NOT b1 => compile_bexp b1 d0 d1
  | AND b1 b2 =>
      let code2 := compile_bexp b2 d1 d0 in
      let code1 := compile_bexp b1 0 (codelen code2 + d0) in
      code1 ++ code2
  end.

(** See the slides for an explanation of the mysterious offsets in the [AND] case. *)


(** The code for a command [c]:
  - updates the store (the values of variables) as prescribed by [c]
  - preserves the stack
  - finishes "at the end" of the generated code: the next instruction
    executed is the instruction that will follow the generated code.
  Again, see the slides for explanations of the generated branch offsets.
*)

Fixpoint compile_com (c: com) : code :=
  match c with
  | SKIP =>
      nil
  | ASSIGN x a =>
      compile_aexp a ++ Isetvar x :: nil
  | SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ Ibranch (codelen code_ifnot)
      :: code_ifnot
  | WHILE b body =>
      let code_body := compile_com body in
      let code_test := compile_bexp b 0 (codelen code_body + 1) in
      code_test
      ++ code_body
      ++ Ibranch (- (codelen code_test + codelen code_body + 1)) :: nil
  | INPUT x =>
      Iinput :: Isetvar x :: nil
  | OUTPUT a =>
      compile_aexp a ++ Ioutput :: nil
  end.

(** The code for a program [p] (a command) is similar, but terminates
  cleanly on an [Ihalt] instruction. *)

Definition compile_program (p: com) : code :=
  compile_com p ++ Ihalt :: nil.


(** Defining the relation between IMP states and stack machine states. *)
Inductive code_at: code -> Z -> code -> Prop :=
  | code_at_intro: forall C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2.

Inductive compile_cont (C: code): cont -> Z -> Prop :=
  | ccont_stop: forall pc,
      instr_at C pc = Some Ihalt ->
      compile_cont C Kstop pc
  | ccont_seq: forall c k pc pc',
      code_at C pc (compile_com c) ->
      pc' = pc + codelen (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (Kseq c k) pc
  | ccont_while: forall b c k pc d pc' pc'',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      code_at C pc' (compile_com (WHILE b c)) ->
      pc'' = pc' + codelen (compile_com (WHILE b c)) ->
      compile_cont C k pc'' ->
      compile_cont C (Kwhile b c k) pc
  | ccont_branch: forall d k pc pc',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      compile_cont C k pc' ->
      compile_cont C k pc.

Lemma codelen_cons:
  forall i c, codelen (i :: c) = codelen c + 1.
Proof.
  unfold codelen; intros; cbn; lia.
Qed.

Lemma codelen_app:
  forall c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2.
Proof.
  induction c1; intros. 
- auto.
- cbn [app]. rewrite ! codelen_cons. rewrite IHc1. lia.
Qed.

Lemma instr_at_app:
  forall i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc.
- auto.
- assert (A: codelen (a :: c1) =? 0 = false). 
  { apply Z.eqb_neq. unfold codelen. cbn [length]. lia. }
  rewrite A. rewrite codelen_cons. apply IHc1. lia.
Qed.

Lemma code_at_head:
  forall C pc i C',
  code_at C pc (i :: C') ->
  instr_at C pc = Some i.
Proof.
  intros. inversion H. simpl. apply instr_at_app. auto.
Qed.

Lemma code_at_tail:
  forall C pc i C',
  code_at C pc (i :: C') ->
  code_at C (pc + 1) C'.
Proof.
  intros. inversion H. 
  change (C1 ++ (i :: C') ++ C3)
    with (C1 ++ (i :: nil) ++ C' ++ C3).
  rewrite <- app_ass. constructor. rewrite codelen_app. subst pc. auto.
Qed. 

Lemma code_at_app_left:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1.
Proof.
  intros. inversion H. rewrite app_ass. constructor. auto.
Qed.

Lemma code_at_app_right:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2.
Proof.
  intros. inversion H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite codelen_app. subst pc. auto.
Qed.

Lemma code_at_app_right2:
  forall C pc C1 C2 C3,
  code_at C pc (C1 ++ C2 ++ C3) ->
  code_at C (pc + codelen C1) C2.
Proof.
  intros. apply code_at_app_right. apply code_at_app_left with (C2 := C3). rewrite app_ass; auto. 
Qed.

Lemma code_at_nil:
  forall C pc C1,
  code_at C pc C1 -> code_at C pc nil.
Proof.
  intros. inversion H. subst. change (C1 ++ C3) with (nil ++ C1 ++ C3).
  constructor. auto.
Qed.

Lemma instr_at_code_at_nil:
  forall C pc i, instr_at C pc = Some i -> code_at C pc nil.
Proof.
  induction C; cbn; intros.
- discriminate.
- destruct (pc =? 0) eqn:PC.
+ assert (pc = 0) by (apply Z.eqb_eq; auto). subst pc. 
  change (a :: C) with (nil ++ nil ++ (a :: C)). constructor. auto.
+ assert (A: code_at C (pc - 1) nil) by eauto.
  inversion A; subst.
  apply code_at_intro with (C1 := a :: C1) (C3 := C3). rewrite codelen_cons. lia.
Qed.

Global Hint Resolve code_at_head code_at_tail code_at_app_left code_at_app_right
      code_at_app_right2 code_at_nil instr_at_code_at_nil: code.
Hint Rewrite codelen_app codelen_cons Z.add_assoc Z.add_0_r : code.
