From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality Streams.
Require Import Sequences IMP Compil.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Module Determ.

(** We give a deterministic semantics in which interruption is not
    possible, and show bisimulation within it. Then we add
    interruption in MachFull.v. *)

(* States of the stack machine executed under deterministic
semantics. Note that the program is unchanging, so it is not included
in the machine state. *)
Definition config : Type := Z * stack * store * global_state.

(* Operational semantics of the deterministic stack machine. *)
Inductive transition (C: code): config -> option event -> config -> Prop :=
  | trans_const: forall pc stk s n g,
      instr_at C pc = Some(Iconst n) ->
      transition C (pc    , stk    , s, g) None 
                  (pc + 1, n :: stk, s, g)
  | trans_var: forall pc stk s x g,
      instr_at C pc = Some(Ivar x) ->
      transition C (pc    , stk      , s, g) None
                  (pc + 1, s x :: stk, s, g)
  | trans_setvar: forall pc stk s x n g,
      instr_at C pc = Some(Isetvar x) ->
      transition C (pc    , n :: stk, s           , g) None
                  (pc + 1, stk    , update x n s, g)
  | trans_add: forall pc stk s n1 n2 g,
      instr_at C pc = Some(Iadd) ->
      transition C (pc    , n2 :: n1 :: stk  , s, g) None
                  (pc + 1, (n1 + n2) :: stk, s, g)
  | trans_opp: forall pc stk s n g,
      instr_at C pc = Some(Iopp) ->
      transition C (pc    , n :: stk    , s, g) None
                  (pc + 1, (- n) :: stk, s, g)
  | trans_branch: forall pc stk s d pc' g,
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , stk, s, g) None
                  (pc', stk, s, g)
  | trans_beq: forall pc stk s d1 d0 n1 n2 pc' g,
      instr_at C pc = Some(Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 =? n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s, g) None
                  (pc', stk          , s, g)
  | trans_ble: forall pc stk s d1 d0 n1 n2 pc' g,
      instr_at C pc = Some(Ible d1 d0) ->
      pc' = pc + 1 + (if n1 <=? n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s, g) None
                  (pc', stk          , s, g)
  | trans_input: forall pc stk s g n g',
      instr_at C pc = Some(Iinput) ->
      (n, g') = take_input g ->
      transition C (pc    , stk    , s, g ) (Some (ev_input n))
                  (pc + 1, n :: stk, s, g')
  | trans_output: forall pc stk s g n,
      instr_at C pc = Some(Ioutput) ->
      transition C (pc    , n :: stk, s, g ) (Some (ev_output n))
                  (pc + 1, stk    , s, produce_output g n).

Definition transitions (C: code): config -> list event -> config -> Prop :=
  star (transition C).


(** The machine terminates normally on an Ihalt instruction, emitting trace tr. *)
Definition machine_terminates (C: code) (s_init: store) (g_init: global_state)
           (tr: trace) (s_final: store) (g_final: global_state) : Prop :=
  exists pc, transitions C (0, nil, s_init, g_init) tr (pc, nil, s_final, g_final)
          /\ instr_at C pc = Some Ihalt.

(** The machine emits trace tr then diverges silently. *)
Definition machine_diverges_silently
           (C: code) (s_init: store) (g_init: global_state) (tr: trace) : Prop :=
  diverges_silently (transition C) (0, nil, s_init, g_init) tr.

(** The machine diverges with an infinte sequence of events itr. *)
Definition machine_diverges_with_inftrace
           (C: code) (s_init: store) (g_init: global_state) (itr: inftrace) : Prop :=
  infseq_with_inftrace (transition C) (0, nil, s_init, g_init) itr.

(** The machine gets "stuck": it reaches a state from which it cannot
step but whose current instruction is not Ihalt.  *)
Definition machine_goes_wrong (C: code) (s_init: store) (g_init: global_state) (tr: trace) : Prop :=
  exists pc stk s g,
      transitions C (0, nil, s_init, g_init) tr (pc, stk, s, g)
   /\ irred (transition C) (pc, stk, s, g)
   /\ (instr_at C pc <> Some Ihalt \/ stk <> nil).

(** The machine takes finintely many steps and emits trace tr. *)
Definition machine_admits_finite
           (C: code) (s_init: store) (g_init: global_state) (tr: trace) : Prop :=
  exists config', transitions C (0, nil, s_init, g_init) tr config'. 


(** Determinism properties for the stack machine executed under the
deterministic semantics. *)

Lemma deterministic_onestep:
  forall C pc stk s g pc1 stk1 s1 g1 eo1,
    transition C (pc, stk, s, g) eo1 (pc1, stk1, s1, g1) ->
    forall pc2 stk2 s2 g2 eo2,
      transition C (pc, stk, s, g) eo2 (pc2, stk2, s2, g2) ->
      pc1 = pc2 /\ stk1 = stk2 /\ s1 = s2 /\ g1 = g2 /\ eo1 = eo2.
Proof.
  intros until 1; dependent induction H; intros;
    match goal with
    | Ht : transition _ _ _ _ |- _ => inversion Ht; subst; try congruence
    end; try solve [repeat split];
    try (match goal with
         | Ha : instr_at ?C ?pc = _, Hb : instr_at ?C ?pc = _ |- _ =>
           rewrite Ha in Hb; injection Hb; intros; subst
         end; repeat split).
  - rewrite <- H0 in H12. inversion H12; subst. repeat split.
Qed.

Lemma deterministic_onestep':
  forall C cd cd1 cd2 eo1 eo2,
    transition C cd eo1 cd1 ->
    transition C cd eo2 cd2 ->
    cd1 = cd2 /\ eo1 = eo2.
Proof.
  intros.
  destruct cd as [[[pc stk] s] g].
  destruct cd1 as [[[pc1 stk1] s1] g1].
  destruct cd2 as [[[pc2 stk2] s2] g2].
  eapply deterministic_onestep in H0; try eapply H.
  destruct H0 as [H1 [H2 [H3 [H4 H5]]]].
  subst; split; trivial.
Qed.

Lemma no_trans_from_Ihalt : forall C pc,
    instr_at C pc = Some Ihalt ->
    (forall stk s g eopt conf',
      ~(transition C (pc, stk, s, g) eopt conf')). 
Proof.
  intuition; intros. inversion H0; subst; rewrite H in H7; discriminate.
Qed. 
  
Lemma deterministic_terminates':
  forall C pc stk s g tr1 s1 g1,
    (exists pc1, transitions C (pc, stk, s, g) tr1 (pc1, [], s1, g1)
            /\ instr_at C pc1 = Some Ihalt) ->
    forall tr2 s2 g2,
      (exists pc2, transitions C (pc, stk, s, g) tr2 (pc2, [], s2, g2)
              /\ instr_at C pc2 = Some Ihalt) ->
      tr1 = tr2 /\ s1 = s2 /\ g1 = g2.       
Proof.
  intros until 1. destruct H as (pc1 & Htr1 & Hhalt1).
  dependent induction Htr1; intros. 
  - destruct H as (pc & Htr2 & Hpc2).
    inversion Htr2; subst; try easy; apply no_trans_from_Ihalt in H; easy.
  - destruct b as [[[pc' stk'] s'] g']. 
    destruct H0 as (pc2 & Htr2 & Hhalt2). inversion Htr2; subst.
    + apply no_trans_from_Ihalt in H; easy.
    + eapply deterministic_onestep' in H0; [ | apply H ].
      destruct H0; rewrite <- H0 in *. eauto. 
    + eapply deterministic_onestep' in H0; [ | apply H ].
      destruct H0; discriminate. 
  - destruct b as [[[pc' stk'] s'] g']. 
    destruct H0 as (pc2 & Htr2 & Hhalt2). inversion Htr2; subst.
    + apply no_trans_from_Ihalt in H; easy.
    + eapply deterministic_onestep' in H0; [ | apply H ].
      destruct H0; discriminate. 
    + eapply deterministic_onestep' in H0; [ | apply H ].
      destruct H0; rewrite <- H0 in *. injection H2; intros; subst. 
      assert (t = t0 /\ s1 = s2 /\ g1 = g2); eauto. 
      destruct H0 as (H0 & H0' & H0''); subst; repeat split. 
Qed. 

Lemma deterministic_terminates:
  forall C s g tr1 s1 g1 tr2 s2 g2,  
    machine_terminates C s g tr1 s1 g1 ->
    machine_terminates C s g tr2 s2 g2 ->
    tr1 = tr2 /\ s1 = s2 /\ g1 = g2. 
Proof. 
  unfold machine_terminates; intros.
  eapply deterministic_terminates' in H0; eauto.
Qed.

Lemma deterministic_diverges_silently:
  forall C s g tr1 tr2,
    machine_diverges_silently C s g tr1 ->
    machine_diverges_silently C s g tr2 ->
    tr1 = tr2.
Proof.
  unfold machine_diverges_silently, diverges_silently. intros.
  destruct H as (b & Hstar & Hinf). destruct H0 as (b' & Hstar' & Hinf').
  pose proof Hstar'. 
  eapply (star_star_inv (deterministic_onestep' C)) in H; [ | eapply Hstar ].
  destruct H as [ (tr'' & Hstar'' & Happ'') | (tr'' & Hstar'' & Happ'') ].
  - enough (tr'' = []).
    { rewrite H in Happ''. rewrite Happ''. now rewrite app_nil_r. }
    eapply (infseq_silent_star_inv' (deterministic_onestep' C)); eauto. 
  - enough (tr'' = []).
    { rewrite H in Happ''. rewrite Happ''. now rewrite app_nil_r. }
    eapply (infseq_silent_star_inv' (deterministic_onestep' C)); eauto. 
Qed.  

Lemma deterministic_diverges_with_inftrace:
  forall C s g tr1 tr2,
    machine_diverges_with_inftrace C s g tr1 ->
    machine_diverges_with_inftrace C s g tr2 ->
    EqSt tr1 tr2.
Proof.
  unfold machine_diverges_with_inftrace. intros.
  eapply deterministic_infseq_with_inftrace; eauto using deterministic_onestep'. 
Qed.  

(** Correctness of generated code for expressions. *)

Lemma compile_aexp_correct:
  forall C s a pc stk g,
  code_at C pc (compile_aexp a) ->
  transitions C
       (pc, stk, s, g) []
       (pc + codelen (compile_aexp a), aeval s a :: stk, s, g).
Proof.
  induction a; simpl; intros.

- (* CONST *)
  apply star_one. apply trans_const. eauto with code. 

- (* VAR *)
  apply star_one. apply trans_var. eauto with code. 

- (* PLUS *)
  eapply star_trans_nil. apply IHa1. eauto with code.
  eapply star_trans_nil. apply IHa2. eauto with code.
  apply star_one. autorewrite with code. apply trans_add. eauto with code.

- (* MINUS *)
  eapply star_trans_nil. apply IHa1. eauto with code.
  eapply star_trans_nil. apply IHa2. eauto with code.
  eapply star_trans_nil.
  apply star_one. apply trans_opp. eauto with code.
  apply star_one.
  replace (aeval s a1 - aeval s a2) 
     with (aeval s a1 + (- aeval s a2))
       by lia.
  autorewrite with code. apply trans_add. eauto with code.
Qed.

Lemma compile_bexp_correct:
  forall C s b d1 d0 pc stk g,
  code_at C pc (compile_bexp b d1 d0) ->
  transitions C
       (pc, stk, s, g) []
       (pc + codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s, g).
Proof.
  induction b; cbn; intros.

- (* TRUE *)
  destruct (d1 =? 0) eqn:Z.
  + (* distance is zero, no branch is generated *)
    assert (d1 = 0) by (apply Z.eqb_eq; auto). subst d1.
    autorewrite with code. apply star_refl.
  + (* a branch is generated *)
    apply star_one. apply trans_branch with (d := d1). eauto with code. auto.

- (* FALSE *)
  destruct (d0 =? 0) eqn:Z.
  + (* distance is zero, no branch is generated *)
    assert (d0 = 0) by (apply Z.eqb_eq; auto). subst d0.
    autorewrite with code. apply star_refl.
  + (* a branch is generated *)
    apply star_one. apply trans_branch with (d := d0). eauto with code. auto.

- (* EQUAL *)
  eapply star_trans_nil. apply compile_aexp_correct with (a := a1). eauto with code.
  eapply star_trans_nil. apply compile_aexp_correct with (a := a2). eauto with code.
  apply star_one. apply trans_beq with (d1 := d1) (d0 := d0). eauto with code.
  autorewrite with code. auto.

- (* LESSEQUAL *)
  eapply star_trans_nil. apply compile_aexp_correct with (a := a1). eauto with code.
  eapply star_trans_nil. apply compile_aexp_correct with (a := a2). eauto with code.
  apply star_one. apply trans_ble with (d1 := d1) (d0 := d0). eauto with code.
  autorewrite with code. auto.

- (* NOT *)
  replace (if negb (beval s b) then d1 else d0)
     with (if beval s b then d0 else d1).
  apply IHb. auto. 
  destruct (beval s b); auto.

- (* AND *)
  set (code2 := compile_bexp b2 d1 d0) in *.
  set (code1 := compile_bexp b1 0 (codelen code2 + d0)) in *.
  eapply star_trans_nil. apply IHb1. eauto with code.
  fold code1. destruct (beval s b1); cbn.
  + (* b1 evaluates to true, the code for b2 is executed *)
    autorewrite with code. apply IHb2. eauto with code.
  + (* b2 evaluates to true, the code for b2 is skipped *)
    autorewrite with code. apply star_refl.
Qed.

(** Proof of backward simulation between IMP and deterministic stack machine. *)

Inductive match_config (C: code): impstate -> config -> Prop :=
  | match_config_intro: forall c k st pc g,
      code_at C pc (compile_com c) ->
      compile_cont C k (pc + codelen (compile_com c)) ->
      match_config C (c, k, st, g) (pc, nil, st, g).

(** We are now ready to prove the expected simulation property.
  Since some transitions in the source command correspond to zero transitions
  in the compiled code, we need a simulation diagram of the "star" kind
  (see the slides).
<<
                      match_config
     c / k / st  ----------------------- machconfig
       |                                   |
       |                                   | + or ( * and |c',k'| < |c,k| )
       |                                   |
       v                                   v
    c' / k' / st' ----------------------- machconfig'
                      match_config 
>>
Note the stronger conclusion on the right:
- either the virtual machine does one or several transitions
- or it does zero, one or several transitions, but the size of the [c,k]
  pair decreases strictly.

It would be equivalent to state:
- either the virtual machine does one or several transitions
- or it does zero transitions, but the size of the [c,k] pair decreases strictly.

However, the formulation above, with the "star" case, is often more convenient.
*)

(** Finding an appropriate "anti-stuttering" measure is a bit of a black art.
  After trial and error, we find that the following measure works.  It is
  the sum of the sizes of the command [c] under focus and all the commands
  appearing in the continuation [k]. *)

Fixpoint com_size (c: com) : nat :=
  match c with
  | SKIP => 1%nat
  | ASSIGN x a => 1%nat
  | (c1 ;; c2) => (com_size c1 + com_size c2 + 1)%nat
  | IFTHENELSE b c1 c2 => (com_size c1 + com_size c2 + 1)%nat
  | WHILE b c1 => (com_size c1 + 1)%nat
  | INPUT x => 1%nat
  | OUTPUT a => 1%nat
  end.

Remark com_size_nonzero: forall c, (com_size c > 0)%nat.
Proof.
  induction c; cbn; lia.
Qed.

Fixpoint cont_size (k: cont) : nat :=
  match k with
  | Kstop => 0%nat
  | Kseq c k' => (com_size c + cont_size k')%nat
  | Kwhile b c k' => cont_size k'
  end.

Definition measure (impconf: impstate) : nat :=
  match impconf with (c, k, m, g) => (com_size c + cont_size k)%nat end.


Lemma compile_cont_Kstop_inv:
  forall C pc s g,
  compile_cont C Kstop pc ->
  exists pc',
  star (transition C) (pc, nil, s, g) [] (pc', nil, s, g)
  /\ instr_at C pc' = Some Ihalt.
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_refl. auto.
- destruct IHcompile_cont as (pc'' & A & B); auto.
  exists pc''; split; auto. eapply star_step; eauto. eapply trans_branch; eauto. 
Qed.

Lemma compile_cont_Kseq_inv:
  forall C c k pc s g,
  compile_cont C (Kseq c k) pc ->
  exists pc',
  star (transition C) (pc, nil, s, g) [] (pc', nil, s, g)
  /\ code_at C pc' (compile_com c)
  /\ compile_cont C k (pc' + codelen(compile_com c)).
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_refl. split; congruence. 
- edestruct IHcompile_cont as (pc'' & A & B). eauto.
  exists pc''; split; auto. eapply star_step; eauto. eapply trans_branch; eauto. 
Qed.

Lemma compile_cont_Kwhile_inv:
  forall C b c k pc s g,
  compile_cont C (Kwhile b c k) pc ->
  exists pc',
  plus (transition C) (pc, nil, s, g) [] (pc', nil, s, g)
  /\ code_at C pc' (compile_com (WHILE b c))
  /\ compile_cont C k (pc' + codelen(compile_com (WHILE b c))).
Proof.
  intros. dependent induction H.
- exists (pc + 1 + d); split.
  apply plus_one. eapply trans_branch; eauto. 
  split; congruence.
- edestruct IHcompile_cont as (pc'' & A & B & D). eauto.
  exists pc''; split; auto. eapply plus_left. eapply trans_branch; eauto. apply plus_star; auto. 
Qed.

Lemma match_config_skip:
  forall C k s pc g,
  compile_cont C k pc ->
  match_config C (SKIP, k, s, g) (pc, nil, s, g).
Proof.
  intros. constructor.
- cbn. inversion H; eauto with code.
- cbn. autorewrite with code. auto.
Qed.

Definition tr_of_eopt (eopt : option event) : trace :=
  match eopt with
  | Some ev => [ev]
  | None => []
  end.


(** Simulation lemma for single steps. *)

Lemma simulation_step:
  forall C impconf1 eopt impconf2 machconf1,
  step impconf1 eopt impconf2 ->
  match_config C impconf1 machconf1 ->
  exists machconf2,
      (plus (transition C) machconf1 (tr_of_eopt eopt) machconf2
       \/ (star (transition C) machconf1 (tr_of_eopt eopt) machconf2
           /\ (measure impconf2 < measure impconf1)%nat))
   /\ match_config C impconf2 machconf2.
Proof.
  intros until machconf1; intros STEP MATCH.
  inversion STEP; clear STEP; subst; inversion MATCH; clear MATCH; subst; cbn in *.

- (* assign *)
  econstructor; split.
  left. eapply plus_right. eapply compile_aexp_correct; eauto with code.
  eapply trans_setvar; eauto with code.
  autorewrite with code in *. apply match_config_skip. auto.

- (* seq *)
  econstructor; split.
  right; split. apply star_refl. lia.
  autorewrite with code in *. constructor. eauto with code. eapply ccont_seq; eauto with code.

- (* if *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b 0 (codelen code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  autorewrite with code in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b). eauto with code.
  destruct (beval s b); lia.
  fold codeb. destruct (beval s b).
  + autorewrite with code. constructor. eauto with code.
    eapply ccont_branch. eauto with code. eauto.
    fold code1.
    replace (pc + codelen codeb + codelen code1 + 1 + codelen code2)
       with (pc + codelen codeb + codelen code1 + codelen code2 + 1) by lia.
    auto.
  + autorewrite with code. constructor. eauto with code. auto.
    fold code2.
    replace (pc + codelen codeb + codelen code1 + 1 + codelen code2)
       with (pc + codelen codeb + codelen code1 + codelen code2 + 1) by lia.
    auto.

- (* while stop *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b 0 (codelen codec + 1)) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b). eauto with code.
  assert (com_size c > 0)%nat by apply com_size_nonzero. lia.
  rewrite H. fold codeb. autorewrite with code in *. apply match_config_skip. auto.

- (* while loop *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b 0 (codelen codec + 1)) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b). eauto with code.
  lia.
  rewrite H. fold codeb. autorewrite with code in *.
  constructor. eauto with code.
  eapply ccont_while with (pc' := pc). eauto with code. fold codec. lia.
  auto.
  cbn. fold codec; fold codeb. eauto.
  autorewrite with code. auto.

- (* skip seq *)
  autorewrite with code in *.
  edestruct compile_cont_Kseq_inv as (pc' & X & Y & Z). eauto.
  econstructor; split.
  right; split. eauto. lia.
  constructor; auto.

- (* skip while *)
  autorewrite with code in *.
  edestruct compile_cont_Kwhile_inv as (pc' & X & Y & Z). eauto.
  econstructor; split.
  left. eauto.
  constructor; auto.

- econstructor; split.
  left. eapply plus_left_ev. econstructor; eauto with code.
  eapply star_step. eapply trans_setvar; eauto with code. eapply star_refl.
  apply match_config_skip. now replace (pc + 1 + 1) with (pc + 2) by lia. 
  
- econstructor; split.
  left. replace [ev_output (aeval s a)] with ([] ++ [ev_output (aeval s a)]) by auto using app_nil_l.
  eapply plus_right_ev. eapply compile_aexp_correct; eauto with code.
  econstructor; eauto with code.
  autorewrite with code in *. apply match_config_skip; auto.
Qed.

(** Simulation lemma for zero or more steps. *)
Lemma simulation_steps:
  forall C impconf1 tr impconf2, star step impconf1 tr impconf2 ->
  forall machconf1, match_config C impconf1 machconf1 ->
  exists machconf2,
     star (transition C) machconf1 tr machconf2
  /\ match_config C impconf2 machconf2.
Proof.
  induction 1; intros.
- exists machconf1; split; auto. apply star_refl.
- edestruct simulation_step as (machconf2 & STEPS2 & MATCH2); eauto.
  edestruct IHstar as (machconf3 & STEPS3 & MATCH3); eauto.
  exists machconf3; split; auto.
  replace t with ([] ++ t) by auto using app_nil_l.
  eapply star_trans; eauto.
  destruct STEPS2 as [A | [A B]]. apply plus_star; auto. auto.
- edestruct simulation_step as (machconf2 & STEPS2 & MATCH2); eauto.
  edestruct IHstar as (machconf3 & STEPS3 & MATCH3); eauto.
  exists machconf3; split; auto.
  replace (e :: t) with ([e] ++ t) by auto.
  eapply star_trans; eauto.
  destruct STEPS2 as [A | [A B]]. apply plus_star; auto. auto.
Qed.

Lemma simulation_steps':
  forall C impconf1 machconf1, match_config C impconf1 machconf1 ->
  (forall tr impconf2, star step impconf1 tr impconf2 ->
   exists machconf2,                                       
    star (transition C) machconf1 tr machconf2
    /\ match_config C impconf2 machconf2).
Proof.
  eauto using simulation_steps. 
Qed.

Lemma match_initial_configs:
  forall c s g,
  match_config (compile_program c) (c, Kstop, s, g) (0, nil, s, g).
Proof.
  intros. set (C := compile_program c).
  assert (code_at C 0 (compile_com c ++ Ihalt :: nil)).
  { replace C with (nil ++ (compile_com c ++ Ihalt :: nil) ++ nil).
    constructor; auto.
    rewrite app_nil_r; auto. }
  constructor. 
- eauto with code.
- apply ccont_stop. eauto with code.
Qed.


(** Proofs of forward simulation for the three kinds of IMP behaviors. *)

Lemma simulation_infseq_inv:
  forall C n impconf1 machconf1 tr,
  infseq step impconf1 tr -> match_config C impconf1 machconf1 ->
  (measure impconf1 < n)%nat ->
  exists impconf2 machconf2 tr' tr'',
      infseq step impconf2 tr''
   /\ plus (transition C) machconf1 tr' machconf2
   /\ match_config C impconf2 machconf2
   /\ tr = app_to_itr tr' tr''.
Proof.
  induction n; intros impconf1 machconf1 tr INFSEQ MATCH MEASURE.
  - exfalso; lia.
  - inversion INFSEQ; clear INFSEQ; subst.
    + edestruct simulation_step as (machconf2 & [PLUS | [STAR LESS]] & MATCH2). eauto. eauto. 
      * cbn in *. exists b, machconf2, [], tr; auto.
      * cbn in *. edestruct IHn as (impconf3 & machconf3 & tr3 & tr''0 & X & Y & Z & W). eauto. eauto. lia.
        exists impconf3, machconf3, tr3, tr''0.
        split. auto.
        split. replace tr3 with ([] ++ tr3) by auto using app_nil_l.  eapply star_plus_trans; eauto.
        auto.
    + edestruct simulation_step as (machconf2 & [PLUS | [STAR LESS]] & MATCH2). eauto. eauto. 
      * cbn in *. exists b, machconf2, [e]; eexists; eauto.
      * cbn in *. edestruct IHn as (impconf3 & machconf3 & tr3 & tr''0 & X & Y & Z & W). eauto. eauto. lia.
        exists impconf3, machconf3, ([e] ++ tr3), tr''0.
        split. auto.
        split. eapply star_plus_trans; eauto.
        split; auto. cbn. now rewrite W. 
Qed.

Lemma simulation_infseq_silent_inv:
  forall C n impconf1 machconf1,
  infseq_silent step impconf1 -> match_config C impconf1 machconf1 ->
  (measure impconf1 < n)%nat ->
  exists impconf2 machconf2,
      infseq_silent step impconf2
   /\ plus (transition C) machconf1 [] machconf2
   /\ match_config C impconf2 machconf2. 
Proof.
  induction n; intros impconf1 machconf1 INFSEQ MATCH MEASURE.
  - exfalso; lia.
  - inversion INFSEQ; clear INFSEQ; subst.
    edestruct simulation_step as (machconf2 & [PLUS | [STAR LESS]] & MATCH2). eauto. eauto. 
    + cbn in *. exists b, machconf2; auto.
    + cbn in *. edestruct IHn as (impconf3 & machconf3 & X & Y & Z). eauto. eauto. lia.
      exists impconf3, machconf3.
      split. auto.
      split. replace [] with ((nil:trace) ++ []) by auto using app_nil_l. eapply star_plus_trans; eauto.
      auto.
Qed.

Lemma infseq_silent_preserved_forward: forall c impconf machconf,
    match_config (compile_program c) impconf machconf ->
    infseq_silent step impconf ->
    infseq_silent (transition (compile_program c)) machconf.
Proof.
  intros. set (C := compile_program c).
  apply infseq_silent_coinduction_principle_2 with
      (X := fun machconf => exists impconf, infseq_silent step impconf /\ match_config C impconf machconf).
  - intros machconf' (impconf' & INFSEQ & MATCH).
    edestruct (simulation_infseq_silent_inv C (S (measure impconf'))); try solve [ eauto | lia ].
    edestruct H1 as (machconf2 & INFSEQ2 & PLUS & MATCH2).
    exists machconf2; repeat split; eauto.
  - exists impconf; split; auto.
Qed. 

Lemma infseq_with_inftrace_preserved_forward: forall c impconf machconf itr,
  match_config (compile_program c) impconf machconf ->
  infseq_with_inftrace step impconf itr ->
  infseq_with_inftrace (transition (compile_program c)) machconf itr.
Proof.
  cofix Hfix; intros.
  inversion H0; subst; clear H0.
  edestruct simulation_steps as [machconf2 [Hstar Hmatch]]; eauto using match_initial_configs, plus_star.
  apply star_inv in Hstar; destruct Hstar as [[? ?] | Hstar]; try congruence. 
  econstructor; eauto using plus_star. 
Qed.

Theorem compile_program_correct_terminating:
  forall c s s' g g' tr,
  imp_terminates c s g tr s' g' ->
  machine_terminates (compile_program c) s g tr s' g'.
Proof.
  intros. set (C := compile_program c).
  edestruct (simulation_steps C) as (ms & A & B). eauto. apply match_initial_configs.
  inversion B; subst.
  edestruct compile_cont_Kstop_inv as (pc' & D & E). eauto.
  exists pc'; split; auto.
  replace tr with (tr ++ []) by auto using app_nil_r.
  eapply star_trans. eauto. cbn in D; autorewrite with code in D. eauto.
Qed.

Theorem compile_program_correct_diverging_silently:
  forall c s g tr,
  imp_diverges_silently c s g tr ->
  machine_diverges_silently (compile_program c) s g tr.
Proof.
  unfold imp_diverges_silently, machine_diverges_silently, diverges_silently.
  intros. set (C := compile_program c) in *.
  destruct H as (b & Hstar & Hinfseq).
  eapply simulation_steps in Hstar; eauto using match_initial_configs. 
  destruct Hstar as (machconf2 & Hstar & Hmatch).
  exists machconf2; split; auto.
  destruct b as [[[c' k'] s'] g'].
  eapply infseq_silent_preserved_forward; eauto. 
Qed.
  
Theorem compile_program_correct_diverging_with_inftrace:
  forall c s g itr,
  imp_diverges_with_inftrace c s g itr ->
  machine_diverges_with_inftrace (compile_program c) s g itr.
Proof.
  unfold imp_diverges_with_inftrace, machine_diverges_with_inftrace; intros. 
  eapply infseq_with_inftrace_preserved_forward; eauto using match_initial_configs.
Qed.


(** Using determinism to obtain backward simulation from forward simulation. *)
Lemma forward_implies_backward_terminating:
  (forall c s s' g g' tr,
    imp_terminates c s g tr s' g' ->
    machine_terminates (compile_program c) s g tr s' g') ->
  (forall c s s' g g' tr,
    machine_terminates (compile_program c) s g tr s' g' ->
    imp_terminates c s g tr s' g').
Proof.
  intros.
  specialize (imp_terminates_or_diverges c s g); intros.
  destruct H1 as [ (tr'' & s'' & g'' & H1) | [ (tr' & H1) | (itr' & H1) ] ].
  - pose proof H1.
    apply H in H1. eapply deterministic_terminates in H1; try eapply H0.
    destruct H1 as (H1 & H1' & H1''); subst; trivial.
  - apply compile_program_correct_diverging_silently in H1.
    unfold machine_terminates, machine_diverges_silently in *. destruct H0 as (pc & H0 & H0').
    exfalso.
    eapply (diverges_silently_finseq_excl (deterministic_onestep' (compile_program c))).
    + eapply H0.
    + unfold irred; intros; eapply no_trans_from_Ihalt; easy.
    + eapply H1.     
  - apply compile_program_correct_diverging_with_inftrace in H1.
    unfold machine_terminates, machine_diverges_with_inftrace in *. destruct H0 as (pc & H0 & H2).
    exfalso.
    eapply (infseq_finseq_excl (deterministic_onestep' (compile_program c))).
    + eapply H0.
    + unfold irred; intros; eapply no_trans_from_Ihalt; easy.
    + eapply infseq_with_inftrace_implies_infseq. eapply H1.
Qed.

Lemma forward_implies_backward_diverging_silently:
  (forall c s g tr,
    imp_diverges_silently c s g tr ->
    machine_diverges_silently (compile_program c) s g tr) ->
  (forall c s g tr,
    machine_diverges_silently (compile_program c) s g tr ->
    imp_diverges_silently c s g tr).
Proof.
  intros.
  specialize (imp_terminates_or_diverges c s g); intros.
  destruct H1 as [ (tr'' & s'' & g'' & H1) | [ (tr' & H1) | (itr' & H1) ] ].
  - apply compile_program_correct_terminating in H1.
    unfold machine_terminates, machine_diverges_silently in *. destruct H1 as (pc & H1).
    exfalso.
    eapply (diverges_silently_finseq_excl (deterministic_onestep' (compile_program c))).
    + eapply H1.
    + unfold irred; intros; eapply no_trans_from_Ihalt; easy.
    + eapply H0.     
  - pose proof H1. apply H in H1.
    eapply deterministic_diverges_silently in H1; try eapply H0. rewrite H1; trivial.
  - apply compile_program_correct_diverging_with_inftrace in H1. 
    unfold machine_diverges_with_inftrace, machine_diverges_silently in *. 
    exfalso.
    eapply (diverges_silently_with_inftrace_excl (deterministic_onestep' (compile_program c))); eauto.   
Qed.

Lemma forward_implies_backward_diverging_with_inftrace:
  (forall c s g itr,
    imp_diverges_with_inftrace c s g itr ->
    machine_diverges_with_inftrace (compile_program c) s g itr) ->
  (forall c s g itr itr',
    machine_diverges_with_inftrace (compile_program c) s g itr' ->
    imp_diverges_with_inftrace c s g itr ->
    EqSt itr itr').
Proof.
  intros.
  specialize (imp_terminates_or_diverges c s g); intros.
  destruct H2 as [ (tr'' & s'' & g'' & H2) | [ (tr' & H2) | (itr'' & H2) ] ].
  - apply compile_program_correct_terminating in H2.
    unfold machine_terminates, machine_diverges_silently in *. destruct H2 as (pc & H2).
    exfalso.
    eapply (diverges_with_inftrace_finseq_excl (deterministic_onestep' (compile_program c))).
    + eapply H2.
    + unfold irred; intros; eapply no_trans_from_Ihalt; easy.
    + eapply H0.     
  - apply compile_program_correct_diverging_silently in H2. 
    unfold machine_diverges_with_inftrace, machine_diverges_silently in *. 
    exfalso.
    eapply (diverges_silently_with_inftrace_excl (deterministic_onestep' (compile_program c))); eauto.   
  - pose proof H2. eapply H in H2.
    assert (EqSt itr itr'') by eauto using (deterministic_diverges_with_inftrace).
    assert (EqSt itr' itr'') by eauto using (deterministic_diverges_with_inftrace).
    eapply trans_EqSt; eauto using sym_EqSt.
Qed.

(** Backward simulation between IMP and stack machine under the
deterministic semantics, for all three valid behaviors. *)

Theorem compile_program_correct_terminating_backward:
  forall c s g tr s' g',
    machine_terminates (compile_program c) s g tr s' g' ->
    imp_terminates c s g tr s' g'.
Proof.
  eauto using forward_implies_backward_terminating, compile_program_correct_terminating.
Qed.

Theorem compile_program_correct_diverging_silently_backward:
  forall c s g tr,
    machine_diverges_silently (compile_program c) s g tr ->
    imp_diverges_silently c s g tr.
Proof.
  eauto using forward_implies_backward_diverging_silently, compile_program_correct_diverging_silently.
Qed.

Theorem compile_program_correct_diverging_with_inftrace_backward:
  forall c s g itr itr',
    machine_diverges_with_inftrace (compile_program c) s g itr ->
    imp_diverges_with_inftrace c s g itr' -> EqSt itr itr'.
Proof.
  intros. apply sym_EqSt. 
  eapply forward_implies_backward_diverging_with_inftrace; eauto.
  eapply compile_program_correct_diverging_with_inftrace.
Qed.

(** Since IMP never goes wrong, and the compiler is correct for each
step, compiled IMP programs can never get stuck. *)
Theorem compile_program_never_goes_wrong:
  forall c s g tr,
    ~machine_goes_wrong (compile_program c) s g tr.
Proof. 
  intros.
  specialize (imp_terminates_or_diverges c s g).
  intros.
  destruct H as [ (tr' & s' & g' & H) | [ (tr' & H) | (itr' & H) ] ].
  - apply compile_program_correct_terminating in H. intuition.
    unfold machine_terminates, machine_goes_wrong in *.
    destruct H as (pc & Htrans & Hins).
    destruct H0 as (pc0 & stk0 & s0 & g0 & Htrans0 & Hirred0 & Hinsstk0).
    eapply star_star_inv in Htrans; eauto using deterministic_onestep', Htrans0.
    destruct Htrans.
    + destruct H as (t & Hprefix & Happtr).
      inversion Hprefix; subst;
        solve [ destruct Hinsstk0; easy | eapply Hirred0; eauto ].
    + destruct H as (t & Hprefix & Happtr). subst.
      inversion Hprefix; subst;
        solve [ destruct Hinsstk0; easy | eapply no_trans_from_Ihalt; eauto ].
  - apply compile_program_correct_diverging_silently in H. intuition.
    unfold machine_diverges_silently, machine_goes_wrong in *.
    destruct H0 as (pc' & stk' & s' & g' & Htrans & Hirred & Hinsstk).
    eapply diverges_silently_finseq_excl; eauto using deterministic_onestep'.
  - apply compile_program_correct_diverging_with_inftrace in H. intuition.
    unfold machine_diverges_with_inftrace, machine_goes_wrong in *.
    destruct H0 as (pc' & stk' & s' & g' & Htrans & Hirred & Hinsstk).
    eapply diverges_with_inftrace_finseq_excl; eauto using deterministic_onestep'.
Qed.


(** Backward simulation for prefixes of executions. *)
Lemma compile_program_correct_infseq_prefix:
  forall machconf1 c (tr : list event) (machconf2 : config),
    transitions (compile_program c) machconf1 tr machconf2 ->
    forall impconf1 itr',
      infseq_with_inftrace step impconf1 itr' ->
      infseq_with_inftrace (transition (compile_program c)) machconf1 itr' ->
      exists impconf2 : impstate, star step impconf1 tr impconf2.
Proof.
  induction 1; intros. 
  - exists impconf1. constructor.
  - eapply IHstar; eauto.
    assert (star (transition (compile_program c)) a [] b) by eauto using star. 
    eapply star_infseq_with_inftrace_inv in H3; eauto using (deterministic_onestep' (compile_program c)).
    destruct H3 as (itr'' & ? & ?). cbn in H4. subst. eauto.
  - assert (star (transition (compile_program c)) a [e] b) by eauto using star.
    eapply star_infseq_with_inftrace_inv in H3; eauto using (deterministic_onestep' (compile_program c)).
    destruct H3 as (itr'' & ? & ?); subst.
    pose proof H1.
    eapply infseq_with_inftrace_star_inv with (t := [e]) in H1; eauto using imp_deterministic_onestep'.
    destruct H1 as (b' & ?).
    eapply star_infseq_with_inftrace_inv with (t := [e]) in H4; eauto using imp_deterministic_onestep'.
    destruct H4 as (it' & ? & ?). cbn in H5; inversion H5; subst. 
    specialize (IHstar _ _ H4 H3). destruct IHstar as (impconf2 & ?).
    exists impconf2. replace (e :: t) with ([e] ++ t) by eauto. eapply star_trans; eauto. 
Qed.

Theorem compile_program_correct_admits_finite:
  forall c s g tr machconf2,
    transitions (compile_program c) (0, nil, s, g) tr machconf2 ->
    exists impconf2,
      star step (c, Kstop, s, g) tr impconf2.
Proof.
  intros. 
  destruct (imp_terminates_or_diverges c s g) as
      [ (tr' & s' & g' & Hstar) | [ (tr' & Hinf) | (itr' & Hinf) ] ].
  - pose proof Hstar.
    apply compile_program_correct_terminating in H0. destruct H0 as (pc' & Htrans & Hins).
    assert (irred (transition (compile_program c)) (pc', [], s', g')).
    { unfold irred. intros. now apply no_trans_from_Ihalt. }
    eapply star_star_inv in Htrans; try eapply H; try eapply (deterministic_onestep' (compile_program c)).
    unfold imp_terminates in Hstar.
    destruct Htrans as [ (t & Ht & Happt) | (t & Ht & Happt) ].
    + eapply star_int in Hstar; eauto.
    + inversion Ht; subst; try solve [ exfalso; eapply no_trans_from_Ihalt in H1; eauto ].
      exists (SKIP, Kstop, s', g'); rewrite app_nil_r; eauto.
  - unfold imp_diverges_silently, diverges_silently in Hinf. destruct Hinf as (impconf2' & Hstar & Hinf).
    pose proof Hstar. eapply simulation_steps' in H0; try eapply match_initial_configs.
    destruct H0 as (machconf2' & Htrans' & Hmatch).
    eapply infseq_silent_preserved_forward in Hinf; eauto. 
    eapply (star_star_inv (deterministic_onestep' (compile_program c))) in Htrans'; try eapply H.
    destruct Htrans' as [ (t & Ht & Happt) | (t & Ht & Happt) ].
    + eapply star_int in Hstar; eauto.
    + apply (infseq_silent_star_inv' (deterministic_onestep' (compile_program c))) in Ht; eauto.
      rewrite Ht in Happt. rewrite app_nil_r in Happt. rewrite <- Happt in Hstar; eauto. 
  - pose proof Hinf. apply compile_program_correct_diverging_with_inftrace in H0. 
    unfold imp_diverges_with_inftrace, machine_diverges_with_inftrace in *.
    eapply compile_program_correct_infseq_prefix; eauto.
Qed.    

End Determ.
