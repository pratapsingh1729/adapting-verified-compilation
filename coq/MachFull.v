From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality Streams.
Require Import Sequences IMP Compil MachDeterm.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** We add nondeterministic interruption to the deterministic
    semantics, obtaining the full semantics for the machine. *)

(* States of the stack machine under full semantics. For simplicity,
we assume that interruption causes the program to step to a special
Intr configuration in one step. *)
Inductive config : Type :=
| OK: Determ.config -> config
| Intr: config.
Notation "$( pc , stk , s , g )" := (OK (pc, stk, s, g)).

(* Operational semantics of the stack machine: either the machine
steps according to the deterministic semantics, or it is
interrupted. *)
Inductive transition (C: code): config -> option event -> config -> Prop :=
| trans_determ : forall conf conf' eopt,
    Determ.transition C conf eopt conf' ->
    transition C (OK conf) eopt (OK conf')
| trans_intr : forall conf,
    transition C (OK conf) (Some ev_intr) Intr.  

Definition transitions (C: code): config -> list event -> config -> Prop :=
  star (transition C).

(** The machine terminates normally on an Ihalt instruction, emitting trace tr. *)
Definition machine_terminates_ok (C: code) (s_init: store) (g_init: global_state)
           (tr: trace) (s_final: store) (g_final: global_state) : Prop :=
  exists pc, transitions C $(0, nil, s_init, g_init) tr $(pc, nil, s_final, g_final)
         /\ instr_at C pc = Some Ihalt.

(** The machine emits trace tr and is then interrupted. *)
Definition machine_intr (C: code) (s_init: store) (g_init: global_state)
           (tr : trace): Prop :=
  transitions C $(0, nil, s_init, g_init) tr Intr. 

(** The machine emits trace tr then diverges silently. *)
Definition machine_diverges_silently
           (C: code) (s_init: store) (g_init: global_state) (tr: trace) : Prop :=
  diverges_silently (transition C) $(0, nil, s_init, g_init) tr.

(** The machine diverges with an infinte sequence of events itr. *)
Definition machine_diverges_with_inftrace (C: code) (s_init: store)
           (g_init: global_state) (itr: inftrace) : Prop :=
  infseq_with_inftrace (transition C) $(0, nil, s_init, g_init) itr.

(** The machine gets "stuck": it reaches a state from which it cannot
step but whose current instruction is not Ihalt.  *)
Definition machine_goes_wrong (C: code) (s_init: store) (g_init: global_state)
           (tr: trace) : Prop :=
  exists pc stk s g,
      transitions C $(0, nil, s_init, g_init) tr $(pc, stk, s, g)
   /\ irred (transition C) $(pc, stk, s, g)
   /\ (instr_at C pc <> Some Ihalt \/ stk <> nil).

(** The machine emits trace tr, then reaches a state from which no
further steps are possible. *)
Definition machine_terminates (C: code) (s_init: store) (g_init: global_state)
           (tr: trace) : Prop :=
    exists config', transitions C $(0, nil, s_init, g_init) tr config'
               /\ irred (transition C) config'.

(* If the machine terminates, it must have either terminated normally,
been interrupted, or gotten stuck. *)
Lemma machine_terminates_ok_intr_or_wrong: forall C s g tr,
    machine_terminates C s g tr ->
    (exists s' g', machine_terminates_ok C s g tr s' g') \/
    (machine_intr C s g tr) \/
    (machine_goes_wrong C s g tr).
Proof.
  intros. inversion H as (conf' & Htrans & Hirred); subst. 
  destruct conf'.
  - destruct c as [[[pc' stk'] s'] g'].
    destruct (instr_at C pc') eqn:E; try destruct i;
      try (right; right; repeat eexists; eauto; left; congruence).
    destruct stk'.
    + left. repeat eexists; eauto.
    + right; right; repeat eexists; eauto; right; congruence. 
  - right; left. now unfold machine_intr. 
Qed.

Lemma no_trans_from_intr : forall C eopt config,
    ~(transition C Intr eopt config).
Proof.
  intuition; inversion H.
Qed.

Lemma intr_irred : forall C,
    irred (transition C) Intr.
Proof.
  unfold irred. auto using no_trans_from_intr.
Qed.


(** Proof of modified backward simulation between machine under
deterministic semantics and machine under full semantics. We show that
if the machine admits trace tr under full semantics, then either it
admits trace tr under deterministic semantics, or tr is a prefix of
some tr' followed by interruption and the machine admits tr' under
deterministic semantics. *)

(* Some helper lemmas *)
Lemma determ_implies_full_one: forall C conf eopt conf',
    Determ.transition C conf eopt conf' ->
    transition C (OK conf) eopt (OK conf').
Proof.
  econstructor; eauto. 
Qed.

Lemma determ_implies_full: forall C conf tr conf',
    Determ.transitions C conf tr conf' ->
    transitions C (OK conf) tr (OK conf').
Proof.
  induction 1.
  - econstructor.
  - econstructor; eauto using transition.
  - eapply star_step_ev; eauto using transition.
Qed.

Lemma full_OK_implies_determ_one: forall C conf eopt conf',
    transition C (OK conf) eopt (OK conf') ->
    Determ.transition C conf eopt conf'.
Proof.
  inversion 1; subst; trivial.
Qed.

Lemma full_OK_implies_determ: forall C conf tr conf',
    transitions C (OK conf) tr (OK conf') ->
    Determ.transitions C conf tr conf'.
Proof.
  intros until 1; dependent induction H. 
  - econstructor.
  - destruct b.
    + specialize (IHstar c conf').
      apply star_step with (b := c).
      now apply full_OK_implies_determ_one.
      now apply IHstar.
    + inversion H.
  - destruct b.
    + specialize (IHstar c conf').
      apply star_step_ev with (b := c).
      now apply full_OK_implies_determ_one.
      now apply IHstar.
    + exfalso. inversion H0; subst; inversion H1.
Qed.

Lemma full_OK_implies_determ_plus: forall C conf tr conf',
    plus (transition C) (OK conf) tr (OK conf') ->
    plus (Determ.transition C) conf tr conf'.
Proof.
  intros. inversion H. 
  - destruct b.
    + apply plus_left with (b := c0).
      now apply full_OK_implies_determ_one.
      now apply full_OK_implies_determ. 
    + inversion H1; inversion H5. 
 - destruct b.
    + apply plus_left_ev with (b := c0).
      now apply full_OK_implies_determ_one.
      now apply full_OK_implies_determ. 
    + inversion H1; inversion H5.
Qed.

Lemma irred_implies_determ_irred: forall C conf,
    irred (transition C) (OK conf) -> irred (Determ.transition C) conf. 
Proof.
  intros.
  unfold irred in *. intros.
  specialize (H (OK b) eo). intuition.
  apply H. now apply determ_implies_full_one. 
Qed. 

Definition wrong_implies_determ_wrong: forall C s g tr,
    machine_goes_wrong C s g tr ->
    Determ.machine_goes_wrong C s g tr.
Proof.
  intros. unfold machine_goes_wrong in H. unfold Determ.machine_goes_wrong. 
  destruct H as (pc' & stk' & s' & g' & Htrans & Hirred & Hinsstk).
  exists pc', stk', s', g'. 
  repeat split.
  - now apply full_OK_implies_determ.
  - now apply irred_implies_determ_irred.
  - easy.
Qed. 

Local Hint Constructors step Determ.transition transition star plus : code.
Local Hint Unfold imp_terminates imp_diverges_silently imp_diverges_with_inftrace
      Determ.machine_terminates Determ.machine_diverges_silently Determ.machine_diverges_with_inftrace
      Determ.transitions machine_terminates machine_diverges_silently machine_diverges_with_inftrace transitions : code.
Local Hint Resolve full_OK_implies_determ wrong_implies_determ_wrong irred_implies_determ_irred : code.

Lemma full_Intr_implies_prefix_OK: forall C conf tr,
    transitions C (OK conf) tr Intr ->
    exists conf' tr', transitions C (OK conf) tr' (OK conf') /\
                 transition C (OK conf') (Some ev_intr) Intr /\
                 tr = tr' ++ [ev_intr].
Proof.
  intros until 1; dependent induction H; intros.
  - destruct b.
    + assert (OK c = OK c) by congruence. assert (Intr = Intr) by congruence.
      specialize (IHstar c H1 H2).
      destruct IHstar as (conf' & tr' & Hok & Hintr & Ht).
      exists conf', tr'. split; eauto 10. econstructor; eauto.
    + inversion H.
  - destruct b.
    + assert (OK c = OK c) by congruence. assert (Intr = Intr) by congruence.
      specialize (IHstar c H1 H2).
      destruct IHstar as (conf' & tr' & Hok & Hintr & Ht).
      exists conf', (e :: tr'). repeat split; eauto 10. eapply star_step_ev; eauto.
      rewrite Ht. now apply app_comm_cons.
    + inversion H; subst.
      exists conf, []. repeat split. econstructor. eauto.
      cbn. inversion H0; subst; auto; inversion H1. 
Qed.

(** Modified backward simulation between deterministic and full
semantics, for all three valid behaviors. *)
Theorem prefix_correct_full_to_determ_semantics: forall C s g tr,
    machine_terminates C s g tr ->
    (exists s' g', Determ.machine_terminates C s g tr s' g')
    \/ (exists m, tr = m ++ [ev_intr] /\ Determ.machine_admits_finite C s g m)
    \/ (Determ.machine_goes_wrong C s g tr).
Proof.
  intros.
  apply machine_terminates_ok_intr_or_wrong in H. destruct H; [ | destruct H ].
  - left. destruct H as (s' & g' & H). exists s', g'.
    unfold machine_terminates_ok in H. unfold Determ.machine_terminates.
    destruct H as (pc & Htrans & Hinstr).
    exists pc; split; eauto using full_OK_implies_determ. 
  - right; left. unfold machine_intr in H.
    apply full_Intr_implies_prefix_OK in H.
    destruct H as (conf' & tr' & Hok & Hintr & Htr). exists tr'; split; auto.
    unfold Determ.machine_admits_finite. exists conf'.
    eauto using full_OK_implies_determ.     
  - right; right; auto using wrong_implies_determ_wrong.
Qed.

Lemma divergence_implies_determ_divergence_silent: forall C s g tr,
    machine_diverges_silently C s g tr ->
    Determ.machine_diverges_silently C s g tr.
Proof.  
  unfold Determ.machine_diverges_silently, machine_diverges_silently, diverges_silently. intros. 
  destruct H as (b & Hstar & Hinf). destruct b.
  - exists c. split. now apply full_OK_implies_determ.
    assert (forall C c, infseq_silent (transition C) (OK c) -> infseq_silent (Determ.transition C) c). {
      clear. cofix CIH; intros.
      inversion H; subst. destruct b; inversion H0; subst.
      econstructor; eauto.
    }
    eauto.
  - inversion Hinf. inversion H.
Qed. 

Lemma divergence_implies_determ_divergence_inftrace: forall C s g itr,
    machine_diverges_with_inftrace C s g itr ->
    Determ.machine_diverges_with_inftrace C s g itr.
Proof.  
  unfold machine_diverges_with_inftrace, Determ.machine_diverges_with_inftrace. intros.
  apply infseq_with_inftrace_coinduction_principle with
      (X := fun conf tr => infseq_with_inftrace (transition C) (OK conf) tr); auto.
  intros. inversion H0; subst.
  destruct b.
  - exists c, t0, it. repeat split; auto using full_OK_implies_determ_plus.
  - inversion H3; subst. inversion H4; subst; inversion H7. 
Qed. 


(** Top-level compiler correctness theorems for all three types of behavior. *)
Theorem compile_program_correct_terminating: forall c s g tr,
    machine_terminates (compile_program c) s g tr ->
    (exists s' g', imp_terminates c s g tr s' g')
    \/ (exists m, tr = m ++ [ev_intr] /\ imp_admits_finite c s g m).
Proof.
  intros.
  apply prefix_correct_full_to_determ_semantics in H. destruct H; [ | destruct H ].
  - left. destruct H as (s' & g' & Hdet). exists s', g'.
    now apply Determ.compile_program_correct_terminating_backward. 
  - right. destruct H as (m & Htr & Hdet). exists m; split; auto.
    unfold Determ.machine_admits_finite in Hdet. destruct Hdet as (machconf2 & Hdet).    
    apply Determ.compile_program_correct_admits_finite in Hdet. 
    destruct Hdet as (impconf2 & Hstep).
    unfold imp_admits_finite. eauto. 
  - now apply Determ.compile_program_never_goes_wrong in H. 
Qed. 

Theorem compile_program_correct_diverging_silently: forall c s g tr,
    machine_diverges_silently (compile_program c) s g tr ->
    imp_diverges_silently c s g tr. 
Proof.
  intros.
  apply Determ.compile_program_correct_diverging_silently_backward. 
  now apply divergence_implies_determ_divergence_silent. 
Qed. 

Theorem compile_program_correct_diverging_with_inftrace: forall c s g itr itr',
    machine_diverges_with_inftrace (compile_program c) s g itr ->
    imp_diverges_with_inftrace c s g itr' -> EqSt itr itr'.  
Proof.
  intros.
  eapply Determ.compile_program_correct_diverging_with_inftrace_backward.
  eapply divergence_implies_determ_divergence_inftrace; eauto.
  eauto.
Qed. 
