From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality Streams.
Require Import Sequences.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** The source language: IMP *)

Definition ident := string.
Definition store : Type := ident -> Z.

(** Arithmetic expressions *)

Inductive aexp : Type :=
  | CONST (n: Z)
  | VAR (x: ident)
  | PLUS (a1: aexp) (a2: aexp)
  | MINUS (a1: aexp) (a2: aexp).

Fixpoint aeval (s: store) (a: aexp) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval s a1 + aeval s a2
  | MINUS a1 a2 => aeval s a1 - aeval s a2
  end.

(** Boolean expressions *)

Inductive bexp : Type :=
  | TRUE
  | FALSE
  | EQUAL (a1: aexp) (a2: aexp)
  | LESSEQUAL (a1: aexp) (a2: aexp)
  | NOT (b1: bexp)
  | AND (b1: bexp) (b2: bexp).

Fixpoint beval (s: store) (b: bexp) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval s a1 =? aeval s a2
  | LESSEQUAL a1 a2 => aeval s a1 <=? aeval s a2
  | NOT b1 => negb (beval s b1)
  | AND b1 b2 => beval s b1 && beval s b2
  end.

(** Commands *)

Inductive com: Type :=
  | SKIP
  | ASSIGN (x: ident) (a: aexp)
  | SEQ (c1: com) (c2: com)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com)
  | WHILE (b: bexp) (c1: com)
  | INPUT (x: ident)
  | OUTPUT (a: aexp).
  
Infix ";;" := SEQ (at level 80, right associativity).

Definition update (x: ident) (v: Z) (s: store) : store :=
  fun y => if string_dec x y then v else s y.


(** Small-step semantics for IMP *)

Inductive cont : Type :=
  | Kstop
  | Kseq (c: com) (k: cont)
  | Kwhile (b: bexp) (c: com) (k: cont).

Fixpoint apply_cont (k: cont) (c: com) : com :=
  match k with
  | Kstop => c
  | Kseq c1 k1 => apply_cont k1 (SEQ c c1)
  | Kwhile b1 c1 k1 => apply_cont k1 (SEQ c (WHILE b1 c1))
  end.

(* States of the IMP operational syntax *)
Definition impstate := (com * cont * store * global_state)%type.

Inductive step: impstate -> option event -> impstate -> Prop :=

  | step_assign: forall x a k s g,
      step (ASSIGN x a, k, s, g) None (SKIP, k, update x (aeval s a) s, g)

  | step_seq: forall c1 c2 s k g,
      step (SEQ c1 c2, k, s, g) None (c1, Kseq c2 k, s, g)

  | step_ifthenelse: forall b c1 c2 k s g,
      step (IFTHENELSE b c1 c2, k, s, g) None ((if beval s b then c1 else c2), k, s, g)

  | step_while_done: forall b c k s g,
      beval s b = false ->
      step (WHILE b c, k, s, g) None (SKIP, k, s, g)

  | step_while_true: forall b c k s g,
      beval s b = true ->
      step (WHILE b c, k, s, g) None (c, Kwhile b c k, s, g)

  | step_skip_seq: forall c k s g,
      step (SKIP, Kseq c k, s, g) None (c, k, s, g)

  | step_skip_while: forall b c k s g,
      step (SKIP, Kwhile b c k, s, g) None (WHILE b c, k, s, g)

  | step_input: forall x k s g z g',
      (z, g') = take_input g ->
      step (INPUT x, k, s, g) (Some (ev_input z)) (SKIP, k, update x z s, g')

  | step_output: forall a k s g z,
      aeval s a = z ->
      step (OUTPUT a, k, s, g) (Some (ev_output z)) (SKIP, k, s, produce_output g z).

(* Command c, starting with store s and world g, terminates normally
with final store s' and final world g', emitting trace tr. *)
Definition imp_terminates c s g tr s' g' : Prop := 
  star step (c, Kstop, s, g) tr (SKIP, Kstop, s', g').

(* Command c, starting with store s and world g, emits (finite) trace
tr then diverges silently. *)
Definition imp_diverges_silently c s g tr : Prop :=
  diverges_silently step (c, Kstop, s, g) tr.

(* Command c, starting with store s and world g, diverges and emits
infinite sequence of events itr. *)
Definition imp_diverges_with_inftrace c s g itr : Prop :=
  infseq_with_inftrace step (c, Kstop, s, g) itr.

(* Command c, starting with store s and world g, emits trace tr then
reaches a "stuck" state where no further steps are possible but the
current command is not SKIP. (We later prove this case is
impossible by construction in IMP.) *)
Definition imp_goes_wrong c s g tr : Prop :=
  exists c' k' s' g',
    star step (c, Kstop, s, g) tr (c', k', s', g')
    /\ irred step (c', k', s', g')
    /\ c' <> SKIP.

(* Command c, starting with store s and world g, can execute for a
finite number of steps and emit trace tr. *)
Definition imp_admits_finite (c: com) (s: store) (g: global_state) (tr: trace) : Prop :=
  exists impconf, star step (c, Kstop, s, g) tr impconf. 

Local Hint Unfold imp_terminates imp_diverges_silently imp_diverges_with_inftrace : code. 
Local Hint Constructors star plus step : code.
Local Hint Resolve app_nil_r app_nil_l app_comm_cons : code. 

(** Determinism properties for IMP. *)

Lemma imp_deterministic_onestep:
  forall c k s g c1 k1 s1 g1 eo1,
    step (c, k, s, g) eo1 (c1, k1, s1, g1) ->
    forall c2 k2 s2 g2 eo2,
      step (c, k, s, g) eo2 (c2, k2, s2, g2) ->
      c1 = c2 /\ k1 = k2 /\ s1 = s2 /\ g1 = g2 /\ eo1 = eo2.
Proof.
  intros until 1; dependent induction H; intros;
    match goal with
    | Hs: step _ _ _ |- _ => inversion Hs; subst; try congruence
    end; try solve [repeat split]. 
  - rewrite <- H in H6. inversion H6; subst. repeat split.
Qed.

Lemma imp_deterministic_onestep':
  forall ist ist1 ist2 eo1 eo2,
    step ist eo1 ist1 ->
    step ist eo2 ist2 ->
    ist1 = ist2 /\ eo1 = eo2.
Proof.
  intros.
  destruct ist as [[[c k] s] g].
  destruct ist1 as [[[c1 k1] s1] g1].
  destruct ist2 as [[[c2 k2] s2] g2].
  eapply imp_deterministic_onestep in H0; try eapply H.
  destruct H0 as (H1 & H2 & H3 & H4 & H5).
  subst; split; trivial.
Qed.

Lemma imp_deterministic_star:
  forall c k s g s1 g1 tr1,
    star step (c, k, s, g) tr1 (SKIP, Kstop, s1, g1) ->
    forall s2 g2 tr2,
      star step (c, k, s, g) tr2 (SKIP, Kstop, s2, g2) ->
      tr1 = tr2 /\ s1 = s2 /\ g1 = g2.
Proof.
  intros until 1; dependent induction H; intros. 
  - inversion H; subst; eauto; inversion H0.
  - destruct b as [[[c' k'] s'] g']. 
    inversion H1; subst.
    + inversion H.
    + eapply imp_deterministic_onestep' in H2; [ | apply H ].
      destruct H2; rewrite <- H2 in *.
      eapply IHstar; eauto. 
    + eapply imp_deterministic_onestep' in H2; [ | apply H ].
      destruct H2; discriminate.
  - destruct b as [[[c' k'] s'] g']. 
    inversion H1; subst.
    + inversion H.
    + eapply imp_deterministic_onestep' in H2; [ | apply H ].
      destruct H2; discriminate.
    + eapply imp_deterministic_onestep' in H2; [ | apply H ].
      destruct H2; rewrite <- H2 in *. injection H4; intros; subst.
      assert (t = t0 /\ s1 = s2 /\ g1 = g2); eauto. 
      destruct H2 as [H2 [H2' H2'']]; subst; repeat split.     
Qed. 

Lemma imp_deterministic_infseq_with_inftrace:
  forall c k s g tr1,
    infseq_with_inftrace step (c, k, s, g) tr1 ->
    forall tr2,
      infseq_with_inftrace step (c, k, s, g) tr2 ->
      EqSt tr1 tr2.
Proof.
  intros.
  eapply deterministic_infseq_with_inftrace; eauto using imp_deterministic_onestep'.
Qed. 
  
Theorem imp_deterministic_terminates:
  forall c s g tr1 s1 g1,
    imp_terminates c s g tr1 s1 g1 ->
    forall tr2 s2 g2,
      imp_terminates c s g tr2 s2 g2 ->
      tr1 = tr2 /\ s1 = s2 /\ g1 = g2.
Proof.
  unfold imp_terminates; intros.
  eapply imp_deterministic_star in H0; eauto.
Qed.

(** "Progress" lemmas for IMP. The IMP language is simple enough that
it never gets stuck by construction. A more complex source language
could use a type system to achieve these guarantees.  *)

Lemma imp_progress_onestep: forall c k s g,
    (exists eo c' k' s' g', step (c, k, s, g) eo (c', k', s', g')) \/ (c = SKIP /\ k = Kstop).
Proof.
  induction c; intros; try solve [ left; repeat eexists; econstructor ].
  - destruct k; try (now right); left; repeat eexists; econstructor. 
  - left. destruct (beval s b) eqn:E; repeat eexists.
    + now eapply step_while_true. 
    + now eapply step_while_done.
  - destruct (take_input g) as (z, g') eqn:E. left.
    exists (Some (ev_input z)), SKIP, k, (update x z s), g'. now constructor.
  - set (z := aeval s a). left.
    exists (Some (ev_output z)), SKIP, k, s, (produce_output g z). now constructor.
Qed.

Lemma imp_progress_star: forall c k s g,
    (exists t c' k' s' g', star step (c, k, s, g) t (c', k', s', g')).
Proof.
  intros; destruct (imp_progress_onestep c k s g).
  - destruct H as (eo & c' & k' & s' & g' & H). destruct eo.
    + exists [e]. repeat eexists; eapply star_step_ev; [ eauto | eapply star_refl ].
    + exists []. repeat eexists; eapply star_step; [ eauto | eapply star_refl ].
  - repeat eexists; eapply star_refl.
Qed.

Lemma imp_irred_is_skip: forall c k s g,
    irred step (c, k, s, g) -> c = SKIP /\ k = Kstop.
Proof.
  intros. destruct (imp_progress_onestep c k s g); auto. 
  exfalso. unfold irred in H. intuition.
  destruct H0 as (eo & c' & k' & s' & g' & H0). eapply H; eapply H0.
Qed.

(* Starting in any configuration, IMP either terminates normally,
diverges silently, or diverges with an infinite trace. *)
Theorem imp_behaves: forall c k s g,
  ((exists tr s' g', star step (c, k, s, g) tr (SKIP, Kstop, s', g'))
   \/ (exists tr, diverges_silently step (c, k, s, g) tr)
   \/ (exists itr, infseq_with_inftrace step (c, k, s, g) itr)).
Proof.
  intros.
  specialize (infseq_or_finseq step (c, k, s, g)); intro.
  destruct H; [ | destruct H ]. 
  - left. destruct H as (t & b & H & H'); destruct b as [[[c' k'] s'] g'].
    destruct (imp_irred_is_skip _ _ _ _ H'); subst. eauto.
  - right; left; eauto.
  - right; right; eauto. 
Qed.

(* Specialization of imp_behaves for executions beginning in a
starting state. *)
Theorem imp_terminates_or_diverges: forall c s g,
    (exists tr s' g', imp_terminates c s g tr s' g') \/
    (exists tr, imp_diverges_silently c s g tr) \/
    (exists itr, imp_diverges_with_inftrace c s g itr).
Proof.
  intros. unfold imp_terminates, imp_diverges_silently, imp_diverges_with_inftrace.
  eapply imp_behaves. 
Qed.

Theorem imp_never_goes_wrong: forall c s g tr,
    ~(imp_goes_wrong c s g tr).
Proof.
  intros. intuition. unfold imp_goes_wrong in H.
  destruct H as (c' & k' & s' & g' & Hstar & Hirred & Hc').
  apply imp_irred_is_skip in Hirred. destruct Hirred; congruence.
Qed.
