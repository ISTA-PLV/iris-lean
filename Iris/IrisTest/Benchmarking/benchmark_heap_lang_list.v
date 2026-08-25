From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Local Definition nil : val := NONEV.
Local Definition cons : val := λ: "l", SOME(ref "l").
Local Definition llength : val := λ: "l", #0.

Fixpoint makeList2 (ls : list Z) (cont : expr -> expr) : expr :=
  match ls with
  | [] => cont nil
  | l::ls => makeList2 ls (fun e =>
               let: "vls" := e in cont (cons (#l, "vls")))%E
  end.

Definition buildList (ls : list Z) : expr :=
  makeList2 ls (fun e =>
  let: "v" := e in
  llength "v")%E.

Section proof.
  Context `{!heapGS_gen hlc Σ}.

  Definition isList (v : val) (l : list Z) : iProp Σ. Admitted.
  Lemma isList_nil : ⊢ isList nil []. Admitted.

  Lemma nil_spec (Phi : val -> iProp Σ) :
    (∀ v, isList v [] -∗ Phi v) -∗
    WP Val nil {{ Phi }}.
  Proof. Admitted.

  Lemma cons_spec v x l (Phi : val -> iProp Σ) :
    isList v l -∗
    (∀ w, isList w (x::l) -∗ Phi w) -∗
    WP cons (#x, v)%V {{ Phi }}.
  Proof. Admitted.

  Lemma length_spec v l (Phi : val -> iProp Σ) :
    isList v l -∗
    (∀ w, isList w l -∗ ⌜ w = #(length l) ⌝ -∗ Phi w) -∗
    WP llength v {{ Phi }}.
  Proof. Admitted.

  Lemma wp_buildList_10 :
    ⊢@{iProp Σ} WP (buildList (replicate 10 1%Z)) {{ v, ⌜ v = #(10%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 10".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_20 :
    ⊢@{iProp Σ} WP (buildList (replicate 20 1%Z)) {{ v, ⌜ v = #(20%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 20".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_30 :
    ⊢@{iProp Σ} WP (buildList (replicate 30 1%Z)) {{ v, ⌜ v = #(30%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 30".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_40 :
    ⊢@{iProp Σ} WP (buildList (replicate 40 1%Z)) {{ v, ⌜ v = #(40%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 40".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_50 :
    ⊢@{iProp Σ} WP (buildList (replicate 50 1%Z)) {{ v, ⌜ v = #(50%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 50".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_60 :
    ⊢@{iProp Σ} WP (buildList (replicate 60 1%Z)) {{ v, ⌜ v = #(60%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 60".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_70 :
    ⊢@{iProp Σ} WP (buildList (replicate 70 1%Z)) {{ v, ⌜ v = #(70%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 70".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_80 :
    ⊢@{iProp Σ} WP (buildList (replicate 80 1%Z)) {{ v, ⌜ v = #(80%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 80".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_90 :
    ⊢@{iProp Σ} WP (buildList (replicate 90 1%Z)) {{ v, ⌜ v = #(90%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 90".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_100 :
    ⊢@{iProp Σ} WP (buildList (replicate 100 1%Z)) {{ v, ⌜ v = #(100%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 100".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_110 :
    ⊢@{iProp Σ} WP (buildList (replicate 110 1%Z)) {{ v, ⌜ v = #(110%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 110".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_120 :
    ⊢@{iProp Σ} WP (buildList (replicate 120 1%Z)) {{ v, ⌜ v = #(120%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 120".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_130 :
    ⊢@{iProp Σ} WP (buildList (replicate 130 1%Z)) {{ v, ⌜ v = #(130%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 130".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_140 :
    ⊢@{iProp Σ} WP (buildList (replicate 140 1%Z)) {{ v, ⌜ v = #(140%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 140".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_150 :
    ⊢@{iProp Σ} WP (buildList (replicate 150 1%Z)) {{ v, ⌜ v = #(150%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 150".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_160 :
    ⊢@{iProp Σ} WP (buildList (replicate 160 1%Z)) {{ v, ⌜ v = #(160%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 160".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_170 :
    ⊢@{iProp Σ} WP (buildList (replicate 170 1%Z)) {{ v, ⌜ v = #(170%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 170".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_180 :
    ⊢@{iProp Σ} WP (buildList (replicate 180 1%Z)) {{ v, ⌜ v = #(180%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 180".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_190 :
    ⊢@{iProp Σ} WP (buildList (replicate 190 1%Z)) {{ v, ⌜ v = #(190%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 190".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_200 :
    ⊢@{iProp Σ} WP (buildList (replicate 200 1%Z)) {{ v, ⌜ v = #(200%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 200".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_210 :
    ⊢@{iProp Σ} WP (buildList (replicate 210 1%Z)) {{ v, ⌜ v = #(210%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 210".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_220 :
    ⊢@{iProp Σ} WP (buildList (replicate 220 1%Z)) {{ v, ⌜ v = #(220%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 220".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_230 :
    ⊢@{iProp Σ} WP (buildList (replicate 230 1%Z)) {{ v, ⌜ v = #(230%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 230".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_240 :
    ⊢@{iProp Σ} WP (buildList (replicate 240 1%Z)) {{ v, ⌜ v = #(240%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 240".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_250 :
    ⊢@{iProp Σ} WP (buildList (replicate 250 1%Z)) {{ v, ⌜ v = #(250%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 250".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

  Lemma wp_buildList_260 :
    ⊢@{iProp Σ} WP (buildList (replicate 260 1%Z)) {{ v, ⌜ v = #(260%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 260".
    Time (unfold buildList; cbn [makeList2 replicate]; wp_pures;
          wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    Time (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
          iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Time Qed.

End proof.
