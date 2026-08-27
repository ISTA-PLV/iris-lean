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
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_15 :
    ⊢@{iProp Σ} WP (buildList (replicate 15 1%Z)) {{ v, ⌜ v = #(15%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 15".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_20 :
    ⊢@{iProp Σ} WP (buildList (replicate 20 1%Z)) {{ v, ⌜ v = #(20%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 20".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_25 :
    ⊢@{iProp Σ} WP (buildList (replicate 25 1%Z)) {{ v, ⌜ v = #(25%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 25".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_30 :
    ⊢@{iProp Σ} WP (buildList (replicate 30 1%Z)) {{ v, ⌜ v = #(30%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 30".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_35 :
    ⊢@{iProp Σ} WP (buildList (replicate 35 1%Z)) {{ v, ⌜ v = #(35%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 35".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_40 :
    ⊢@{iProp Σ} WP (buildList (replicate 40 1%Z)) {{ v, ⌜ v = #(40%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 40".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_45 :
    ⊢@{iProp Σ} WP (buildList (replicate 45 1%Z)) {{ v, ⌜ v = #(45%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 45".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_50 :
    ⊢@{iProp Σ} WP (buildList (replicate 50 1%Z)) {{ v, ⌜ v = #(50%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 50".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_55 :
    ⊢@{iProp Σ} WP (buildList (replicate 55 1%Z)) {{ v, ⌜ v = #(55%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 55".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_60 :
    ⊢@{iProp Σ} WP (buildList (replicate 60 1%Z)) {{ v, ⌜ v = #(60%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 60".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_65 :
    ⊢@{iProp Σ} WP (buildList (replicate 65 1%Z)) {{ v, ⌜ v = #(65%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 65".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_70 :
    ⊢@{iProp Σ} WP (buildList (replicate 70 1%Z)) {{ v, ⌜ v = #(70%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 70".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_75 :
    ⊢@{iProp Σ} WP (buildList (replicate 75 1%Z)) {{ v, ⌜ v = #(75%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 75".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_80 :
    ⊢@{iProp Σ} WP (buildList (replicate 80 1%Z)) {{ v, ⌜ v = #(80%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 80".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_85 :
    ⊢@{iProp Σ} WP (buildList (replicate 85 1%Z)) {{ v, ⌜ v = #(85%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 85".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_90 :
    ⊢@{iProp Σ} WP (buildList (replicate 90 1%Z)) {{ v, ⌜ v = #(90%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 90".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_95 :
    ⊢@{iProp Σ} WP (buildList (replicate 95 1%Z)) {{ v, ⌜ v = #(95%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 95".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

  Lemma wp_buildList_100 :
    ⊢@{iProp Σ} WP (buildList (replicate 100 1%Z)) {{ v, ⌜ v = #(100%nat) ⌝ }}.
  Proof.
    idtac "BENCH heaplang_list 100".
    (unfold buildList; cbn [makeList2 replicate]; wp_pures;
     wp_bind (cons _); iApply cons_spec; [ iApply isList_nil |]).
    Time (repeat (iIntros (?) "?"; wp_pures;
                  wp_bind (cons _); iApply (cons_spec with "[$]"))).
    (iIntros (?) "Hv"; wp_pures; wp_bind (llength _);
     iApply (length_spec with "Hv"); iIntros (?) "Hw %Hlen"; done).
  Qed.

End proof.