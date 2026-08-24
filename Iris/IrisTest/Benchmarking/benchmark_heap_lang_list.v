From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Tactic Notation "timeN" int_or_var(k) string(lbl) tactic3(tac) :=
  do k (time lbl tac); tac.

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

  Definition n := 250.

  Lemma wp_buildList :
    ⊢@{iProp Σ} WP (buildList (replicate n 1%Z)) {{ v, ⌜ v = #n ⌝ }}.
  Proof.
    unfold buildList, n.
    cbn [makeList2].
    wp_pures.
    wp_bind (cons _).
    iApply cons_spec.
    { iApply isList_nil. }
    Time repeat (iIntros (?) "?"; wp_pures;
                 wp_bind (cons _); iApply (cons_spec with "[$]")).
    iIntros (?) "Hv". wp_pures.
    wp_bind (llength _).
    iApply (length_spec with "Hv").
    iIntros (?) "Hw %Hlen".
    done.
  Qed.

End proof.
