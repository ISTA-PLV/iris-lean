From iris.proofmode Require Import proofmode.
From iris.bi Require Import bi.
From iris.prelude Require Import options.

Section frame_benchmark.
  Context {PROP : bi}.
  Context (P : nat -> PROP).

  Lemma frame_simple_pat_10 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9).
  Proof.
    idtac "BENCH frame_simple_pat 10".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_15 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14).
  Proof.
    idtac "BENCH frame_simple_pat 15".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_20 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19).
  Proof.
    idtac "BENCH frame_simple_pat 20".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 H19]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_25 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24).
  Proof.
    idtac "BENCH frame_simple_pat 25".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 H24]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_30 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29).
  Proof.
    idtac "BENCH frame_simple_pat 30".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 H29]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_35 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34).
  Proof.
    idtac "BENCH frame_simple_pat 35".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 H34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_40 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39).
  Proof.
    idtac "BENCH frame_simple_pat 40".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 H39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_45 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44).
  Proof.
    idtac "BENCH frame_simple_pat 45".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 H44]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_50 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49).
  Proof.
    idtac "BENCH frame_simple_pat 50".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 H49]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_55 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54).
  Proof.
    idtac "BENCH frame_simple_pat 55".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 H54]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_simple_pat_60 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59).
  Proof.
    idtac "BENCH frame_simple_pat 60".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 H59]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_10 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9) ⊢ (P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 10".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_15 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14) ⊢ (P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 15".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_20 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19) ⊢ (P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 20".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 H19]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_25 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24) ⊢ (P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 25".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 H24]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_30 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29) ⊢ (P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 30".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 H29]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_35 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34) ⊢ (P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 35".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 H34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_40 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39) ⊢ (P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 40".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 H39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_45 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44) ⊢ (P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 45".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 H44]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_50 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49) ⊢ (P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 50".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 H49]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_55 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54) ⊢ (P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 55".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 H54]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_60 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59) ⊢ (P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 60".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 H59]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_65 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64) ⊢ (P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 65".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 H64]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_70 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69) ⊢ (P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 70".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 H69]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_75 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74) ⊢ (P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 75".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 H74]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_80 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79) ⊢ (P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 80".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 H79]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_85 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84) ⊢ (P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 85".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 H84]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_90 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89) ⊢ (P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 90".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 H89]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_95 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89 ∗ P 90 ∗ P 91 ∗ P 92 ∗ P 93 ∗ P 94) ⊢ (P 94 ∗ P 93 ∗ P 92 ∗ P 91 ∗ P 90 ∗ P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 95".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 [H89 [H90 [H91 [H92 [H93 H94]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_100 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89 ∗ P 90 ∗ P 91 ∗ P 92 ∗ P 93 ∗ P 94 ∗ P 95 ∗ P 96 ∗ P 97 ∗ P 98 ∗ P 99) ⊢ (P 99 ∗ P 98 ∗ P 97 ∗ P 96 ∗ P 95 ∗ P 94 ∗ P 93 ∗ P 92 ∗ P 91 ∗ P 90 ∗ P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 100".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 [H89 [H90 [H91 [H92 [H93 [H94 [H95 [H96 [H97 [H98 H99]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_105 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89 ∗ P 90 ∗ P 91 ∗ P 92 ∗ P 93 ∗ P 94 ∗ P 95 ∗ P 96 ∗ P 97 ∗ P 98 ∗ P 99 ∗ P 100 ∗ P 101 ∗ P 102 ∗ P 103 ∗ P 104) ⊢ (P 104 ∗ P 103 ∗ P 102 ∗ P 101 ∗ P 100 ∗ P 99 ∗ P 98 ∗ P 97 ∗ P 96 ∗ P 95 ∗ P 94 ∗ P 93 ∗ P 92 ∗ P 91 ∗ P 90 ∗ P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 105".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 [H89 [H90 [H91 [H92 [H93 [H94 [H95 [H96 [H97 [H98 [H99 [H100 [H101 [H102 [H103 H104]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_110 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89 ∗ P 90 ∗ P 91 ∗ P 92 ∗ P 93 ∗ P 94 ∗ P 95 ∗ P 96 ∗ P 97 ∗ P 98 ∗ P 99 ∗ P 100 ∗ P 101 ∗ P 102 ∗ P 103 ∗ P 104 ∗ P 105 ∗ P 106 ∗ P 107 ∗ P 108 ∗ P 109) ⊢ (P 109 ∗ P 108 ∗ P 107 ∗ P 106 ∗ P 105 ∗ P 104 ∗ P 103 ∗ P 102 ∗ P 101 ∗ P 100 ∗ P 99 ∗ P 98 ∗ P 97 ∗ P 96 ∗ P 95 ∗ P 94 ∗ P 93 ∗ P 92 ∗ P 91 ∗ P 90 ∗ P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 110".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 [H89 [H90 [H91 [H92 [H93 [H94 [H95 [H96 [H97 [H98 [H99 [H100 [H101 [H102 [H103 [H104 [H105 [H106 [H107 [H108 H109]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_115 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89 ∗ P 90 ∗ P 91 ∗ P 92 ∗ P 93 ∗ P 94 ∗ P 95 ∗ P 96 ∗ P 97 ∗ P 98 ∗ P 99 ∗ P 100 ∗ P 101 ∗ P 102 ∗ P 103 ∗ P 104 ∗ P 105 ∗ P 106 ∗ P 107 ∗ P 108 ∗ P 109 ∗ P 110 ∗ P 111 ∗ P 112 ∗ P 113 ∗ P 114) ⊢ (P 114 ∗ P 113 ∗ P 112 ∗ P 111 ∗ P 110 ∗ P 109 ∗ P 108 ∗ P 107 ∗ P 106 ∗ P 105 ∗ P 104 ∗ P 103 ∗ P 102 ∗ P 101 ∗ P 100 ∗ P 99 ∗ P 98 ∗ P 97 ∗ P 96 ∗ P 95 ∗ P 94 ∗ P 93 ∗ P 92 ∗ P 91 ∗ P 90 ∗ P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 115".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 [H89 [H90 [H91 [H92 [H93 [H94 [H95 [H96 [H97 [H98 [H99 [H100 [H101 [H102 [H103 [H104 [H105 [H106 [H107 [H108 [H109 [H110 [H111 [H112 [H113 H114]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

  Lemma frame_reverse_pat_120 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59 ∗ P 60 ∗ P 61 ∗ P 62 ∗ P 63 ∗ P 64 ∗ P 65 ∗ P 66 ∗ P 67 ∗ P 68 ∗ P 69 ∗ P 70 ∗ P 71 ∗ P 72 ∗ P 73 ∗ P 74 ∗ P 75 ∗ P 76 ∗ P 77 ∗ P 78 ∗ P 79 ∗ P 80 ∗ P 81 ∗ P 82 ∗ P 83 ∗ P 84 ∗ P 85 ∗ P 86 ∗ P 87 ∗ P 88 ∗ P 89 ∗ P 90 ∗ P 91 ∗ P 92 ∗ P 93 ∗ P 94 ∗ P 95 ∗ P 96 ∗ P 97 ∗ P 98 ∗ P 99 ∗ P 100 ∗ P 101 ∗ P 102 ∗ P 103 ∗ P 104 ∗ P 105 ∗ P 106 ∗ P 107 ∗ P 108 ∗ P 109 ∗ P 110 ∗ P 111 ∗ P 112 ∗ P 113 ∗ P 114 ∗ P 115 ∗ P 116 ∗ P 117 ∗ P 118 ∗ P 119) ⊢ (P 119 ∗ P 118 ∗ P 117 ∗ P 116 ∗ P 115 ∗ P 114 ∗ P 113 ∗ P 112 ∗ P 111 ∗ P 110 ∗ P 109 ∗ P 108 ∗ P 107 ∗ P 106 ∗ P 105 ∗ P 104 ∗ P 103 ∗ P 102 ∗ P 101 ∗ P 100 ∗ P 99 ∗ P 98 ∗ P 97 ∗ P 96 ∗ P 95 ∗ P 94 ∗ P 93 ∗ P 92 ∗ P 91 ∗ P 90 ∗ P 89 ∗ P 88 ∗ P 87 ∗ P 86 ∗ P 85 ∗ P 84 ∗ P 83 ∗ P 82 ∗ P 81 ∗ P 80 ∗ P 79 ∗ P 78 ∗ P 77 ∗ P 76 ∗ P 75 ∗ P 74 ∗ P 73 ∗ P 72 ∗ P 71 ∗ P 70 ∗ P 69 ∗ P 68 ∗ P 67 ∗ P 66 ∗ P 65 ∗ P 64 ∗ P 63 ∗ P 62 ∗ P 61 ∗ P 60 ∗ P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0).
  Proof.
    idtac "BENCH frame_reverse_pat 120".
    iIntros "[H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 [H62 [H63 [H64 [H65 [H66 [H67 [H68 [H69 [H70 [H71 [H72 [H73 [H74 [H75 [H76 [H77 [H78 [H79 [H80 [H81 [H82 [H83 [H84 [H85 [H86 [H87 [H88 [H89 [H90 [H91 [H92 [H93 [H94 [H95 [H96 [H97 [H98 [H99 [H100 [H101 [H102 [H103 [H104 [H105 [H106 [H107 [H108 [H109 [H110 [H111 [H112 [H113 [H114 [H115 [H116 [H117 [H118 H119]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]".
    Time iFrame.
  Qed.

End frame_benchmark.
