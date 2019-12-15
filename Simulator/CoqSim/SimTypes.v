Require Import String Fin.

Class IsMap (M : Type -> Type -> Type) := {
  empty : forall {K V}, M K V;
  map_lookup : forall {K V}, K -> M K V -> option V;
  insert : forall {K V}, K -> V -> M K V -> M K V
  }.

Class IsVector (V : nat -> Type -> Type) := {
  index : forall {X n}, Fin.t n -> V n X -> X;
  vec_map : forall {X Y n}, (X -> Y) -> V n X -> V n Y;
  vec_eq : forall {X n}, (X -> X -> bool) -> V n X -> V n X -> bool;
  vec_to_list : forall {X n}, V n X -> list X;
  make_vec : forall {X n}, (Fin.t n -> X) -> V n X;
  slice : forall {X n} (i m : nat), V n X -> (V m X)
  }.

Class IsWord (W : nat -> Type) := {
  inv : forall {m}, W m -> W m;
  trunc_lsb : forall {m n}, W (m + n) -> W m;
  trunc_msb : forall {m n}, W (m + n) -> W n;
  uand : forall {m}, W m -> W 1;
  uor : forall {m}, W m -> W 1;
  uxor : forall {m}, W m -> W 1;

  sub : forall {m}, W m -> W m -> W m;
  div : forall {m}, W m -> W m -> W m;
  rem : forall {m}, W m -> W m -> W m;
  sll : forall {m n}, W m -> W n -> W m;
  srl : forall {m n}, W m -> W n -> W m;
  sra : forall {m n}, W m -> W n -> W m;
  concat : forall {m n}, W m -> W n -> W (n + m);

  add : forall {m}, list (W m) -> W m;
  mul : forall {m}, list (W m) -> W m;
  band : forall {m}, list (W m) -> W m;
  bor : forall {m}, list (W m) -> W m;
  bxor : forall {m}, list (W m) -> W m;

  wltb : forall {m}, W m -> W m -> bool;

  weqb : forall {m}, W m -> W m -> bool;

  word_to_nat : forall {m}, W m -> nat;
  nat_to_word : forall {m}, nat -> W m;
  }.

Class PrintMonad{W V}`{IsWord W, IsVector V} (M : Type -> Type) := {
  ret : forall {X}, X -> M X;
  bind : forall {X Y}, M X -> (X -> M Y) -> M Y;
  error : forall {X}, string -> M X;
  print : string -> M unit;
  rand_bool : M bool;
  rand_word : forall n, M (W n);
  rand_vec : forall {X n}, M X -> M (V n X);
  exit : forall {X}, M X
  }.