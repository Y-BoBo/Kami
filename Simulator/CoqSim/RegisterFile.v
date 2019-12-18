Require Import String.

Require Import Kami.AllNotations.

Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.Eval.
Require Import Kami.Simulator.CoqSim.SimTypes.

Section RegFile.

Context {V : nat -> Type -> Type}.
Context `{IsVector V}.

Context {W : nat -> Type}.
Context `{IsWord W}.

Context {M : Type -> Type -> Type}.
Context `{IsMap M}.

Definition Val k := eval_Kind W V k.
Definition ValFK k := eval_FK W V k.

Inductive FileCall :=
  | AsyncRead : FileCall
  | ReadReq : string -> FileCall
  | ReadResp : string -> FileCall
  | WriteFC : FileCall.

(*
Inductive FileUpd :=
  | IntRegWrite : string -> Val -> FileUpd
  | ArrWrite : string -> list (nat * Val) -> FileUpd.
*)

Record RegFile := {
  file_name : string;
  is_wr_mask : bool;
  chunk_size : nat;
  readers : RegFileReaders;
  write : string;
  size : nat;
  kind : Kind;
  arr : V size (Val kind)
  }.

Record FileState := {
  methods : M string (FileCall * string);
  int_regs : M string {k : Kind & Val k};
  files : M string RegFile;
  }.

Definition empty_state : FileState := {|
  methods := empty;
  int_regs := empty;
  files := empty
  |}.

Definition file_async_read(file : RegFile)(i : nat) : Val (Array (chunk_size file) (kind file)) :=
  slice i _ (arr file).

Definition isAddr(file : RegFile) : bool :=
  match readers file with
  | Sync isAddr _ => isAddr
  | _ => false
  end.

Axiom cheat : forall {X},X.

Definition file_sync_readreq(val : {k : Kind & Val k})(file : RegFile)(regName : string) : option {k : Kind & Val k}. refine
  match readers file with
  | Async _ => None
  | Sync true _ => if Kind_decb (projT1 val) (Bit (Nat.log2_up (size file))) then Some val else None
  | Sync false _ => _
  end.
Proof.
  (* isAddr = false *)
  destruct val as [k v].
  destruct (Kind_decb k (Bit (Nat.log2_up (size file)))) eqn:Keq.
  - rewrite Kind_decb_eq in Keq.
    rewrite Keq in v.
    apply Some.
    exists (Array (chunk_size file) (kind file)).
    exact (slice (word_to_nat v) (chunk_size file) (arr file)).
  - exact None.
Defined.

Definition file_sync_readresp(state : FileState)(file : RegFile)(regName : string) : option (Val (Array (chunk_size file) (kind file))). refine
  match map_lookup (M := M) regName (int_regs state) with
  | None => None
  | Some (existT k v) =>
      match readers file with
      | Async _ => None
      | Sync true _ => _
      | Sync false _ => _
      end
  end.
Proof.
  (* isAddr = true *)
  - destruct (Kind_decb k (Bit (Nat.log2_up (size file)))) eqn:Keq.
    * rewrite Kind_decb_eq in Keq.
      rewrite Keq in v.
      exact (Some (slice (word_to_nat v) (chunk_size file) (arr file))).
    * exact None.
  (* isAddr = false *)
  - destruct (Kind_decb k (Array (chunk_size file) (kind file))) eqn:Keq.
    * rewrite Kind_decb_eq in Keq.
      rewrite Keq in v.
      exact (Some v).
    * exact None.
Defined.

Definition file_writes_mask(file : RegFile)(i : nat)(mask : Val (Array (chunk_size file) Bool))(vals : Val (Array (chunk_size file) (kind file))) : list (nat * Val (kind file)) :=
  


End RegFile.