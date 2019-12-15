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
  int_regs : M string {k : FullKind & ValFK k};
  files : M string RegFile;
  }.

Definition empty_state : FileState := {|
  methods := empty;
  int_regs := empty;
  files := empty
  |}.

Check slice.

Definition file_async_read(file : RegFile)(i : nat) : V (chunk_size file) (Val (kind file)) :=
  slice i _ (arr file).

(*
Definition file_sync_readreq(file : RegFile)(v : Val Bool)(reg : string) : option (Val Bool) :=
  match readers file with
  | Async _ => None
  | Sync isAddr rs => 
  end.

Definition file_sync_readreq : Val -> FileState -> RegFile -> string -> option Val. :=
  fun val state file regName =>
    match readers file with
    | Async _ => cheat
    | Sync isAddr rs => if isAddr then val else arrayVal (slice (word_to_nat (
    end.
*)

End RegFile.