
Require Import Kami.Syntax.
Require Import Kami.Simulator.CoqSim.Eval.
Require Import Kami.Compiler.Test.
Require Import Kami.Simulator.NativeTest.
Require Import Kami.Simulator.CoqSim.HaskellTypes.

Definition testRegMod := snd (snd (separateModRemove testReg)).

Definition timeout := 1000.

Check eval_BaseMod_Haskell.

Axiom cheat : forall {X},X. (* used to produce a wf proof, for now*)

Definition coqSim_reg : (HWord Xlen -> IO (HWord Xlen)) -> IO unit := eval_BaseMod_Haskell timeout [("times_two", (Data,Data))] testRegMod cheat.

Check separateModRemove.

Definition coqSim_native : IO unit :=
  let '(_,(_,bm)) := separateModRemove testNative in
  eval_BaseMod_Haskell timeout [] bm cheat.