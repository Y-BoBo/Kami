Require Import Kami.Simulator.CoqSim.SimTypes.
Require Extraction.

Extraction Language Haskell.

(* We postulate Haskell's more efficient datatypes and package them for extraction *)

(* Maps *)

Parameter HMap : Type -> Type -> Type.

Parameter Hempty : forall {K V}, HMap K V.
Parameter Hmap_lookup : forall {K V}, K -> HMap K V -> option V.
Parameter Hinsert : forall {K V}, K -> V -> HMap K V -> HMap K V.

Instance HMapIsMap : IsMap HMap := {|
  empty := @Hempty;
  map_lookup := @Hmap_lookup;
  insert := @Hinsert
  |}.

Extract Constant HMap "k" "v" => "H.Map k v".
Extract Constant Hempty => "H.empty".
Extract Constant Hmap_lookup => "H.lookup".
Extract Constant Hinsert => "H.insert".

(* Vectors *)

Parameter HVec : nat -> Type -> Type.

Parameter Hindex : forall {X n}, Fin.t n -> HVec n X -> X.
Parameter Hmap : forall {X Y n}, (X -> Y) -> HVec n X -> HVec n Y.
Parameter Heq : forall {X n}, (X -> X -> bool) -> HVec n X -> HVec n X -> bool.
Parameter Hto_list : forall {X n}, HVec n X -> list X.
Parameter Hmake_vec : forall {X n}, (Fin.t n -> X) -> HVec n X.
Parameter Hslice : forall {X n} (i m : nat),  HVec n X -> HVec m X.

Instance HVecIsVec : IsVector HVec := {|
  index := @Hindex;
  vec_map := @Hmap;
  vec_eq := @Heq;
  vec_to_list := @Hto_list;
  make_vec := @Hmake_vec;
  slice := @Hslice
  |}.

Fixpoint Fin_to_list{X n} : (Fin.t n -> X) -> list X :=
  match n with
  | 0 => fun _ => nil
  | S m => fun f => cons (f Fin.F1) (Fin_to_list (fun i => f (Fin.FS i)))
  end.

Extract Constant HVec "a" => "Data.Vector.Vector a".
Extract Constant Hindex => "(\_ (n,i) v -> v Data.Vector.! i)".
Extract Constant Hmap => "(\_ -> Data.Vector.map)".
Extract Constant Heq => "(\_ eqb v1 v2 -> Data.Vector.foldr (Prelude.&&) Prelude.True (Data.Vector.zipWith eqb v1 v2))".
Extract Constant Hto_list => "(\ _ -> Data.Vector.toList)".
Extract Constant Hmake_vec => "(\n f -> Data.Vector.fromList (coq_Fin_to_list n f))".
Extract Constant Hslice => "(\_ i m v -> Data.Vector.slice i m v)".

(* Words *)

Parameter HWord : nat -> Type.
Parameter Hinv : forall {m}, HWord m -> HWord m.
Parameter Htrunc_lsb : forall {m n}, HWord (m + n) -> HWord m.
Parameter Htrunc_msb : forall {m n}, HWord (m + n) -> HWord n.
Parameter Huand : forall {m}, HWord m -> HWord 1.
Parameter Huor : forall {m}, HWord m -> HWord 1.
Parameter Huxor : forall {m}, HWord m -> HWord 1.
Parameter Hsub : forall {m}, HWord m -> HWord m -> HWord m.
Parameter Hdiv : forall {m}, HWord m -> HWord m -> HWord m.
Parameter Hrem : forall {m}, HWord m -> HWord m -> HWord m.
Parameter Hsll : forall {m n}, HWord m -> HWord n -> HWord m.
Parameter Hsrl : forall {m n}, HWord m -> HWord n -> HWord m.
Parameter Hsra : forall {m n}, HWord m -> HWord n -> HWord m.
Parameter Hconcat : forall {m n}, HWord m -> HWord n -> HWord (n + m).
Parameter Hadd : forall {m}, list (HWord m) -> HWord m.
Parameter Hmul : forall {m}, list (HWord m) -> HWord m.
Parameter Hband : forall {m}, list (HWord m) -> HWord m.
Parameter Hbor : forall {m}, list (HWord m) -> HWord m.
Parameter Hbxor : forall {m}, list (HWord m) -> HWord m.
Parameter Hwltb : forall {m}, HWord m -> HWord m -> bool.
Parameter Hweqb : forall {m}, HWord m -> HWord m -> bool.
Parameter Hword_to_nat : forall {m}, HWord m -> nat.
Parameter Hnat_to_word : forall {m}, nat -> HWord m.

Instance HWordIsWord : IsWord HWord := {|
  inv := @Hinv;
  trunc_lsb := @Htrunc_lsb;
  trunc_msb := @Htrunc_msb;
  uand := @Huand;
  uor := @Huor;
  uxor := @Huxor;
  sub := @Hsub;
  div := @Hdiv;
  rem := @Hrem;
  sll := @Hsll;
  srl := @Hsrl;
  sra := @Hsra;
  concat := @Hconcat;
  add := @Hadd;
  mul := @Hmul;
  band := @Hband;
  bor := @Hbor;
  bxor := @Hbxor;
  wltb := @Hwltb;
  weqb := @Hweqb;
  word_to_nat := @Hword_to_nat;
  nat_to_word := @Hnat_to_word
  |}.

Extract Constant HWord => "Data.BitVector.BV".
Extract Constant Hinv => "(\_ -> Data.BitVector.not)".
Extract Constant Htrunc_lsb => "(\m _ -> if m Prelude.== 0 then Prelude.const Data.BitVector.nil else Data.BitVector.least m)".
Extract Constant Htrunc_msb => "(\_ n -> if n Prelude.== 0 then Prelude.const Data.BitVector.nil else Data.BitVector.most n)".
Extract Constant Huand => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude.&&) Prelude.True v))".
Extract Constant Huor => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude.||) Prelude.False v))".
Extract Constant Huxor => "(\_ v -> Data.BitVector.fromBool (Data.BitVector.foldr (Prelude./=) Prelude.False v))".
Extract Constant Hsub => "(\_ -> (Prelude.-))".
Extract Constant Hdiv => "(\_ -> Prelude.div)".
Extract Constant Hrem => "(\_ -> Prelude.rem)".
Extract Constant Hsll => "(\_ _ -> Data.BitVector.shl)".
Extract Constant Hsrl => "(\_ _ -> Data.BitVector.shr)".
Extract Constant Hsra => "(\_ _ -> Data.BitVector.ashr)".
Extract Constant Hconcat => "(\_ _ -> (Data.BitVector.#))".
Extract Constant Hadd => "(\_ -> Prelude.foldr (Prelude.+) 0)".
Extract Constant Hmul => "(\_ -> Prelude.foldr (Prelude.*) 1)".
Extract Constant Hband => "(\n -> Prelude.foldr (Data.Bits..&.) (Data.BitVector.ones n))".
Extract Constant Hbor => "(\n -> Prelude.foldr (Data.Bits..|.) (Data.BitVector.zeros n))".
Extract Constant Hbxor => "(\n -> Prelude.foldr Data.Bits.xor (Data.BitVector.zeros n))".
Extract Constant Hwltb => "(\_ -> (Data.BitVector.<.))".
Extract Constant Hweqb => "(\_ -> (Data.BitVector.==.))".
Extract Constant Hword_to_nat => "(\_ x -> Prelude.fromIntegral (Data.BitVector.nat x))".
Extract Constant Hnat_to_word => "Data.BitVector.bitVec".

(* IO *)

Require Import String.

Parameter IO : Type -> Type.
Parameter Hret : forall {X}, X -> IO X.
Parameter Hbind : forall {X Y}, IO X -> (X -> IO Y) -> IO Y.
Parameter Herror : forall {X}, string -> IO X.
Parameter Hprint : string -> IO unit.
Parameter Hrand_bool : IO bool.
Parameter Hrand_word : forall n, IO (HWord n).
Parameter Hrand_vec : forall {X n}, IO X -> IO (HVec n X).
Parameter Hexit : forall {X}, IO X.

Instance IOPrintMonad : PrintMonad IO := {|
  ret := @Hret;
  bind := @Hbind;
  error := @Herror;
  print := Hprint;
  rand_bool := Hrand_bool;
  rand_word := Hrand_word;
  rand_vec := @Hrand_vec;
  exit := @Hexit
  |}.

Extract Constant IO "a" => "Prelude.IO a".
Extract Constant Hret => "Prelude.return".
Extract Constant Hbind => "(GHC.Base.>>=)".
Extract Constant Herror => "Prelude.error".
Extract Constant Hprint => "Prelude.putStrLn".
Extract Constant Hrand_bool => "Prelude.return Prelude.False". (*FIXME*)
Extract Constant Hrand_word => "Prelude.undefined". (*FIXME*)
Extract Constant Hrand_vec => "Prelude.undefined". (*FIXME*)
Extract Constant Hexit => "System.Exit.exitSuccess".
