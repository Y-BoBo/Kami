Require Import Compare_dec List String Streams.
Import ListNotations.

Require Import Kami.AllNotations.

Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.SimTypes.
Require Import Kami.Simulator.CoqSim.HaskellTypes.

Section Eval.

Variable Word : nat -> Type.
Variable Vec : nat -> Type -> Type.
Variable M : Type -> Type.

Context `{IsWord Word}.
Context `{IsVector Vec}.
Context `{PrintMonad Word Vec M}.

Fixpoint eval_Kind(k : Kind) : Type :=
  match k with
  | Bool => bool
  | Bit n => Word n
  | Struct n ks fs => Tuple (fun i => eval_Kind (ks i))
  | Array n k' => Vec n (eval_Kind k')
  end.

Definition print_BF(bf : BitFormat) : nat -> string :=
  match bf with
  | Binary => nat_binary_string
  | Decimal => nat_decimal_string
  | Hex => nat_hex_string
  end.

Fixpoint print_Kind(k : Kind)(ff : FullFormat k) : eval_Kind k -> string :=
  match ff with
  | FBool n _ => fun x => space_pad n (if x then "1" else "0")
  | FBit n m bf => fun x => zero_pad m (print_BF bf (word_to_nat x))
  | FStruct n fk fs ffs => fun x => ("{" ++ String.concat "; " (v_to_list (vmap (fun '(str1,str2) => str1 ++ ":" ++ str2) (add_strings fs (tup_to_vec _ (fun i => print_Kind (ffs i)) x)))) ++ "}")%string
  | FArray n k' ff' => fun _ => "arr" (*fix*)
  end.

Fixpoint Kind_eq{k} : eval_Kind k -> eval_Kind k -> bool :=
  match k return eval_Kind k -> eval_Kind k -> bool with
  | Bool => Bool.eqb
  | Bit n => weqb
  | Struct n ks fs => TupEq (fun i => eval_Kind (ks i)) (fun i => @Kind_eq (ks i))
  | Array n k' => vec_eq (@Kind_eq k')
  end.

Definition eval_FK(k : FullKind) :=
  match k with
  | SyntaxKind k' => eval_Kind k'
  | NativeKind t _ => t
  end.

Notation "'do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).

Fixpoint rand_tuple{n} : forall ts : Fin.t n -> Type, (forall i, M (ts i)) -> M (Tuple ts) :=
  match n with
  | 0 => fun _ _ => ret tt
  | S m => fun ts mxs => (
      do x <- mxs Fin.F1;
      do xs <- rand_tuple (fun j => ts (Fin.FS j)) (fun j => mxs (Fin.FS j));
      ret (x,xs)
      )
  end.

Fixpoint rand_val(k : Kind) : M (eval_Kind k) :=
  match k return M (eval_Kind k) with
  | Bool => rand_bool
  | Bit n => rand_word n
  | Struct n ks fs => rand_tuple (fun i => eval_Kind (ks i)) (fun i => rand_val (ks i))
  | Array n k' => rand_vec (rand_val k')
  end.

Fixpoint rand_val_FK(k : FullKind) : M (eval_FK k) :=
  match k with
  | SyntaxKind k' => rand_val k'
  | NativeKind k' c => ret c
  end.

Definition eval_UniBool(op : UniBoolOp) : bool -> bool :=
  match op with
  | Neg => negb
  end.

Definition eval_CABool(op : CABoolOp) : list bool -> bool :=
  match op with
  | And => fun xs => fold_left andb xs true
  | Or => fun xs => fold_left orb xs false
  | Xor => fun xs => fold_left xorb xs false
  end.

Definition eval_UniBit{m n}(op : UniBitOp m n) : Word m -> Word n :=
  match op with
  | Inv n => inv
  | TruncLsb lsb msb => trunc_lsb
  | TruncMsb lsb msb => trunc_msb
  | UAnd n => uand
  | UOr n => uor
  | UXor n => uxor
  end.

Definition eval_BinBit{m n p}(op : BinBitOp m n p) : Word m -> Word n -> Word p :=
  match op with
  | Sub n => sub
  | Div n => div
  | Rem n => rem
  | Sll n m => sll
  | Srl n m => srl
  | Sra n m => sra
  | Concat msb lsb => concat
  end.

Definition eval_CABit{n}(op : CABitOp) : list (Word n) -> Word n :=
  match op with
  | Add => add
  | Mul => mul
  | Band => band
  | Bor => bor
  | Bxor => bxor
  end.

Definition eval_BinBitBool{m n}(op : BinBitBoolOp m n) : Word m -> Word n -> bool :=
  match op with
  | LessThan n => wltb
  end.

Fixpoint eval_ConstT{k}(e : ConstT k) : eval_Kind k :=
  match e with
  | ConstBool b => b
  | ConstBit n w => nat_to_word (wordToNat w)
  | ConstStruct n ks ss es => mkTup (fun i => eval_Kind (ks i)) (fun i => eval_ConstT (es i))
  | ConstArray n k' es => make_vec (fun i => eval_ConstT (es i))
  end.

Definition eval_ConstFullT{k} (e : ConstFullT k) : eval_FK k :=
  match e with
  | SyntaxConst k' c' => eval_ConstT c'
  | NativeConst t c' => c'
  end.

Fixpoint eval_Expr{k}(e : Expr eval_Kind k) : eval_FK k :=
  match e with
  | Var _ v => v
  | Const _ v => eval_ConstT v
  | UniBool op e => eval_UniBool op (eval_Expr e)
  | CABool op es => eval_CABool op (List.map eval_Expr es)
  | UniBit m n op e => eval_UniBit op (eval_Expr e)
  | BinBit m n p op e1 e2 => eval_BinBit op (eval_Expr e1) (eval_Expr e2)
  | CABit n op es => eval_CABit op (List.map eval_Expr es)
  | BinBitBool m n op e1 e2 => eval_BinBitBool op (eval_Expr e1) (eval_Expr e2)
  | ITE _ p e1 e2 => eval_Expr (if eval_Expr p then e1 else e2)
  | Eq _ e1 e2 => Kind_eq (eval_Expr e1) (eval_Expr e2)
  | ReadStruct n ks ss e i => tup_index i _ (eval_Expr e)
  | BuildStruct n ks ss es => mkTup _ (fun i => eval_Expr (es i))
  | ReadArray n m k v i => match lt_dec (word_to_nat (eval_Expr i)) n with
                           | left pf => index (Fin.of_nat_lt pf) (eval_Expr v)
                           | right _ => eval_ConstT (getDefaultConst k)
                           end
  | ReadArrayConst n k v i => index i (eval_Expr v)
  | BuildArray n k v => make_vec (fun i => eval_Expr (v i))
  end.

Definition eval_SysT(s : SysT eval_Kind) : M unit :=
  match s with
  | DispString s => print s
  | DispExpr k e ff => print (print_Kind ff (eval_Expr e))
  | Finish => exit
  end.

Fixpoint eval_list_SysT(xs : list (SysT eval_Kind)) : M unit :=
  match xs with
  | [] => ret tt
  | s::ys => (
      do _ <- eval_SysT s;
      eval_list_SysT ys
      )
  end.

Section EvalAction.

(* Variable KindInfo : Map string FullKind 
Hypothesis ActionGood: forall Write r k in a, KindInfo r = k /\ forall Read r k in a, KindInfo r = k
Lemma: SimRegGood: (r, k) in SimReg -> KindInfo r = k
Theorem: ActionSimRegGood: forall Write r k in a, (r, k') in SimReg -> k = k' *)

Definition SimReg := (string * {x : _ & fullType eval_Kind x})%type.
Definition SimRegs := list SimReg.

Variable regs : SimRegs.

Record Update := {
  reg_name : string;
  kind : FullKind;
  old_val : fullType eval_Kind kind;
  new_val : fullType eval_Kind kind;
  lookup_match : lookup String.eqb reg_name regs = Some (existT _ kind old_val)
  }.

Definition Updates := list Update.

Fixpoint mkProd(ts : list Type) : Type :=
  match ts with
  | [] => unit
  | T::ts' => (T * mkProd ts')%type
  end.

Fixpoint return_meth(meth : string)(sig : Signature)(meths : list (string * Signature)) : mkProd (List.map (fun dec => eval_Kind (fst (snd dec)) -> M (eval_Kind (snd (snd dec)))) meths) -> option (eval_Kind (fst (sig)) -> M (eval_Kind (snd (sig)))).
 refine match meths return mkProd (List.map (fun dec => eval_Kind (fst (snd dec)) -> M (eval_Kind (snd (snd dec)))) meths) -> option (eval_Kind (fst (sig)) -> M (eval_Kind (snd (sig)))) with
  | [] => fun _ => None
  | dec::meths' => match string_sigb (meth,sig) dec with
                   | left pf => fun fs => Some _
                   | right _ => fun fs => return_meth meth sig meths' (snd fs)
                   end
  end.
Proof.
  assert (sig = snd dec).
  rewrite <- pf; auto.
  rewrite H4.
  exact (fst fs).
Defined.

Definition reg_not_found{X} : string -> M X :=
  fun reg => error ("register " ++ reg ++ " not found.").

Fixpoint wf_action{k}(a : ActionT eval_Kind k) : Prop :=
  match a with
  | MCall meth s e cont => forall x, wf_action (cont x)
  | LetExpr k e cont => forall x, wf_action (cont x)
  | LetAction k a cont => (wf_action a /\ forall x, wf_action (cont x))
  | ReadNondet k cont => forall x, wf_action (cont x)
  | ReadReg r k' cont => match lookup String.eqb r regs with
                         | None => False
                         | Some (existT k'' _) => k' = k'' /\ forall x, wf_action (cont x)
                         end
  | WriteReg r k' e a => match lookup String.eqb r regs with
                         | None => False
                         | Some (existT k'' _) => k' = k'' /\ wf_action a
                         end
  | IfElse e k1 a1 a2 cont => (wf_action a1 /\ wf_action a2 /\ forall x, wf_action (cont x))
  | Sys _ a => wf_action a
  | Return _ => True
  end.

Fixpoint eval_ActionT{k}(meths : list (string * Signature))(updates : Updates)(a : ActionT eval_Kind k)(a_wf : wf_action a)(fs : mkProd (List.map (fun dec => eval_Kind (fst (snd dec)) -> M (eval_Kind (snd (snd dec)))) meths)){struct a} : M (Updates * eval_Kind k).
  refine (match a return wf_action a -> _ with
  | MCall meth s e cont => fun pf => match return_meth meth s meths fs with
                           | None => error ("Method " ++ meth ++ " not found")
                           | Some f => (
                                do v <- f (eval_Expr e);
                                eval_ActionT _ meths updates (cont v) _ fs
                                )
                           end
  | LetExpr k e cont => fun pf => eval_ActionT _ meths updates (cont (eval_Expr e)) _ fs
  | LetAction k a cont => fun pf => (
      do p <- eval_ActionT _ meths updates a _ fs;
      eval_ActionT _ meths (fst p) (cont (snd p)) _ fs
      )
  | ReadNondet k cont => fun pf => (
      do v <- rand_val_FK k;
      eval_ActionT _ meths updates (cont v) _ fs
      )
  | ReadReg r k cont => fun pf=> match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end
  | WriteReg r k e a => fun pf => match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end
  | IfElse e k a1 a2 cont => fun pf => let a := if (eval_Expr e) then a1 else a2 in (
      do p <- eval_ActionT _ meths updates a _ fs;
      eval_ActionT _ meths (fst p) (cont (snd p)) _ fs
      )
  | Sys ss a => fun pf => (
      do _ <- eval_list_SysT ss;
      eval_ActionT _ meths updates a _ fs
      )
  | Return e => fun pf => ret (updates, eval_Expr e)
  end a_wf).
Proof.
  - apply pf.
  - apply pf.
  - apply pf.
  - apply pf.
  - apply pf.
  (* ReadReg *)
  - destruct p.
    simpl in pf.
    destruct lookup in pf.
    * destruct s; destruct pf as [keq pf'].
      rewrite <- keq in f0.
      exact (eval_ActionT _ meths updates (cont f0) (pf' _) fs).
    * destruct pf.
  (* WriteReg *)
  - simpl in pf.
    destruct lookup eqn:lk in pf.
    * destruct s.
      destruct pf as [keq pf'].
      rewrite keq in e.
      pose (upd := {|
        reg_name := r;
        kind := x;
        old_val := f;
        new_val := eval_Expr e;
        lookup_match := lk
        |}).
      exact (eval_ActionT _ meths (upd::updates) a pf' fs).
    * destruct pf.
  - simpl in pf; destruct (eval_Expr e); tauto.
  - apply pf.
  - exact pf.
Defined.

Fixpoint curried(X : Type)(ts : list Type) : Type :=
  match ts with
  | [] => X
  | T::ts' => T -> curried X ts'
  end.

Fixpoint curry(X : Type)(ts : list Type) : (mkProd ts -> X) -> curried X ts :=
  match ts return (mkProd ts -> X) -> curried X ts with
  | [] => fun f => f tt
  | T::ts' => fun f t => curry ts' (fun xs => f (t,xs))
  end.

Definition eval_RuleT(meths : list (string * Signature))(r : RuleT)(r_wf : wf_action (snd r eval_Kind))(fs : mkProd (List.map (fun dec => eval_Kind (fst (snd dec)) -> M (eval_Kind (snd (snd dec)))) meths)) : M (Updates * eval_Kind Void) :=
  eval_ActionT meths [] ((snd r) eval_Kind) r_wf fs.

Fixpoint do_single_update(upd : Update)(regs : SimRegs) : SimRegs :=
  match regs with
  | [] => []
  | (reg',v')::regs' => if String.eqb (reg_name upd) reg' then (reg', existT _ (kind upd) (new_val upd))::regs' else (reg',v')::do_single_update upd regs'
  end.

Definition do_updates(upds : Updates)(regs : SimRegs) : SimRegs :=
  fold_right do_single_update regs upds.

End EvalAction.

Definition consistent(regs1 regs2 : SimRegs) := forall r k v,
  lookup String.eqb r regs1 = Some (existT _ k v) -> exists v', lookup String.eqb r regs2 = Some (existT _ k v').

Lemma consistent_refl : forall regs, consistent regs regs.
Proof.
  intros regs r k v lk.
  exists v; auto.
Qed.

Lemma consistent_trans : forall regs1 regs2 regs3, consistent regs1 regs2 -> consistent regs2 regs3 -> consistent regs1 regs3.
Proof.
  intros regs1 regs2 regs3 cons12 cons23 r k v Hv.
  destruct (cons12 r k v) as [v' Hv']; auto.
  destruct (cons23 r k v') as [v'' Hv'']; auto.
  exists v''; auto.
Qed.

Check lookup.

Lemma lookup_cons : forall K V (eqb : K -> K -> bool) k k' v (ps : list (K*V)), lookup eqb k ((k',v)::ps) =
  if eqb k k' then Some v else lookup eqb k ps.
Proof.
  intros.
  unfold lookup.
  unfold find.
  simpl.
  destruct (eqb k k'); auto.
Qed.

Lemma consistent_cons_cong : forall (regs1 regs2 : SimRegs)(r : SimReg), consistent regs1 regs2 -> consistent (r::regs1) (r::regs2).
Proof.
  intros regs1 regs2 r cons12 s k v Hv.
  destruct r.
  rewrite lookup_cons in Hv.
  rewrite lookup_cons.
  destruct (String.eqb s s0).
  - exists v; auto.
  - destruct (cons12 s k v); auto.
    exists x; auto.
Qed.

(*
Lemma consistent_do_update_cong : forall (regs1 regs2 : SimRegs)(upd : Update regs1),
  consistent regs1 regs2 -> consistent (do_single_update upd regs1) (do_single_update upd regs2).
Proof.
Admitted.

Lemma update_consistent : forall (regs : SimRegs)(upd : Update regs), consistent regs (do_single_update upd regs).
Proof.
  intros regs upd r k v Hv.
  pose (lookup_match upd).
  Print Update.
*)

Lemma wf_consistent_stable : forall {k} (a : ActionT eval_Kind k) regs1 regs2, consistent regs1 regs2 -> wf_action regs1 a -> wf_action regs2 a.
Proof.
  intros.
  induction a; simpl.
Admitted.

Lemma updates_consistent : forall (regs : SimRegs)(upds : Updates regs), consistent regs (do_updates upds regs).
Proof.
  intros; induction upds; simpl.
  - apply consistent_refl.
  - apply (@consistent_trans _ (do_single_update a regs) _).
Admitted.

Lemma wf_updates_stable{k} : forall (regs : SimRegs)(upds : Updates regs)(a : ActionT eval_Kind k),
  wf_action regs a -> wf_action (do_updates upds regs) a.
Proof.
  intros.
  apply (@wf_consistent_stable _ _ regs).
  - apply updates_consistent.
  - auto.
Qed.

Definition maintain_wf{k} regs (upds : Updates regs) (a : ActionT eval_Kind k) : {r : RuleT & wf_action regs a} -> {r : RuleT & wf_action (do_updates upds regs) a}.
Admitted.

Fixpoint eval_Rules(timeout : nat)(meths : list (string * Signature))(init_regs : SimRegs)(rules : Stream {r : RuleT & wf_action init_regs (snd r eval_Kind)}){struct timeout} : mkProd (List.map (fun dec : string * (Kind * Kind) => eval_Kind (fst (snd dec)) -> M (eval_Kind (snd (snd dec)))) meths) -> M unit. refine
  match timeout with
  | 0 => fun fs => (
      do _ <- print "TIMEOUT";
      exit
      )
  | S timeout' => fun fs => match rules with
                            | Cons r rules' => (
                                do p <- eval_RuleT init_regs meths (projT1 r) (projT2 r)  fs;
                                eval_Rules timeout' meths (do_updates (fst p) init_regs) (Streams.map _ rules') fs
                                )
                            end
  end.
Proof.
  intros [rule wf].
  exists rule.
  apply wf_updates_stable; auto.
Defined.

Definition initialize_SimRegs(regs : list RegInitT) : SimRegs :=
  List.map (fun '(r,existT k v) => match v return SimReg with
                                   | None => (r,existT _ k (eval_ConstFullT (getDefaultConstFullKind k)))
                                   | Some c => (r,existT _ k (eval_ConstFullT c))
                                   end) regs.

Lemma cons_neq{X}(x : X)(xs : list X) : x::xs <> [].
Proof.
  discriminate.
Qed.

Print RuleT.

Fixpoint wf_rules(regs : SimRegs)(rules : list RuleT) :=
  match rules with
  | [] => True
  | r::rs => wf_action regs (snd r eval_Kind) /\ wf_rules regs rs
  end.

Definition wf_bm(basemod : BaseModule) : Prop :=
  match basemod with
  | BaseRegFile rf => False
  | BaseMod regs rules dms => wf_rules (initialize_SimRegs regs) rules
  end.

Definition get_wf_rules : forall regs rules, wf_rules (initialize_SimRegs regs) rules -> 
  list {r : RuleT & wf_action (initialize_SimRegs regs) (snd r eval_Kind)}.
Proof.
  intros.
  induction rules.
  - exact [].
  - simpl in H4; destruct H4.
    exact ((existT _ a H4)::IHrules H5).
Defined.

Definition eval_Basemodule_rr(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : wf_bm basemod) : mkProd (List.map (fun dec : string * (Kind * Kind) => eval_Kind (fst (snd dec)) -> M (eval_Kind (snd (snd dec)))) meths) -> M unit. refine (
  match basemod return wf_bm basemod -> _ with
  | BaseRegFile rf => fun pf fs => _
  | BaseMod regs rules dms =>
      match rules with
      | [] => fun _ _ => error "empty rules"
      | r::rs => fun pf fs => _ (* eval_Rules timeout meths (initialize_SimRegs regs) (unwind_list (r::rs) (@cons_neq _ r rs)) *)
      end
  end wf).
Proof.
  - destruct pf.
  - unfold wf_bm in pf.
    refine (eval_Rules timeout meths (initialize_SimRegs regs) (unwind_list (get_wf_rules _ _ pf) _) fs).
    simpl.
    destruct pf; discriminate.
Defined.

Definition eval_BaseMod(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : wf_bm basemod) :=
  curry _ (eval_Basemodule_rr timeout meths basemod wf).

End Eval.

Definition eval_BaseMod_Haskell := @eval_BaseMod HWord HVec IO _ _ _ _ _.

Check eval_BaseMod_Haskell.

