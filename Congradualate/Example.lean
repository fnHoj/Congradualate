import Congradualate.Eval

inductive GroundType where
  | boolean
  | number
deriving DecidableEq

instance : Repr GroundType where
  reprPrec
  | .boolean, _ => "boolean"
  | .number, _ => "number"

inductive Constant where
  | false | true
  | ofNat (n : Nat)
  | succ
deriving DecidableEq

notation "#f" => Constant.false
notation "#t" => Constant.true
instance : OfNat Constant n where ofNat := .ofNat n

instance : Repr Constant where
  reprPrec
  | #f, _ => "#f"
  | #t, _ => "#t"
  | .ofNat n, p => reprPrec n p
  | .succ, _ => "succ"

open GroundType

abbrev TSys : ComputationSystem where
  𝕏 := String
  𝔾 := GroundType
  ℂ := Constant
  Δ
  | #f | #t => boolean
  | .ofNat _ => number
  | .succ => number ⟶ number
  δ
  | .succ, .ofNat n => .ofNat (n + 1)
  | _, _ => #f
  δ_lawful | .succ, .ofNat _, number, number, rfl, .rfl => .rfl

abbrev succ : TSys.𝔼 := Constant.succ

macro "#annotate" t:term : command =>
  `(#eval Gradual.annotate TSys (fun _ ↦ none) $t)

/--
info: some ⟨boolean, (lambda "r1" : ref (?? ⟶ ??) =>
   (#t : boolean) : ref (?? ⟶ ??) ⟶ boolean)
   (getref (lambda "x" : ?? =>
     ("x" : ??) : ?? ⟶ ??) : ref (?? ⟶ ??)) : boolean⟩
-/
#guard_msgs in #annotate
  say "r1" : ref (?? ⟶ ??) := getref (lambda "x" => "x");
  #t

/-- info: none -/
#guard_msgs in #annotate
  say "r1" : ref (?? ⟶ ??) := getref (lambda "x" => "x");
  say "r2" : ref ?? := "r1";
  say "_" := "r2" ⟵ 1;
  deref "r1" 2

/--
info: some ⟨??, (lambda "r1" : ?? =>
   ((lambda "r2" : ref ?? =>
     ((lambda "_" : ?? =>
       ((deref ("r1" : ?? : ref ??) : ?? : number ⟶ ??)
         (2 : number) : ??) : ?? ⟶ ??)
       ("r2" : ref ?? ⟵
         (1 : number : ??) : ref ?? : ??) : ??) : ref ?? ⟶ ??)
     ("r1" : ?? : ref ??) : ??) : ?? ⟶ ??)
   (getref (lambda "x" : ?? =>
     ("x" : ??) : ?? ⟶ ??) : ref (?? ⟶ ??) : ??) : ??⟩
-/
#guard_msgs in #annotate
  say "r1" := getref (lambda "x" => "x");
  say "r2" : ref ?? := "r1";
  say "_" := "r2" ⟵ 1;
  deref "r1" 2
