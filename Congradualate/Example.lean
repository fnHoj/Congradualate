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
  | isnumber
  | mystery
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
  | .isnumber, _ => "isnumber"
  | .mystery, _ => "mystery"

open GroundType

abbrev TSys : ComputationSystem where
  𝕏 := String
  𝔾 := GroundType
  ℂ := Constant
  Δ
  | #f | #t => boolean
  | .ofNat _ => number
  | .succ => number ⟶ number
  | .isnumber => ?? ⟶ boolean
  | .mystery => ??
  δ
  | .succ, .ofNat n => .ofNat (n + 1)
  | .isnumber, .ofNat _ => #t
  | .isnumber, _ => #f
  | _, _ => .mystery
  δ_lawful
  | .succ, .ofNat _, number, number, _, _ => .rfl
  | .succ, .mystery, number, number, _, _ => .unknown_con
  | .isnumber, v, ??, boolean, _, _ => by cases v <;> exact .rfl

abbrev succ : TSys.𝔼 := Constant.succ
abbrev isnumber : TSys.𝔼 := Constant.isnumber
abbrev mystery : TSys.𝔼 := Constant.mystery

macro "#evaluate" t:term : command => `(#eval! (fun ⟨τ, e⟩ ↦ Sigma.mk τ <| eval TSys (Γ := []) (.mk #[] rfl) nofun .nil e) <$> Gradual.annotate TSys [] $t)

/--
info: some ⟨boolean, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.ok (#t : boolean))⟩⟩⟩
-/
#guard_msgs in #evaluate isnumber (succ 4)

/--
info: some ⟨boolean, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.ok (#f : boolean))⟩⟩⟩
-/
#guard_msgs in #evaluate isnumber succ

/--
info: some ⟨boolean, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.error (EvalError.ConstantError))⟩⟩⟩
-/
#guard_msgs in #evaluate isnumber <| lambda "x" : number => "x"

/--
info: some ⟨number, ⟨1, ⟨{ toArray := #[number], size_toArray := _ }, (![0: (2 : number), ], Except.ok (2 : number))⟩⟩⟩
-/
#guard_msgs in #evaluate deref <| getref 0 ⟵ 2

/--
info: some ⟨number, (lambda "x" : ?? =>
   ((lambda "x" : number =>
     ("x" : number) : number ⟶ number)
     ("x" : ?? : number) : number) : ?? ⟶ number)
   (#t : boolean : ??) : number⟩
-/
#guard_msgs in
#eval Gradual.annotate TSys [] <|
  (lambda "x" => (lambda "x" : number => "x") "x") #t

/--
info: some ⟨number, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.error (EvalError.CastError))⟩⟩⟩
-/
#guard_msgs in #evaluate (lambda "x" => (lambda "x" : number => "x") "x") #t
