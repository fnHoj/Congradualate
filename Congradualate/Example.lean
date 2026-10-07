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

/--
info: some ⟨boolean, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.ok (#t : boolean))⟩⟩⟩
-/
#guard_msgs in
#eval (fun ⟨τ, e⟩ ↦ Sigma.mk τ <| eval TSys (.mk #[] rfl) nofun e) <$>
  Gradual.annotate TSys (fun _ ↦ none)
    (isnumber (succ 4))

/--
info: some ⟨boolean, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.ok (#f : boolean))⟩⟩⟩
-/
#guard_msgs in
#eval (fun ⟨τ, e⟩ ↦ Sigma.mk τ <| eval TSys (.mk #[] rfl) nofun e) <$>
  Gradual.annotate TSys (fun _ ↦ none)
    (isnumber succ)

/--
info: some ⟨boolean, ⟨0, ⟨{ toArray := #[], size_toArray := _ }, (![], Except.error (EvalError.ConstantError))⟩⟩⟩
-/
#guard_msgs in
#eval (fun ⟨τ, e⟩ ↦ Sigma.mk τ <| eval TSys (.mk #[] rfl) nofun e) <$>
  Gradual.annotate TSys (fun _ ↦ none)
    (isnumber <| lambda "x" : number => "x")
