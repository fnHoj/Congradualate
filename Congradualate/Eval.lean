import Congradualate.Gradual

open Gradual

inductive EvalError where
  | TypeError | CastError | ConstantError | NotImplemented
deriving Repr

export EvalError (TypeError CastError ConstantError NotImplemented)

inductive Value (S : TypeSystem) (C : Vector S.𝕋 m) (τ : S.𝕋) where
  | const (c : S.ℂ) (h : S.Δ c ~ τ)
  | lambda (x : S.𝕏) (σ σ' : S.𝕋)
    (e : TypedExpression S (if · = x then some σ else none) σ')
    (h : σ ⟶ σ' ~ τ)
  | location (l : Fin m) (h : ref (C[l]) ~ τ)

instance [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ] : Repr (Value S C τ) where
  reprPrec v _ := "(" ++ (match v with
  | .const c _ => reprPrec c 10
  | .lambda x σ _ e _ =>
    "lambda " ++ reprPrec x 10 ++ " : " ++ reprPrec σ 10 ++ " =>" ++
    .indentD (reprPrec e 10)
  | .location l _ => s!"*{l}"
  ) ++ " : " ++ reprPrec τ 10 ++ ")"

def Result (S : TypeSystem) (C : Vector S.𝕋 m) (τ : S.𝕋) :=
  Except EvalError (Value S C τ)

instance [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ] : Repr (Result S C τ) :=
  inferInstanceAs <| Repr (Except ..)

def Value.cast : Value S C σ → Result S C τ
  | .const c _ =>
    if h : S.Δ c ~ τ then .ok (.const c h) else .error CastError
  | .lambda x σ σ' e _ =>
    if h : σ ⟶ σ' ~ τ then .ok (.lambda x σ σ' e h) else .error CastError
  | .location l _ =>
    if h : ref (C[l]) ~ τ then .ok (.location l h) else .error CastError

def Memory (S : TypeSystem) (C : Vector S.𝕋 m) :=
  ∀ l : Fin m, Value S C C[l]

instance [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ] (C : Vector S.𝕋 m) :
  Repr (Memory S C) where reprPrec μ _ := "![" ++ run μ 0 ++ "]"
where run (μ : Memory S C) (i : Nat) : Std.Format :=
  if h : i < m then
    toString i ++ ": " ++ reprPrec (μ ⟨i, h⟩) 10 ++ "," ++ .line ++ run μ (i + 1)
  else .nil

-- def newRef (C : Vector S.𝕋 m) (μ : Memory S C) (v : Value S C τ) :
--     Σ C : Vector S.𝕋 (m + 1), Memory S C :=
--   ⟨.mk (C.toList.concat τ).toArray (by simp), fun l ↦
--     if h : l < m then sorry else by
--       have : l = ⟨m, m.lt_add_one⟩ := by ext; simp only; omega
--       simp [this]
--       sorry⟩

set_option linter.checkUnivs false
structure ComputationSystem extends TypeSystem where
  δ : ℂ → ℂ → ℂ
  δ_lawful (f x : ℂ) (σ τ : ⦗𝔾⦘) :
    Δ f = σ ⟶ τ →
    Δ x ~ σ →
    Δ (δ f x) ~ τ

instance : Coe ComputationSystem TypeSystem where
  coe := ComputationSystem.toTypeSystem

instance (S : ComputationSystem) (τ : S.𝕋) : Inhabited <|
    Σ m, Σ C : Vector S.𝕋 m, Memory S.toTypeSystem C ×
      Result S.toTypeSystem C τ where
  default := ⟨0, .mk #[] rfl, nofun, .error NotImplemented⟩

set_option linter.unusedVariables false in
def eval (S : ComputationSystem) (C : Vector S.𝕋 m)
  (μ : Memory S.toTypeSystem C) :
    {τ : S.𝕋} → TypedExpression S (fun _ ↦ none) τ →
      Σ m, Σ C : Vector S.𝕋 m, Memory S C × Result S C τ
  | _, .const c => ⟨m, C, μ, .ok <| .const c .rfl⟩
  | τ ⟶ τ', .lambda x e => ⟨m, C, μ, .ok <| .lambda x τ τ' e .rfl⟩
  | τ', .apply (τ := τ) e₁ e₂ => match eval S C μ e₁ with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok <| .const c₁ h₁⟩ => match eval S C μ e₂ with
      | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
      | ⟨m, C, μ, .ok <| .const c₂ _⟩ => ⟨m, C, μ, match h : S.Δ c₁ with
        | .ground _ | ref _ => nomatch h ▸ h₁
        | ?? => Value.cast (.const (S.δ c₁ c₂) .con_unknown)
        | σ ⟶ σ' => if h₂ : S.Δ c₂ ~ σ
          then Value.cast (.const (S.δ c₁ c₂) <| S.δ_lawful c₁ c₂ σ σ' h h₂)
          else .error CastError⟩
      | ⟨m, C, μ, .ok <| _⟩ => ⟨m, C, μ, .error ConstantError⟩
    | ⟨m, C, μ, .ok <| .lambda x σ σ' e h⟩ => match eval S C μ e₂ with
      | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
      | ⟨m, C, μ, .ok v₂⟩ => panic! "lambda 替换未实现"
  | _, .getref e => panic! "新地址分配未实现"
  | τ, .deref e => match eval S C μ e with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok <| .const _ _⟩ => ⟨m, C, μ, .error ConstantError⟩
    | ⟨m, C, μ, .ok <| .location l _⟩ => ⟨m, C, μ, (μ l).cast⟩
  | _, .assign e₁ e₂ => match eval S C μ e₁ with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok <| .const _ _⟩ => ⟨m, C, μ, .error ConstantError⟩
    | ⟨m, C, μ, .ok <| .location l h⟩ => match eval S C μ e₂ with
      | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
      | ⟨m, C, μ, .ok v₂⟩ => panic! "储存写入未实现"
  | _, .cast (σ := σ) τ e _ _ => match eval S C μ e with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok v⟩ => ⟨m, C, μ, v.cast⟩
