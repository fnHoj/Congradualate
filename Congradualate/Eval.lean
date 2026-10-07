import Congradualate.Gradual

open Gradual

inductive EvalError where
  | TypeError | CastError | ConstantError

export EvalError (TypeError CastError)

inductive SimpleValue (S : TypeSystem) (C : Vector S.𝕋 m) (τ : S.𝕋) where
  | const (c : S.ℂ) (h : S.Δ c = τ)
  | lambda (x : S.𝕏) (σ : S.𝕋)
    (e : TypedExpression S (if · = x then some σ else none) σ')
    (h : σ ⟶ σ' = τ)
  | location (l : Fin m) (h : ref (C[l]) = τ)

/-
inductive SimpleValue (S : TypeSystem) (C : Vector S.𝕋 m) :
    S.𝕋 → Type where
  | const (c : S.ℂ) : SimpleValue S C (S.Δ c)
  | lambda (x : S.𝕏) (σ : S.𝕋) {τ : S.𝕋}
    (e : TypedExpression S (if · = x then some σ else none) τ) :
      SimpleValue S C (σ ⟶ τ)
  | location (l : Fin m) : SimpleValue S C (ref C[l])

def SimpleValue.functionCasesOn {C : Vector S.𝕋 m}
  {motive : SimpleValue S C (σ ⟶ τ) → Sort u}
  (const : ∀ (c : S.ℂ) (h : S.Δ c = σ ⟶ τ), motive (h ▸ SimpleValue.const c))
  («lambda» : ∀ x : S.𝕏,
    ∀ e : TypedExpression S (if · = x then some σ else none) τ,
      motive (.lambda x σ e)) :
    ∀ s : SimpleValue S C (σ ⟶ τ), motive s := rfl |>
  show ∀ {ν}, ∀ h : ν = σ ⟶ τ, ∀ s : SimpleValue S C ν, motive (h ▸ s) from fun
  | _, .const c => const c _
  | _, .location l => nomatch ‹ref C[l] = σ ⟶ τ›
  | _, .lambda x σ' (τ := τ') e => by
    injection ‹σ' ⟶ τ' = σ ⟶ τ› with hσ hτ
    cases hσ
    cases hτ
    exact «lambda» x e
-/

inductive Value (S : TypeSystem) (C : Vector S.𝕋 m) :
    S.𝕋 → Type where
  | simple : SimpleValue S C τ → Value S C τ
  | cast τ (ne : σ ≠ τ := by decide) (con : σ ~ τ := by decide) :
    SimpleValue S C τ → Value S C σ

namespace Value

instance : Coe (SimpleValue S C τ) (Value S C τ) where coe := .simple

protected def castCases {C : Vector S.𝕋 m}
  {motive : Value S C τ → Sort u}
  (cast : ∀ σ, (con : τ ~ σ) → ∀ s : SimpleValue S C σ, motive <|
    if eq : τ = σ then .simple (eq ▸ s) else .cast σ eq con s) :
      ∀ v, motive v
  | .simple s => dif_pos (Eq.refl τ) |>.ndrec <| cast τ .rfl s
  | .cast σ ne con s => dif_neg ne |>.ndrec <| cast σ con s

def unbox : Value S C τ → Σ τ', SimpleValue S C τ'
  | .simple s => ⟨τ, s⟩
  | .cast τ _ _ s => ⟨τ, s⟩

-- abbrev const (c : S.ℂ) : Value S C (S.Δ c) := .simple (.const c)
-- abbrev «lambda» (x : S.𝕏) (σ : S.𝕋) {τ : S.𝕋}
--   (e : TypedExpression S (if · = x then some σ else none) τ) :
--     Value S C (σ ⟶ τ) := .simple (.lambda x σ e)
-- abbrev location {C : Vector S.𝕋 m} (l : Fin m) :
--   Value S C (ref C[l]) := .simple (.location l)

end Value

def Result (S : TypeSystem) (C : Vector S.𝕋 m) (τ : S.𝕋) :=
  Except EvalError (Value S C τ)

def Memory (S : TypeSystem) (C : Vector S.𝕋 m) :=
  ∀ l : Fin m, Value S C C[l]

set_option linter.checkUnivs false
structure ComputationSystem extends TypeSystem where
  -- δ (c : ℂ) (σ τ : ⦗𝔾⦘) (h : Δ c = σ ⟶ τ) :
  --   Value toTypeSystem C σ → Value toTypeSystem C τ
  δ : ℂ → ℂ → ℂ
  δ_lawful (f x : ℂ) (σ τ : ⦗𝔾⦘) :
    Δ f = σ ⟶ τ →
    Δ x ~ σ →
    Δ (δ f x) ~ τ

instance : Coe ComputationSystem TypeSystem where
  coe := ComputationSystem.toTypeSystem

-- def eval (S : ComputationSystem) (C : Vector S.𝕋 m)
--   (μ : Memory S.toTypeSystem C) :
--     {τ : S.𝕋} → TypedExpression S (fun _ ↦ none) τ →
--       Σ m, Σ C : Vector S.𝕋 m, Memory S C × Result S C τ
--   | _, .const c => ⟨m, C, μ, .ok <| .simple <| .const c rfl⟩
--   | τ ⟶ _, .lambda x e => ⟨m, C, μ, .ok <| .simple <| .lambda x τ e rfl⟩
--   | τ', .apply (τ := τ) e₁ e₂ => match eval S C μ e₁ with
--     | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
--     | ⟨m, C, μ, .ok v₁⟩ => v₁.castCases (motive := fun _ ↦ _) fun
--       | _, _, .const c rfl => _
--       | _, _, .lambda x σ e rfl => by
--         rename_i σ' h
--         obtain ⟨h, h'⟩ := TypeConsistent.function_iff.mp h
--   | _, .getref _ => _
--   | _, .deref _ => _
--   | _, .assign _ _ => _
--   | _, .cast _ _ _ _ => _
