import Congradualate.Gradual

open Gradual

inductive EvalError where
  | TypeError | CastError | ConstantError | NotImplemented
deriving Repr

export EvalError (TypeError CastError ConstantError NotImplemented)

def Vector.concat (C : Vector α n) (x : α) : Vector α (n + 1) :=
  .mk (C.toArray.push x) (by simp)

@[simp] theorem Vector.concat_getElem_lt {C : Vector α n} {ilt : i < n} :
    (C.concat x)[i] = C[i] := by
  rw [concat, getElem_mk, Array.getElem_push_lt] <;> simp [*]

@[simp] theorem Vector.concat_getLast {C : Vector α n} :
    (C.concat x)[n] = x := by
  rw [concat, getElem_mk]
  conv in n => rw [C.size_toArray.symm]
  exact Array.getElem_push_eq

def Compatible {m n : Nat} (C : Vector α m) (C' : Vector α n) : Prop :=
  ∃ s : Array α, ∃ h : m + s.size = n, C' = .mk (C.toArray ++ s) (by simpa)

namespace Compatible

protected theorem rfl : Compatible C C := ⟨#[], rfl, rfl⟩

protected theorem le
    {C : Vector α m} {C' : Vector α n} : Compatible C C' → m ≤ n
  | ⟨_, h, _⟩ => Nat.le.intro h

protected theorem trans
  {C₁ : Vector α m₁} {C₂ : Vector α m₂} {C₃ : Vector α m₃} :
    Compatible C₁ C₂ → Compatible C₂ C₃ → Compatible C₁ C₃ := by
  rintro ⟨s, rfl, rfl⟩ ⟨t, rfl, rfl⟩
  exists s ++ t, by simp [Nat.add_assoc]
  simp

theorem getElem_eq {C : Vector α m} {C' : Vector α n}
  (h : Compatible C C') (l : Fin m) :
    C[l] = C'[l]'(l.val_lt_of_le h.le) := by
  rcases h with ⟨h, rfl, rfl⟩
  simp

theorem getElem_eq' {C : Vector α m} {C' : Vector α n}
  (h : Compatible C C') (hl : l < m) :
    C[l] = C'[l]'(Nat.lt_of_lt_of_le hl h.le) := by
  rcases h with ⟨h, rfl, rfl⟩
  simp [hl]

theorem ofConcat {C : Vector α n} : Compatible C (C.concat x) := by
  exists #[x], by simp

end Compatible

mutual

inductive Value (S : TypeSystem) (C : Vector S.𝕋 m) : S.𝕋 → Type where
  | const (c : S.ℂ) (h : S.Δ c ~ τ) : Value S C τ
  | lambda (V : ContextValue S C Γ)
    (x : S.𝕏) (σ σ' : S.𝕋)
    (e : TypedExpression S ((x, σ) :: Γ) σ')
    (h : σ ⟶ σ' ~ τ) : Value S C τ
  | location (l : Fin m) (h : ref (C[l]) ~ τ) : Value S C τ

inductive ContextValue (S : TypeSystem) (C : Vector S.𝕋 m) : List (S.𝕏 × S.𝕋) → Type where
  | nil : ContextValue S C []
  | cons (v : Value S C τ) (V : ContextValue S C xs) :
    ContextValue S C ((x, τ) :: xs)

end

instance [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ] : Repr (Value S C τ) where
  reprPrec v _ := "(" ++ (match v with
  | .const c _ => reprPrec c 10
  | .lambda _ x σ _ e _ =>
    "lambda " ++ reprPrec x 10 ++ " : " ++ reprPrec σ 10 ++ " =>" ++
    .indentD (reprPrec e 10)
  | .location l _ => s!"*{l}"
  ) ++ " : " ++ reprPrec τ 10 ++ ")"

mutual

def ContextValue.get (V : ContextValue S C Γ) (x : S.𝕏)
    (h : Γ.lookup x = some τ) : Value S C τ := match V with
  | .cons (x := x') (τ := τ') (xs := xs) v V =>
    if hx : x = x' then
      have : τ' = τ := by simpa [hx] using h
      this ▸ v
    else V.get x <| by
      rw [List.lookup_cons] at h
      split at h
      · rw [beq_iff_eq] at ‹x == x'›
        contradiction
      · exact h

def Value.lift (v : Value S C τ) (hc : Compatible C C') : Value S C' τ :=
  match v with
  | .const c h => .const c h
  | .lambda V x σ σ' e h => .lambda (V.lift hc) x σ σ' e h
  | .location l h => .location ⟨l, l.val_lt_of_le hc.le⟩ (hc.getElem_eq l ▸ h)

def ContextValue.lift (V : ContextValue S C Γ) (hc : Compatible C C') :
    ContextValue S C' Γ := match V with
  | .nil => .nil
  | .cons v V => .cons (v.lift hc) (V.lift hc)

end

def Result (S : TypeSystem) (C : Vector S.𝕋 m) (τ : S.𝕋) :=
  Except EvalError (Value S C τ)

instance [Repr S.𝕏] [Repr S.𝔾] [Repr S.ℂ] : Repr (Result S C τ) :=
  inferInstanceAs <| Repr (Except ..)

def Value.cast : Value S C σ → Result S C τ
  | .const c _ =>
    if h : S.Δ c ~ τ then .ok (.const c h) else .error CastError
  | .lambda V x σ σ' e _ =>
    if h : σ ⟶ σ' ~ τ then .ok (.lambda V x σ σ' e h) else .error CastError
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

set_option linter.checkUnivs false
structure ComputationSystem extends TypeSystem where
  δ : ℂ → ℂ → ℂ
  δ_lawful (f x : ℂ) (σ τ : ⦗𝔾⦘) :
    Δ f = σ ⟶ τ →
    Δ x ~ σ →
    Δ (δ f x) ~ τ

instance : Coe ComputationSystem TypeSystem where
  coe := ComputationSystem.toTypeSystem

set_option linter.unusedVariables false in
def eval (S : ComputationSystem) {Γ : List (S.𝕏 × S.𝕋)} (C : Vector S.𝕋 m)
  (μ : Memory S.toTypeSystem C) (V : ContextValue S C Γ)
  {τ : S.𝕋} (e : TypedExpression S Γ τ) :
    Σ m', Σ C' : {C' : Vector S.𝕋 m' // Compatible C C'},
      Memory S C'.val × Result S C'.val τ :=
  match τ, e with
  | _, .const c => ⟨m, ⟨C, .rfl⟩, μ, .ok <| .const c .rfl⟩
  | _, .var (τ := τ) (x := x) h => ⟨m, ⟨C, .rfl⟩, μ, .ok <| V.get x h⟩
  | τ ⟶ τ', .lambda x e => ⟨m, ⟨C, .rfl⟩, μ, .ok <| .lambda V x τ τ' e .rfl⟩
  | τ', .apply (τ := τ) e₁ e₂ => match eval S C μ V e₁ with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, ⟨C, hC⟩, μ, .ok <| .const c₁ h₁⟩ => match eval S C μ (V.lift hC) e₂ with
      | ⟨m, ⟨C, hC'⟩, μ, .error ε⟩ => ⟨m, ⟨C, hC.trans hC'⟩, μ, .error ε⟩
      | ⟨m, ⟨C, hC'⟩, μ, .ok <| .const c₂ _⟩ => ⟨m, ⟨C, hC.trans hC'⟩, μ,
        match h : S.Δ c₁ with
        | .ground _ | ref _ => nomatch h ▸ h₁
        | ?? => Value.cast (.const (S.δ c₁ c₂) .con_unknown)
        | σ ⟶ σ' => if h₂ : S.Δ c₂ ~ σ
          then Value.cast (.const (S.δ c₁ c₂) <| S.δ_lawful c₁ c₂ σ σ' h h₂)
          else .error CastError⟩
      | ⟨m, ⟨C, hC'⟩, μ, .ok <| _⟩ => ⟨m, ⟨C, hC.trans hC'⟩, μ, .error ConstantError⟩
    | ⟨m, ⟨C, hC⟩, μ, .ok <| .lambda (Γ := Γ) V' x σ σ' e h⟩ =>
      match eval S C μ (V.lift hC) e₂ with
      | ⟨m, ⟨C, hC'⟩, μ, .error ε⟩ => ⟨m, ⟨C, hC.trans hC'⟩, μ, .error ε⟩
      | ⟨m, ⟨C, hC'⟩, μ, .ok v₂⟩ => match v₂.cast (τ := σ) with
        | .error ε => ⟨m, ⟨C, hC.trans hC'⟩, μ, .error ε⟩
        | .ok v =>
          match eval S (Γ := (x, σ) :: Γ) C μ (V'.lift hC' |>.cons v) e with
          | ⟨m, ⟨C, hC''⟩, μ, .error ε⟩ => ⟨m, ⟨C, hC.trans hC' |>.trans hC''⟩, μ, .error ε⟩
          | ⟨m, ⟨C, hC''⟩, μ, .ok v⟩ => ⟨m, ⟨C, hC.trans hC' |>.trans hC''⟩, μ, v.cast⟩
  | _, .getref (τ := τ) e => match eval S C μ V e with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, ⟨C, hC⟩, μ, .ok v⟩ => ⟨m + 1, ⟨C.concat τ, hC.trans .ofConcat⟩,
      fun l ↦ if hl : l < m then by
        simpa [hl] using (μ ⟨l, hl⟩).lift Compatible.ofConcat
      else by
        simpa [show l = ⟨m, m.lt_add_one⟩ by ext; simp only; omega]
          using v.lift Compatible.ofConcat,
      .ok <| .location ⟨m, m.lt_add_one⟩ <| by simpa using .rfl⟩
  | τ, .deref e => match eval S C μ V e with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok <| .const _ _⟩ => ⟨m, C, μ, .error ConstantError⟩
    | ⟨m, C, μ, .ok <| .location l _⟩ => ⟨m, C, μ, (μ l).cast⟩
  | _, .assign e₁ e₂ => match eval S C μ V e₁ with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok <| .const _ _⟩ => ⟨m, C, μ, .error ConstantError⟩
    | ⟨m, ⟨C, hC⟩, μ, .ok <| .location l h⟩ => match eval S C μ (V.lift hC) e₂ with
      | ⟨m, ⟨C, hC'⟩, μ, .error ε⟩ => ⟨m, ⟨C, hC.trans hC'⟩, μ, .error ε⟩
      | ⟨m, ⟨C, hC'⟩, μ, .ok v₂⟩ => ⟨m, ⟨C, hC.trans hC'⟩,
        fun i ↦ if ieq : i = ⟨l, l.val_lt_of_le hC'.le⟩ then by
          simp [TypeConsistent.ref_iff, hC'.getElem_eq] at h
          simpa [ieq, h] using v₂
        else μ i,
        .ok <| .location ⟨l, l.val_lt_of_le hC'.le⟩ <| by simpa [← hC'.getElem_eq']⟩
  | _, .cast (σ := σ) τ e _ _ => match eval S C μ V e with
    | ⟨m, C, μ, .error ε⟩ => ⟨m, C, μ, .error ε⟩
    | ⟨m, C, μ, .ok v⟩ => ⟨m, C, μ, v.cast⟩
termination_by sizeOf e
decreasing_by
  all_goals simp_all; try omega
  sorry
