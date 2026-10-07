import Congradualate

open GroundType

def main : IO Unit := do
  IO.println "这是原文作者的疏漏"
  IO.println "在原文中，常量（如 `succ`）只能与其他常量作用（如 `succ 3`）。"
  IO.println "假如编程语言定义常量 `isnumber : ?? ⟶ boolean`，"
  IO.println "那么 `isnumber (lambda \"x\" : number => \"x\")` 是一个类型正确的表达式，"
  IO.println "但既没有运算规则能算出它的数值，又没有报错规则认为其错误。"
  IO.println "这理论上能修，但我暂且把所有由这种疏漏造成的运行问题叫 `ConstantError`。"
  IO.println <| repr <| (fun e ↦ Sigma.mk e <| eval TSys (.mk #[] rfl) nofun e.2) <$>
    Gradual.annotate TSys (fun _ ↦ none)
      (isnumber <| lambda "x" : number => "x")
