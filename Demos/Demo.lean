import Logic.DL.Semantics
import Logic.REPEAT.Semantics

inductive MyStateType : Type where
  | s₀ : MyStateType
  | s₁ : MyStateType
  | s₂ : MyStateType

namespace Logic.DL


namespace PDLExample
inductive Rels where
  | a : Rels
  | b : Rels

inductive Atom where
  | p: Atom
  | q: Atom

def model: KripkeModel Rels Atom MyStateType where
  rel := λ rel s s' =>
    match rel, s, s' with
    | .a, .s₀, .s₁ => True      --  s₀ --a--> s₁
    | .a, .s₁, .s₂ => True      --  s₁ --a--> s₂
    | .b, .s₁, .s₀ => True      --  s₁ --b--> s₀
    | _, _, _ => False          -- no other transition is possible

  val := λ atom s =>
    match atom, s with
    | .p, .s₀ => True
    | .p, .s₂ => True
    | .q, .s₁ => True
    | _, _ => False

def φ : DLForm Rels Atom :=
  .diamond (.relAtom .a) (.atom .q)

example: eval model φ .s₀ := by
  simp[φ, eval, evalRel]
  exists MyStateType.s₁
end PDLExample


namespace Euclidean

--procedure identifiers
def GCD: Int := 0
def SWAP: Int := 1

--global variables
def a : GlobVar := .name "a"
def b : GlobVar := .name "b"
def tmp : GlobVar := .name "tmp"

def aVal : Expr := Expr.var (Var.glob a)
def bVal : Expr := Expr.var (Var.glob b)
def tmpVal : Expr := Expr.var (Var.glob tmp)


/-- # GCD proc
0 call SWAP()
1 if b <= 0 return
2 a = a - b
3 repeat
-/
def gcdProc : Proc :=
{
  id := GCD,
  params := [],
  body := [
    {
      line := 0,
      stmt := Stmt.call (Expr.const SWAP) []
    },
    {
      line := 1,
      stmt := Stmt.returnIf (Cond.le bVal (Expr.const 0))
    },
    {
      line := 2,
      stmt := Stmt.assign (Var.glob a) (Expr.const 0) (Expr.sub aVal bVal)
    },
    {
      line := 3,
      stmt := Stmt.repeat
    }
  ]
}

/-- # Swap proc
0 if b <= a return
1 tmp = a
2 a = b
3 b = tmp
4 repeat
-/
def swapProc : Proc :=
{
  id := SWAP
  params := [],
  body := [
    {
      line := 0,
      stmt := Stmt.returnIf (Cond.le bVal aVal)
    },
    {
      line := 1,
      stmt := Stmt.assign (Var.glob tmp) (Expr.const 0) (aVal)
    },
    {
      line := 2,
      stmt := Stmt.assign (Var.glob a) (Expr.const 0) (bVal)
    },
    {
      line := 3,
      stmt := Stmt.assign (Var.glob b) (Expr.const 0) (tmpVal)
    },
    {
      line := 4,
      stmt := Stmt.repeat
    }
  ]
}

--program mapping
def euclidean : Program :=
  λ id ↦ if id = GCD then some gcdProc else
            if id = SWAP then some swapProc else none


--prompt
def prompt : Stmt := Stmt.call (Expr.const GCD) []

theorem gcdWellFormedProc : wellFormedProc gcdProc := by
  constructor
  · rfl
  · intro call hcall
    simp[gcdProc] at *
    aesop
    simp[noDuplicateRefs]

theorem swapWellFormedProc : wellFormedProc swapProc := by
  constructor
  · rfl
  · intro call hcall
    simp[swapProc] at *
    aesop


def tar : DynIndex → Option Proc
  | ε => some gcdProc
  | s ∘ᵢ $ => tar s
  | s ∘ᵢ ι i => match tar s with
    | some p =>
      if p.id = 0 ∧ i = 0 then some swapProc
      else none
    | _ => none
  | _ => none


def cftStates : List DynIndex := [
  ε,
  --first gcd iteration
  ε ∘ᵢ ι 0,
  (ε ∘ᵢ ι 0) ∘ᵢ ι 0,
  (ε ∘ᵢ ι 0) ∘ᵢ #,
  ε ∘ᵢ ι 1,
  ε ∘ᵢ ι 2,
  ε ∘ᵢ ι 3,

  --second gcd iteration
  ε ∘ᵢ $,
  (ε ∘ᵢ $) ∘ᵢ ι 0,
  ((ε ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ ι 0,
  ((ε ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ #,
  (ε ∘ᵢ $) ∘ᵢ ι 1,
  (ε ∘ᵢ $) ∘ᵢ ι 2,
  (ε ∘ᵢ $) ∘ᵢ ι 3,

  --third gcd iteration
  (ε ∘ᵢ $) ∘ᵢ $,
  ((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ ι 0,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ ι 1,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ ι 2,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ ι 3,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ ι 4,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ $,
  ((((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ $) ∘ᵢ ι 0,
  ((((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ $) ∘ᵢ #,
  (((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 0) ∘ᵢ #,
  ((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ ι 1,
  ((ε ∘ᵢ $) ∘ᵢ $) ∘ᵢ #,
  (ε ∘ᵢ $) ∘ᵢ #,
  ε ∘ᵢ #
]

def gcdCFT : CFTrace where
  Q := λ n ↦ cftStates[n]?
  prompt := prompt
  tar := tar


-- initial valuation val_ε/val₀
def gcdVal₀ : Var → Int → Int
  | .glob (.name "a") =>
    λ k ↦ if k = 0 then 2 else 0
  | .glob (.name "b") =>
    λ k ↦ if k = 0 then 1 else 0
  | _ => λ _ ↦ 0


def gcdLiberal : LiberalExecution where
  cft := gcdCFT
  val₀ := gcdVal₀
  seed := λ _ _ _ ↦ 0

def gcdVal : Valuation :=
  λ s var k ↦
    match var with
      | (Var.glob (.name "a")) =>
        if k = 0 then
          if s ∈ (cftStates.take 6) then 2
          else if s ∈ ((cftStates.drop 13).take 6) then 0
          else 1
        else 0
      | (Var.glob (.name "b")) =>
        if k = 0 then
          if s ∈ (cftStates.take 20) then 1 else 0
        else 0
      | (Var.glob (.name "tmp")) => 0
      | _ => 0


def gcdExecution
  (hCFT: validCFTrace gcdCFT)
  (hVal: validValuation gcdVal gcdLiberal)
  (hExec: validExecution gcdVal gcdLiberal): Execution where
    liberal := gcdLiberal
    val := gcdVal
    hCFT := hCFT
    hVal := hVal
    hExec := hExec


def φ : DLForm DynIndexSym Cond :=
  .diamond (.relAtom (.line 3)) (conj (.atom (.le aVal bVal)) (.atom (.le bVal aVal)))

example
  (hCFT: validCFTrace gcdCFT)
  (hVal: validValuation gcdVal gcdLiberal)
  (hExec: validExecution gcdVal gcdLiberal):
    eval (executionModel (gcdExecution hCFT hVal hExec)) φ ⟨ε, ⟨0, rfl⟩⟩ := by
      let targetState : CFTrace.State gcdCFT := ⟨ε ∘ᵢ ι 3, ⟨6, rfl⟩⟩

      apply Exists.intro targetState
      constructor
      · rfl
      · rw[eval_conj_iff]
        constructor <;> rfl
end Euclidean
end DL
