import Logic.REPEAT.Semantics

namespace Logic.DL

theorem rel_iff
  (e: Execution)
  (s s': CFTrace.State e.liberal.cft):

  (executionModel e).rel (DL.DynIndexSym.line i) s s' ↔
  s'.val = DynIndex.cons s.val (DynIndexSym.line i) := by
    rfl


/- The kripke model execution model induced by an execution e is always non-branching-/

theorem rel_non_branching
  (e: Execution)
  (a: DynIndexSym)
  (s t₁ t₂: CFTrace.State e.liberal.cft)
  (h₁ : (executionModel e).rel a s t₁)
  (h₂ : (executionModel e).rel a s t₂):
    t₁ = t₂ := by
      change t₁.val = DynIndex.cons s.val a at h₁
      change t₂.val = DynIndex.cons s.val a at h₂
      apply Subtype.ext
      exact h₁.trans h₂.symm


theorem model_non_branching
  (e: Execution):
  DL.nonBranching (executionModel e) := by
    simp[DL.nonBranching]
    intro relAtom
    intro s t₁ t₂
    intro h₁
    intro h₂
    exact rel_non_branching e relAtom s t₁ t₂ h₁ h₂


def extendModel (M: KripkeModel RelType AtomType State):
  KripkeModel RelType AtomType (Sum State Unit) where
    val := λ atom s ↦ match s with
                        | Sum.inl old_state => M.val atom old_state
                        | Sum.inr () => False
    rel := λ atomic_rel s s' ↦
                      match s, s' with
                        | Sum.inl old_state, Sum.inl old_state' => M.rel atomic_rel old_state old_state'
                        | _, _ => False

end Logic.DL
