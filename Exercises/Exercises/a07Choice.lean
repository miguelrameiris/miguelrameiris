import Exercises.a05Functions

open Classical

/-
Classical.choice h chooses an element from h : Nonempty but does not tell us which element
Classical.choose h gives an element satisfying P with h : ∃ (a : A), P
Classical.choose_spec h gives the proof that the element of Classical.choose h satisfies P with h : ∃ (a : A), P
-/

-- Under Classical.Choice, if a function is injective and the domain is Nonempty then the function has a left inverse
theorem TInjtoHasLeftInv {A B : Type} {f : A → B} : injective f →  Nonempty A → hasleftinv f := by
  intro hInjective
  intro hNonempty
  unfold hasleftinv

  let g : B → A := fun b => if h : ∃ (a : A), f a = b then Classical.choose h -- Classical.choose chooses an element satisfying a term
                            else Classical.choice hNonempty -- Classical.choice chooses from Nonempty

  have hg : g ∘ f = id := by
    apply funext
    intro a
    have ha : ∃ (a' : A), f a' = f a := by
      exact ⟨ a , rfl ⟩
    have hEq : Classical.choose ha = a := by
      apply hInjective
      exact Classical.choose_spec ha -- Gives us the proof that our element satisfies ha
    calc
      (g ∘ f) a = g (f a) := by rfl
              _ = Classical.choose ha := by simp[g , ha] -- We simplify g using that ha; simp does also simplify the resulting expression
              -- If we wanted to have the exact expression of the definition of g we would have to use dif_pos ha
              _ = a := hEq
  exact ⟨ g , hg ⟩


-- Under Classical.Choice, every surjective function has a right inverse
noncomputable def Inverse {A B : Type} (f : A → B) (h : surjective f) : B → A := by
  unfold surjective at h
  intro b
  specialize @h b
  exact Classical.choose h

-- Under Classical.Choice, the inverse of a surjective function is a right inverse
theorem InvR {A B : Type} (f : A → B) (h : surjective f) : f ∘ (Inverse f h)  = id := by
  apply funext
  intro x
  unfold surjective at h
  calc
    (f ∘ (Inverse f h)) x = f (Inverse f h x) := by rfl
                        _ = f (Classical.choose h) := by rfl
                        _ = x := Classical.choose_spec h -- Exactly the identity: f (Classical.choose h) = x

-- Under Classical.Choice, every surjective function has a right inverse
theorem TSurjtoHasRightInv {A B : Type} {f : A → B} : surjective f  → hasrightinv f := by
  intro hSurjective
  exact ⟨ Inverse f hSurjective , InvR f hSurjective⟩

-- Under Classical.Choice, the inverse of a bijective function is a left inverse
theorem InvL {A B : Type} (f : A → B) (h : bijective f) :  (Inverse f h.right) ∘ f = id := by
  apply funext
  intro x
  calc
    ((Inverse f h.right) ∘ f) x = Inverse f h.right (f x) := by rfl
                              _ = Classical.choose (@h.right (f x)) := by rfl -- Gives me y such that f y = f x
                              _ = x := h.left (Classical.choose_spec (@h.right (f x))) -- Since f is also inyective, we introduce
                              -- a proof that f y = f x (Classical.choose_spec (@h.right (f x))) and apply injectivity

-- Under Classical.Choice bijective and isomorphism are equivalent concepts
theorem TCarBijIso {A B : Type} {f : A → B} : bijective f ↔ isomorphism f :=  by
  apply Iff.intro
  intro hBijective
  exact ⟨ Inverse f hBijective.right , ⟨ InvL f hBijective , InvR f hBijective.right ⟩ ⟩
  exact TCarIsotoBij
