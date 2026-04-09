open Classical
variable (A : Type)
variable (P Q : A → Prop)
variable (a b c : A)
variable (R : Prop)

/- Whenever we want to prove an ↔ I will denote by LR to the left to right implication
and RL to the right to left one.

Moreover, every intermidiate term (proof) will be denoted by hSomething.

If we have an implication P → Q, then I will denote hL (proof of the left hand-side) to
a proof of P and hR (proof of the right hand-side) to a proof of Q.
-/

theorem E1 : (∃ (a : A), R) → R := by
  intro hExists
  cases hExists -- this lets us work with the witness and the proposition
  rename_i a hR -- this gives us a : A and hR : R
  exact hR

theorem E2 (a : A) : R → (∃ (a : A), R) := by
  intro hPremise -- has type R
  exact Exists.intro a hPremise -- We introduce an ∃ (a : A) over the proof of R

theorem E3 : (∃ (a : A), P a ∧ R) ↔ (∃ (a : A), P a) ∧ R := by
  have LR : (∃ (a : A), P a ∧ R) → (∃ (a : A), P a) ∧ R := by -- left to right implication
    intro hL
    cases hL
    rename_i a hCon -- we have a witness a : A and hCon : P a ∧ R
    have hPa : P a := by
      exact hCon.left
    have hR : R := by
      exact hCon.right
    exact ⟨ Exists.intro a hPa , hR ⟩

  have RL : (∃ (a : A), P a) ∧ R → (∃ (a : A), P a ∧ R) := by -- right to left implication
    intro hL
    have hExists : ∃ (a : A), P a := by
      exact hL.left
    have hR : R := by
      exact hL.right
    -- we need to get P a, then P a ∧ R, and then ∃a (P a ∧ R)
    cases hExists
    rename_i a hP -- we have a = witness of P a, and we also have hP = a proof of P a
    have hPaR : P a ∧ R := by
      exact ⟨ hP , hR ⟩
    exact Exists.intro a hPaR

  exact Iff.intro LR RL -- We introduce the ↔

-- in order to have this make sense, we have to define what P ∨ Q means


theorem E4 : (∃ (a : A), (P a ∨ Q a)) ↔ (∃ (a : A), P a) ∨ (∃ (a : A), Q a) :=  by sorry
  -- We do the same as before, two implications
  /-have LR : (∃ (a : A), (P ∨ Q) a) → (∃ (a : A), P a) ∨ (∃ (a : A), Q a) := by
    intro hL
    cases hL
    rename_i a hPorQ -- a such that (P a ∨ Q a)
    cases hPorQ -- we break the ∨
    rename_i hPa
    have hExists_Pa: (∃ (a : A), P a) := by
      exact Exists.intro a hPa
    exact Or.inl hExists_Pa
    rename_i hQa
    have hExists_Qa: (∃ (a : A), Q a) := by
      exact Exists.intro a hQa
    exact Or.inr hExists_Qa

  have RL : (∃ (a : A), P a) ∨ (∃ (a : A), Q a) → (∃ (a : A), (P ∨ Q) a) := by
    intro hL
    cases hL -- we break the ∨
    rename_i hExists_Pa
    cases hExists_Pa
    rename_i a hPa
    have hPaorQa : (P ∨ Q) a := by
      exact Or.inl hPa
    exact Exists.intro a hPaorQa
    rename_i hExists_Qa
    cases hExists_Qa
    rename_i a hQa
    have hPaorQa : (P ∨ Q) a := by
      exact Or.inr hQa
    exact Exists.intro a hPaorQa

  exact Iff.intro LR RL-/

theorem E5 : (∀ (a : A), P a) ↔ ¬(∃ (a : A), ¬ P a) := by
  have LR : (∀ (a : A), P a) → ¬(∃ (a : A), ¬ P a) := by
    intro hL
    -- We need to assume the non negated conclusion and arrive at a contradiction
    intro hR
    cases hR
    rename_i a hNotP
     -- We instanciate the ∀x Px to the particual value a
     -- a is conserved as a and Pa as hL
    specialize hL a
    exact hNotP hL -- We derive False

  have RL : ¬(∃ (a : A), ¬P a) → (∀ (a : A), P a) := by
    intro hL
    intro a
    -- By contradiction
    -- We build a proof of False
    have hF : (¬P a) → False := by
      intro hNotP
      have hExistsNotP : (∃ (a : A), ¬P a) := by
        exact Exists.intro a hNotP
      exact hL hExistsNotP
    -- Since he have a proof of False we have a contradiction
    apply byContradiction hF

  exact Iff.intro LR RL

theorem E6 : (∃ (a : A), P a) ↔ ¬ (∀ (a : A), ¬P a) := by
  have LR : (∃ (a : A), P a) → ¬ (∀ (a : A), ¬P a) := by
    intro hL
    intro hNotR -- proof of (∀ (a : A), (¬P) a)
    cases hL
    rename_i a hPa
    specialize hNotR a
    exact hNotR hPa

  have RL : ¬ (∀ (a : A), ¬P a) → (∃ (a : A), P a) := by
    intro hL
    -- By contradiction
    have hF : ¬(∃ (a : A), P a) → False := by
      intro hNotExistsP
      -- This will be our contradiction, we will get it from theorem E5
      have hNotL : (∀ (a : A), ¬P a) := by
        /- If we want to use theorem E5 we need first a proof of
         ∃ (a : A) ¬¬ P a
         We can get it with Classical Logic -/
        have hExistsNotNotP : ¬(∃ (a : A), ¬¬ P a) := by
          intro hExistsNotNotP -- We need to arrive at contradiction here
          cases hExistsNotNotP
          rename_i a hNotNotP
          have hExistsP : (∃ (a : A), P a) := by
            have hP : P a := by
              exact not_not.mp hNotNotP -- ¬¬ P → P
            exact Exists.intro a hP
          exact hNotExistsP hExistsP
        apply (E5 (A := A) (P := fun a => ¬P a)).mpr hExistsNotNotP -- We apply Theorem E5 right to left
      exact hL hNotL
    apply byContradiction hF

  exact Iff.intro LR RL

theorem E7 : (¬∃ (a : A), P a) ↔ (∀ (a : A), ¬P a) := by
  have LR : (¬∃ (a : A), P a) → (∀ (a : A), ¬P a) := by
    intro hL
    -- By contradiction
    have hF : ¬(∀ (a : A), ¬P a) → False := by
      intro hNotForNotP
      have hExistsP : (∃ (a : A), P a) := by
        apply (E6 (A := A) (P := P)).mpr hNotForNotP
      exact hL hExistsP
    apply byContradiction hF

  have RL : (∀ (a : A), ¬P a) → (¬∃ (a : A), P a) := by
    intro hL
    intro hR
    cases hR
    rename_i a hP
    specialize hL a
    exact hL hP

  exact Iff.intro LR RL


theorem E8 : (¬∀ (a : A), P a) ↔ (∃ (a : A), ¬P a) := by
  have LR : (¬∀ (a : A), P a) → (∃ (a : A), ¬P a) := by
    intro hL
    -- By contradiction
    have hF : ¬(∃ (a : A), ¬P a) → False := by
      intro hNotExistsNotP
      have hForP : ∀ (a : A), P a := by
        apply (E5 (A := A) (P := P)).mpr hNotExistsNotP
      exact hL hForP
    apply byContradiction hF

  have RL : (∃ (a : A), ¬P a) → (¬∀ (a : A), P a) := by
    intro hL
    cases hL
    rename_i a hNotP
    -- By contradiction
    have hF : ¬(¬∀ (a : A), P a) → False := by
      intro hNotNotP
      have hForP : ∀ (a : A), P a := by
        apply not_not.mp hNotNotP
      specialize hForP a
      exact hNotP hForP
    apply byContradiction hF

  exact Iff.intro LR RL

theorem E9 : (∀ (a : A), P a → R) ↔ (∃ (a : A), P a) → R := by -- Lean reads (∀ (a : A), P a → R) ↔ ((∃ (a : A), P a) → R)
  have LR : (∀ (a : A), P a → R) → (∃ (a : A), P a) → R := by
    intro hL
    intro hEPa
    cases hEPa
    rename_i a hPa
    specialize hL a
    exact hL hPa

  have RL : ((∃ (a : A), P a) → R) → (∀ (a : A), P a → R) := by
    intro hL
    intro a
    intro hPa
    have hEPa : (∃ (a : A), P a) := by
      exact Exists.intro a hPa
    exact hL hEPa

  exact Iff.intro LR RL

theorem E10 : (∃ (a : A), P a → R) → (∀ (a : A), P a) → R := by
  intro hL
  intro hFPa
  cases hL
  rename_i a hPaToR
  specialize hFPa a
  exact hPaToR hFPa

theorem E11 : (∃ (a : A), R  →  P a) → (R → ∃ (a : A), P a) :=  by
  intro hL
  intro R
  cases hL
  rename_i a hRtoPa
  have hPa : P a := by
    exact hRtoPa R
  exact Exists.intro a hPa
