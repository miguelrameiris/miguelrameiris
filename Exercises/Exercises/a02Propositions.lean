namespace Exercises
variable (A B C D I L M P Q R : Prop)

theorem T51 (h1 : P) (h2 : P → Q) : P ∧ Q := by
  exact ⟨ h1 , h2 h1 ⟩

theorem T52 (h1 : P ∧ Q → R) (h2 : Q → P) (h3 : Q) : R := by
  exact h1 ⟨ h2 h3 , h3 ⟩

theorem T53 (h1 : P → Q) (h2 : Q → R) : P → (Q ∧ R) := by
  intro hP -- intro does not accept that we specify the type, so intro hP : P is wrong
  have hQ : Q := by -- have makes intermediate steps with a reference name
    exact h1 hP
  have hR : R := by
    exact h2 hQ
  exact ⟨ hQ , hR ⟩

 -- otherwise
theorem T53_2 (h1 : P → Q) (h2 : Q → R) : P → (Q ∧ R) := by
  intro hP
  exact ⟨ h1 hP , h2 (h1 hP) ⟩ -- we give a direct proof

theorem T54 (h1 : P) : Q → P := by
  intro hQ
  exact h1

theorem T55 (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  intro hP -- it is defined ¬P = P → False
  have hQ := by
    exact h1 hP
  exact h2 hQ

theorem T56 (h1 : P → (Q → R)) : Q → (P → R) := by
  intro hQ
  have hPR : P → R := by -- proof of P → R
    intro hP
    have hQR : Q → R := by -- proof of Q → R
      exact h1 hP
    exact hQR hQ
  exact hPR

theorem T57 (h1 : P ∨ (Q ∧ R)) : P ∨ Q := by
  cases h1
  -- Case P
  rename_i hP
  exact Or.inl hP
  -- Case Q ∧ R
  rename_i hQR
  have hQ := by -- We extract the proof of Q from the proof of Q ∧ R
    exact hQR.left
  exact Or.inr hQ

theorem T58 (h1 : (L ∧ M) → ¬P) (h2 : I → P) (h3 : M) (h4 : I) : ¬L := by
  intro hL
  have hNotP : ¬ P := by
    exact h1 ⟨ hL , h3 ⟩
  have hP : P := by
    exact h2 h4
  exact hNotP hP

theorem T59 : P → P := by
  intro hP
  exact hP

theorem T510 : ¬ (P ∧ ¬P) := by
  intro hPorNotP
  have hP : P := by exact hPorNotP.left
  have hNotP : ¬ P := by exact hPorNotP.right
  exact hNotP hP

theorem T511 : P ∨ ¬P := by
  exact Classical.em P -- Classical.em has to be applied to a proposition P

theorem T512 (h1 : P ∨ Q) (h2 : ¬P) : Q := by
  cases h1
  rename_i hP
  exact False.elim (h2 hP) -- allows us to get any prop from False
  rename_i hQ
  exact hQ


theorem T513 (h1 : A ∨ B) (h2 : A → C) (h3 : ¬D → ¬B) : C ∨ D := by
  cases h1
  rename_i hA
  have hC : C := by
    exact h2 hA
  exact Or.inl hC
  rename_i hB
  have hNND : ¬¬ D := by
    intro hND
    have hNB : ¬ B := by
      exact h3 hND
    exact False.elim (hNB hB)
  have hD : D := by
    exact Classical.not_not.mp hNND -- Deduces that ¬¬D → D
  exact Or.inr hD

-- Proof that ¬¬P → P
theorem TNNP : ¬¬P → P := by
  intro hNNP -- ¬¬P = (P → False) → False
  have hF : ¬P → False := by -- We build a proof of false
    intro hNP
    exact hNNP hNP
  exact Classical.byContradiction hF -- if we have a contradiction ¬P → Fals, it gives us P

theorem T514 (h1 : A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) := by
  have hAB : A → B := by
    exact h1.mp
  have hBA : B → A := by
    exact h1.mpr
  let hAorhNA : A ∨ ¬A := by -- We use theorem T511 applied to A
    exact T511 A
  cases hAorhNA -- We have that A ∨ ¬A, so we break the cases
  rename_i hA
  have hB : B := by exact hAB hA
  exact Or.inl ⟨ hA , hB ⟩
  rename_i hNA
  have hNB : B → False := by -- We prove ¬B
    intro hB
    have hA : A := by
      exact hBA hB
    exact hNA hA
  exact Or.inr ⟨ hNA , hNB⟩

end Exercises
