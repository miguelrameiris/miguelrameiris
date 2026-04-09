import Exercises.a03Quantifiers

open Classical

variable (A B C D : Type)
variable (f : A → B)
variable (g : B → C)
variable (h : C → D)

theorem TCompAss {A B : Type} {f : A → B} {g : B → C} {h : C → D} : h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  funext a -- Function Extensinallity Axiom: (∀x fx = gx) → f = g
  exact rfl -- reflexivity, checks that both sides are the same

theorem TIdNeutral : (f ∘ id = f) ∧ (id ∘ f = f) := by
  apply And.intro

  funext a
  exact rfl

  funext a
  exact rfl

def injective {A B : Type} (f : A → B) : Prop := ∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2)

-- I will prove first a Theorem I will have to use
theorem neg_Exists {A : Type} {P : A → Prop} : ¬(∃ (a : A), P a) ↔ ∀ (a : A), ¬P a := by
  apply Iff.intro
  intro hL
  intro a
  apply Classical.byContradiction
  intro hNNP
  have hP : P a := by apply (Classical.not_not).mp hNNP
  exact hL ⟨ a , hP ⟩ -- this is applying directlly ∃a Pa to hL

  intro hR
  apply Classical.byContradiction
  intro hNNE
  have hEP : ∃ (a : A), P a := by apply (Classical.not_not).mp hNNE
  rcases hEP with ⟨ a , hP ⟩ -- tells us that a witnesses hP
  exact (hR a) hP -- This specializes ∀x ¬Px to x=a and then get the contradiction

theorem neg_and_or : ¬ (P ∧ Q) ↔ ((¬P) ∨ (¬Q)) := by
  apply Iff.intro
  intro hL
  by_cases hP : P -- By cases gives you a new hypothesis, first P and then ¬P
  have hNQ : ¬Q := by
    intro hQ
    exact hL ⟨ hP , hQ ⟩
  exact Or.inr hNQ
  exact Or.inl hP -- Directly the other case

  intro hR
  intro hPQ
  cases hR
  rename_i hNP
  exact hNP hPQ.left
  rename_i hNQ
  exact hNQ hPQ.right

-- Negation of injective
theorem TNegInj {A B : Type} {f : A → B} : ¬ (injective f) ↔ ∃(a1 a2 : A),
f a1 = f a2 ∧ a1 ≠ a2 := by
  apply Iff.intro
  intro hL
  apply Classical.byContradiction
  intro hR
  have hENEP : ∀ (a1 : A), ¬ (∃ (a2 : A), f a1 = f a2 ∧ a1 ≠ a2 ):= (E7 (A := A) (P := fun a1 => (∃ (a2 : A), f a1 = f a2 ∧ a1 ≠ a2 ))).mp hR
  have hENP : ∀ (a1 a2 : A), ¬( f a1 = f a2 ∧ a1 ≠ a2 ) := by
    intro a1
    exact (E7 (A := A) (P := fun a2 => f a1 = f a2 ∧ a1 ≠ a2)).mp (hENEP a1)
  have hEP : ∀ (a1 a2 : A), ((f a1 ≠ f a2) ∨ (a1 = a2)) := by
    intro a1 a2
    by_cases hP : a1 = a2 -- caso a1 = a2
    exact Or.inr hP
    -- now we have that a1 ≠ a2
    have hNfandP : ¬(f a1 = f a2 ∧ a1 ≠ a2) := hENP a1 a2
    have hF : ¬(f a1 = f a2) := by
      apply Classical.byContradiction
      intro hF1
      have hF2 : f a1 = f a2 := Classical.not_not.mp hF1
      exact hNfandP ⟨ hF2 , hP ⟩
    exact Or.inl hF

  have hInjective : ∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2) := by
    intro a1 a2
    intro hEquality
    have hDisjunction : (f a1 ≠ f a2) ∨ (a1 = a2) := hEP a1 a2
    cases hDisjunction
    rename_i hNEquality -- f a1 ≠ f a2
    exact False.elim (hNEquality hEquality)
    rename_i hEqualityA -- a1 = a2
    exact hEqualityA

  exact hL hInjective

  intro hR
  intro hInjective
  rcases hR with ⟨ a1 , a2 , hR1 ⟩
  unfold injective at hInjective
  exact hR1.right (hInjective hR1.left) -- We dont need to specify a1 and a2 since they are implicit

-- The composition of injective functions is injective
theorem TCompInj {A B : Type}  {f : A → B} {g : B → C} (h1 : injective f)
(h2 : injective g) : injective (g ∘ f) := by
  unfold injective
  intro a1 a2
  intro hEquality_Comp
  have hg : f a1 = f a2 := by exact h2 hEquality_Comp -- I use that g is injective the hypothesis hEquality_Comp
  exact h1 hg

-- If the composition (g∘f) is injective, then f is injective
theorem TCompRInj {A B C: Type} {f : A → B} {g : B → C} (h1 : injective (g ∘ f))
: (injective f) := by
  unfold injective
  intro x y
  intro hf
  have hgf : (g ∘ f) x = (g ∘ f) y := by
    calc -- allows us to do a concatenation of equalities
      (g ∘ f) x = g (f x) := by rfl -- rfl check that they are equal BY DEFINITION
              _ = g (f y) := by rw [hf] -- rw [hf] changes every f x IN THE GOAL by f y
              _ = (g ∘ f) y := by rfl
  exact h1 hgf

def monomorphism {A B : Type} (f : A → B) : Prop :=  ∀{C : Type},
∀{g h : C → A}, f ∘ g = f ∘ h → g = h

-- Injective and Monomorphism are equivalent concepts
theorem TCarMonoInj {A B : Type} {f : A → B} : injective f ↔ monomorphism f := by
  apply Iff.intro

  intro hInjective
  unfold monomorphism
  unfold injective at hInjective
  intro C g h
  intro hComp

  have hCompX: ∀ (x : C), f (g x) = f (h x) := by -- We need this to apply function extensionality
    intro x
    calc
      f (g x) = (f ∘ g) x := by rfl
            _ = (f ∘ h) x := by rw[hComp]
            _ = f (h x) := by rfl

  have hForComp : ∀ (x : C), g x = h x := by -- We want to apply function extensionality
    intro x
    exact hInjective (hCompX x)

  exact funext hForComp

  intro hMono
  unfold injective
  unfold monomorphism at hMono
  intro x y
  intro hf

  -- We will define some functions that will give us the proof
  let g : A → A := fun _ => x
  let h : A → A := fun _ => y

  have hComp : f ∘ g = f ∘ h := by
    funext a
    calc
      (f ∘ g) a = f (g a) := by rfl
              _ = f x := by rfl
              _ = f y := by rw[hf]
              _ = f (h a) := by rfl
              _ = (f ∘ h) a := by rfl

  have hgf : ∀ (a : A), g a = h a := by
    exact congrFun (hMono hComp)

  exact (calc
    x = g x := by rfl
    _ = h x := by rw[hgf x]
    _ = y := by rfl
    )

def hasleftinv {A B : Type} (f : A → B) : Prop := ∃(g : B → A), g ∘ f = id

-- If a function has a left inverse then it is injective
theorem THasLeftInvtoInj {A B : Type} {f : A → B} : hasleftinv f → injective f := by
  intro hInv
  rcases hInv with ⟨ g , hgf ⟩
  unfold injective
  intro x y hf
  exact (calc
    x = id x := by rfl
    _ = (g ∘ f) x := by rw[hgf]
    _ = g (f x) := by rfl
    _ = g (f y) := by rw[hf]
    _ = (g ∘ f) y := by rfl
    _ = id y := by rw[hgf]
    _ = y := by rfl
  )

----- Surjections
def surjective {A B : Type} (f : A → B) : Prop := ∀{b : B}, ∃(a : A),
f a = b

def epimorphism {A B : Type} (f : A → B) : Prop := ∀{C : Type},
∀{g h : B → C}, g ∘ f = h ∘ f → g = h

def hasrightinv {A B : Type} (f : A → B) : Prop := ∃(g : B → A), f ∘ g = id

-- Negation of surjective
theorem TNegSurj {A B : Type} {f: A → B} : ¬ (surjective f) ↔ ∃(b : B),
∀ (a : A), f a ≠ b := by
  apply Iff.intro
  intro hNSur
  apply Classical.byContradiction
  intro hNE
  -- We eliminate the ¬ in hNE
  have hFN : ∀ (b : B), ¬∀ (a : A), f a ≠ b := (E7 (A := B) (P := (fun b => ∀ (a : A), f a ≠ b))).mp hNE
  have hFEN : ∀ (b : B), ∃ (a : A), ¬ (f a ≠ b) := by
    intro b
    exact (E8 (A := A) (P := fun a => (f a ≠ b))).mp (hFN b)
  simp at hFEN -- We simplify the righ hand side
  -- We eliminate the ¬ in hNSur
  unfold surjective at hNSur
  simp at hNSur -- This does the previous but directly
  rcases hNSur with ⟨ y , hFSur ⟩
  rcases (hFEN y) with ⟨ a , hFENa ⟩
  exact (hFSur a) hFENa

  intro hE
  rcases hE with ⟨ b , hEb ⟩
  unfold surjective
  apply Classical.byContradiction
  intro hNF
  simp at hNF
  rcases (@hNF b) with ⟨ a , hFab ⟩
  --We use @hNF to make the implicit arguments into explicit,
  --this way we can intro the desired b
  exact (hEb a) hFab

-- The composition of surjective functions is surjective
theorem TCompSurj {A B C : Type} {f : A → B} {g : B → C} (h1 : surjective f)
(h2 : surjective g) : surjective (g ∘ f) := by
  unfold surjective
  intro c
  unfold surjective at h2
  rcases (@h2 c) with ⟨ b , hgb ⟩
  unfold surjective at h1
  rcases (@h1 b) with ⟨ a, hfa ⟩
  have hgfa : (g ∘ f) a = c := by
    calc
      (g ∘ f) a = g (f a) := by rfl
              _ = g b := by rw[hfa]
              _ = c := by rw[hgb]
  exact ⟨ a , hgfa ⟩ -- This works as an Exists.intro


-- If the composition (g ∘ f) is surjective, then g is surjective
theorem TCompLSurj {A B : Type} {f : A → B} {g : B → C}
(h1 : surjective (g ∘ f)) : (surjective g) := by
  unfold surjective
  intro c
  unfold surjective at h1
  rcases (@h1 c) with ⟨ a, hfga ⟩
  have hg : g (f a) = c := by
    calc
      g (f a) = (g ∘ f) a := by rfl
            _ = c := by rw[hfga]
  exact ⟨ f a , hg ⟩

-- Surjective and Epimorphism are equivalent concepts
theorem TCarEpiSurj {A B : Type} {f : A → B} : surjective f ↔ epimorphism f := by
  apply Iff.intro

  intro hSur
  unfold epimorphism
  intro C g h hgf
  unfold surjective at hSur
  apply funext
  intro b
  rcases (@hSur b) with ⟨ a , hfa ⟩
  exact (calc
    g b = g (f a) := by rw[hfa]
      _ = (g ∘ f) a := by rfl
      _ = (h ∘ f) a := by rw[hgf]
      _ = h (f a) := by rfl
      _ = h b := by rw[hfa]
  )

  intro hEpi
  unfold surjective
  intro b
  apply Classical.byContradiction
  intro hNE
  simp at hNE
  unfold epimorphism at hEpi

  let g : B → Bool := fun x => if x ≠ b then true else false --This needs Classical
  let h : B → Bool := fun x => true

  have hgh : (g ∘ f) = (h ∘ f) := by
    apply funext
    intro x
    have hx : f x ≠ b := by
      apply Classical.byContradiction
      intro hfx
      simp at hfx
      exact (hNE x) hfx
    exact (calc
      (g ∘ f) x = g (f x) := by rfl
              _ = true := by simp[g , hx]
              _ = h (f x) := by simp[h]
              _ = (h ∘ f) x := by rfl
    )

  have hgh1 : g = h := by
    exact (@hEpi Bool g h) hgh

  have hghb : g b = h b := by rw[hgh1]
  simp [g , h] at hghb --This gives us that false = true and that is our contradiction

-- If a function has a right inverse then it is surjective
theorem THasRightInvtoInj {A B : Type} {f : A → B} : hasrightinv f → surjective f := by
  intro hInv
  unfold hasrightinv at hInv
  rcases hInv with ⟨ g , hfg ⟩
  unfold surjective
  intro b
  have hfgb : f (g b) = b := by
    exact(calc
      f (g b) = (f ∘ g) b := by rfl
            _ = id b := by rw[hfg]
            _ = b := by rfl
    )
  exact ⟨ g b , hfgb ⟩

-- Bijections
def bijective {A B : Type} (f : A → B) : Prop := injective f ∧ surjective f

def isomorphism {A B : Type} (f : A → B) : Prop := ∃ (g : B → A),
g ∘ f = id ∧ f ∘ g = id

-- The composition of bijective functions is bijective
theorem TCompBij {A B C : Type} {f : A → B} {g : B → C} (h1 : bijective f)
(h2 : bijective g) : bijective (g ∘ f) := by
  unfold bijective
  apply And.intro -- We will prove both thing parts of the and

  unfold injective
  intro x y hgcompf
  have hf : f x = f y := by
    exact h2.left hgcompf
  exact h1.left hf

  unfold surjective
  intro c
  have hg : ∃(b : B), g b = c := by
    exact @h2.right c
  rcases hg with ⟨ b , hgb ⟩
  have hf : ∃(a : A), f a = b := by
    exact @h1.right b
  rcases hf with ⟨ a , hfa ⟩
  have hgfa : (g ∘ f) a = c := by
    exact(calc
      (g ∘ f) a = g (f a) := by rfl
              _ = g b := by rw[hfa]
              _ = c := by rw[hgb]
    )
  exact ⟨ a , hgfa ⟩

-- A function is an isomorphism if and only if
-- it has left and right inverse
theorem TCarIso {A B : Type} {f : A → B} : isomorphism f ↔ (hasleftinv f
∧ hasrightinv f) := by
  apply Iff.intro

  intro hIso
  rcases hIso with ⟨ g , hfg_doble ⟩

  apply And.intro
  unfold hasleftinv
  exact ⟨ g , hfg_doble.left ⟩
  exact ⟨ g, hfg_doble.right ⟩

  intro hInv_doble
  rcases hInv_doble.left with ⟨ g , hgf ⟩
  rcases hInv_doble.right with ⟨ h , hfh ⟩

  have hgh : g = h := by
    exact(calc
      g = g ∘ id := by rfl
      _ = g ∘ (f ∘ h) := by rw[hfh]
      _ = (g ∘ f) ∘ h := by rw[TCompAss]
      _ = id ∘ h := by rw[hgf]
      _ = h := by rfl
    )

  -- We now susbtitute the h by g in the proof of f ∘ h = id
  -- Since we proved that g = h, we need to substitute the
  -- right side by the left one, rw does the left one by the right
  -- so we need to write the ← to indicate we want the other.
  rw[← hgh] at hfh
  exact ⟨ g , ⟨ hgf , hfh ⟩ ⟩

-- Every isomorphism is bijective
theorem TCarIsotoBij {A B : Type} {f : A → B} : isomorphism f → bijective f := by
  intro hIso
  unfold isomorphism at hIso
  unfold bijective
  rcases hIso with ⟨ g , hfg_doble ⟩

  apply And.intro
  -- We will apply both previous theorems
  exact THasLeftInvtoInj ⟨ g , hfg_doble.left ⟩
  exact THasRightInvtoInj ⟨ g , hfg_doble.right ⟩
