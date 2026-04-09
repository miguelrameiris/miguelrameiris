import Exercises.a05Functions

/-
We have that ⟨ a , h ⟩ ∈ {a : A // P a} ↔ a ∈ A ∧ h : P a. Subtype P gives us this tuple,
so Subtype.val P = a and Subtype.property P = h
-/

-- We may define the Subtype Image of a function
def Im {A B : Type} (f : A → B) : Type := { b : B // ∃ (a : A), f a = b }

-- Two subtypes are equal iff their values in A are equal
#check Subtype.eq     -- a1.val = a2.val → a1 = a2
#check Subtype.eq_iff -- a1.val = a2.val ↔ a1 = a2

-- We may define the inclusion function from a Subtype P → A where A is its underlying Type.
-- What we are doing is defining inc: ⟨ a , h ⟩ ↦ a
def inc {A : Type} {P : A → Prop} : Subtype P → A := by
  intro a
  exact a.val

-- We may also restrict a function f : A → B to a subset of A. For this, we define {a : A // P a}
-- and then we do rest f : ⟨ a , h ⟩ ↦ f a
def rest {A B : Type} {P : A → Prop} (f : A → B) : Subtype P → B := by
  intro a
  exact f a.val

-- We may do the same but in B provided that every b ∈ Im f satisfies some condition Q. Therefore, we define the
-- function a ↦ ⟨ f a , Q (f a) ⟩
def correst {A B : Type} {Q : B → Prop} (f : A → B) (h : ∀ (b : Im f), Q b.val)
: A → Subtype Q := by
  intro a
  have ha : ∃ (a1 : A), f a1 = f a := by
    apply Exists.intro a
    exact rfl
  apply Subtype.mk (f a) (h ⟨f a, ha⟩)

-- We define the equalizer of two functions
def Equalizer {A B : Type} (f g : A → B) : Type := { a : A // f a = g a }

-- Now the inclusion function from the Equalizer to A
-- It is clear that this function will be defined ⟨ a.val , a.property ⟩ ↦ a.val
def incEq {A B : Type} (f g : A → B) : Equalizer f g → A := @inc A (fun a => f a = g a)

theorem TEqInc {A B : Type} (f g : A → B) : f ∘ (incEq f g) = g ∘ (incEq f g) := by
  apply funext
  intro a
  calc
    (f ∘ (incEq f g)) a = f a.val := by rfl
                      _ = g a.val := a.property
                      _ = (g ∘ (incEq f g)) a := rfl

-- If two Properties are equivalent, the corresponding subtypes are equal.
theorem TEqSubtype {A : Type} {P1 P2 : A → Prop}
(h : ∀ (a : A), P1 a ↔ P2 a) : Subtype P1 = Subtype P2 := by
  have hP : P1 = P2 := by
    apply funext -- P1 and P2 are functions A → Prop
    intro a
    apply propext -- P1 a and P2 a are Prop
    exact h a
  rw[hP]

-- Im (inc) = Subtype
theorem TUPSub {A : Type} {P : A → Prop} : Im (@inc A P) = Subtype P := by
  apply TEqSubtype
  intro a
  apply Iff.intro
  intro hE
  rcases hE with ⟨ a1 , hinc ⟩ -- a1 = ⟨ a , hP ⟩ with hP : P a
  rw[hinc.symm] -- we change in the goal that a = hinc a1
  exact a1.property

  intro hP
  exact ⟨ ⟨ a , hP ⟩  , rfl ⟩

-- rest f = f ∘ inc (directly from the fact that f ∘ (inc A P) = f {x : A // P x} = rest P f)
theorem TRest {A B : Type} {f : A → B} {P : A → Prop}: (@rest A B P f) = f ∘ (@inc A P) := by
  rfl

-- f = inc ∘ correst (directly from the fact that (inc B Q) ∘ (correst f h) = (inc B Q) f {x : B // Q (f x)}= f {x : A} = f
-- where the second = comes from hypothesis h)
theorem TUPCorrest {A B : Type} {Q : B → Prop} {f : A → B} (h : ∀ (b : Im f), Q b.val) : f = (@inc B Q) ∘ (correst f h) := by
  rfl

-- Unicity
theorem TUPCorrestUn {A B : Type} {Q : B → Prop} {f : A → B}
(h : ∀ (b : Im f), Q b.val) (g : A → Subtype Q) (h1 : f = (@inc B Q) ∘ g) : (correst f h) = g := by
  apply funext
  intro x
  have hQ : Q (f x) := (correst f h x).property
  apply Subtype.ext
  calc
    (correst f h x).val = f x := by rfl
                      _ = ((@inc B Q) ∘ g) x := by rw[h1]
                      _ = @inc B Q (g x) := by rfl
                      _ = (g x).val := by rfl

-- The function incEq is a monomorphism
theorem TincEqMono {A B : Type} {f g : A → B} : monomorphism (incEq f g) := by
  unfold monomorphism
  intro C i j hL
  apply funext
  intro x
  apply Subtype.ext
  calc
    (i x).val = (incEq f g ∘ i) x := by rfl
            _ = (incEq f g ∘ j) x := congrFun hL x
            _ = (j x).val := rfl

-- An epic incEq is an isomorphism
theorem TincEqEpi {A B : Type} {f g : A → B} : epimorphism (incEq f g) →
isomorphism (incEq f g) := by
  intro hEpi
  unfold isomorphism
  unfold epimorphism at hEpi
  have hfg : f = g := by
    exact hEpi (TEqInc f g)
  -- We define the inverse as the function a ↦ ⟨ a , h : fa = ga ⟩
  -- clearly ∀ (a : A), f a = h a from hfg, we introduce a proof of this fact directly
  let finv : A → Equalizer f g := fun a => Subtype.mk a (congrFun hfg a)
  have hl : finv ∘ incEq f g = id := by rfl
  have hr : incEq f g ∘ finv = id := by rfl

  exact ⟨ finv , ⟨ hl , hr ⟩ ⟩
