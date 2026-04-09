import Exercises.a05Functions
import Exercises.a07Choice
import Exercises.a08Subtypes
import Exercises.a09Relations

#print meet
#print Equivalence

-- Quotients work as intended:
theorem TEqQuotient {A : Type} {S : Setoid A} {a1 a2 : A} :
Quotient.mk S a1 = Quotient.mk S a2 ↔ S.r a1 a2 := by
  apply Iff.intro
  -- Quotient.mk S a1 = Quotient.mk S a2 → Setoid.r a1 a2
  apply Quotient.exact
  -- Setoid.r a1 a2 → Quotient.mk S a1 = Quotient.mk S a2
  apply Quotient.sound

def Ker {A B : Type} (f : A → B) : A → A → Prop := by
  intro a1 a2
  exact f a1 = f a2

  -- The projection function
def pr {A : Type} (S : Setoid A) : A → Quotient S := by
  intro a
  exact Quotient.mk S a

-- The meet of two equivalence relations is an equivalence relation
instance TMeetEqv {A : Type} {R S : A → A → Prop} (hR : Equivalence R)
(hS : Equivalence S) : Equivalence (R ∧ S) := by
  constructor
  · intro x
    exact ⟨ hR.refl x, hS.refl x⟩
  · intro x y ⟨ hRxy , hSxy ⟩
    exact ⟨ hR.symm hRxy, hS.symm hSxy ⟩
  · intro x y z ⟨ hRxy , hSxy ⟩ ⟨ hRyz , hSyz ⟩
    exact ⟨ hR.trans hRxy hRyz , hS.trans hSxy hSyz ⟩

#check Quotient
-- If two setoids have equivalent underlying relations, the corresponding quotient types are equal
theorem TEqQuotype {A : Type} {R1 R2 : Setoid A}
(h : ∀ (a1 a2 : A), R1.r a1 a2 ↔ R2.r a1 a2) : Quotient R1 = Quotient R2 := by
  have hR : R1 = R2 := by
    cases R1
    rename_i R_1 hR1
    cases R2
    rename_i R_2 hR2
    congr -- If we prove that R_1 = R_2 then generating the Equivalence relation with them will yield the same
    apply funext
    intro x
    apply funext
    intro y
    apply propext
    exact h x y
  rw[hR]

  -- Ker (pr R) = R.r
theorem TUPQuot {A : Type} {R : Setoid A} : Ker (pr R) = R.r := by
  apply funext
  intro x
  apply funext
  intro y
  apply propext
  apply Iff.intro
  intro hKer
  have hpr : pr R x = pr R y := hKer
  exact TEqQuotient.mp hpr

  intro hSet
  have hpr : pr R x = pr R y := TEqQuotient.mpr hSet
  exact hpr

def ast {A B : Type} {S : Setoid B} (f : A → B) : A → Quotient S := by
  intro a
  exact Quotient.mk S (f a)

-- The astriction ast f is equal to pr ∘ f.
theorem TAst {A B : Type} {f : A → B} {S : Setoid B}: (@ast A B S f) =
(@pr B S) ∘ f := by
  rfl

-- We convert elements of type A → B into ℚuotient R → B
def coast {A B : Type} {R : Setoid A} (f : A → B) (h : ∀ (a1 a2 : A),
R.r a1 a2 → (Ker f) a1 a2) : Quotient R → B := by
  apply Quotient.lift f
  intro a1 a2 h1
  exact (h a1 a2) h1

-- f = coast ∘ pr
theorem TUPCoast {A B : Type} {R : Setoid A} {f : A → B} (h : ∀ (a1 a2 : A),
R.r a1 a2 → (Ker f) a1 a2) : f =  (coast f h) ∘ (@pr A R) := by
  rfl

-- Unicity
theorem TUPCoastUn {A B : Type} {R : Setoid A} {f : A → B} (h : ∀ (a1 a2 : A),
R.r a1 a2 → (Ker f) a1 a2) (g : Quotient R → B) (h1 : f = g ∘ (@pr A R)) : (coast f h) = g := by
  apply funext
  intro x
  rcases Quotient.exists_rep x with ⟨ x_A , hx_A ⟩
  rw[hx_A.symm]
  calc
    coast f h (Quotient.mk R x_A) = (coast f h ∘ (@pr A R)) x_A := by exact rfl
                                _ = f x_A := by rfl
                                _ = (g ∘ (@pr A R)) x_A := by rw[h1]
                                _ = g (@pr A R x_A) := by rfl
                                _ = g (Quotient.mk R x_A) := rfl

-- The subtype of all isomorphisms from a type A to a type B
def Iso (A B : Type) := {f : A → B // isomorphism f}

-- Two types A and B are isomorphic if there is some isomorphism from A to B
def Isomorphic : Type → Type → Prop := by
  intro A B
  exact Nonempty (Iso A B)

-- Notation for Isomorphic types (\cong)
notation : 65 lhs:65 " ≅ " rhs:66 => Isomorphic lhs rhs

theorem TidInj (A : Type): injective (@id A) := by
  intro x y hid
  exact hid

theorem TidSur (A : Type) : surjective (@id A) := by
  intro a
  exact ⟨ a , rfl ⟩

-- Being isomorphic is an equivalence relation
theorem TIsoEqv : Equivalence Isomorphic := by
  constructor
  intro A
  /- We first create an element of the subtype Iso (A A)
  using the fact that id is an isomorphism
  and then we prove that that subtype is nonempty
  -/
  exact Nonempty.intro (Subtype.mk (@id A) (TCarBijIso.mp ⟨ TidInj A , TidSur A ⟩))

  intro A B hAB
  unfold Isomorphic at hAB
  have hFAB := Classical.choice hAB
  have hEBA := (TCarIso.mp hFAB.property)
  rcases hEBA.left with ⟨ fInv_left , hFinv_left ⟩
  rcases hEBA.right with ⟨ fInv_right , hFinv_right ⟩
  let f := hFAB.val
  have hFBA : isomorphism fInv_left := by
    unfold isomorphism
    have hffl : f ∘ fInv_left = id := by
      apply funext
      intro x
      calc
        (f ∘ fInv_left) x = (f ∘ fInv_left ∘ id) x := by rfl
                        _ = (f ∘ fInv_left ∘ f ∘ fInv_right) x := by rw[hFinv_right]
                        _ = (f ∘ ((fInv_left ∘ f) ∘ fInv_right)) x := by rw[← TCompAss]
                        _ = (f ∘ id ∘ fInv_right) x := by rw[hFinv_left.symm]
                        _ = (f ∘ fInv_right) x := by rfl
                        _ = id x := by rw[hFinv_right]
                        _ = x := by rfl
    exact ⟨ f , ⟨ hffl , hFinv_left ⟩ ⟩
  exact Nonempty.intro (Subtype.mk fInv_left hFBA)

  intro A B C hAB hBC
  rcases Classical.choice hAB with ⟨ f , hf ⟩
  rcases Classical.choice hBC with ⟨ g , hg ⟩
  have hbij : bijective f := TCarBijIso.mpr hf
  have hcomp : bijective (g ∘ f) := by
    apply TCompBij
    exact TCarBijIso.mpr hf
    exact TCarBijIso.mpr hg
  exact Nonempty.intro (Subtype.mk (g ∘ f) (TCarBijIso.mp hcomp))

-- The diagonal is reflexive
theorem TDiagRefl {A : Type} : Reflexive (@diag A) := by
  intro a
  exact rfl

-- The diagonal is symmetric
theorem TDiagSymm {A : Type} : Symmetric (@diag A) := by
  intro a1 a2 h
  exact h.symm

-- The diagonal is transitive
theorem TDiagTrans {A : Type} : Transitive (@diag A) := by
  intro a1 a2 a3 h1 h2
  exact h1.trans h2

theorem TDiagEqv {A : Type} : Equivalence (@diag A) := {
  refl  := by
    intro a
    exact TDiagRefl
  symm  := by
    intro a1 a2
    exact TDiagSymm
  trans := by
    intro a1 a2 a3
    exact TDiagTrans
}

instance DiagSetoid {A : Type} : Setoid A := {
  r     := @diag A
  iseqv := TDiagEqv
}
def QDiag {A : Type} := Quotient (@DiagSetoid A)

theorem TDiag {A : Type} : A ≅ @QDiag A := by
  let f : A → @QDiag A := fun a => Quotient.mk (@DiagSetoid A) a
  have hfIso : isomorphism f := by
    apply TCarBijIso.mp
    apply And.intro
    -- f is injective
    intro x y hfxy
    have hR : (@DiagSetoid A).r x y := by
      apply TEqQuotient.mp
      exact hfxy
    exact hR
    -- f is surjective
    intro b
    apply Quotient.exists_rep

  exact Nonempty.intro (Subtype.mk f hfIso)

-- The total quotient
theorem TTotalEqv {A : Type} : Equivalence (@total A) := {
  refl  := by
    intro _
    exact trivial
  symm  := by
    intro a1 a2 _
    exact trivial
  trans := by
    intro a1 a2 a3 _ _
    exact trivial
}

instance TotalSetoid {A : Type} : Setoid A := {
  r     := @total A
  iseqv := TTotalEqv
}

def QTotal {A : Type} := Quotient (@TotalSetoid A)

theorem TTotal {A B : Type} (hA : Nonempty A) (hB : Nonempty B) :
@QTotal A ≅ @QTotal B := by
  have a : A := Classical.choice hA
  have b : B := Classical.choice hB
  let f : @QTotal A → @QTotal B := fun _ => Quotient.mk (@TotalSetoid B) b
  have hfIso : isomorphism f := by
    apply TCarBijIso.mp
    apply And.intro
    -- f injective
    intro x y hfxy
    rcases Quotient.exists_rep x with ⟨ x_A , hx_A ⟩
    rcases Quotient.exists_rep y with ⟨ y_A , hy_A ⟩
    have hR : (@TotalSetoid A).r x_A y_A := by trivial
    rw[hx_A.symm]
    rw[hy_A.symm]
    exact TEqQuotient.mpr hR
    -- f surjective
    intro c
    rcases Quotient.exists_rep c with ⟨ c_B , hc_B ⟩
    have hcb : Quotient.mk (@TotalSetoid B) b = c := by
      rw[hc_B.symm]
      apply TEqQuotient.mpr
      trivial
    exact ⟨ Quotient.mk (@TotalSetoid A) a, by trivial ⟩

  exact Nonempty.intro (Subtype.mk f hfIso)

-- The kernel of a function is an equivalence relation
theorem TKerEqv {A B : Type} {f : A → B} : Equivalence (Ker f) := {
  refl  := by
    intro a
    exact rfl
  symm  := by
    intro a1 a2 h1
    exact h1.symm
  trans := by
    intro a1 a2 a3 h1 h2
    exact h1.trans h2
}

instance KerSetoid {A B : Type} (f : A → B) : Setoid A := {
  r     := Ker f
  iseqv := TKerEqv
}

def QKer {A B : Type} (f : A → B) := Quotient (KerSetoid f)

-- First Isomorphism Theorem
theorem TKerIm {A B : Type} (f : A → B) : QKer f ≅ Im f := by
  have h1 : ∀ (b : Im f), ∃ (a : A), f a = b.val := by
    intro b
    exact b.property
  -- we restrict f : A → B to g : A → Im f
  let g : A → Im f := correst f h1
  have hKer : Ker f = Ker g := by
    apply TEqRel.mpr
    intro x y
    apply Iff.intro
    intro hkerf
    unfold Ker
    apply Subtype.ext
    calc
      (g x).val = (correst f h1 x).val := by rfl
              _ = f x := by rfl
              _ = f y := hkerf
              _ = (correst f h1 y).val := by rfl
              _ = (g y).val := by rfl

    intro hkerg
    unfold Ker
    unfold Ker at hkerg
    calc
      f x = (correst f h1 x).val := by rfl
        _ = (g x).val := by rfl
        _ = (g y).val := by apply congrArg Subtype.val hkerg
        _ = (correst f h1 y).val := by rfl
        _ = f y := by rfl

  have h : ∀ (a1 a2 : A), (KerSetoid g).r a1 a2 → (Ker g) a1 a2 := by
    intro a b hKer
    trivial

  have hCoast : isomorphism (coast g h) := by
    apply TCarBijIso.mp
    apply And.intro
    -- coast g h injective
    intro x y hcoastxy
    rcases Quotient.exists_rep x with ⟨ x_A , hx_A ⟩
    rcases Quotient.exists_rep y with ⟨ y_A , hy_A ⟩
    rw[hx_A.symm]
    rw[hy_A.symm]
    apply TEqQuotient.mpr
    have hf : g x_A = g y_A := by calc
      g x_A = coast g h (Quotient.mk (KerSetoid g) x_A) := by rfl
          _ = coast g h x := by rw[hx_A]
          _ = coast g h y := hcoastxy
          _ = coast g h (Quotient.mk (KerSetoid g) y_A) := by rw[hy_A]
          _ = g y_A := by rfl
    trivial

    -- coast f h surjective
    intro b
    rcases b.property with ⟨ a , hfa ⟩
    apply Exists.intro
    apply Eq.symm
    apply Subtype.ext
    calc
      b.val = f a := by rw[hfa]
          _ = (correst f h1 a).val := by rfl
          _ = (g a).val := by rfl
          _ = (coast g h (Quotient.mk (KerSetoid g) a)).val:= by rfl

  unfold QKer
  unfold KerSetoid
  simp[hKer]
  exact Nonempty.intro (Subtype.mk (coast g h) hCoast) -- I have proved that A/Ker g ≅ Im f
