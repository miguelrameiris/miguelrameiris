-- Two relations are the equal if they coincide in every pair
theorem TEqRel {A : Type} {R S : A → A → Prop} : R = S ↔ ∀ (a1 a2 : A),
R a1 a2 ↔ S a1 a2 := by
  apply Iff.intro
  intro hL x y
  apply Iff.intro
  intro hR
  rw[hL] at hR
  exact hR
  intro hS
  rw[hL.symm] at hS
  exact hS

  intro hR
  apply funext
  intro x
  apply funext
  intro y
  apply propext
  exact hR x y

-- Some relations
-- The empty relation on A
def empty {A : Type} : A → A → Prop := fun _ _ => False

-- The total relation on A
def total {A : Type} : A → A → Prop := fun _ _ => True

-- The diag (diagonal) relation on A
def diag {A : Type} : A → A → Prop := fun x y => (x = y)

-- Properties
def Reflexive {A : Type} (R : A →  A → Prop) : Prop := ∀{a : A}, R a a

def Symmetric {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 : A}, R a1 a2 → R a2 a1

def Antisymmetric {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 : A}, R a1 a2 → R a2 a1 → (a1 = a2)

def Transitive {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a2 a3 → R a1 a3

def Serial {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 : A}, ∃(a2 : A), R a1 a2

def Euclidean {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → R a2 a3

def PartiallyFunctional {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → a2 = a3

def Functional {A : Type} (R : A → A → Prop) : Prop :=
∀(a1 : A), ∃(a2 : A), ∀(a3 : A), R a1 a3 ↔ a2 = a3

def WeaklyDense {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 : A}, (R a1 a2 → ∃(a3 : A), (R a1 a3) ∧ (R a3 a2))

def WeaklyConnected {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → ((R a2 a3) ∨ (a2 = a3) ∨ (R a3 a2))

def WeaklyDirected {A : Type} (R : A → A → Prop) : Prop :=
∀{a1 a2 a3 : A}, R a1 a2 → R a1 a3 → ∃(a4 : A), ((R a2 a4) ∧ (R a3 a4))

variable (A : Type)
variable (R S T: A → A → Prop)

-- Reflexive implies serial
theorem TRefltoSerial : Reflexive R → Serial R := by
  intro hRef
  unfold Serial
  intro x
  exact ⟨ x , hRef ⟩

-- For a symmetric relation, transitive and Euclidean are equivalent
theorem TSymmTransIffSer (hS : Symmetric R) : Transitive R ↔ Euclidean R := by
  apply Iff.intro
  unfold Euclidean
  intro hTrans x y z hRxy hRxz
  have hRyx : R y x := hS hRxy
  exact hTrans hRyx hRxz

  unfold Transitive
  intro hEu x y z hRxy hRyz
  have hRyx : R y x := hS hRxy
  exact hEu hRyx hRyz

-- If a relation is symmetric then it is weakly directed
theorem TSymmtoWDir : Symmetric R → WeaklyDirected R := by
  unfold WeaklyDirected
  intro hSym x y z hRxy hRxz
  exact ⟨ x , ⟨ hSym hRxy , hSym hRxz ⟩ ⟩

-- If a relation is Euclidean and antisymmetric, then it is weakly directed
theorem TEuclASymmtoWDir : Euclidean R → Antisymmetric R → WeaklyDirected R := by
  unfold WeaklyDirected
  intro hEu hAnti x y z hRxy hRxz
  have hRyz : R y z := hEu hRxy hRxz
  have hRzz : R z z := by exact hEu hRxz hRxz
  exact ⟨ z , ⟨ hRyz , hRzz ⟩ ⟩

-- If a relation is Euclidean, then it is weakly connected
theorem TEucltoWConn : Euclidean R → WeaklyConnected R := by
  unfold WeaklyConnected
  intro hEu x y z hRxy hRxz
  have hRyz : R y z := hEu hRxy hRxz
  exact Or.inl hRyz

-- If a relation is functional, then it is serial
theorem TFunctoSer : Functional R → Serial R := by
  unfold Serial
  intro hFun x
  rcases hFun x with ⟨ y , hRxyP ⟩
  have hRxy : R x y := (hRxyP y).mpr rfl
  exact ⟨ y , hRxy ⟩

-- If a relation is symmetric and transitive, then it is Euclidean
theorem TSymmTranstoEucl : Symmetric R → Transitive R → Euclidean R := by
  unfold Euclidean
  intro hSym hTran x y z hRxy hRxz
  exact hTran (hSym hRxy) hRxz

-- If a relation is reflexive and Euclidean, then it is symmetric
theorem TReflEucltoSymm : Reflexive R → Euclidean R → Symmetric R := by
  intro hRef hEu x y hRxy
  exact hEu hRxy (@hRef x)

-- If a relation is symmetric and Euclidean, then it is transitive
theorem TSymmEucltoTrans : Symmetric R → Euclidean R → Transitive R := by
  intro hSym hEu x y z hRxy hRyz
  exact hEu (hSym hRxy) hRyz

-- If a relation is serial, symmetric and transitive, then it is reflexive
theorem TSerSymmTranstoRefl : Serial R → Symmetric R → Transitive R → Reflexive R := by
  intro hSe hSym hTran x
  rcases (@hSe x) with ⟨ y , hRxy ⟩
  exact hTran hRxy (hSym hRxy)

-- Operations on relations

def composition {A : Type} (R S : A → A → Prop) : A → A → Prop := by
  intro a1 a3
  exact ∃ (a2 : A), (R a1 a2) ∧ (S a2 a3)

-- Notation for the composition (\circ)
notation : 65 lhs:65 " ∘ " rhs:66 => composition lhs rhs
#check R ∘ S

def inverse {A : Type} (R : A → A → Prop) : A → A → Prop := by
  intro a1 a2
  exact R a2 a1

-- Notation for the inverse (^)
notation : 65 lhs:65 "^" => inverse lhs
#check R^

def meet {A : Type} (R S : A → A → Prop) : A → A → Prop := by
  intro a1 a2
  exact (R a1 a2) ∧ (S a1 a2)

-- Notation for the meet  (\and)
notation : 65 lhs:65 " ∧ " rhs:66 => meet lhs rhs
#check R ∧ S

def join {A : Type} (R S : A → A → Prop) : A → A → Prop := by
  intro a1 a2
  exact (R a1 a2) ∨ (S a1 a2)

-- Notation for the join (\or)
notation : 65 lhs:65 " ∨ " rhs:66 => join lhs rhs
#check R ∨ S

-- Associativity of composition
theorem TAssComp : R ∘ (S ∘ T) = (R ∘ S) ∘ T := by
  apply funext
  intro x
  apply funext
  intro y
  apply propext

  apply Iff.intro
  intro hRST
  have hE : ∃ (z: A), R x z ∧ (S ∘ T) z y := hRST
  rcases hE with ⟨ z , hRxzandSTzy ⟩
  have hEE : ∃ (w : A), S z w ∧ T w y := hRxzandSTzy.right
  rcases hEE with ⟨ w , hSzwandTwy ⟩
  have hRS : (R ∘ S) x w := by exact ⟨ z , ⟨ hRxzandSTzy.left , hSzwandTwy.left ⟩ ⟩
  exact ⟨ w , ⟨ hRS , hSzwandTwy.right ⟩ ⟩

  intro hRST
  have hE : ∃ (z : A), (R ∘ S) x z ∧ T z y := hRST
  rcases hE with ⟨ z , hRSxz_Tzy ⟩
  have hEE : ∃ (w : A), R x w ∧ S w z := hRSxz_Tzy.left
  rcases hEE with ⟨ w , hRxw_Swz ⟩
  have hST : (S ∘ T) w y := by exact ⟨ z , ⟨ hRxw_Swz.right , hRSxz_Tzy.right ⟩ ⟩
  exact ⟨ w , ⟨ hRxw_Swz.left , hST ⟩ ⟩

-- The diagonal is a left neutral element for the composition
theorem TDiagL : R ∘ (@diag A) = R := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro
  intro hL
  rcases hL with ⟨ z , hRD ⟩
  have hz : z = y := hRD.right
  rw[hz] at hRD
  exact hRD.left

  intro hR
  exact ⟨ y , ⟨ hR , rfl ⟩ ⟩

-- The diagonal is a right neutral element for the composition
theorem TDiagR : (@diag A) ∘ R = R := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro
  intro hL
  rcases hL with ⟨ z , hDR ⟩
  have hz : x = z := hDR.left
  rw[hz.symm] at hDR
  exact hDR.right

  intro hR
  exact ⟨ x , ⟨ rfl , hR ⟩ ⟩

-- The inverse relation of the inverse relation is the original relation
theorem TInvInv : (R^)^ = R := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro hL
  have hRinv : (R^) y x := hL
  exact hRinv

  intro hR
  have hRinv : (R^) y x := hR
  exact hR

-- The inverse of the composition
theorem TInvComp : (R ∘ S)^ = (S^) ∘ (R^) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro hL
  have hRS : (R ∘ S) y x := hL
  rcases hRS with ⟨ z , hRSz ⟩
  have hS : (S^) x z := hRSz.right
  have hR : (R^) z y := hRSz.left
  exact ⟨ z , ⟨ hS, hR ⟩ ⟩

  intro hR
  rcases hR with ⟨ z , hSRz ⟩
  have hR1 : R y z := hSRz.right
  have hS : S z x := hSRz.left
  exact ⟨ z , hR1 , hS ⟩

-- The inverse of the meet
theorem TInvMeet : (R ∧ S)^ = (S^) ∧ (R^) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro ⟨ hR , hS ⟩ -- we may enter both proofs directly
  exact ⟨ hS , hR ⟩

  intro ⟨ hS , hR ⟩
  exact ⟨ hR , hS ⟩

-- The inverse of the join
theorem TInvJoin : (R ∨ S)^ = (S^) ∨ (R^) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro hL
  cases hL
  rename_i hR
  exact Or.inr hR

  rename_i hS
  exact Or.inl hS

  intro hR
  cases hR
  rename_i hS
  exact Or.inr hS

  rename_i hR1
  exact Or.inl hR1

-- Distributivity of composition on the left over join
theorem TDisL : R ∘ (S ∨ T) = (R ∘ S) ∨ (R ∘ T) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro ⟨ z , ⟨ hRxz , hSTzy ⟩ ⟩ -- we brake the ∃ directly
  cases hSTzy
  rename_i hSzy
  exact Or.inl ⟨ z , ⟨ hRxz , hSzy ⟩ ⟩

  rename_i hTzy
  exact Or.inr ⟨ z , ⟨ hRxz , hTzy ⟩ ⟩

  intro hR
  cases hR
  rename_i hRS
  rcases hRS with ⟨ z , ⟨ hRxz , hSzy ⟩ ⟩
  exact ⟨ z , ⟨ hRxz , Or.inl hSzy ⟩ ⟩

  rename_i hRT
  rcases hRT with ⟨ z , ⟨ hRxz , hTzy ⟩ ⟩
  exact ⟨ z , ⟨ hRxz , Or.inr hTzy ⟩ ⟩

-- Distributivity of composition on the right over join
theorem TDisR : (R ∨ S) ∘ T = (R ∘ T) ∨ (S ∘ T) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro ⟨ z , ⟨ hRSxz , hTzy ⟩ ⟩
  cases hRSxz
  rename_i hRxz
  exact Or.inl ⟨ z , ⟨ hRxz , hTzy ⟩ ⟩

  rename_i hSxz
  exact Or.inr ⟨ z , ⟨ hSxz , hTzy ⟩ ⟩

  intro hR
  cases hR
  rename_i hRT
  rcases hRT with ⟨ z , ⟨ hRxz , hTzx ⟩ ⟩
  exact ⟨ z , ⟨ Or.inl hRxz , hTzx ⟩ ⟩

  rename_i hST
  rcases hST with ⟨ z , ⟨ hSxz , hTzx ⟩ ⟩
  exact ⟨ z , ⟨ Or.inr hSxz , hTzx ⟩ ⟩

-- Empty is a left zero for the composition
theorem TEmptLZ : (@empty A) ∘ R = (@empty A) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro ⟨ z , h ⟩
  exact False.elim h.left

  intro hR
  exact False.elim hR

-- Empty is a right zero for the composition
theorem TEmptRZ : R ∘ (@empty A) = (@empty A) := by
  apply TEqRel.mpr
  intro x y
  apply Iff.intro

  intro ⟨ z , h ⟩
  exact False.elim h.right

  intro hR
  exact False.elim hR
