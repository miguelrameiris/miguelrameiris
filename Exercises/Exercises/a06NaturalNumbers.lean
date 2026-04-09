import Exercises.a05Functions

-- We define our natural numbers to understand how the work
inductive N : Type where
  | z : N
  | s : N →  N
deriving Repr -- This makes the defined type readable for humans

#print N

open N -- so we can write z instead of N.z
theorem TZInj : ∀ (n : N), z ≠ s n := by
  intro n
  intro h
  cases h
  /- Since the constructors of the inductive type N are disjoint,
  Lean knows that both parts of the equation of h are not
  built the same way and hence, that h is false -/

def max : N → N → N := by
  intro n m
  match n, m with
    | z, m  => exact m
    | n, z  => exact n
    | s n, s m => exact s (max n m)

def min : N → N → N := by
  intro n m
  match n, m with
    | z, _  => exact z
    | _, z  => exact z
    | s n, s m => exact s (min n m)

def Addition : N → N → N := by
  intro n m
  cases n with
  | z   => exact m
  | s n => exact s (Addition n m)
-- Notation for Addition
notation : 65 lhs:65 " + " rhs:66 => Addition lhs rhs

def Fib : N → N := by
  intro n
  match n with
    | z => exact z
    | s z => exact s z
    | s (s n) => exact n + s n

def Multiplication : N → N → N := by
  intro n m
  cases n with
    | z   => exact z
    | s n => exact Multiplication n m + m
-- Notation for Multiplication
notation : 70 lhs:70 " * " rhs:71 => Multiplication lhs rhs

def Factorial : N → N := by
  intro n
  match n with
    | z   => exact s z
    | s n => exact Factorial n * n

-- Prove that no natural number is equal to its own successor
theorem TInjSucc {n : N} : ¬ (n = s n) := by
  intro hP
  cases hP -- Directly by the inductive definition and the fact that
  -- the defining inductive functions are injective

theorem TSinjective : injective s := by
    unfold injective
    intro x y hEq
    cases hEq
    rfl

-- Max (z, n) = n
theorem TMaxzL : ∀ {n : N}, (max z n) = n := by
  intro n
  rfl -- Directly by definition

-- Max (n, z) = n
theorem TMaxzR : ∀ {n : N}, (max n z) = n := by
  intro n
  cases n with -- Here Lean does not know if the first argument is z of s n, we have to consider cases
  -- What is happening is that Lean does not know if it has to use
  -- line 1 or 2 of the definition of max, so we have to consider
  -- both cases
    | z   => rfl
    | s n => rfl

-- Max (n, m) = Max (m, n)
theorem TMaxComm : ∀ {n m : N}, (max n m) = (max m n) := by
  intro n
  induction n
  -- case n = z
  intro m
  exact (calc
    max z m = m := by rfl
          _ = max m z := by rw[TMaxzR]
  )
  -- case n = s n' with H.I.
  rename_i n hInduction_n
  intro m
  cases m with
    | z   => exact (calc
      max (s n) z = s n := by rw[TMaxzR]
                _ = max z (s n) := by rfl
      )
    | s m => exact (calc
      max (s n) (s m) = s (max n m) := by rfl
                    _ = s (max m n) := by rw[hInduction_n]
                    _ = max (s m) (s n) := by rfl
      )

-- Max (n, m) = n ∨ Max (n, m) = m
theorem TMaxOut : ∀ {n m : N}, ((max n m) = n) ∨ ((max n m) = m) := by
  intro n
  induction n
  intro m
  -- case n = z
  exact (Or.inr TMaxzL)
  -- case n = s n'
  rename_i n hInduction
  intro m
  cases m with
    | z   => exact (Or.inl TMaxzR)
    | s m => cases hInduction with -- We break the I.H.
      | inl hmax_n => have h1 : max (s n) (s m) = s n := by
                        exact (calc
                          max (s n) (s m) = s (max n m) := by rfl
                          _ = s n := by rw[hmax_n]
                        )
                      exact Or.inl h1
      | inr hmax_m => have h2 : max (s n) (s m) = s m := by
                        exact (calc
                          max (s n) (s m) = s (max n m) := by rfl
                          _ = s m := by rw[hmax_m]
                        )
                      exact Or.inr h2

-- Max (n, n) = n
theorem TMaxIdpt : ∀ {n : N}, max n n = n := by
  intro n
  induction n
  -- case n = z
  exact rfl
  -- case n = s n'
  rename_i n hInduction
  exact (calc
    max (s n) (s n) = s (max n n) := by rfl
                  _ = s n := by rw[hInduction]
  )

-- Min (z, n) = z
theorem TMinzL : ∀ {n : N}, (min z n) = z := by
  intro n
  rfl

-- Min (n, z) = z
theorem TMinzR : ∀ {n : N}, (min n z) = z := by
  intro n
  cases n with
    | z   => rfl
    | s n => rfl

-- Min (n, m) = Min (m, n)
theorem TMinComm : ∀ {n m : N}, (min n m) = (min m n) := by
  intro n
  induction n
  intro m
  calc
    min z m = z := by rfl
          _ = min m z := TMinzR.symm
  rename_i n hIH
  intro m
  cases m with
    | z   => exact (calc
              min (s n) z = z := by rw[TMinzR]
                        _ = min z (s n) := by rfl
            )
    | s m => exact (calc
              min (s n) (s m) = s (min n m) := by rfl
                            _ = s (min m n) := by rw[hIH]
                            _ = min (s m) (s n) := rfl
            )

-- Min (n, m) = n ∨ Min (n, m) = m
theorem TMinOut : ∀ {n m : N}, ((min n m) = n) ∨ ((min n m) = m) := by
  intro n
  induction n
  intro m
  exact Or.inl TMinzL

  rename_i n hIH
  intro m
  cases m with
    | z   => exact Or.inr TMinzR
    | s m => cases hIH with
      | inl hmin_n => exact Or.inl (calc
                        min (s n) (s m) = s (min n m) := by rfl
                                      _ = s n := by rw[hmin_n]
                      )
      | inr hmin_m => exact Or.inr (calc
                        min (s n) (s m) = s (min n m) := by rfl
                                      _ = s m := by rw[hmin_m]
                      )


-- Min (n, n) = n
theorem TMinIdpt : ∀ {n : N}, min n n = n := by
  intro n
  have h : min n n = n ∨ min n n = n := TMinOut
  cases h with
    | inl h1 => exact h1
    | inr h2 => exact h2

-- Min (n, m) = Max (n, m) → n = m
theorem TMinMaxEq : ∀ {n m : N}, min n m = max n m → n = m := by
  intro n
  induction n
  -- case n = z
  intro m
  cases m with
    | z   => intro hEq
             exact rfl -- We need to give rfl because it gives a TERM of z=z, not the proposition z=z
    | s m => intro hEq
             calc
                z = min z (s m) := by symm; rw[TMinzL]
                _ = max z (s m) := by rw[hEq]
                _ = s m := by rfl
  -- case n = s n
  rename_i n hInduction_n
  intro m
  cases m with
    | z   => intro hEq
             calc
              (s n) = max (s n) z := by symm; rw[TMaxzR]
               _ = min (s n) z := by symm; rw[hEq]
               _ = z := by rfl
    | s m => intro hEq
             have h1 : min n m = max n m := TSinjective hEq -- We can prove this with the injectivity of s over hEq
             have h2: n = m := by exact hInduction_n h1
             exact congrArg s h2 -- this gives a term of s n = s m

-- Min (n, m) = n ↔ Max (n, m) = m
theorem TMinMax : ∀ {n m : N}, min n m = n ↔ max n m = m := by
  intro n m
  apply Iff.intro
  -- left to right
  intro hL
  by_cases h: n = m
  -- case n = m
  calc
    max n m = max n n := by symm; rw[h]
          _ = n := by rw[TMaxIdpt]
          _ = m := by rw[h]
  -- case n ≠ m
  have hdisj : ((max n m) = n) ∨ ((max n m) = m) := by exact TMaxOut
  cases hdisj
  -- case max n m = n
  rename_i hmax_n
  have hminmax : min n m = max n m := by
    calc
      min n m = n := by rw[hL]
            _ = max n m := by symm; rw[hmax_n]
  have hnm : n = m := by exact TMinMaxEq hminmax
  exact False.elim (h hnm ) -- we get a contradiction
  -- case max n m = m
  rename_i hmax_m
  exact hmax_m -- free case

  -- right to left, the proof is symmetric
  intro hR
  by_cases h : n = m
  -- case n = m
  calc
    min n m = min n n := by rw[h]
          _ = n := by rw[TMinIdpt]
  -- case n ≠ m
  have hdisj : ((min n m) = n) ∨ ((min n m) = m) := by exact TMinOut
  cases hdisj
  -- case min n m = n
  rename_i hmin_n
  exact hmin_n
  -- case min n m = m
  rename_i hmin_m
  have hminmax : min n m = max n m := by
    calc
      min n m = m := by rw[hmin_m]
            _ = max n m := by symm; rw[hR]
  have hnm : n = m := by exact TMinMaxEq hminmax
  exact False.elim (h hnm ) -- we get a contradiction

  -- z is a left identity for addition
theorem TAdd0L : ∀ {n : N}, z + n = n := by
  intro n
  rfl

-- z is a right identity for addition
theorem TAdd0R : ∀ {n : N}, n + z = n := by
  intro n
  induction n
  rfl
  rename_i n hIH
  calc
    s n + z = s (n + z) := by rfl
          _ = s n := by rw[hIH]

-- Addition of natural numbers is commutative up to a successor
theorem TAddOne : ∀ {n m : N}, (s n) + m = n + (s m) := by
  intro n
  induction n
  intro m
  calc
    s z + m = s (z + m) := by rfl
          _ = s m := by rw[TAdd0L]
          _ = z + s m := by symm; rw[TAdd0L]
  rename_i n hIH
  intro m
  calc
    s (s n) + m = s (s n + m) := by rfl
              _ = s (n + s m) := by rw[hIH]
              _ = s n + s m := by rfl

-- Addition is commutative
theorem TAddComm : ∀ {n m : N}, n + m = m + n := by
  intro n
  induction n
  intro m
  calc
    z + m = m := by rw[TAdd0L]
        _ = m + z := by symm; rw[TAdd0R]
  rename_i n hIH
  intro m
  calc
    s n + m = s (n + m) := by rfl
          _ = s (m + n) := by rw[hIH]
          _ = s m + n := by rfl
          _ = m + s n := by rw[TAddOne]

-- If the sum of two natural numbers is zero, then the first number must be zero
theorem TAddZ : ∀ {n m : N}, n + m = z → n = z := by
  intro n
  induction n
  intro m hL
  rfl
  rename_i n hIH
  intro m hL
  cases hL

-- If the sum of two natural numbers is zero, then both numbers are zero
theorem TAddZ2 : ∀ {n m : N}, n + m = z → (n = z) ∧ (m = z) := by
  intro n m hL
  apply And.intro
  exact TAddZ hL
  rw[TAddComm] at hL
  exact TAddZ hL

-- Addition is associative
theorem TAddAss : ∀{n m p : N}, (n + m) + p = n + (m + p) := by
  intro n
  induction n
  intro m p
  calc
    (z + m) + p = m + p := by rw[TAdd0L]
              _ = z + (m + p) := by rw[TAdd0L]
  rename_i n hIH
  intro m p
  calc
    (s n + m) + p = (n + s m) + p := by rw[TAddOne]
                _ = n + (s m + p) := by rw[hIH]
                _ = n + s (m + p) := by rfl
                _ = s n + (m + p) := by rw[TAddOne]

-- n can never be equal to n + s k
theorem TAddSucc : ∀ {n k : N}, n = n + (s k) → False := by
  intro n
  induction n
  intro k hL
  cases hL
  rename_i n hIH
  intro k hsnsk
  have h : s n = s (n + s k) := calc
     s n = s n + s k := by exact hsnsk
       _ = s (n + s k) := by rfl
  have h1 : n = n + s k := TSinjective h
  exact False.elim (hIH h1)

-- A number cannot be both ahead of and behind another number by a positive amount
theorem TIncAdd : ∀ {n m k : N}, m = n + (s k) →  n = m + (s k) → False := by
  intro n
  induction n
  intro m k h1 h2
  have h : z = s (k + s k) := by calc
    z = m + s k := by exact h2
    _ = (z + s k) + s k := by rw[h1]
    _ = s k + s k := by rw[TAdd0L]
    _ = s (k + s k) := by rfl
  exact False.elim (TZInj (k + s k) h) -- We have a contradiction with the fact that z ∉ Im[s]

  rename_i n hIH
  intro m k h1 h2
  have h : s n = s n + s (k + s k) := by calc
    s n = m + s k := by exact h2
      _ = (s n + s k) + s k := by rw[h1]
      _ = s n + (s k + s k) := by rw[TAddAss]
      _ = s n + s (k + s k) := by rfl
  exact False.elim (TAddSucc h)

-- Right congruence of addition
theorem TAddCongR : ∀ {n m k : N}, m = k → n + m = n + k := by
  intro n
  induction n
  intro m k hL
  exact (calc
    z + m = m := by rw[TAdd0L]
        _ = k := by exact hL
        _ = z + k := by rw[TAdd0L]
  )

  rename_i n hIH
  intro m k hL
  exact (calc
    s n + m = n + s m := by rw[TAddOne]
          _ = n + s k := by exact hIH (congrArg s hL) -- we need to give hIH that s m = s k
          _ = s n + k := by rw[TAddOne]
  )

-- Left congruence of addition
theorem TAddCongL : ∀ {n m k : N}, m = k → m + n = k + n := by
  intro n m k hL
  exact (calc
    m + n = n + m := by rw[TAddComm]
        _ = n + k := by exact TAddCongR hL
        _ = k + n := by rw[TAddComm]
  )

-- Addition on the left is cancellative
theorem TAddCancL : ∀ {n m k : N}, n + m = n + k → m = k := by
  intro n
  induction n
  intro m k hL
  exact (calc
    m = z + m := by rw[TAdd0L]
    _ = z + k := by exact hL
    _ = k := by rw[TAdd0L]
  )

  rename_i n hIH
  intro m k hL
  have h : n + s m = n + s k := by calc
    n + s m = s n + m := by rw[TAddOne]
          _ = s n + k := by exact hL
          _ = n + s k := by rw[TAddOne]
  have h1 : s m = s k := by exact hIH h
  have h2 : m = k := TSinjective h1 -- by the injectivity of s
  exact h2

-- Addition on the right is cancellative
theorem TAddCancR : ∀ {n m k : N}, m + n = k + n → m = k := by
  intro n m k hL
  have h : n + m = n + k := by calc
    n + m = m + n := by rw[TAddComm]
        _ = k + n := by exact hL
        _ = n + k := by rw[TAddComm]
  exact TAddCancL h

-- Left cancellation property of addition with zero
theorem TAddCancLZ : ∀ {n m : N}, n + m = n → m = z := by
  intro n m hL
  have h : n + m = n + z := by calc
    n + m = n := by exact hL
        _ = n + z := by rw[TAdd0R]
  exact TAddCancL h

-- Right cancellation property of addition with zero
theorem TAddCancRZ : ∀ {n m : N}, m + n = n → m = z := by
  intro n m hL
  have h : n + m = n := by calc
    n + m = m + n := by rw[TAddComm]
        _ = n := by exact hL
  exact TAddCancLZ h

  -- z is a left zero for multiplication
theorem TMult0L : ∀ {n : N}, z * n = z := by
  intro n
  rfl

-- z is a right zero for multiplication
theorem TMult0R : ∀ {n : N}, n * z = z := by
  intro n
  induction n
  rfl
  rename_i n hIH
  exact (calc
    s n * z = (n * z) + z := by rfl
          _ = z + z := by rw[hIH]
          _ = z := TAdd0R
  )

-- We introduce one
def one : N := s z

-- one + n = s n
theorem TOneAddR : ∀ {n : N}, one + n = s n := by
  intro n
  calc
    one + n = s z + n := by rfl
          _ = z + s n := by rw[TAddOne]
          _ = s n := by rw[TAdd0L]

-- n + one = s n
theorem TOneAddL : ∀ {n : N}, n + one = s n := by
  intro n
  calc
    n + one = one + n := by rw[TAddComm]
          _ = s n := by rw[TOneAddR]


-- The different cases for two numbers adding to one
theorem TAddOneCases : ∀ {n m : N}, n + m = one → (n = z ∧ m = one) ∨
(n = one ∧ m = z) := by
  intro n
  induction n
  intro m hL
  have hm : m = one := by calc
    m = z + m := by rw[TAdd0L]
    _ = one := by exact hL
  exact Or.inl ⟨ rfl , hm ⟩
  -- case n = s n
  rename_i n hIH
  intro m hL
  have h : s (n + m) = s z := by calc
    s (n + m) = s n + m := by rfl
            _ = one := by exact hL
            _ = s z := by rfl
  have h1 : n + m = z := TSinjective h -- by injectivity of s
  have h2 : (n = z) ∧ (m = z) := by exact TAddZ2 h1
  exact Or.inr ⟨ by rw[h2.left]; rfl , h2.right ⟩

-- one is a left identity for multiplication
theorem TMult1L : ∀ {n : N}, one * n = n := by
  intro n
  cases n with
    | z   => rfl
    | s n => calc
              one * s n = s z * s n := by rfl
                      _ = (z * s n) + s n := by rfl
                      _ = z + s n := by rw[TMult0L]
                      _ = s n := by rw[TAdd0L]

-- one is a right identity for multiplication
theorem TMult1R : ∀ {n : N}, n * one = n := by
  intro n
  cases n with
    | z   => rfl
    | s n => calc
              s n * one = (n * one) + one := by rfl
                      _ = n + one := by rw[TMult1R]
                      _ = s n + z := by rw[TAddOne]; rfl -- We need two lines because we actually do n + one = n + s z = s n + z
                      _ = s n := by rw[TAdd0R]

-- Multiplication is left distributive over addition
theorem TMultDistL : ∀ {n m k : N}, (n + m) * k = (n * k) + (m * k) := by
  intro n
  induction n
  intro m k
  calc
    (z + m) * k = m * k := by rw[TAdd0L]
              _ = (z * k) + m * k := by rw[TMult0L]; rw[TAdd0L]
  rename_i n hIH
  intro m k
  calc
    (s n + m) * k = (n + s m) * k := by rw[TAddOne]
                _ = (n * k) + (s m * k) := by exact hIH
                _ = (n * k) + ((m * k) + k) := by rfl
                _ = (n * k) + (k + (m * k)) := by rw[@TAddComm (m * k) k]
                _ = ((n * k) + k) + (m * k) := by rw[TAddAss]
                _ = (s n * k) + (m * k) := by rfl

-- Multiplication is right distributive over addition
theorem TMultDistR : ∀ {n m k : N}, n * (m + k) = (n * m) + (n * k) := by
  intro n
  induction n
  intro m k
  calc
    z * (m + k) = z := by rw[TMult0L]
              _ = z + z := by rw[TAdd0R]
              _ = (z * m) + (z * k) := by rw[TMult0L]; rw[TMult0L]
  rename_i n hIH
  intro m k
  calc
    s n * (m + k) = n * (m + k) + (m + k) := by rfl
                _ = ((n * m) + (n * k)) + (m + k) := by rw[hIH]
                _ = (n * m) + (n * k) + (k + m) := by rw[@TAddComm m k]
                _ = (n * m) + ((n * k) + (k + m)) := by rw[TAddAss]
                _ = (n * m) + ((n * k) + k + m) := by rw[TAddAss]
                _ = (n * m) + (s n * k + m) := by rfl
                _ = (n * m) + (m + s n * k) := by rw[@TAddComm (s n * k) m]
                _ = (n * m) + m + s n * k := by rw[TAddAss]
                _ = s n * m + s n * k := by rfl

-- Multiplication is commutative
theorem TMultComm : ∀ {n m : N}, n * m = m * n := by
  intro n
  induction n
  intro m
  calc
    z * m = z := by rw[TMult0L]
        _ = m * z := by rw[TMult0R]
  rename_i n hIH
  intro m
  calc
    s n * m = (n * m) + m := by rfl
          _ = (m * n) + m := by rw[hIH]
          _ = (m * n) + (m * one) := by rw[TMult1R]
          _ = m * (n + one) := by rw[TMultDistR]
          _ = m * s n:= by rw[TOneAddL]

-- If the product of two natural numbers is zero, then one of them must be zero
theorem TMultZ : ∀ {n m : N}, n * m = z → (n = z) ∨ (m = z) := by
  intro n m hL
  cases n with
    | z   => exact Or.inl rfl
    | s n => have hm : (n * m) + m = z := by calc
               (n * m) + m = s n * m := by rfl
                         _ = z := by exact hL
             have hdis : n * m = z ∧ m = z := by exact TAddZ2 hm
             exact Or.inr hdis.right

-- Right congruence of multiplication
theorem TMultCongR : ∀ {n m k : N}, m = k → n * m = n * k := by
  intro n
  induction n
  intro m k hL
  rfl
  rename_i n hIH
  intro m k hL
  calc
    s n * m = n * m + m := by rfl
          _ = n * k + m := by rw[hIH hL]
          _ = n * k + k := by rw[hL]
          _ = s n * k := by rfl

-- Left congruence of addition
theorem TMultCongL : ∀ {n m k : N}, m = k → m * n = k * n := by
  intro n m k hL
  calc
    m * n = n * m := by rw[TMultComm]
        _ = n * k := by rw[TMultCongR hL]
        _ = k * n := by rw[TMultComm]

-- Multiplication is associative
theorem TMultAss : ∀{n m k : N}, (n * m) * k = n * (m * k) := by
  intro n
  induction n
  intro m k
  rfl
  rename_i n hIH
  intro m k
  calc
    (s n * m) * k = ((n * m) + m) * k := by rfl
                _ = (n * m) * k + (m * k) := by rw[TMultDistL]
                _ = n * (m * k) + (m * k) := by rw[hIH]
                _ = n * (m * k) + one * (m * k) := by rw[TMult1L]
                _ = (n + one) * (m * k) := by rw[TMultDistL]
                _ = s n * (m * k) := by rw[TOneAddL]

-- Fix points for multiplication
theorem TMultFix : ∀{n m : N}, n * m = n → n = z ∨ m = one := by
  intro n m hL
  cases m
  have hnz : n = z := by calc
    n = n * z := by exact hL.symm
    _ = z := TMult0R
  exact Or.inl hnz
  rename_i m
  have hn : n * m + n = n := by calc
    n * m + n = n * m + n * one := by rw[TMult1R]
            _ = n * (m + one) := TMultDistR.symm
            _ = n * (s m) := by rw[TOneAddL]
            _ = n := hL
  have hZ : n * m = z := TAddCancRZ hn
  apply Or.elim (TMultZ hZ)
  intro hNZ
  exact Or.inl hNZ
  intro hMZ
  exact Or.inr (congrArg s hMZ)

-- One is the unique idempotent for multiplication
theorem TMultOne : ∀ {n m : N}, n * m = one ↔ (n = one ∧ m = one) := by
  intro n m
  apply Iff.intro
  intro hL
  induction n
  -- Case n = z
  rw[TMult0L] at hL
  cases hL
  -- Case n = s n
  rename_i n hIH
  have hL1 : n * m + m = one := Eq.trans rfl hL
  apply Or.elim (TAddOneCases hL1)

  -- Case n * m = z ∧ m = one
  intro hAnd
  have hsnone : s n = one := by calc
    s n = s n * one := by rw[TMult1R]
      _ = s n * m := by rw[hAnd.right]
      _ = one := hL
  exact ⟨ hsnone , hAnd.right ⟩

  -- Case n * m = one ∧ m = z (Impossible)
  intro hAnd
  have hFalse : z = one := by calc
    z = n * z := TMult0R.symm
    _ = n * m := by rw[hAnd.right]
    _ = one := hAnd.left
  cases hFalse

  -- Right to Left in the Theorem
  intro hR
  calc
    n * m = one * m := by rw[hR.left]
        _ = m := by rw[TMult1L]
        _ = one := by rw[hR.right]
