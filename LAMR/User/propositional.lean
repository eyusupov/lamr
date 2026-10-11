import LAMR.Util.Propositional

def PropForm.eval (τ : PropAssignment) : PropForm → Bool
  | .var v => PropAssignment.eval τ v
  | .tr => true
  | .fls => false
  | .neg A => ! eval τ A
  | .conj A B => eval τ A && eval τ B
  | .disj A B => eval τ A || eval τ B
  | .impl A B => !(eval τ A) || eval τ B
  | .biImpl A B => eval τ A == eval τ B

def PropForm.atoms : PropForm → List String
  | .var v => [v]
  | .tr => []
  | .fls => []
  | .neg A => atoms A
  | .conj A B => atoms A ++ atoms B
  | .disj A B => atoms A ++ atoms B
  | .impl A B => atoms A ++ atoms B
  | .biImpl A B => atoms A ++ atoms B

def formula := prop!{q → p ∧ ⊤ }
def props := propassign!{q,-p}

#eval formula.eval props

#eval prop!{p ∧ q → q ∧ r}.eval propassign!{p,-q,r}
#eval prop!{p ∧ q → q ∧ r}.eval propassign!{p,q,-r}
#eval formula.atoms

-- Modified theorem 2.1:
-- the size (cardinality) of atoms p is always less than or equal to the total length of the formula string
def size : PropForm → Nat
  | .var _     => 1
  | .tr        => 1
  | .fls       => 1
  | .neg A     => size A + 1
  | .conj A B  => size A + size B + 1
  | .disj A B  => size A + size B + 1
  | .impl A B  => size A + size B + 1
  | .biImpl A B => size A + size B + 1

theorem length_atoms_le_size_short (p : PropForm) : p.atoms.length ≤ size p := by
  induction p with

  | tr | fls | var v => 
    dsimp [PropForm.atoms, size]; omega
  | neg A ih =>
    dsimp [PropForm.atoms, size]; omega

  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB | biImpl A B ihA ihB =>
    dsimp [PropForm.atoms, size]
    rw [List.length_append]
    omega

-- Theorem 2.2
theorem eval_eq_of_atoms_agree (p : PropForm) (τ τ' : PropAssignment)
    (h : ∀ x ∈ p.atoms, PropAssignment.eval τ x = PropAssignment.eval τ' x) :
    p.eval τ = p.eval τ' := by
  induction p generalizing τ τ' with
  | tr => rfl
  | fls => rfl
  | var v => 
    dsimp [PropForm.eval]
    -- Unfold atoms so that it reduces to v ∈ [v]
    exact h v (by simp [PropForm.atoms])
  | neg A ih => 
    dsimp [PropForm.eval]
    have hA : ∀ x ∈ A.atoms, τ.eval x = τ'.eval x := by
      intro x hx
      -- atoms (neg A) is definitionally just atoms A
      exact h x hx
    rw [ih τ τ' hA]

  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB | biImpl A B ihA ihB =>
    -- This single block runs for all 4 binary operators simultaneously
    dsimp [PropForm.eval]
    have hA : ∀ x ∈ A.atoms, τ.eval x = τ'.eval x := by
      intro x hx
      -- Unfold atoms so h knows about the append (++) operator, then use hx
      exact h x (by simp [PropForm.atoms, hx])
    have hB : ∀ x ∈ PropForm.atoms B, PropAssignment.eval τ x = PropAssignment.eval τ' x := by
      intro x hx
      -- Unfold atoms so h knows about the append (++) operator, then use hx
      exact h x (by simp [PropForm.atoms, hx])
    rw [ihA τ τ' hA, ihB τ τ' hB]

def onAllValuations 
  (subfn : PropAssignment → Bool) 
  (v : PropAssignment) 
  (ats : List String) : Bool :=
match ats with
| [] => subfn v
| p :: ps =>
  onAllValuations subfn ((p, false) :: v) ps && 
  onAllValuations subfn ((p, true) :: v) ps

def printTruthTable (fm : PropForm) : String :=
  let ats := fm.atoms
  -- 1. Find the maximum length of the atom names (with a fallback minimum width of 5)
  let maxLen := ats.foldr (fun s acc => max s.length acc) 5
  let width := maxLen + 1

  -- 2. Define string spacing helpers
  let fixw (s : String) : String := 
    s ++ String.ofList (List.replicate (width - s.length) ' ')
  
  let truthString (p : Bool) : String := 
    fixw (if p then "true" else "false")

  -- 3. Row generator that collects each row into a string line
  let rec mkRows (assignment : PropAssignment) (atsRemaining : List String) : String :=
    match atsRemaining with
    | [] => 
      -- Header inputs are fully evaluated in the context of `assignment`
      -- We lookup each atom in our PropAssignment list (falling back to false if missing)
      let lookupAtom (x : String) : Bool := 
        (assignment.lookup x).getD false
      let lis := ats.map (fun x => truthString (lookupAtom x))
      let ans := truthString (fm.eval assignment)
      -- Concatenate row inputs together, followed by the formula outcome separator
      String.join lis ++ "| " ++ ans ++ "\n"
    | p :: ps => 
      -- Recursively branch valuations exactly like onAllValuations
      mkRows ((p, false) :: assignment) ps ++ 
      mkRows ((p, true) :: assignment) ps

  -- 4. Construct Table Headers & Separators
  let headerCells := ats.map fixw
  let header := String.join headerCells ++ "| formula\n"
  
  let sepLength := width * ats.length + 9
  let separator := String.ofList (List.replicate sepLength '-') ++ "\n"

  -- 5. Combine structural pieces together
  header ++ separator ++ (mkRows [] ats) ++ separator

#eval IO.print (printTruthTable prop!{p ∧ q → r})

def tautology ( fm: PropForm ) : Bool :=
  onAllValuations (fun v => fm.eval v) [] (fm.atoms)

#eval tautology prop!{p ∧ q → q ∧ p}

def unsatisfiable (fm: PropForm) : Bool :=
  tautology (PropForm.neg fm)

def satisfiable (fm: PropForm) : Bool :=
  !unsatisfiable fm

def onatoms (f : PropForm → PropForm): PropForm → PropForm
  | .var v => f (.var v)
  | .tr => .tr
  | .fls => .fls
  | .neg A => .neg (onatoms f A)
  | .conj A B => .conj (onatoms f A) (onatoms f B)
  | .disj A B => .disj (onatoms f A) (onatoms f B)
  | .impl A B => .impl (onatoms f A) (onatoms f B)
  | .biImpl A B => .biImpl (onatoms f A) (onatoms f B)

#eval toString (onatoms (fun a => if a == prop!{p} then prop!{p ∧ q} else a) prop!{p → q})

