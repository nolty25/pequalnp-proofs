import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_662_aux

-- The triangle on 1, 2 and 4 has one pendant edge at each vertex.
-- Its three disjoint pendant edges force every cover to have size at least three.
def adjBits (i j : Fin 6) : Bool :=
  match i.val with
  | 0 => j == 1
  | 1 => j == 0 || j == 2 || j == 4
  | 2 => j == 1 || j == 3 || j == 4
  | 3 => j == 2
  | 4 => j == 1 || j == 2 || j == 5
  | _ => j == 4

def G : SimpleGraph (Fin 6) where
  Adj i j := adjBits i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

def adjDecidable : DecidableRel G.Adj :=
  fun i j => inferInstanceAs (Decidable (adjBits i j = true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem noC4 : ∀ a b c e : Fin 6, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a →
    a = c ∨ b = e := by
  letI : DecidableRel G.Adj := adjDecidable
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem cover : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) →
    3 ≤ T.card := by
  letI : DecidableRel G.Adj := adjDecidable
  decide

def edges : Finset (Sym2 (Fin 6)) := {s(0,1), s(1,2), s(2,3), s(1,4), s(2,4), s(4,5)}

theorem edgeCount : G.edgeSet.ncard = 6 := by
  have q : ∀ a b : Fin 6, G.Adj a b ↔ s(a,b) ∈ edges := by
    letI : DecidableRel G.Adj := adjDecidable
    decide
  have h : G.edgeSet = (edges : Set (Sym2 (Fin 6))) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b => exact q a b
  rw [h, Set.ncard_coe_finset]
  decide

-- Wires 6 through 10 detect the path 0-1-2-3. Wire 8 also feeds wire 11,
-- so the circuit can test the three neighbors of vertex 4 using one more OR.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit where
  gates := [⟨.or, [0,2]⟩, ⟨.or, [1,3]⟩, ⟨.or, [1,2]⟩,
    ⟨.and, [6,7]⟩, ⟨.and, [9,8]⟩, ⟨.or, [8,5]⟩,
    ⟨.and, [4,11]⟩, ⟨.or, [10,12]⟩]
  output := 13

theorem mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem correct : ∀ (x : Fin 6 → Bool), C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 6, G.Adj u v ∧ x u = true ∧ x v = true := by
  letI : DecidableRel G.Adj := adjDecidable
  decide

open PEqualNP.CircuitLowerBounds

def A : Finset ℕ := {3, 4, 6}
def B : Finset ℕ := {0, 1, 2, 5}
def D : Finset ℕ := {7}

abbrev Wide (j : ℕ) : Prop :=
  ∃ u v : Fin 6, u ≠ v ∧
    (C.wires (List.ofFn (fun i : Fin 6 => decide (i = u)))).getD (6 + j) false = true ∧
    (C.wires (List.ofFn (fun i : Fin 6 => decide (i = v)))).getD (6 + j) false = true

def andTag : GateOp → Bool
  | .and => true
  | _ => false

def orTag : GateOp → Bool
  | .or => true
  | _ => false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem classTable : ∀ j : Fin 8,
    (andTag (C.gates[j.val]'j.isLt).op = true → j.val ∈ A) ∧
    (orTag (C.gates[j.val]'j.isLt).op = true → Wide j.val → j.val ∈ B) ∧
    (orTag (C.gates[j.val]'j.isLt).op = true → ¬ Wide j.val → j.val ∈ D) := by
  decide

theorem and_class (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (ho : g.op = GateOp.and) : j ∈ A := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  apply (classTable ⟨j, h⟩).1
  change andTag (C.gates[j]'h).op = true
  simp [ho, andTag]

theorem wide_class (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (ho : g.op = GateOp.or) (hw : Wide j) : j ∈ B := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  apply (classTable ⟨j, h⟩).2.1 _ hw
  change orTag (C.gates[j]'h).op = true
  simp [ho, orTag]

theorem narrow_class (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (ho : g.op = GateOp.or) (hw : ¬ Wide j) : j ∈ D := by
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  apply (classTable ⟨j, h⟩).2.2 _ hw
  change orTag (C.gates[j]'h).op = true
  simp [ho, orTag]

theorem counts : A.card = 3 ∧ B.card = 4 ∧ D.card = 1 := by decide

end PEqualNP.Outside.L_meta_662_aux

open PEqualNP.Outside.L_meta_662_aux

theorem PEqualNP.Outside.L_meta_662 : ¬ (
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (A B D : Finset ℕ),
      (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) →
      (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∃ u v : Fin n, u ≠ v ∧
          (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧
          (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) →
        j ∈ B) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ¬ (∃ u v : Fin n, u ≠ v ∧
          (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧
          (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) →
        j ∈ D) →
      G.edgeSet.ncard + 2 * k ≤ A.card + B.card + 2 * D.card + 2) := by
  intro bound
  have h := bound 6 3 G C A B D noC4 cover mono correct and_class wide_class narrow_class
  rw [edgeCount, counts.1, counts.2.1, counts.2.2] at h
  omega
