import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

theorem fanInTwo_of {C : Circuit}
    (h : C.gates.all (fun g => okOp g.op && decide (g.inputs.length ≤ 2)) = true) :
    FanInTwo C := by
  intro g hg
  have hg' := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
  refine ⟨?_, hg'.2⟩
  have h1 := hg'.1
  cases hop : g.op <;> simp_all [okOp]

theorem all2 {P : (Fin 2 → Bool) → Prop}
    (h : ∀ a b : Bool, P ![a, b]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _

theorem all3 {P : (Fin 3 → Bool) → Prop}
    (h : ∀ a b c : Bool, P ![a, b, c]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _ _

theorem all4 {P : (Fin 4 → Bool) → Prop}
    (h : ∀ a b c d : Bool, P ![a, b, c, d]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _ _ _

theorem all5 {P : (Fin 5 → Bool) → Prop}
    (h : ∀ a b c d e : Bool, P ![a, b, c, d, e]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _ _ _ _

theorem all6 {P : (Fin 6 → Bool) → Prop}
    (h : ∀ a b c d e f : Bool, P ![a, b, c, d, e, f]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _ _ _ _ _

theorem all7 {P : (Fin 7 → Bool) → Prop}
    (h : ∀ a b c d e f g : Bool, P ![a, b, c, d, e, f, g]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _ _ _ _ _ _

theorem conj_1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 :=
  ⟨⟨[⟨.and, [0, 1]⟩], 2⟩, fanInTwo_of (by decide), by decide, all2 (by decide +kernel)⟩

theorem conj_2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩], 4⟩, fanInTwo_of (by decide), by decide, all3 (by decide +kernel)⟩

theorem conj_3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩, fanInTwo_of (by decide), by decide, all3 (by decide +kernel)⟩

theorem conj_4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 :=
  ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩, fanInTwo_of (by decide), by decide, all4 (by decide +kernel)⟩

theorem conj_5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩, fanInTwo_of (by decide), by decide, all4 (by decide +kernel)⟩

theorem conj_6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩, fanInTwo_of (by decide), by decide, all4 (by decide +kernel)⟩

theorem conj_7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩, fanInTwo_of (by decide), by decide, all4 (by decide +kernel)⟩

theorem conj_8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩], 8⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩], 8⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 :=
  ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩], 11⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all5 (by decide +kernel)⟩

theorem conj_18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 :=
  ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩], 10⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [10, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [10, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [11, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [11, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [11, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all6 (by decide +kernel)⟩

theorem conj_43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 :=
  ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩], 12⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 :=
  ⟨⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [12, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

theorem conj_85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 :=
  ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, fanInTwo_of (by decide), by decide, all7 (by decide +kernel)⟩

end PEqualNP.Outside.L_meta_926_aux

open PEqualNP.Outside.L_meta_926_aux

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨conj_1, conj_2, conj_3, conj_4, conj_5, conj_6, conj_7, conj_8, conj_9, conj_10, conj_11, conj_12, conj_13, conj_14, conj_15, conj_16, conj_17, conj_18, conj_19, conj_20, conj_21, conj_22, conj_23, conj_24, conj_25, conj_26, conj_27, conj_28, conj_29, conj_30, conj_31, conj_32, conj_33, conj_34, conj_35, conj_36, conj_37, conj_38, conj_39, conj_40, conj_41, conj_42, conj_43, conj_44, conj_45, conj_46, conj_47, conj_48, conj_49, conj_50, conj_51, conj_52, conj_53, conj_54, conj_55, conj_56, conj_57, conj_58, conj_59, conj_60, conj_61, conj_62, conj_63, conj_64, conj_65, conj_66, conj_67, conj_68, conj_69, conj_70, conj_71, conj_72, conj_73, conj_74, conj_75, conj_76, conj_77, conj_78, conj_79, conj_80, conj_81, conj_82, conj_83, conj_84, conj_85⟩
