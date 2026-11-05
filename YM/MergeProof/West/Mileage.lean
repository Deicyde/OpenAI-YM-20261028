import YM.Next.RANK.LedgerGate
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {n:Side} {V:Type}
lemma trek {c: V→Site n} {S:Finset V} {d:ℕ} {i j:V} (h:ReflTransGen (glows c S d) i j):
    separation (c i) (c j) ≤ S.card*d:=by
  let E u:= separation (c i) (c u)
  have he (k:V) (h:ReflTransGen (glows c S d) i k): ∀ M : ℕ,M≤ E k→ M≤ (S.filter (fun j=> E j < M)).card*d:= by
    induction h with
    | refl=> simp [E,separation_self]
    | @tail x y hL hD h =>
      intro M H
      by_cases hm : M≤ E x
      · exact h M hm
      have hp: M≤ E x+d:= H.trans ((separation_triangle (c i) (c x) _).trans (Nat.add_le_add_left hD.2.2 _))
      have hv : (S.filter (fun j=> E j < E x)).card+1 ≤ (S.filter (fun j=> E j < M)).card:=by
          rw [← card_insert_of_notMem (a:=x)]
          · exact card_le_card (insert_subset (mem_filter.mpr ⟨hD.1, Nat.lt_of_not_ge hm⟩) (fun v hv=> mem_filter.mpr ⟨(mem_filter.mp hv).1,(mem_filter.mp hv).2.trans (Nat.lt_of_not_ge hm)⟩))
          simp
      have he := h (E x) le_rfl
      apply hp.trans; apply le_trans _ (Nat.mul_le_mul_right d hv); rw [add_mul, one_mul]; omega
  exact (he j h _ le_rfl).trans (Nat.mul_le_mul_right _ (card_le_card (filter_subset ..)))
end YM.Next.Rank.Tapes.West
