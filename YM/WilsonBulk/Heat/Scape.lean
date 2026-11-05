import YM.WilsonBulk.Heat.Strict

/-! Combining period projection intermediates through immersion. Again no
scalar cover-normalizing vacuum term or input of such wanted. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Equiv Finset Bloch Lattice Pert.Bulk
open scoped Topology Classical BigOperators ENNReal
variable {D : ℕ→Side} {α : Type} [Fintype α]
variable (hd : Tendsto (fun i=> (D i).val) atTop atTop)
variable {V : Leaf D α 2} {C : Text α 2} {N : ∀ i, Record (Co (D i) α)} {M : Record (Market α)}
namespace Proxy
include hd
lemma immersed (h : Proxy V C) (hN : ∀ e n,n≠0→ Proxy (fun i=> N i e n) (M e n)) (d e n : ℕ)
    (hn : n ≠ 0) (a b : Bool) : Proxy (fun i=> immerse (V i) (N i) a d e n) (immerse C M b d e n) := by
  induction d using Nat.strong_induction_on generalizing e n with
  | h d ih=>
     cases d with
     | zero => simp_rw [start,if_neg (show ¬(n=0∧a) from fun h=>hn h.1), if_neg (show ¬(n=0∧b) from fun h=>hn h.1)]; exact hN e n hn
     | succ d =>
        have ht (i : Split e) (j : Split d) (k : Split n) :=
          (Proxy.bridge h (ih (l j) ((left_small j).trans_lt (by omega)) (l i) (l k+1) (by omega))
            (ih (r j) ((right_small j).trans_lt (by omega)) (r i) (r k+1) (by omega)) (by rw [parts]; exact hn)).reindex (finCongr (parts k))
        simp_rw [restore, if_neg (show ¬(n=0∧a) from fun h=>hn h.1), if_neg (show ¬(n=0∧b) from fun h=>hn h.1)]
        apply Proxy.eq (((h.lap hd (ih d (by omega) e (n+2) (by omega)) hn).plus (Proxy.gather univ fun p _=>Proxy.gather univ fun j _=> Proxy.gather univ fun k _=> ht p j k)).scale _)
        apply Eventually.of_forall; intro i; simp [torpedo]
lemma received (h : Proxy V C) (hN : ∀ e n,n≠0→ Proxy (fun i=> N i e n) (M e n)) (e n : ℕ) (hn : n ≠ 0) :
    Proxy (fun i=> receive (V i) (N i) false e n) (receive C M true e n) :=
  (Proxy.gather (spend e) fun d _=> Proxy.immersed hd h hN d e n hn false true).eq (Eventually.of_forall fun i=> by simp [receive])
end Proxy
end YM.WilsonBulk.Sheet
