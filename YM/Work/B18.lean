import YM.Bid.Fetch

/-!
# Episodes for the corrected detectors

Encode the polynomial before taking roots. Each term of the episode retains
its actual slot indices in the row (even when names agree or are unit
labels). At the cluster end it uses `later`, and at the cutoff end `lift`;
constant terms use the empty word at both ends.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B18
open Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction Retain Cells Wilson Bid
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal

private structure Monomial (n : ℕ) where
  coeff : ℂ
  arity : ℕ
  slot : Fin arity → Fin n
  separate : Injective slot

private def scalar {n : ℕ} (z : ℂ) : Monomial n :=
  ⟨z, 0, Fin.elim0, fun _ _ _ => Subsingleton.elim _ _⟩

private def unary {n : ℕ} (z : ℂ) (j : Fin n) : Monomial n :=
  ⟨z, 1, fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩

private def binary {n : ℕ} (z : ℂ) (j x : Fin n) (h : j < x) : Monomial n := by
  refine ⟨z, 2, ![j, x], ?_⟩
  intro a b e
  fin_cases a <;> fin_cases b <;> simp_all [h.ne, Ne.symm h.ne]

variable {G : Gauge} {C : Family G} {F : Order} {S : Table C.book}
  {V : Chamber S timeAxis} {d : ℕ} {X : Columns C S d}
  (Q : X.Trials) (K : Columns.Trials.Valid F Q) (A : Spread V)
  (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1))
  (j x : Fin ((X.row i).extra+1))

/-- Use subwords on exactly Q's mesh, and keep actual and limiting
coefficients coupled by `K.responds`. -/
private def enact {m : ℕ} (P : Fin m → Monomial ((X.row i).extra+1)) :
    Episode C F (Q.depth k) where
  num := m
  factor l := (P l).coeff
  image l := (P l).arity
  seats l s := Q.mark k i ((P l).slot s)
  gen l a := (show Injective _ from K.generic k i a).comp (P l).separate
  weight _ _ := d
  point l s := Q.later k (Columns.Trials.names (X:=X) i c ((P l).slot s))
  current l s N p := Q.lift k N p (Columns.Trials.names (X:=X) i c ((P l).slot s))
  views _ _ := K.responds k _

private lemma within_subtract (b N p : ℕ) (h : b ≤ N)
    (u : Interior ((center C.S p h 0).chamber 0) (Q.weigh k N p i c j)) :
    Interior ((center C.S p h 0).chamber 0) (Q.subtract1 k N p i c j) := by
  unfold Columns.Trials.subtract1
  simpa only [sub_eq_add_neg] using
    u.plus (Interior.constant _ (-Q.singleton k i c j))

include K in
private lemma first_send (H : Theme V A) :
    Sends A F (Q.width k) (Q.depth k) (Q.gap k) (Δone Q A k i c j) := by
  let E := enact Q K k i c ![unary 1 j, scalar (-Q.singleton k i c j)]
  refine ⟨E, ?cluster, ?sold⟩
  case cluster =>
    simp only [E, Episode.cluster, enact]
    change
      (1:ℂ) • atOne A (plant Q k i c j) +
      ((-Q.singleton k i c j) • M A [] (locations.mpr (by simp)) + 0)
        = Δone Q A k i c j
    rw [H.vacant, add_zero, neg_smul, one_smul, Δone, sub_eq_add_neg]
  case sold =>
    have bill (N p) : E.cuts N p 0 = Q.subtract1 k N p i c j := by
      funext v
      simp only [E, Episode.cuts, enact, add_zero]
      change
        1*(Q.weigh k N p i c j v * 1) + ((-Q.singleton k i c j)*1 + 0) = _
      rw [one_mul, mul_one, mul_one, add_zero, Columns.Trials.subtract1, sub_eq_add_neg]
    intro ε he
    have hc := K.cheap k ε he
    unfold Order.late at hc ⊢
    refine hc.mono fun l hl => hl.mono fun m hm => ?_
    obtain ⟨h,u⟩ := hm
    refine ⟨(Q.window k).trans h, ?_⟩
    simp only [bill]
    exact ⟨within_subtract Q k i c j _ _ _ _ (u i c j).1, (u i c j).2.1⟩

private lemma second_send (H : Theme V A) (hj : j<x) :
    Sends A F (Q.width k) (Q.depth k) (Q.gap k) (Δtwo Q K A k i c j x hj) := by
  let a := Q.singleton k i c j
  let b := Q.singleton k i c x
  let r := Q.cumulant k i c j x
  let E := enact Q K k i c ![binary 1 j x hj, unary (-a) x, unary (-b) j, scalar (b*a-r)]
  refine ⟨E, ?cluster, ?sold⟩
  case cluster =>
    simp only [E, Episode.cluster, enact]
    change
      (1:ℂ) • M A _ (Retain.apart Q K k i c j x hj) +
      ((-a) • atOne A (plant Q k i c x) +
      ((-b) • atOne A (plant Q k i c j) +
      ((b*a-r) • M A [] (locations.mpr (by simp)) + 0)))
        = Δtwo Q K A k i c j x hj
    rw [H.vacant]
    simp only [Δtwo, a, b, r, one_smul, neg_smul, add_zero, sub_eq_add_neg, add_assoc]
  case sold =>
    have bill (N p) : E.cuts N p 0 = Q.subtract2 k N p i c j x := by
      funext v
      simp only [E, Episode.cuts, enact, add_zero]
      let J := Q.weigh k N p i c j v
      let Z := Q.weigh k N p i c x v
      change
        1*(J*(Z*1)) + ((-a)*(Z*1) + ((-b)*(J*1) + ((b*a-r)*1 + 0)))
          = (J-a)*(Z-b)-r
      ring
    intro ε he
    have hc := K.cheap k ε he
    unfold Order.late at hc ⊢
    refine hc.mono fun l hl => hl.mono fun m hm => ?_
    obtain ⟨h,u⟩ := hm
    refine ⟨(Q.window k).trans h, ?_⟩
    simp only [bill]
    refine ⟨?_, (u i c j).2.2 x hj⟩
    have uj := within_subtract Q k i c j _ _ _ _ (u i c j).1
    have ux := within_subtract Q k i c x _ _ _ _ (u i c x).1
    unfold Columns.Trials.subtract2
    simpa only [sub_eq_add_neg] using
      (uj.times ux).plus (Interior.constant _ (-Q.cumulant k i c j x))

theorem answer : YM.Bid.B18 := by
  intro G C F S s V A H d X Q K
  exact ⟨fun k i c j => first_send Q K A k i c j H,
         fun k i c j x hj => second_send Q K A k i c j x H hj⟩
end YM.Work.B18
