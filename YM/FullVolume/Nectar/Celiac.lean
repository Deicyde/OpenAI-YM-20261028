import YM.FullVolume.Nectar.Avalon
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna.Aank
open Filter Function Set MeasureTheory Push Push.AbsoluteSums RG Lattice Finset
open FullVolume.Ray Jams FullVolume.Ray.Weigh MergeProof Marker Accent
open scoped Topology ContDiff BigOperators Classical
variable {V I Y: Type}[DecidableEq V][Fintype V][Fintype I]{B: Marker.Census V} {G:Gauge} {n:Side}
variable {F:sun→I→Y→Poly B}{q p C:ℝ} {b:ℕ}(S:I→ Support n)(v:V→ ℝ) (hv:∀ i,0<v i)
-- Observatory takes any nonempty mark shape. coarse Marks.Support.V flows.All boxes Oracle may ask arbitrary ids and even outside Occupancy. Price supply if support contain anchor; cut to zero otherwise.Coin K-quiet allocate separately.
def orbit (X:Support n)(z:V→Site n):Prop:=∃ i,z i∈ X
variable (k:Finset (B.Mode))(z:V→Site n)
abbrev organs (b :ℕ)(e:ℝ)(F:I→Y→Poly B)(i:I× B.Mode)(U:Y):ℂ:= if i.2∈k ∧ orbit (S i.1) z then (Real.exp (e*coverNumber b (S i.1))*Poly.toll v i.snd:ℝ) • ((F i.fst U).part i.snd) else 0
def curtain (b:ℕ)(e:ℝ) (f:I→Y→Poly B):Glacier (I× B.Mode) ℂ Y:= Glacier.castle (organs S v k z b e f)
variable (hq: 1≤q)
include hv hq
lemma portal (h: Ankh v q F b S p C): (∀ t, Glacier.Bagged (organs S v k z b p (F t)))∧ Rebar q (phraseS (fun t=> (curtain S v k z b p (F t):Glacier (I× B.Mode) ℂ Y))) (Fintype.card V*C):=by
    obtain ⟨a,ha,hB,H⟩:=h.beam; choose t ht hh hP using fun i=> (H i).2
    let f(i:I) x:=t i x * Poly.toll v x
    have he(i) x:0 ≤ f i x:= mul_nonneg (ht i x) (Poly.worth hv _|>.le)
    let g(i:I× B.Mode):ℝ:=if orbit (S i.1) z then Real.exp (p*coverNumber b (S i.1)) * f i.1 i.2 else 0
    have hg(i):0 ≤ g i:=by unfold g;split; exact mul_nonneg (Real.exp_pos _).le (he ..); rfl
    refine Glacier.compass hq (show 0 ≤ g from hg) ?_ (fun i U=> ?_)
    · let c(i):=if orbit (S i) z then a i * Real.exp (p*coverNumber b (S i)) else 0
      apply le_trans (b:=∑ i,c i); rw [Fintype.sum_prod_type]; apply sum_le_sum;intro i _; unfold c; split
      next hi=> unfold g;dsimp only; simp_rw [if_pos hi]; rw [← mul_sum]; refine (mul_le_mul_of_nonneg_left (show _≤a i from ?_) (Real.exp_pos _).le).trans_eq (mul_comm ..); unfold f; simp_rw [mul_comm (t i _)]; exact hP i
      next hi=> apply le_of_eq;unfold g; dsimp only; rw [Finset.sum_eq_zero]; intro r _; exact if_neg hi
      let K(y : V) (i:I):ℝ:= if z y∈ S i then a i*Real.exp (p*coverNumber b (S i)) else 0
      have hy(i): c i≤∑ v,K v i:=by
         unfold c; split
         next h=> obtain ⟨u,ht⟩:=h; rw [← show K u i=_ from if_pos ht]; exact Finset.single_le_sum (fun j _=> (show 0≤K j i from (hB ..).1 _)) (mem_univ u)
         next=> exact sum_nonneg fun j _=> (hB ..).1 _
      refine (sum_le_sum (fun i _=> hy i)).trans ?_; rw [sum_comm]; refine (sum_le_sum (g:=fun _=>C) (fun i _=> budget_sum (hB (z i)) _ )).trans_eq ?_; simp
    unfold organs; split_ifs with hx
    · let w:= Real.exp (p*coverNumber b (S i.1)) * Poly.toll v i.2; have hv :0 ≤ w:=mul_nonneg (Real.exp_pos _).le (Poly.worth hv _|>.le); apply ((hh i.1 i.2 U).scale w).enlarged; unfold g; rw [if_pos hx.2,Real.norm_of_nonneg hv]; exact le_of_eq (by unfold w f; ring)
    exact (Scout.still hq (0:ℂ)).enlarged (norm_zero.trans_le (hg i))
section single
open Wilson
variable {Z:sun→I→ Config G n→ℂ}{P:BudgetPoint} (ht:RollsUp P S Z q p C)
def pack (p:ℝ) (P:BudgetPoint) (Z:I→Y→ℂ) (i:I)(y:Y):ℂ:=Real.exp (p*coverNumber P.B (S i)) • Z i y
omit hv
include ht
lemma journeys : let F t:= pack S p P (Z t)
     (∀ t,Glacier.Bagged (F t))∧Rebar q (phraseS (fun t=>Glacier.castle (F t))) C:=by
    obtain ⟨a,ha,hX⟩:=ht.funds; intro f; let g i:= Real.exp (p*coverNumber P.B (S i)); refine Glacier.compass hq (show 0≤(fun i=> g i*a i) from ha.1) (budget_sum ha _) (fun i u=>?_)
    exact (((hX i u).scale (g i)).enlarged (by rw [Real.norm_of_nonneg (Real.exp_pos _).le]))
end single
end YM.PhysicalNext.Repeat.Luna.Aank
