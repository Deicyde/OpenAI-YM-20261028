import YM.MergeProof.Biscuit

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D){f:Extraction.Order}
set_option quotPrecheck false
variable {N p d:ℕ}
-- quantitative passport all cutouts. potentially Mark translates.
local notation "A"=> (C.labels.level d)

local notation "γ"=> Push.RelayDifference.gamma
include B
omit H h in
lemma rotates {E:Cutoffs→ℝ}{ζ:ℕ→ℕ→ℝ}{Z : Trial C} (hh:Slow C f E) (hS:Stencilled f Z)(d:ℕ)
    (hP:∀ᶠ i in f.fuse, ∀ m k:ℕ,C.ref d ≤ k → k < i.1 → Stock.Tabs.opens C.path.levels 1 m k → ∀ h:m ≤ i.1,(center C.S i.2 h 0).rootTest (C.beta i.1 i.2) (Z i.1 i.2 0) ≤ cider C ζ d m k*E i*flight C (-Push.RelayDifference.gamma) i) : CenterRents Z (flight C (-(1/16))) f:=by
   refine ⟨hS.literal,fun j=> ?_⟩; let m:=max j (C.ref d); let k:= Stock.Tabs.chosen C.path.levels 1 B m; have hk:Stock.Tabs.opens C.path.levels 1 m k:= Stock.Tabs.opened _ _ _ _
   have he := (Slow.const (cider C ζ d m k)).mul hh; have hx:= he.sink (show 1/16 < γ by norm_num [RelayDifference.gamma]); refine ⟨m,le_max_left ..,(Order.fused f (fun i=>∃ hn:m ≤ i.1, Interior ((center C.S i.2 hn 0).chamber 0) (Z i.1 i.2 0)∧ (center C.S i.2 hn 0).rootTest (C.beta i.1 i.2) (Z i.1 i.2 0) ≤ flight C (-(1/16)) i)).mp ?_⟩
   filter_upwards [hx,hP,(cutoff_grows f).eventually (eventually_gt_atTop k),Stencilled.fits m hS] with i hi hp ht ⟨hn,hN⟩; exact ⟨hn,hN _, (hp m k ((le_max_right ..).trans hk.1) ht hk hn).trans hi⟩
-- generic orientation b-Z. Center transform root.Test neg sign. Useful stationary. charge.Carry. Works same tile identifier. 
omit B in
lemma unitsC (s : Side) (T:Tiling s) (F : Config G s→ℂ)(x:ℝ): T.rootTest x F= T.rootTest x (-F):= by rw [← neg_one_smul ℂ F,root_smul T]; simp

omit B in
private lemma deferChoice {ι β:Type*}[Nonempty β] {x : Filter ι}{p:ι→β→Prop}(h:∀ᶠ i in x,∃ v,p i v):∃ v:ι→β,∀ᶠ i in x,p i (v i):=by
    classical
    exact ⟨fun i=> if h:∃ v,p i v then Classical.choose h else Classical.arbitrary _, h.mono (fun i hi=>by simp only [dif_pos hi]; exact Classical.choose_spec hi)⟩
include h H
lemma served_dollar {F:Trial C}{E:Cutoffs→ℝ} (H':Slow C f E)(ht:Stencilled f F) (hp:∀ᶠ i in f.fuse,C.ref d ≤ i.1 ∧ ∃ Z t Q, Cream C i.1 i.2 d u ζ (F i.1 i.2 0) Z Q t (E i)) : ∃ v:Rowe C d,dollar C f v ∧ CenterRents (upper C v - F) (flight C (-(1/16))) f :=by
    have hw : ∀ᶠ i in f.fuse, ∃ v:C.label d, ‖(C.factory d i.1 i.2).terminal.symm v‖ ≤ 2*E i ∧ ∀ m k:ℕ,C.ref d ≤ k→k < i.1 → Stock.Tabs.opens C.path.levels 1 m k →∀ hn:m ≤ i.1,(center C.S i.2 hn 0).rootTest (C.beta i.1 i.2) (C.O i.1 i.2 v 0-F i.1 i.2 0) ≤ cider C ζ d m k*E i*flight C (-γ) i:= by
       filter_upwards [hp] with i ⟨hi,Z,t,Q,hT⟩; obtain ⟨v,hV,hL⟩:= pudding C i.1 i.2 d B W u ψ φ δ ζ r D H h (F i.1 i.2 0) Z Q t (E i) hi hT; refine ⟨v,?_,fun m k hm hk hb hn=>?_⟩
       · let x:= (C.factory d i.1 i.2).terminal.symm v; let A0:= (C.path.levels.params i.1).columns
         have ht:0 ≤ Q:= hT.fuel.le; have hA : 1 ≤ A0:= (C.path.levels.params _).columns_ge; have hp:2*(1+A0)*Q ≤ E i:=le_trans (mul_le_mul_of_nonneg_right (show 2*(1+A0)≤4*(1+A0) by linarith only [hA]) ht) hT.dom
         have hz:0 ≤ Q:=ht; have hc:(A).coeffSize Z.x ≤ E i:=(le_trans (b:=(A).coeffSize Z.x+t) (le_add_of_nonneg_right (rem_nonneg hT.pay)) hT.charge).trans ((le_mul_of_one_le_left ht (show 1 ≤ 2*(1+A0) by linarith only [hA])).trans hp)
         have hr:(A).coeffSize (x-Z.x) ≤ E i:=by rw [Work.G08.size_sub_rev]; exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (show 1 ≤ 32*(1+A0)^2 by nlinarith only [hA])).trans (hV.trans hp)
         exact (RelayDifference.norm_cost A x).trans ((Work.G08.size_triangle A x Z.x).trans ((add_le_add hc hr).trans_eq (two_mul _).symm))
       · let A0:= C.O i.1 i.2 v 0; let T0:= F i.1 i.2 0; let V:= center C.S i.2 hn 0
         have hx:=hL m k hm hk hb Motion.nil hn; rw [dance_nil] at hx; rw [unitsC]; rw [neg_sub]; exact hx
    rcases deferChoice hw with ⟨v,hV⟩ -- inspect
    refine ⟨v,(dollar_slow _).2 (((Slow.const (C:=C) (f:=f) (2:ℝ)).mul H').reduce (hV.mono (fun i he=> he.1.trans (Real.le_norm_self _)))),rotates B H' ((Stencilled.upper H v).sub ht) d (hV.mono fun i hi=> hi.2)⟩
end YM.MergeProof
