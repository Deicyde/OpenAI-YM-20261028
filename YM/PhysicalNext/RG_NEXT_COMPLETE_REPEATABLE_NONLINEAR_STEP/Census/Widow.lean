import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Horns
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Price
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Use

/-! # Earn sharp HIGH-arity unforced activities at the actual early budget

Two forest bounds simultaneously. Higher arity means every vertex,
 occurrence count, not just each cluster slot. Includes seed gain
 via stamp. Movement through F-average uses uniform bound not
 requiring that a Rain patch be analytic outside mask convention.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
section first
variable (N : Captain H j C' d v Y A b r B q k χ) {D : ℝ} (hd : 1 ≤ D)
def pins (S : StepData c f) (p:Molecule S) := ∑ i∈p,Sum.elim (fun _ : Stores S=>0) Silica.horn i
-- stronger marks with long full-footprint recovery

def stronger (H : Cash W s μ L Q o α T R) (p : Molecule S) := (grow G L s)^pins S p *gust S (Q.mark L μ s) (grow G L s) p *Real.exp (Q.ε * H.shapeW p)
lemma lifts' (i:Molecule S) (x : ℝ) :
    let f (z:Head S):=D^(Sum.elim (fun _ : Stores S=>0) Silica.horn z)*N.conduit.fare z
    (∏ v∈i,gale S x D f v)=D^pins S i*gust S x D i*(∏ v∈i, N.conduit.fare v) := by
  intro f
  simp only [gust,gale,f,pins,Cash.numP,Finset.prod_mul_distrib,Finset.prod_const,Nat.cast_sum,mul_sum,Real.exp_sum,Finset.prod_pow_eq_pow_sum]; ring

-- recover exp(ε*setPrice) jointly with all polynomial marks. Keep same ε.
set_option linter.unusedVariables false in
private theorem strongerSet {ι:Type*} [DecidableEq ι] (p:ι→Support c) (B:ℕ) (u e : ι→ℝ) (a v : ℝ) {h k : ℝ} {n m:ℕ} (hu:∀ i,0≤u i) (hw:∀ i,0≤ e i)
    (ha:0≤a) (hv:0<v) (hp:Ready p B (tariff u e 0 v) (a+2*v) h k (1/2)) (x : Site c) :
    SumBudget (fun s:Finset ι=> Reserves.rooted p B u x a s*(1+setPrice p B e s)^n * Real.exp (v*setPrice p B e s))
      (Reserves.extract v n 0 0* treeYield h (1/2) 0) := by
  have he:= touch_tail p B hp x 0; simp only [Nat.zero_le, ↓reduceIte] at he
  have hh : polyPrice v n = Reserves.extract v n 0 0 := by simp [Reserves.extract]
  rw [← hh]; apply budget_mono (budget_scale (show 0≤ polyPrice v n by unfold Reserves.polyPrice; positivity) he)
  · intro i; unfold Reserves.rooted; split; next =>
      apply mul_nonneg _ (Real.exp_pos _).le; refine mul_nonneg (mul_nonneg (prod_nonneg fun i _=>hu _) (Real.exp_pos _).le) (pow_nonneg (add_nonneg zero_le_one ?_) _)
      exact Finset.sum_nonneg fun i _=> add_nonneg (Nat.cast_nonneg _) (hw i)
    rw [zero_mul,zero_mul]
  intro i; unfold Reserves.rooted; split
  next hI =>
    have hY : (∏ j∈i,u j)*currency B a (i.biUnion p) ≤ touches p B u a x i := by
      unfold touches; rw [if_pos hI]; unfold currency; simp only [Finset.prod_mul_distrib, ← Real.exp_sum,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Ac.cover p B hI.1) ha)) (prod_nonneg fun i _=> hu _)
    rw [Reserves.set_exchange]
    let D:= setPrice p B e i; have hd:0 ≤ D:= Finset.sum_nonneg fun i _=> add_nonneg (Nat.cast_nonneg _) (hw i)
    have hx:0≤(∏ j∈i,u j)*currency B a (i.biUnion p):=mul_nonneg (prod_nonneg fun _ _=>hu _) (Real.exp_pos _).le
    apply (mul_le_mul_of_nonneg_right (mul_le_mul hY (polynomial_cost hv hd n) (show 0 ≤ (1+D)^n by positivity) (hx.trans hY)) (Real.exp_pos _).le).trans
    -- fixed syntax
    simp only [Pi.zero_apply,sum_const_zero,add_zero]; change _ ≤ _*(touches p B u a x i * Real.exp (2*v*D)); rw [show 2*v*D=v*D+v*D by ring,Real.exp_add]; apply le_of_eq; unfold D Reserves.polyPrice; ring
  next hk=> unfold touches; rw [if_neg hk,zero_mul,zero_mul,mul_zero]
variable (hhd : 1 ≤ grow G L s) (h : Heavy N.conduit)
include hhd N h
lemma strikes (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2) : Ac.Hit H.unionP (radiusB s)
    (fun p : Molecule S=> stronger H p*N.conduit.meant p k) Q.exp (grow G L s*Q.overture L μ s k) := by
  let D:=grow G L s; let X:=Q.costs L μ R.beta s C'; let E:=N.conduit; let Z:=H.supportP; let w:=Mixed.lengths S X (ConnectedActivityE6.lengths T R)
  let g (z:Head S):=D^(Sum.elim (fun _=>0) Silica.horn z)*E.fare z; let u:=gale S X.markSeed D g
  let b:= radiusB s
  have hv : Ready Z b (tariff g w (Mixed.stamp S X) Q.ε) (Q.exp+2*Q.ε) X.rootHit Q.δ (1/2) := by
    let z p := D ^ Silica.horn p * E.flair p
    rw [show g=Mixed.costs S Q.halo b (steamP S X) z from ?_]; swap
    · funext p; rcases p with p|p
      · unfold g Utopia.fare stout Mixed.costs; simp; rfl
      rfl
    exact Mixed.ready_vertices S Q.halo b X H.birth z (ConnectedActivityE6.lengths T R) (steamP S X) E.lives ⟨E.accrues.packetBound,h.nonneg,E.accrues.extra,h.hit⟩
  have hD:0<D:=zero_lt_one.trans_le hhd
  have hg p : 0≤ g p:= mul_nonneg (pow_nonneg hD.le _) (E.fares _)
  have he z:tariff u w 0 Q.ε z=D*tariff g w (Mixed.stamp S X) Q.ε z := by unfold u tariff gale Mixed.stamp; simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring
  have hz: Ready Z b (tariff u w 0 Q.ε) (Q.exp+2*Q.ε) (D*X.rootHit) Q.δ (1/2) := by rw [funext he]; exact ⟨mul_pos hD hv.1,Q.pos,hs,by norm_num,fun z=> mul_nonneg hD.le (hv.2.2.2.2.1 z), Quotes.hit_scale hD.le hv.2.2.2.2.2⟩
  intro x
  have hx i:0 ≤ w i:= by
    rcases i with i | i
    · exact mul_nonneg E.lives.extra (Nat.cast_nonneg _)
    exact Nat.cast_nonneg _
  have hp:= strongerSet (m:=k) (n:=k) Z b u w Q.exp Q.ε (fun z=>mul_nonneg (mul_nonneg hD.le (hg _)) (Real.exp_pos _).le) hx Q.bound Q.usable hz x
  convert hp using 1; ext p
  · dsimp only; unfold Reserves.rooted; split
    next hv=>
      by_cases hg : H.ticketsP 0 0 0 p
      · rw [Utopia.meant,if_pos hg,if_pos (show Ac.Spark Z p ∧ x∈p.biUnion Z from ⟨(H.attends _).1 hg,hv⟩), show (∏ i∈p,u i)=_ from lifts' (D:=D) N p X.markSeed, show setPrice Z b w p=H.shapeW p from rfl, stronger, currency]
        change _=(D^pins S p*gust S (Q.mark L μ s) D p*(∏ i∈p,N.conduit.fare i))*Real.exp (Q.exp*coverNumber (radiusB s) (H.unionP p))*_*_; unfold D; ring
      rw [Utopia.meant,if_neg hg,mul_zero,zero_mul,if_neg fun h=>hg ((H.attends _).2 h.1),zero_mul,zero_mul]
    next hx => rw [if_neg fun h=>hx h.2,zero_mul,zero_mul]
  unfold ConnectedActivityE6.Target.overture ConnectedActivityE6.Target.quantum Mixed.Costs.ceiling Reserves.treeYield
  change D*(_ * ((X.rootHit*_)*_))=Reserves.extract _ _ _ _ *((D*X.rootHit)*_ *_)
  dsimp only [ConnectedActivityE6.Target.costs,Buy.quote] at *; norm_num; ring
lemma stable (i a : ℝ) (hi : 0 < i) (hT : a+i+i ≤ Q.exp) (hv : 0<Q.overture L μ s k)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2) (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2) :
    Ready H.smallAt (radiusB s) (fun p:H.ThinP=> stronger H p.val*N.stone p) (a+i) (grow G L s*salary Q L μ B s j k) i (1/2) := by
  let m (u:Molecule S):=stronger H u
  let f z:=m z*N.conduit.meant z k
  have hr : Ac.Hit H.unionP (radiusB s) f Q.exp _ := strikes N hhd h hs
  have hD:0<grow G L s:=zero_lt_one.trans_le hhd; have hh:=N.balance
  refine ⟨by unfold salary; positivity,hi,hp,by norm_num,fun p=>mul_nonneg (by unfold stronger gust; positivity) (N.stone_pos _),fun x=>?_⟩
  have hy:= budget_scale (show 0≤(2:ℝ)^j*B by positivity) (budget_pull (fun z:H.ThinP=>z.val) Subtype.val_injective (hr x))
  refine budget_loosen (budget_mono hy (fun z=>?_) (fun z=>?_)) ?_
  · dsimp only; split
    next => exact mul_nonneg (mul_nonneg (by unfold stronger gust; positivity) (N.stone_pos _)) (Real.exp_pos _).le
    exact le_rfl
  · dsimp only; split
    next hx => rw [if_pos (show x∈H.unionP z.val from hx), ← mul_assoc, show 2^j*B*f z.val=m z.val*N.stone z by unfold f Captain.stone; ring]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg _))) (mul_nonneg (show 0 ≤ m z.val by unfold m stronger gust; positivity) (N.stone_pos _))
    exact hy.1 z
  unfold salary; nlinarith only [mul_pos hD hv]
end first
end YM.PhysicalNext.Repeat.Height
