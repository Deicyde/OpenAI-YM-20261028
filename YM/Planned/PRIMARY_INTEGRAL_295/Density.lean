import YM.Next.SCHEDULE.Chorus
import YM.Planned.PRIMARY_INTEGRAL_295.Little
import YM.Push.STATIONARY_UNIFORM.Calculus
/-!
# Real torus dL fee bounds for PreGram analytic per-address queries

Post-L counts includes number of *different* rows/paths ungrouped. Keeps
local sizes of the same K geometry. No period-price uplift. Budget primitive
before application is not claiming ready from trace. These primitives later
activated by upper score/authentic F0 & D cost on actual support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Density
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bid (pulled bills Sworn stretch)
open Bunks Little Work.F01 Little.Core
open Progress.StationaryScenes.Green Push.Uniform
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {z n k:ℕ} {c f:Side} {S : StepData c f}

section
-- physical distance measured in output. Not for symmetric-midpoint cutoff.
def chair (S:StepData c f) (x:Acres f G):= S.ratio.parent x.1.1
def shade (S:StepData c f) (x:Drops c f) := x.2.elim (fun i=>S.ratio.parent (affine x.1 0 i.1.1)) (fun i=> affine x.1 0 i.1)
def origin (S:StepData c f) (x:Seats G c f):=shade S x.1
def curlN (G:Gauge) (L:Side): ℕ:= (Fintype.card (Site L×Axis×G.ColorIndex))
def originN (G:Gauge) (L:Side): ℕ:= Fintype.card (Signed× G.ColorIndex × ((Site L × PlaqAxes×Bool) ⊕ Axis))

private lemma mapping {ι κ:Type} [Fintype ι] [Fintype κ] (a:ι→Site c) (b:ι→κ) (hb:Injective (fun i=>(a i,b i))): Multiplicity a (Fintype.card κ):= by
   intro x; let s:=Finset.univ.filter fun i=> a i=x
   have he : Injective (b ∘ Subtype.val: s→κ) := by
     intro i j hi; apply Subtype.ext; apply hb;
     exact Prod.ext ((Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp j.property).2.symm) hi
   simpa using Fintype.card_le_of_injective _ he

lemma chair_count (G:Gauge) (S:StepData c f): Multiplicity (chair (G:=G) S) (curlN G S.ratio.count):=by
   let b(x:Acres f G):= (S.ratio.residue x.1.1,x.1.2,x.2)
   apply mapping _ b
   rintro ⟨⟨x,i⟩,j⟩ ⟨⟨y,a⟩,b'⟩ h
   simp only [chair,b,Prod.mk.injEq] at h; rw [show x=y from S.ratio.splitSites.injective (by rw [←Ratio.unpack,←Ratio.unpack]; exact Prod.ext h.1 h.2.1),h.2.2.1,h.2.2.2]
lemma origin_count (G:Gauge) (S:StepData c f): Multiplicity (origin (G:=G) S) (originN G S.ratio.count):=by
   let b(x:Seats G c f): Signed× G.ColorIndex × ((Site S.ratio.count × PlaqAxes × Bool)⊕ Axis):= (x.1.1,x.2,x.1.2.elim
      (fun i => .inl (S.ratio.residue (affine x.1.1 0 i.1.1),i.1.2,i.2)) (fun i=> .inr i.2))
   apply mapping _ b
   rintro ⟨⟨p,x⟩,a⟩ ⟨⟨q,y⟩,b'⟩ h
   simp only [b,origin,shade,Prod.mk.injEq] at h; obtain ⟨hq,rfl,rfl,h⟩:=h
   rcases x with ⟨i,w⟩ | ⟨x,w⟩ <;> rcases y with ⟨j,u⟩ | ⟨y,u⟩
   · simp only [Sum.elim_inl,Sum.inl.injEq,Prod.mk.injEq] at hq h; obtain ⟨h,r,g⟩:=h
     have he : affine p 0 i.1 = affine p 0 j.1:= S.ratio.splitSites.injective (by rw [←Ratio.unpack,←Ratio.unpack]; exact Prod.ext hq h)
     rw [g,show i=j from Prod.ext (p.act_injective (by simpa [affine] using he)) r]
   · simp at h
   · simp at h
   simp only [Sum.elim_inr,Sum.inr.injEq] at hq h; rw [show x=y from p.act_injective (by simpa [affine] using hq),h]

variable {x y:Site c} {ι:Type} [Fintype ι] {N:ℕ} {l:ι→Site c} {a:ℝ}
lemma haul (h:Multiplicity l N) (ha:0<a) (x y:Site c): (∑ i,Decay a (l i) x * Decay a (l i) y) ≤
     (N * Push.Uniform.countCost (a/2)) * Decay (a/2) x y := by
   let r:= a/2; have hr:0<r := half_pos ha
   have he i : Decay a (l i) x * Decay a (l i) y ≤ Decay r x (l i) * Decay r x y := by
     have ht (x y: Site c) : Decay a x y=Decay r x y * Decay r x y:=by unfold Decay; rw [← Real.exp_add]; congr 1; unfold r; ring
     rw [ht,ht, decay_comm r (l i) x,mul_assoc, ←mul_assoc _ (Decay r _ _) (Decay r _ _)]
     apply mul_le_mul_of_nonneg_left _ (decay_pos ..).le
     exact (mul_le_of_le_one_right (mul_nonneg (decay_pos ..).le (decay_pos ..).le) (decay_le hr.le ..)).trans (decay_step hr.le ..)
   apply (Finset.sum_le_sum (fun i _=>he i)).trans; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h.count l hr x) (decay_pos ..).le

lemma weight_budget {a b : ℝ} (ht:b<a) (h:Multiplicity l N) (x:Site c):
    (∑ i, Progress.StationaryScenes.Green.wt b x (l i) * Decay a (l i) x) ≤ N*Push.Uniform.countCost (a-b):= by
   have he(i:ι): wt b x (l i)*Decay a (l i) x=Decay (a-b) x (l i):=by rw [decay_comm a]; unfold wt Decay; rw [← Real.exp_add]; congr 2; ring
   simp_rw [he]; exact h.count l (sub_pos.mpr ht) x
end

-- analytic Gard interface will prove independently from Rings Teller. Over-precise
-- cost b at zero input ̅Aflat in zLin.
variable (K:Core G S)
structure Trinket where
   start : ℝ -- bottom for Gram(0)
   radius : ℝ
   C : ℝ -- preGrade post-L
   α : ℝ -- common threshold fee exp
   health : 0< start
   rprice : 0 ≤ radius -- in application >0
   witness : 1 ≤ C
   wisdom : 0< α

/-- Full supply (dTerms analytic at *every* actual p path in unforced K extended log-neighborhood).
Caller K.R, branches, orientations and pre history must provide. λ harmonic witness
included explicitly. Does not care about origins away truthful stencil. Later derive
this along Proc. Note bias using actual fderiv F0 at 0, not at archived p. -/
structure Quantum (w:Trinket) (W:Lines S.ratio.count) (k:ℕ) : Prop where
   root : Bottom (K.Gram 0) w.start
   hands (i : Seats G c f) (v:Dir G c) : ‖v‖≤w.radius → Allows (k+2) (fun y=> K.F0 y i) v w.C
   drums (i : Seats G c f) (j:Acres f G) (v:Dir G c) : ‖v‖ ≤ w.radius →
      Allows (k+2) (fun y=> K.D y i j) v (w.C * Decay w.α (origin S i) (chair S j))
   self : K.F0 0=0
   score (v:Dir G c) : ‖K.dawn v W‖ ≤ w.C* ‖v‖
   tracks (i:Seats G c f) (v:Dir G c) : ‖(K.D 0).mulVec (K.dawn v W) i + fderiv ℝ (fun y=>K.F0 y i) 0 v‖ ≤
      w.C*Real.exp (-w.α*K.R)*‖v‖
end YM.Planned.PrimaryIntegral295.Density
