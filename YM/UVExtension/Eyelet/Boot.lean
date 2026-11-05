import YM.UVExtension.Eyelet.Shelves
import YM.UVExtension.Concert.Stethoscope
import Mathlib.Analysis.Normed.Lp.lpSpace
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ} {F:Frame G d} (H: Hol G) (i:Region n) (p: BudgetPoint)

-- dense concrete REAL domains (complex amplitudes); linear closures for operator bounds
structure Credit (d:ℕ)(f:Config G n→ℂ): Prop where
    pose : p.Regular i.val f
    zero : f 1=0
    horizons : Nonwrapping i.val 0 → H.PiVanish d 0 f
    cost : ∃ a,p.supBounds 0 i.val f a
    -- argument H i p order check vector
variable (d)

def Birth (d:ℕ) : Submodule ℂ (Config G n→ℂ) where
    carrier:={f| Credit H i p d f}
    zero_mem':=⟨(hot _ _ (o:=(0:Site n))).1,rfl,fun _ _=>⟨contDiffAt_const,fun j _=> by change iteratedDeriv j (fun _=>(0:ℂ)) 0=0; simp⟩,0,(hot ..).2⟩
    add_mem':=fun {x y hx hy}=>by
       have hz:Credit H i p d x:=hx; have h': Credit H i p d y:=hy
       obtain ⟨s,hw⟩:= hz.cost; obtain ⟨w,hP⟩:= h'.cost
       refine ⟨regular_add hz.pose h'.pose,by change x 1 + y 1=0; rw [hz.zero,h'.zero,add_zero],fun ht J=>?_,s+w,bound_add hz.pose h'.pose hw hP⟩
       obtain ⟨ha,hb⟩:=hz.horizons ht J; obtain ⟨hh,hk⟩:=h'.horizons ht J
       refine ⟨ha.add hh,fun k hv=>?_⟩; simp only [Pi.add_apply]; rw [iteratedDeriv_fun_add (ha.of_le (Nat.cast_le.mpr hv)) (hh.of_le (Nat.cast_le.mpr hv)),hb k hv,hk k hv,add_zero] -- lean
    smul_mem':=fun c x hx=> by
       have h:Credit H i p d x:=hx
       obtain ⟨v,hv⟩:=h.cost
       refine ⟨regular_smul c h.pose,by rw [Pi.smul_apply,h.zero,smul_zero],fun ht J=>?_,_, bound_smul c hv⟩
       obtain ⟨ha,hb⟩:=h.horizons ht J
       refine ⟨ha.const_smul c, fun j hj=>?_⟩; change iteratedDeriv j (c • fun t : ℝ=> x (H.testLinks d (0:Site n) J t)) 0=0; rw [iteratedDeriv_const_smul (ha.of_le (Nat.cast_le.mpr hj)),hb j hj,smul_zero]
instance (k:Site n)(i:Support n) : TopologicalSpace (Concert.Tap p G k i):= ⊥
instance (k:Site n)(i:Support n) : DiscreteTopology (Concert.Tap p G k i):= discreteTopology_bot _
open BoundedContinuousFunction
abbrev Hall (p:BudgetPoint)(X:Support n) := Tap p G 0 X →ᵇ ℂ
lemma recognizes (x:Birth (d:=d) H i p) : Credit H i p d x.val:= x.property
-- check binder order after. Bound is raw cost c, then later multiply by exp.
def born (x:Birth (d:=d) H i p): Hall (G:=G) p i.val:= ofNormedAddCommGroupDiscrete (fun k=> k.read x.val) (recognizes d H i p x|>.cost.choose) ((tap_bound.mp (recognizes d H i p x|>.cost.choose_spec)).2)

def tin : (Birth (d:=d) H i p)→ₗ[ℂ] Hall (G:=G) p i.val where
    toFun:= born d H i p
    map_add' f g := DFunLike.ext _ _ (fun k=>Local.left_add k.poll ((recognizes d H i p f).pose.smooth _ k.live) ((recognizes d H i p g).pose.smooth _ k.live) k.card)
    map_smul' c x := DFunLike.ext _ _ (fun k=>Local.left_linear (c • ContinuousLinearMap.id ℝ ℂ) k.poll ((recognizes d H i p x).pose.smooth _ k.live) k.card)
lemma pays (x:Birth (d:=d) H i p){s:ℝ} : p.supBounds 0 i.val x.val s↔‖tin d H i p x‖≤ s:= by
    rw [tap_bound]; constructor; exact fun h=> (BoundedContinuousFunction.norm_le h.1).2 h.2
    exact fun h=> ⟨(norm_nonneg _).trans h,fun v=> ((tin d H i p x).norm_coe_le_norm v).trans h⟩

section mountain
variable {A B: Type}[AddCommGroup A] [Module ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B] (u:A→ₗ[ℂ] B)
def boxes := (LinearMap.range u).topologicalClosure
abbrev Quoit := ↥(boxes u)
instance [CompleteSpace B]: CompleteSpace (Quoit u):= isClosed_closure.completeSpace_coe
def twig : A→ₗ[ℂ] Quoit u := u.codRestrict _ (fun _=> (LinearMap.range u).le_topologicalClosure (LinearMap.mem_range_self ..))
lemma steams : DenseRange (twig u):=by
   apply Metric.dense_iff.mpr; intro x ε he
   obtain ⟨v,h,hq⟩:= Metric.mem_closure_iff.mp x.property _ he; obtain ⟨w,rfl⟩:= show v∈ LinearMap.range u from h
   exact ⟨twig u w,(dist_comm ..).trans_lt hq,⟨_,rfl⟩⟩
end mountain
abbrev Gondola:= Quoit (tin d H i p)

section gas
variable (j:StockTag n)
structure Tail (p: BudgetPoint)(j:StockTag n)(f:Config G n→ℂ) : Prop where
   read : UsesFinal p.threshold j.val.1 f
   bop : Measurable f
   shelf : GaugeInvariant f
   posed : f≠ 0 → (0:Site n)∈ j.val.1
   poll U : f U≠ 0 → j.val.1∩flags p.threshold U=j.val.2
   earns : ∃ c:ℝ,∀ U, ‖f U‖ ≤ c

def Bolt (p:BudgetPoint)(j:StockTag n): Submodule ℂ (Config G n→ℂ) where
   carrier:={f| Tail p j f}
   zero_mem':= ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _=>rfl,fun h=>(h rfl).elim,fun _ h=>(h rfl).elim,0,by simp⟩
   add_mem':=fun {x y hx hy}=>by
      have hx:Tail p j x:=hx; have hy:Tail p j y:=hy
      obtain ⟨c,hc⟩:=hx.earns; obtain ⟨b,hB⟩:=hy.earns
      refine ⟨fun _ _ e k=> congr_arg₂ (· + ·) (hx.read _ _ e k) (hy.read _ _ e k),hx.bop.add hy.bop,fun t i=> congr_arg₂ (·+·) (hx.shelf t i) (hy.shelf t i),?_,?_,c+b,fun i=>(norm_add_le ..).trans (add_le_add (hc _) (hB _))⟩
      · intro he; by_cases hz:x=0; · exact hy.posed (fun hv=>he (by rw [hz,hv,add_zero]))
        exact hx.posed hz
      intro i he; by_cases hz : x i=0; · exact hy.poll _ (fun hv=>he (by rw [Pi.add_apply,hz,hv,add_zero]))
      exact hx.poll _ hz
   smul_mem':= fun c x hx=>by
      have hx:Tail p j x:=hx
      obtain ⟨B,hB⟩:= hx.earns
      refine ⟨fun _ _ e k=> congr_arg (c • ·) (hx.read _ _ e k),hx.bop.const_smul _,fun t i=>congr_arg (c • ·) (hx.shelf t i), fun hg=>hx.posed (fun h=> hg (by rw [h,smul_zero])),fun U he=>hx.poll U (fun h=>he (by rw [Pi.smul_apply,h,smul_zero])), ‖c‖*B,fun U=>?_⟩
      simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hB U) (norm_nonneg c)

structure Lab (G:Gauge)(n: Side) where
   tag : Config G n
instance : TopologicalSpace (Lab G n):= ⊥
instance : DiscreteTopology (Lab G n):= discreteTopology_bot _

lemma wings (x:Bolt (G:=G) p j): Tail p j x.val:= x.property

def goat (x:Bolt (G:=G) p j): Lab G n→ᵇℂ:= ofNormedAddCommGroupDiscrete (fun i=> x.val i.tag) (wings p j x|>.earns.choose) (fun _=> (wings p j x).earns.choose_spec _)

def sink : Bolt (G:=G) p j→ₗ[ℂ] (Lab G n→ᵇℂ) where
    toFun:= goat p j
    map_add' _ _:= DFunLike.ext _ _ fun _=>rfl
    map_smul' _ _:= DFunLike.ext _ _ fun _=>rfl
lemma debts (x:Bolt (G:=G) p j){s:ℝ} : (∀ U, ‖x.val U‖ ≤ s) ↔ ‖sink p j x‖ ≤ s:= by
    constructor; · intro h; exact (BoundedContinuousFunction.norm_le ((norm_nonneg _).trans (h 1))).2 (fun _=> h _)
    exact fun h i=> ((sink p j x).norm_coe_le_norm ⟨i⟩).trans h
abbrev Stream (G:Gauge) (p:BudgetPoint) (j:StockTag n):=Quoit (sink (G:=G) p j)
end gas
end YM.UVExtension.Eyelet
