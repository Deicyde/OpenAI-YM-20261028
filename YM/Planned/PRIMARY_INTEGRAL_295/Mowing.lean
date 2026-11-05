import YM.Planned.PRIMARY_INTEGRAL_295.Bosom
import YM.Planned.PRIMARY_INTEGRAL_295.Density


/-!
# Core D rows when coordinate is not in numerical support

Before summing actual votes. Genuine v.Core untruncated powers including
axes that flip sign. Exhaust Euclidean A derivative ACTUALLY applied at 0
a.Even f where not differentiable fallback, but don't rely on default
at any future proofs. No shrinking Y in judgments. Uses d_L coarse parent
eviction or fine parent similarly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Mowing
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform   Density
open Next.Fluctuations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {r:ℕ} {c f : Side} {S:StepData c f} (s: Signed) (K:Core G S)

/-- compare C.parent signed moving path budget. -/
lemma wanders (g: Site c) (i:Bond f):separation (affine s 0 g) (S.ratio.parent (sendEdge s 0 i).1) ≤ separation g (S.ratio.parent i.1) +1 := by
   have he : S.ratio.parent (affine s 0 i.1) = affine s 0 (S.ratio.parent i.1):= by simp only [affine,add_zero,S.ratio.parent_signed S.patch.odd_side]
   let d:Step:= (posDir i.2).rotate s
   let x:=affine s 0 i.1
   apply (separation_triangle (affine s 0 g) (S.ratio.parent x) (S.ratio.parent (d.used x).1)).trans
   rw [show separation (affine s 0 g) (S.ratio.parent x)=separation g (S.ratio.parent i.1) from by rw [he]; simp [affine]]
   apply Nat.add_le_add_left
   unfold Step.used; split
   · rw [separation_comm]; have hp:= Work.E03.parent_step S (x-step d.dir) d.dir; rw [sub_add_cancel] at hp; exact hp
   simp

omit s K in
lemma evades (q:E→F)(e:E) (h:∀ x:ℝ,q (x • e)=q 0): fderiv ℝ q 0 e=0:=by
   by_cases hw:DifferentiableAt ℝ q 0
   · have hh:= YM.Push.side q hw e; rw [show (fun t:ℝ=>q (t • e))=(fun _=>q 0) from funext h] at hh; exact hh.unique (hasDerivAt_const _ _)
   rw [fderiv_zero_of_not_differentiableAt hw]; simp

variable (x:Dir G c) (e:Acres f G)
lemma shadows (q: Site c) (hr:r+1 < separation (affine s 0 q) (chair S e)) (t:ℝ):
   AgreeNear S.ratio.parent q r (K.seek s x (t • Pi.single e 1)) (K.seek s x 0) := by
   intro i hi
   have hp : sendEdge s 0 i≠e.1:=by
      intro hp; have hv:=wanders (S:=S) s q i; rw [hp] at hv; unfold chair at hr; omega
   let v:Temps G f:=t • Pi.single e 1
   let p:=sendEdge s 0 i
   have hc : menu (S:=S) x (K.reachable v) p=menu (S:=S) x (K.reachable 0) p := by
      unfold menu increment; rw [Bosom.count_root, Bosom.count_root]; split
      · rfl
      have he (j:G.ColorIndex) : (sendEdge s 0 i,j)≠e:=fun H=>hp (congr_arg Prod.fst H)
      congr! 3; unfold v; simp [p,he]
   unfold seek pull Lattice.Step.read; split
   · change (menu (S:=S) x _ p)⁻¹= (menu (S:=S) x _ p)⁻¹; rw [hc]
   exact hc

section Color
-- contraction component (raw* operator norm)
def shot (p:Dir G c→Temps G f→G.Color) (e:Acres f G)(i:G.ColorIndex) (v:Dir G c): ℝ:= ballast * (fderiv ℝ (p v) 0 (Pi.single e 1)) i

def perif (K:Core G S) (p:Cell f)(s:Signed) (Z:Slot) (v:Dir G c)(u:Temps G f):G.Color:=
    kink Z (K.seek s v 0) (K.seek s v u) p.1

def dropF (G:Gauge) (s:Signed)(p:Twin f) (k:G.ColorIndex):Seats G c f:= ((s,.inl p),k)
def dropQ (s:Signed)(p:Bond c) (k:G.ColorIndex): Seats G c f:= ((s,.inr p),k)

lemma curved (p : Cell f)(z:G.ColorIndex) (Z:Slot) (h : Z.length +1<separation (origin S (dropF G s (p,true) z)) (chair S e)):
    Mowing.shot (perif K p s Z) e z x=0 := by -- remove K
   let r:=S.ratio
   have hr : r.parent (affine s 0 p.1)=affine s 0 (r.parent p.1):=by simp only [affine,add_zero,r.parent_signed S.patch.odd_side]
   have hc : ∀ t:ℝ, perif K p s Z x (t • Pi.single e 1)= perif K p s Z x 0 := by
     intro t; set v:= Work.F03.slotFace Z p.1
     let A(t:ℝ):=K.seek s x (t • Pi.single e 1)
     have hh : v.1=stop p.1 Z.walk:=by
        unfold v Work.F03.slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 2 [show p.1=p.1+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
     have hp : separation (r.parent p.1) (r.parent v.1)+4≤Z.length:=by rw [hh]; apply Nat.add_le_add_right (Work.E03.sep_walk _ (Work.E03.parent_step S) ..)
     have hf : AgreeNear r.parent (r.parent p.1) Z.length (A t) (K.seek s x 0):= shadows s K x e _ (by change _+1<separation (r.parent (affine s 0 p.1)) (chair S e) at h; rwa [hr] at h) t
     let D:=square Z.plaq.val.1 Z.plaq.val.2
     have hz := travel_near r.parent (Work.E03.parent_step S) (A t) (K.seek s x 0) v.1 D 4 (show _≤4 by simp [D,square]) (hf.shrink hp)
     unfold perif kink faceValue; simp only [travel_at]; exact congr_arg (fun v => G.adjoint _ (G.curvature v)) hz
   unfold shot; rw [evades _ _ hc]; simp

lemma cool (p:Cell f)(z:G.ColorIndex) (h:4+1<separation (origin S (dropF G s (p,false) z)) (chair S e)) :
    Mowing.shot (K.jump (s,.inl (p,false))) e z x=0:=by
   let r:=S.ratio
   have hr : r.parent (affine s 0 p.1)=affine s 0 (r.parent p.1):=by simp only [affine,add_zero,r.parent_signed S.patch.odd_side]
   have he :∀ t:ℝ,_= _:=fun t=> travel_near r.parent (Work.E03.parent_step S) _ _ p.1 (square p.2.val.1 p.2.val.2) 4 (by simp [square]) (shadows s K x e _ (by
      change _<separation (r.parent (affine s 0 p.1)) (chair S e) at h; rwa [hr] at h) t)
   have hp(t:ℝ):K.jump (s,.inl (p,false)) x (t • Pi.single e 1)=K.jump (s,.inl (p,false)) x 0:=by
      change Pressure.shoot _ _ p=Pressure.shoot _ _ p; unfold Pressure.shoot faceValue; rw [he t]
   unfold shot; rw [evades _ _ hp]; simp

lemma focus (p:Bond c)(z:G.ColorIndex)(hb:S.patch.Branches S.kernel G)(h:predReach S.patch+1<separation (origin S (dropQ s p z)) (chair S e)):
    Mowing.shot (K.jump (s,.inr p)) e z x=0:=by
    have hp(t:ℝ):K.jump (s,.inr p) x (t • Pi.single e 1)= K.jump (s,.inr p) x 0:=by
       have he:= prediction_near_eq hb _ _ (Push.SectorMeasure.Oriented.choice s K.k) p (shadows s K x e _ h t)
       change K.conf s x _ p= K.conf s x 0 p; unfold Little.Core.conf Little.Core.target; rw [he]
    unfold shot; rw [evades _ _ hp]; simp
end Color
end YM.Planned.PrimaryIntegral295.Mowing
