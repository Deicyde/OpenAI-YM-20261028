import YM.TraceExtension.Filch.Tune
import YM.Extra.ITERATION_NO_LOSS.Geometry
import YM.Extra.ITERATION_NO_LOSS.Atoms
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Filch
open RG Wilson Function Filter Lattice Precision Exterior Stationary Push.Uniform WilsonStartup
open Finset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X]{G:Gauge}{n:Side}{x:X} {k r:ℕ}

def fly(o y:Site n):= route 0 (lift (y-o)) 1
lemma flyEnd(o y:Site n): stop o (fly o y)=y:=by simpa only[fly,map_zero,add_zero,wrap_lift,add_sub_cancel] using Work.E03.stop_route o 0 (lift (y-o))
lemma fly_length(o y:Site n): (fly o y).length ≤ 4*separation o y:=by
    let u:=lift (y-o); obtain ⟨hl,hv⟩:=box_test.mp (Work.E08.lift_mem_box (x:=o) (y:=y) le_rfl)
    rw [fly,Extra.Iteration.route_length,sub_zero]; refine le_trans (sum_le_sum (s:= (univ:Finset Axis)) (f:=fun i=> (u i).natAbs) (g:=fun i=>separation o y) (fun i _=>?_)) (by simp); have hh:=hl i; have hx:=hv i; unfold u; omega

def march(o:Site n)(U:Config G n): Coats G n:=fun x=>travel U o (fly o x)
def flock(o:Site n)(U:Config G n):= Lattice.gauge (march o U) U
lemma priced(o:Site n)(U:X→ Config G n)(a:X)(k:ℕ)(C:ℝ)(h:∀ i,Allows k (fun y=>G.mat (U y i)) a C)(y:Site n)(hY:separation o y ≤ r): Allows k (fun v=>G.mat (march o (U v) y)) a (travelCost G k (4*r) C):=travel_jets (U:=U) h o (w:=fly o y) ((fly_length ..).trans (Nat.mul_le_mul_left 4 hY))
def swarm(G:Gauge)(k r:ℕ)(C:ℝ):= let t:=travelCost G k (4*(r+1)) C; 2^k*(2^k*t*C)*t
lemma stepsH(o:Site n)(U:X→ Config G n)(a:X)(k:ℕ)(C:ℝ)(h:∀ i,Allows k (fun y=>G.mat (U y i)) a C)(y:Site n)(hY:separation o y ≤ r)(i:Axis) : Allows k (fun v=> G.mat (flock o (U v) (y,i))) a (swarm G k r C):=by
    let Z v:=march o (U v); have he:separation o (y+step i)≤r+1:=by apply (separation_triangle _ y _).trans; have hp:= Work.E03.sep_step y i; omega
    have hz := priced o U a k C h y (r:=r+1) (by omega); have hr:=priced o U a k C h _ he
    exact (hz.times (f:=fun v=>Z v y) (g:=fun v=>U v (y,i)) (h _)).times (g:=fun v=>(Z v (y+step i))⁻¹) (hr.inverse (f:=fun v=>Z v (y+step i)))
abbrev feed(o:Site n)(r:ℕ):=halo (4*(r+1)) {o}
lemma grazes(o y:Site n)(h:separation o y≤r): LocalOn (feed o r) (fun U:Config G n=>march o U y):=by
    have hv (z:Site n)(hx:z∈visits o (fly o y)): z∈feed o r:=halo_spec.mpr ⟨o,by simp, by have hh:= Extra.Iteration.Shapes.visits_dist o z (fly o y) hx; have hb:=fly_length o y; omega⟩
    exact fun U V he=> travel_local o (fly o y) U V (fun e hx hy=> he _ (hv _ hx) (hv _ hy))
lemma eaten(o y:Site n)(i:Axis)(h:separation o y≤r): LocalOn (feed o (r+1)) (fun U:Config G n=> flock o U (y,i)):=by
    intro U V H; have he:= (separation_triangle o y (y+step i)).trans (Nat.add_le_add h (Work.E03.sep_step y i)); unfold flock Lattice.gauge
    dsimp only; rw [show march o U y = _ from grazes o y (r:=r+1) (by omega) U V H, show march o U (y+step i)=march o V _ from grazes o (y+step i) (r:=r+1) he U V H,H (y,i) (halo_spec.mpr ⟨o,by simp,show separation o y ≤ _ from by omega⟩) (halo_spec.mpr ⟨o,by simp,show separation o (y+step i) ≤ _ from by omega⟩)]
lemma herald(o x:Site n)(U:Config G n)(V:Coats G n): march o (Lattice.gauge V U) x=V o*march o U x*(V x)⁻¹:=by unfold march; rw[travel_gauge,flyEnd]
lemma heaved(o:Site n)(U:Config G n)(V:Coats G n)(e:Edge (Site n)): flock o (Lattice.gauge V U) e= V o*flock o U e*(V o)⁻¹:=by
    simp only [flock,Lattice.gauge]; rw[herald o e.1 U V,herald o (e.1+step e.2) U V]; group
lemma herd_zero(o:Site n):march o (1:Config G n)=1:=by
    funext x; unfold march; have hx:=Push.stroll_zero (G:=G) (fly o x) o; rw[link_one] at hx; exact hx
lemma flock_zero(o:Site n):flock o (1:Config G n)=1:=by unfold flock; rw [herd_zero]; exact gauge_one _
lemma herd_warm(o:Site n)(U:X→ Config G n)(a:X)(p:Army U a): Army (march o ∘ U) a:=by
    have hp (W:Walk) (i:Site n): ContDiffAt ℝ ω (fun z=>G.mat (travel (U z) i W)) a:=by
       induction W generalizing i with
       | nil => exact contDiffAt_const
       | cons k t ih=>
         simp only [travel,G.mat_mul]; refine ContDiffAt.mul ?_ (ih _)
         unfold Step.read; split
         · exact p.inv _
         exact p _
    exact fun i=>hp (fly o i) o
lemma flock_warm(o:Site n)(U:X→ Config G n)(a:X)(p:Army U a): Army (flock o ∘ U) a:= (herd_warm o U a p).slant p
end YM.Trace.Filch
