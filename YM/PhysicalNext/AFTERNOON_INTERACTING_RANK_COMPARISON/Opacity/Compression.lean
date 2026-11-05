import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Conditions
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Valve
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Slate
/-!
# Composition of the actual Charts on the pictured data

Enough to test the whole unshifted Photos at variable scalar on the SAME
frozen/dust split. Do not try to divide a measurable realized field by a fixed
g to reconstruct Z. Reads applications in a following file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Stores Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter SectorTools.PhysicalGaussianSwitch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A : Stores S}
    {F : Forest S.ratio} {X : Support c}
structure Pilot (G : Gauge) (S : StepData c f) (x : ℝ) where
  key : Stores S
  park : Forest S.ratio
  tag : S.Choices
  view : Config G c
  y : RoomView key x park G

def spires (p : Wheel c) (z : Pilot G S x) : Pilot G S x:=
  ⟨book p.1 p.2 z.key,Locations.forest p.1 p.2 z.park,ticket p.1 p.2 z.tag,pull p.1 p.2 z.view,cusps z.key z.park p.1 p.2 x z.view z.y⟩
def burnish (z : Site c→G.El) (v : Pilot G S x) : Pilot G S x:= {v with view:= gauge z v.view,y:=rotate_bus x z v.y}

def kid (V : Config G c) (Y : RoomView A x F G) (g : ℝ) := photo g V 0 Y.1 Y.2
lemma rig (p : Wheel c) (Y : RoomView A x F G) (V : Config G c) (g) :
    kid (pull p.1 p.2 V) (cusps A F p.1 p.2 x V Y) g = pull p.1 (S.ratio.embed p.2) (kid V Y g):= by
  have he : fan A F p.1 p.2 x V 0=0:= Matrix.mulVec_zero _
  unfold kid; nth_rw 1 [← he]; exact circulate A F p.1 p.2 V x g Y 0
lemma guising (z : Site c→G.El) (Y : RoomView A x F G) (V : Config G c) (g) :
    kid (gauge z V) (rotate_bus x z Y) g=gauge (constantGauge z S.ratio) (kid V Y g):= by
  unfold kid; nth_rw 1 [← Matrix.mulVec_zero (toGauge z A F x)]; exact turning_photo z A F x V 0 Y.1 g Y.2
lemma friend (V : Config G c) {Y Z : RoomView A x F G} (h : ∀ g,kid V Y g=kid V Z g): Y=Z:= by
  refine Prod.ext ?_ ?_
  · funext j
    have he (y : RoomView A x F G) : kid V y 0 j.val.val = y.1 j := (F.off_tree _ j.val).trans (freeze_held (j:=j) ..)
    rw [← he,←he,h]
  apply tape.injective
  funext i
  have hf (g) (y:RoomView A x F G): kid V y g i.val.val= G.lieExp (g • tape y.2 i)*replica S.ratio V i.val.val:= by
    change photo g V 0 _ _ i.val.val=_; unfold photo; rw [zero_add,show tape (g • y.2)=g • tape y.2 from colors.map_smul ..]; exact (F.off_tree _ i.val).trans (freeze_regular (j:=i) ..)
  have he g:G.lieExp (g • tape Y.2 i)=G.lieExp (g • tape Z.2 i):= mul_right_cancel (show _ * _=_ * replica S.ratio V i.val.val from by rw [← hf,← hf,h])
  let r:= 1+‖tape Y.2 i‖+‖tape Z.2 i‖; have hr : 0<r:=by unfold r; positivity
  let v:=firstRadius G/r; have h0:= first_pos G; have hv:0<v:=div_pos h0 hr
  have hx (u : G.Color) (hh:‖u‖<r) : v • u ∈ firstBall G:= mem_ball_zero_iff.mpr (by rw [norm_smul,Real.norm_of_nonneg hv.le]; exact (mul_lt_mul_of_pos_left hh hv).trans_eq (div_mul_cancel₀ _ hr.ne'))
  apply (smul_right_injective (G.Color) hv.ne'); exact (over_ball (hx _ (by unfold r; linarith [norm_nonneg (tape Z.2 i)]))).symm.trans ((congr_arg _ (he v)).trans (over_ball (hx _ (by unfold r; linarith [norm_nonneg (tape Y.2 i)]))))

def rods (z : Pilot G S x) := kid z.view z.y
lemma mates {p q : Pilot G S x} (hk : p.key=q.key) (hg : p.park=q.park) (ht : p.tag=q.tag) (hv : p.view=q.view) (hr : ∀ g, rods p g=rods q g): p=q:= by
  obtain ⟨A,F,k,U,Y⟩:= p; obtain ⟨A',F',k',U',Y'⟩:= q
  dsimp only at hk hg ht hv; subst A' F' k' U'; rw [friend U (Y:=Y) (Z:=Y') hr]
lemma shooting (p : Wheel c) (z : Pilot G S x) (g) : rods (spires p z) g=pull p.1 (S.ratio.embed p.2) (rods z g):= rig ..
lemma burn (v : Site c→G.El) (z : Pilot G S x) (g) : rods (burnish v z) g=gauge (constantGauge v S.ratio) (rods z g):= guising ..
lemma g_comp (v w : Site c→G.El) (V : Config G c) : gauge v (gauge w V)=gauge (v*w) V:= by funext i; simp only [Lattice.gauge,Pi.mul_apply]; group
lemma flow (p q : Wheel c) (z : Pilot G S x) : spires (meet p q) z=spires q (spires p z):= by
  refine mates (marks p q z.key) (merged ..) (paying z.tag ..) (pull_pull .. |>.symm) fun g=>?_
  rw [shooting, shooting, shooting, pull_pull]; change pull _ _ _ = pull (meet ..).1 (meet (inflow S p) (inflow S q)).2 _
  rw [← grow]; rfl
lemma refine_eq (v w : Site c→G.El) (z : Pilot G S x) : burnish (v*w) z=burnish v (burnish w z):= by
  refine mates rfl rfl rfl (g_comp v w z.view|>.symm) fun g=>?_
  rw [burn,burn,burn,g_comp]; rfl
lemma alloys (v : Site c→G.El) (p : Wheel c) (z : Pilot G S x) : spires p (burnish v z)=burnish (v ∘ orient p) (spires p z):= by
  refine mates rfl rfl rfl (Push.Local.pull_gauge ..) fun g=>?_
  rw [shooting,burn,burn,shooting,Push.Local.pull_gauge]
  refine congr_arg (fun t => Lattice.gauge t (pull p.1 (S.ratio.embed p.2) (rods z g))) (funext ?_); intro i
  exact congr_arg _ (Locations.parent_map p.1 p.2 (S:=S) i)
end YM.PhysicalNext.InteractingRank.Pump
