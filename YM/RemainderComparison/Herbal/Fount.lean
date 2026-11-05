import YM.RemainderComparison.Herbal.Silk
import YM.RemainderComparison.Portal.Lamps
/-!
 # Output formal rendered density is still part of the shared analytic DOMAIN

 Don't assume that pop weather is automatic. Get Script from authentic tickets
 on virtual torus at this beta. Sec conventions: consider AUTHENTICATED inputs
 AFTER presentation choices (RG02 coefficients, supports and RU mask/law).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Herbal
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Merge Palette Cascade Lyric Lotus Marker Next.Rank.Glyph Next.Rank.Exponential
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} (F : Forest S.ratio) {Θ : ChartRatio G} {k': S.Choices} (ρ:Bid.Dir G c→AxisChart G F) (B V:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "v'"=> eaves G L t
local notation "A'"=> Access.apron G L t
local notation "D'"=> wick G L d t
local notation "e'"=> furl G L t
local notation "g"=> gStep β
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G} {R:Rep G f}
variable [Fintype ι] (P:Eden c G α) (Φ:Config G c→ℝ) (i:modes ι)
local notation "g₀"=> gStep R.beta
variable (ht:Eden.Culture P N k V.threshold (outerCost G k Z) A 0)
variable (hv : ∀ U ∈ Boulevard.sunny V, Portal.ideal (T:=T) (R:=R) V Φ i U + Portal.chronos c₀ i=P.groups R.beta U)
variable (hW:Weather T F Θ k' ρ B R.beta d t a W u C K O k x L)(he:Climate G L t d u C R.beta)(hZ:PaintSupply G k Z)(hh:j+N≤k)

-- proof from registered AUX; Model.H stationary may not be used for output (coupling reset expression variant to pass often).
def sail : Xs×Y→ Config G c := fun x'=>Uniform.outer G F (combineH F x')
lemma ship (x:Xs)(z:Y): sail F (usage θ z (g,x)) = Arc.route G β x:=by
   unfold usage Lantern.visit kite sail; rfl -- 1 irrelevant
omit [Fintype ι] in
lemma anchor (h:PaintSupply G k Z) : Inputs (sail (G:=G) F) k (outerCost G k Z):=by
   let A:=(combineH (G:=G) F).toContinuousLinearMap; have he:=feesComb (G:=G) F
   let Q:=Uniform.outer G F; have hf:= outer_supply F h; refine ⟨(congr_arg Q (map_zero A)).trans hf.1,hf.2.1,?_⟩
   intro i z hz; let f' y:= G.mat (Q y i); have ht : Allows k f' (A z) _:= hf.2.2 i (A z) ((A.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans hz))
   have hH := Brush.reading A (Brush.offer.mpr ⟨ht.analytic.of_le le_top,ht.norm_le⟩) he; rw [one_mul] at hH; exact ⟨ht.analytic.comp z A.contDiff.contDiffAt, (Brush.offer.mp hH).inside⟩
include hW ht he hZ hh

def poet (l:α):= Germ.promote (Germ.baggage ((P.oil l) ∘ sail F) (Lapis.orbit F ρ)) (P.order l) (P.grade l)
def aria (x: ℝ×Positions (Uniform.Primary c G)):=∑ i∈P.ground,poet F ρ P i x 0
omit [Fintype ι] in
lemma singing (l:α)(hl:l∈P.ground):
   Cloud (poet F ρ P l) D' A' u j (j+N) (skys j N D' u A C) ∧ ∀ q: Xs,(gStep R.beta,q) ∈ Germ.patch Xs (Access.apron G L t) u →
     poet F ρ P l (g₀,q) 0=worn (P.oil l) g₀ (P.order l) (P.grade l) (Arc.route G R.beta q):=by
   obtain ⟨hp,hy,hR⟩:= ht.enroll l hl
   have h:=anchor F hZ; have hA:=hR.mode _ _ h; have hq:0<u:= lt_trans (add_pos_of_nonneg_of_pos (norm_nonneg _) he.rad) hW.cabin
   let a:=P.order l; let b:=P.grade l; let W' := (P.oil l) ∘ sail F; have hp': j+a≤k := (Nat.add_le_add_left hy j).trans hh
   have hz : Germ.braces W' θ (j+a) D' A' u A := fun y hx z hz=> (hR.tall _ _ h _ (ethereal T F Θ k' ρ B hW he hx hz)).smaller hp'
   obtain ⟨hB,hX⟩:= Germ.scored (r:=b) hW.paint.core hp' (he.g_pos.trans he.below) he.next.le he.width hq hz hW.paint.origin (fun i hi=> norm_eq_zero.mp (hA.2 i (by exact le_trans hi.le (hy.trans ((Nat.le_add_left _ _).trans hh))) hi))
   refine ⟨hB.raise le_rfl le_rfl le_rfl (earnUp j hy hp) (Nat.add_le_add_left hy _),fun i hi=> (?_)⟩
   apply (hX _ hi _ he.g_pos.ne' (norm_zero.trans_le hW.paint.core.off)).trans; change g₀^b*((g₀^a)⁻¹*(P.oil l) (sail F (usage θ 0 (g₀,i))))=_
   rw [ship]; unfold worn; rw [mul_assoc]
include hv
lemma fellows (hx:Arc.route G R.beta x∈Boulevard.sunny V):
   Portal.Script V R T Φ (aria F ρ P) c₀ i x j (Access.apron G L t) u (halberd G L j N t d u A C):=by
   let v'':= A'; let g':=g₀; have hhP : ‖x‖<u:= lt_of_le_of_lt (le_add_of_nonneg_right he.rad.le) (show _ from hW.cabin)
   have hg : (g',x)∈ Germ.patch Xs v'' u:= (patch_test ..).2 ⟨by change ‖g₀‖<_; rw [Real.norm_of_nonneg he.g_pos.le]; exact he.below,hhP⟩
   have hf i (hi:i∈P.ground):= singing F ρ B V P ht hW he hZ hh i hi
   refine ⟨fun y hy=>?_,?_⟩
   · have hz:0≤ skys j N D' u A C:=by unfold skys; positivity
     let C':=halberd G L j N t d u A C; have hK' : (∑ _∈P.ground, skys j N D' u A C)≤ C' := by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht.occupancy) hz
     exact ((cloud_sum P.ground _ _ (fun i hi=> (hf i hi).1)).budget y hy 0 (norm_zero.trans_le hW.paint.core.off)).climb hK' le_rfl
   have hxP: Continuous (Arc.route (c:=c) G R.beta):= by unfold Arc.route Boulevard.actual represent increment YM.Exterior.collect; fun_prop
   filter_upwards [(Boulevard.sky V|>.preimage hxP).mem_nhds hx, ((Germ.patch_open ..).preimage (show Continuous (fun i:Xs=> (g',i)) by fun_prop)).mem_nhds hg] with y hy hb
   rw [hv _ (show _ from hy)]; exact Finset.sum_congr rfl (fun i hi=> ((hf i hi).2 y hb).symm)

omit hv ht hh he hZ hW [Fintype ι] in -- [Fintype ι] auto included? check
lemma copier (hv:0<R.beta) (U:Config G c)(hX:U∈Boulevard.sunny V): Portal.baser (T:=T) (R:=R) V U = worn (center T.down T.low) (gStep R.beta) 2 0 U:=by
   let g':=gStep R.beta; have he:((gStep R.beta)^2)⁻¹=R.beta:=by unfold gStep; rw [inv_pow,inv_inv,Real.sq_sqrt hv.le]; -- edit
   unfold Portal.baser worn center; rw [pow_zero,he,one_mul]; apply congr_arg (R.beta*·); apply congr_arg SectorMeasure.Oriented.averaged; funext s
   exact Pane.crystal _ _ V (pull s 0 U) (Pane.tranquility U (Boulevard.smoky hX) s 0)
end YM.RemainderComparison.Herbal
