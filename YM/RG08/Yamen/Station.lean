import YM.RG08.Yamen.Pledge

/-! # Foyer & Duo on actual compatible horizons. Top Wilson convention,
 met with GIVEN all-torus H Floor (not necessarily id on offcurl).
-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Supplies Flat Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{P X:MapPrices}{H:Yard G}
variable {a:Levels G}{F:Horizon a}(hF:F.Suffices P)(N m:ℕ)

local notation "j!"=>a.clock.J m
local notation "j#"=>a.clock.J (m+1)
abbrev lamp (P X:MapPrices)(a:Levels G)(m:ℕ): Yard G:= Yamen.atlas G P X a.clock.kernel (a.clock.J m)
def base (P X:MapPrices)(a:Levels G)(m:ℕ)(A:Bed):= initial (lamp P X a m) A
lemma zeal :0<(lamp P X a m).need 0 0 ∧ (lamp P X a m).need 0 0 ≤ min 1 (P.α (a.clock.J m)):= by
 refine ⟨(lamp P X a m).tall _ _, (honesty_small G P X _ _ 0).trans ?_⟩; unfold trod;exact (min_le_left ..).trans (min_le_left ..)
include hF in
lemma star (h:m ≤ N):0≤P.Ω (a.clock.J m):=by
 have hf:=(hF.rows N m h); -- Ω_pos uses hF globally
 exact Ω_pos hF m
include hF in
lemma veils (hg:G.Simple)(h:m ≤ N)(hf:∀ n,Bid.Sworn (F.H N m) n G):
 Sedan.Seed (F.H N m) (Yamen.base P X a m (F.H N m)) ∧ Held (carpet (Tone G.ColorIndex)) ((lamp P X a m).coats 0 0) (basis G P X a.clock.kernel j!) (Yamen.base P X a m (F.H N m)):=by
 obtain ⟨hf0,hb⟩:=zeal (P:=P) (X:=X) (a:=a) m
 have he:0 ≤ max 0 (P.Ω j!):=le_max_left ..
 exact attained (lamp P X a m) (F.H N m) hg (fun i j=> ((hF.rows _ _ h).2.1 i j).mono (le_min_iff.mp hb).2 (le_max_right ..)) (hF.all N m h) hf (le_min_iff.mp hb).1 he -- Ω floor u remains p.Ω

include hF in
lemma warms (h:m<N):Cell.Warm G a.clock.kernel (Supplies.stone a m) (F.H N (m+1)) (PlanCurve G a.clock.kernel P j#) (planSupply G a.clock.kernel P j# (a.S.block m)):=
   (planSupply_spec G a.clock.kernel P _).2 _ (a.blocks m 0).branches rfl _ (hF.rows N (m+1) h).2.1 _ _ (fun n=>hF.all N (m+1) h n)

-- uniform Proceed (starting [T] even if frame arrays chosen in different charts)
lemma landed (C:Castle G){B:Bed}{c:Side}(hC:Mount.Stable C)(hT:Sedan.Seed B (C 0 0)){σ p:ℝ}(hp:B.metric.strip σ p)(hs:0<σ)(ht:σ≤1)(hd:0≤p):Proceed C B c:=by
 intro x;obtain ⟨H,t,w,he,hW,hb⟩:=hT.honor
 rw [Aggregate.reserve (Mount.stick 0) (Mount.stick 0) (hC.banner 0 0).path (hC.hold 0 0) (hC.weight 0 0) (hC.dial 0 0), Carrel.complete_top (C 0 0) _ H hb hW he,hT.cast]
 have hT' :pour (P:=c) (compress 1 (Cast.root G B)) (Mount.stick 0)= Cast.arcade (quadratic B c):=by
    rw [Cast.root,Cast.beam,show compress 1 (Anchor.extend 1 (Cast.spur G (Flat.output B)))=Cast.spur G (Flat.output B) from funext (fun i=>Anchor.extend_top ..)]; exact Cast.spur_matches ((Flat.output_cost hp hd hs.le ht).2 c)
 have he(F:Rudder.Raw G.ColorIndex 2):Isles.pour (P:=c) (compress 1 ((1/2:ℝ) • F)) (Mount.stick 0)=(1/2:ℝ) • Isles.pour (P:=c) (compress 1 F) (Mount.stick 0):=by
    ext z;rw [Pi.smul_apply,Isles.pour_at,Isles.pour_at];change (∑' x:Isles.lantern (Mount.stick 0) z,(1/2:ℝ)*compress 1 F x.val)=_; rw [tsum_mul_left,smul_eq_mul]
 rw [he,hT',Prism.binal]

variable {Z:ChartRatio G}
-- adapter on constructed overlap
include hF in
lemma studio (hg:G.Simple)(h : m<N) (hf:∀ n,Bid.Sworn (F.H N m) n G)(hx:LocalRatio Z)(C:Castle G)(hC:Tires (F.H N (m+1)) C):
 Reach (K:=a.clock.kernel) (Supplies.stone a m) Z (F.H N (m+1)) (F.H N m) C (base P X a m (F.H N m)):=by
 let k:= a.clock.kernel;let s:= Supplies.stone a m
 let t := PlanCurve G k P j#; let D:= planSupply G k P j# (a.S.block m)
 have hu :0<t ∧ t ≤ 1:=⟨(plan_hr ..).1,(plan_hr ..).2.1⟩
 have h0:=warms (F:=F) hF N m h
 let v:=min 1 (P.α j!);have hv:0<v:=lt_min (by positivity) (P.alpha_pos _)
 have he (m)(hi:m ≤ N): let v:=min 1 (P.α (a.clock.J m))
   ; (F.H N m).metric.strip v (P.Ω (a.clock.J m)):=fun i j=> ((hF.rows _ _ hi).2.1 i j).mono (min_le_right ..) le_rfl
 refine ⟨⟨⟨hC.ethos.rails,⟨_,_,hu.1,hu.2,h0⟩,⟨v,_,hv,min_le_left ..,Ω_pos hF m,he _ h.le⟩,hx,fun i=>landed C hC.ethos.rails hC.origin (he _ h) (lt_min zero_lt_one (P.alpha_pos _)) (min_le_left ..) (Ω_pos hF _),⟨_,_,_,fun i=>hF.all N (m+1) h _⟩,?_⟩⟩, (veils hF N m hg h.le hf).1⟩ -- nesting Nonempty.wrap?
 let N0(i):Side:=a.S.side m i
 let M0(i:ℕ):= (N0 i).val-1
 have hE(i) : Isles.chain (M0 i)=N0 i:=Subtype.ext (Nat.sub_add_cancel (show 1 ≤ (N0 i).val from (N0 i).pos))
 refine ⟨M0,tendsto_atTop.mpr (fun r=> ((Flat.mesh_sides a.S m).eventually (eventually_ge_atTop (r+1))).mono (fun i he=>?_)),?_⟩
 · change r+1 ≤ (N0 i).val at he; change r≤(N0 i).val-1;omega
 intro i; rw [hE]
 -- align fine side by elimination of side equality via lemma
 have he'(c f:Side)(S:StepData c f)(U V:Bed)(W:Towers S.patch.L)(hD:Towers.Diagonal S U V W):∃ L,Inputs (RG08.Line.habitat S.patch S.kernel c) L (U.metric.acts (c*S.patch.L)) (V.metric.acts c):=by
    rcases S with ⟨p,K,h⟩; have heq : f=c*p.L:=Subtype.ext h;subst f
    exact ⟨_,hD.trial⟩
 exact he' _ _ (a.clock.op m i) (F.H N (m+1)) (F.H N m) _ (hF.crossings N m i h)
end YM.RG08.Yamen
