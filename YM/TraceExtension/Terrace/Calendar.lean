import YM.TraceExtension.Terrace.Rivers
import YM.Next.UV_STRESS.Limit
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=>C.labels.level 4
local notation "B"=> Climb.Bel C.book
variable {Z:Arch C} (hZ:steep 𝓛 Z) {S:Table C.book}{X: Scaling S} {a : (Cells.standard C).Hierarchy}
variable (H:C.Makes) (hb: (𝓛:Filter (ℕ×ℕ)) ≤ F.fuse) (h:S.Hierarchy) (ht:StarPath F a X h 𝓛)
variable {V:∀ i,Vane C i}{Y:∀ (d i:ℕ),(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F a X 𝓛 V Y)
def Moment4 (Z:Arch C)(X:Scaling S)(V:∀ i,Vane C i)(i:ℕ) : C.label 4 →L[ℂ] (Cells.standard C).Field 4 := LinearMap.toContinuousLinearMap ((X.U i 4).symm.toLinearMap.comp ((centering S 4).comp (Vault S Z 4 (Stern V i) (crown Z X (Stern V) 4 i))))
def Hill4 (C:Family G): C.label 4 →L[ℂ] (Cells.standard C).Field 4 := LinearMap.toContinuousLinearMap ((centering (Cells.standard C) 4).comp ((Cells.standard C).project 4))
include h hZ H hb
lemma Vault_c0 (j:ℕ)(hv:C.ref 4 ≤ j)(b:ℝ): centering S 4 (Vault S Z 4 j b (C.labels.level 4).e0)=0:=by
    let F':= C.labels.level 4
    rw [show Vault S Z 4 j b F'.e0= b • Vault S Z 4 j 1 F'.e0 from ?_,show centering S 4 (b • _)=_ from ((centering S 4).restrictScalars ℝ).map_smul b _]; swap
    · change S.project 4 (booty Z 4 j b _) = b • _; rw[treasure,mul_smul,show S.project 4 (b • _)=_ from ((S.project 4).restrictScalars ℝ).map_smul ..]
      simp only[Vault,LinearMap.comp_apply,treasure, one_mul];rfl
    rw [show (centering S 4|>.restrictScalars ℝ) (Vault S Z 4 j 1 F'.e0) =0 from ?_, smul_zero]
    change centering S 4 (S.project 4 (booty Z 4 j 1 _))=_; rw [receipt hZ H hb hv,map_smul,map_smul,← king_unit,show centering S 4 (S.project 4 (C.book.scalar 4))=0 from const_out h.laws,smul_zero]
lemma charge_ret (k:ℕ)(x:C.label 4)(hk:C.ref 4 ≤ (Stern V k)): Moment4 Z X V k (prize Z X V 4 k x)= (X.U k 4).symm (centering S 4 (S.project 4 x)):=by
    let b:= crown Z X (Stern V) 4 k; have hp:0 < b:=by unfold b crown; have ht:= X.positive k;have hu := measured hb H hZ (Stern V k); positivity
    let T:=Vault S Z 4 (Stern V k) b; let f:= (centering S 4).comp T; change (X.U k 4).symm (f (b⁻¹ • swale Z 4 (Stern V k) x))=_; rw [show f (b⁻¹ • _)=_ from (f.restrictScalars ℝ).map_smul .., show (f.restrictScalars ℝ) _=_ from cash_pinc hZ H hb S h.laws _ b hk,inv_smul_smul₀ hp.ne']

variable {W:Worth} {u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
variable (K:Sceptre C W)(θ:PostT C.path.levels)(hG:G.Simple)
include K θ hG ht hq
variable {J:DiffPlan S} {P:DiffPlan (Cells.standard C)} (hJ:J.Derivatives S)(hP:P.Derivatives (Cells.standard C))
include hJ hP
lemma unveil : Tendsto (Moment4 Z X V) atTop (𝓝 (Hill4 C)):=by
    let Q i:=Stern V i; let q:=prize Z X V 4; let s:=Moment4 Z X V
    let T:= Cells.standard C
    let v(i:ℕ):Module.End ℂ (C.label 4):= ((q i).comp (Y 4 i).toLinearMap|>.comp (LinearMap.comp (T.project 4) (LinearMap.id : Module.End ℂ (C.label 4))))+(LinearMap.id-(C.labels.level 4).core)
    let B₁:= Hill4 C
    have hv : Tendsto (fun i=> LinearMap.toContinuousLinearMap (v i)) atTop (𝓝 1):=by
        refine Dash.fit_plane v (LinearMap.id) ?_; intro x
        let f:=Further.CorrectedLift.ladder C 4
        have he:= short_jig hZ H hb hq K θ hG (T.project 4 x)
        rw [show f (T.project _ _)=_ from royal4 hG x] at he
        let L:= C.labels.level 4
        have hs:= he.add_const (x-L.core x); rw [show L.core x+(x-L.core x)=x by abel] at hs
        exact hs
    refine revise _ _ _ hv (Dash.fit_plane (fun i=>(s i|>.toLinearMap).comp (v i)) B₁.toLinearMap ?_)
    intro x; let p:= T.project 4 x
    have ht₁:Tendsto (fun i=>p-expectation S 4 (X.U i 4 p) • (Cells.standard C).unit 4) atTop (𝓝 (B₁ x)):= by
        have hz:Tendsto (fun i=> expectation S 4 (X.U i 4 p)) atTop (𝓝 (expectation T 4 p)):= center_expect h hJ a hP X ht.approach (fun _=>p) p tendsto_const_nhds
        exact tendsto_const_nhds.sub (hz.smul tendsto_const_nhds)
    refine ht₁.congr' ?_; filter_upwards [ht.units 4,(Sstar (A)).comp hq.growth|>.eventually_ge_atTop (C.ref 4), hq.terminal 4] with i hi hn he
    have hs : s i (C.labels.level 4).e0=0:=by
        change (X.U i 4).symm (centering S 4 (Vault S Z 4 (Stern V i) _ _))=0; rw[Vault_c0 hZ H hb h (Q i) hn,map_zero]
    let L:= C.labels.level 4; change p - _ = s i (q i (Y 4 i p)+(x-L.core x)); rw[map_add,show s i (x-L.core x)=0 from ?_, add_zero]; swap
    · unfold L; rw [drop,sub_sub_self,map_smul,hs,smul_zero]
    have hx : s i (q i (Y 4 i p))= (X.U i 4).symm (centering S 4 (X.U i 4 p)):= by rw [show s i _= _ from charge_ret hZ H hb h _ (Y 4 i p) hn,he.2];
    rw[hx,value_center,map_sub,LinearEquiv.symm_apply_apply,map_smul,← hi.2,LinearEquiv.symm_apply_apply]
end YM.Trace.Terrace
