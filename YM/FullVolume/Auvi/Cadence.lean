import YM.FullVolume.Auvi.Raise
/- point of departure -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Beacon Stationary.Shade Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
open Rain Pane Roof ConnectedActivityE6.Lim FullVolume.Shadow
variable {m:ℕ}{Z:f.val=c.val*(A.B.a.S.block m).val}{W:Listing G f}{N:ℕ}
local notation "K"=> A.B.kin
local notation "B"=> A.B.a
local notation "Q"=> A.B.a.budget m
local notation "Ω"=> A.B.a.budget (m+1)
variable {p:ℕ}
namespace Pith
variable (hG:G.Simple){t v:ℝ}{u v':ℕ→ℕ}(h:Artes.Cadre A.post A.B.kin)(hk:Next.Free.Amplify A.B.M)(hu:Tendsto u atTop atTop)(hh:Tendsto v' atTop atTop)(hx:Near A m u)(hy:Near A m v')(H:∀ n,Chord R (u n) m p t v)(T:∀ n, Chord R (v' n) m p t v)
    (M:∀ n,Chord.Flight A (u n) m p)(L:∀ n,Chord.Flight A (v' n) m p)
set_option quotPrecheck false
local notation "P'"=> A.B.a.S.side m p
local notation "f'"=>A.B.a.S.side (m+1) p
set_option quotPrecheck false
local notation "γ"=> fun n=> A.B.kin.alpha (u n) m
local notation "δ"=> fun n=> A.B.kin.alpha (v' n) m
local notation "V"=>fun n=> (M n).val
local notation "V'"=>fun n=>(L n).val
local notation "W"=> FullVolume.Urns.layout G (f') Ω -- replace
open FullVolume.Urns Pass Progress.DirectedRecipe
lemma absolves {S:FullVolume.Urns.Price G c} {Y Z:ℕ→ Show S}(h:Canopy S.p (drawer G c).reg (fun n=>(Y n).proper.E) (fun n=>(Z n).proper.E))(he:Angel (fun n=> (Y n).proper.K) (fun n=>(Z n).proper.K)): Tendsto (fun n=> Y n-Z n) atTop (𝓝 0):=by
   refine Metric.tendsto_nhds.mpr fun ε hp=>?_ ; let t:=ε/2
   filter_upwards [h.loan (t*S.b) (mul_pos (half_pos hp) S.b0),he.hazel («B»:=S.p) (A:=fun i=> ((layout G c S.p).hard i).support) (t*S.k) (mul_pos (half_pos hp) S.k0)] with n hn hx
   rw [dist_zero_right]; apply lt_of_le_of_lt _ (half_lt_self hp); apply (Show.budget ..).mpr; obtain ⟨a,ha,h'⟩:= hn; obtain ⟨d,hd,hD⟩:=hx; let T:=Y n-Z n; have hf:= (Show.budget T ‖T‖).mp le_rfl
   refine ⟨hf.1,hf.2.1,⟨a,ha,fun x=>budget_mono h' (fun i=>?_) (fun i=>?_)⟩,⟨d,hd,fun x=>budget_mono hD (fun i=>?_) (fun i=>?_)⟩⟩
   · split; exact h'.1 _; rfl
   · split; rfl; exact h'.1 _
   · split; exact hD.1 _; rfl
   split; rfl; exact hD.1 _
variable (E F:ℕ→ Show (Pass.stageP A.B.a (m+1) p)) (Y Y':ℕ→ Show (Pass.stageP A.B.a m p)) (hZ:Jams.Wild R.shape A.delay)
variable (hA:∀ n,(M n).val.activities=(E n).proper)(hA':∀ n,(L n).val.activities=(F n).proper)(hT:∀ n,(H n|>.moment (M n)).activities=(Y n).proper)(hT':∀ n,(T n|>.moment (L n)).activities=(Y' n).proper) (hB:Glints atTop (fun n=> (M n).val.beta) (fun n=>(L n).val.beta))(hE:CauchySeq E)(hF:CauchySeq F) (hm:Tendsto (fun n=> E n-F n) atTop (𝓝 0))
abbrev CloseA (H:∀ n, Chord R (u n) m p t v)(T:∀ n,Chord R (v' n) m p t v)
    (M:∀ n,Chord.Flight A (u n) m p)(L:∀ n,Chord.Flight A (v' n) m p)(Y Y':ℕ→ Show (Pass.stageP A.B.a m p)):= Tendsto (fun n=> (H n|>.moment (M n)).beta-(T n|>.moment (L n)).beta) atTop (𝓝 0) ∧ Tendsto (fun n=> Y n-Y' n) atTop (𝓝 0)
include hG h hk hu hh hx hy H T E F Y Y' hZ hA hA' hT hT' hB hE hF hm
lemma tours : CloseA H T M L Y Y':=by
    obtain ⟨hp,hq,h⟩:= rises hG h hk hu hh hx hy H T M L hZ (fun n=>by unfold listIn; rw [hA n]; rfl) (fun n=>by unfold listIn; rw [hA' n]; rfl) (by simp_rw [hA,hA']; exact Trill.gloves hE hF hm) (by simp_rw [hA,hA']; exact Trill.hockey hE hF hm) hB
    simp_rw [hT,hT'] at hq h; exact ⟨hp,absolves hq h⟩
omit hG h hk hu hh hx hy H T E F Y Y' hZ hA hA' hT hT' hB hE hF hm
lemma exportY {X:Type}[UniformSpace X]{S:ℕ→X}(h:CauchySeq S){φ:ℕ→ℕ}(he:Tendsto φ atTop atTop): CauchySeq fun i=> S (φ i):= by
    change Cauchy (Filter.map (S∘φ) atTop); rw [← Filter.map_map]; exact Cauchy.mono h (Filter.map_mono he) -- need NeBot
lemma high {X:Type}[TopologicalSpace X]{f:ℕ→X}{x}(n:ℕ)(h:Tendsto (fun i=>f (i+n)) atTop (𝓝 x)):Tendsto f atTop (𝓝 x):=by
   intro S hS; obtain ⟨k,hk⟩:= eventually_atTop.mp (h.eventually hS); refine eventually_atTop.mpr ⟨k+n,fun b hb=>?_⟩; obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le (show n≤ b by omega); rw [add_comm]; exact hk _ (by omega)
include hG h hk hu hh H T E F Y Y' hZ hA hA' hT hT' hB hE hF hm
lemma shall : CloseA H T M L Y Y':=by
   obtain ⟨n,hn⟩:= eventually_atTop.mp ((follows h hu m).and (follows h hh m)); let f(i:ℕ):= i+n; have hf:Tendsto f atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id
   have he i: n≤ f i:= Nat.le_add_left ..
   have hx: Near A m (u∘f):= fun i=> ⟨(H (f i)).paid,(hn _ (he i)).1⟩; have hg : Near A m (v'∘f):= fun i=> ⟨(T (f i)).paid,(hn _ (he i)).2⟩
   obtain ⟨ha,hK⟩:= tours hG h hk (hu.comp hf) (hh.comp hf) hx hg (fun i=>H (f i)) (fun i=> T (f i)) (fun i=> M (f i)) (fun i=> L (f i)) (E∘ f) (F∘ f) (Y∘ f) (Y'∘f) hZ (fun _=>hA _) (fun _=> hA' _) (fun _=> hT _) (fun _=> hT' _) (glitters hB hf hf) (exportY hE hf) (exportY hF hf) (hm.comp hf)
   exact ⟨high n ha,high n hK⟩
end Pith
end YM.PhysicalNext.Repeat.Lark
