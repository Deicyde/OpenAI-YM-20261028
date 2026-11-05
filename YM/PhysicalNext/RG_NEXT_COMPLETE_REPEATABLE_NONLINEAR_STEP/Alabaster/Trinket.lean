import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Bands
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Uncut
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Grotto
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Pollen
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Raisin
import YM.Primitives.SMALL_FIELD_EXTERIOR.Core
/-! # Warp rays purchasing AFTER η; gets Captain independently (fringe).
    Canary YES for all schedules, same Probe seen. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {x μ C v D' d r D K' : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R} {η εK θ β a h g l b Y A q e r' u : ℝ}
set_option maxHeartbeats 320000 in
lemma discover (P : Teller G) (Q : ConnectedActivityE6.Target G P) : ∃ n:ℕ,∀ (L:Side),n≤L.val→∀ (D:Patch), D.Branches P.bind G→∀ (i:ℕ) (χ:Chi) (W : ℝ),0<W→∀ (μ:ℝ),0<μ→∀ (o:Target.Order G W)
    (A f:ℝ), Canary G A f→ ∀ (V:ℝ→ℝ),Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) → ∀ᶠ x in atTop,
    ∀ (c f':Side) (S:StepData c f') (T:Tube G S), S.patch=D→ Stamp T→ ∀ (R:Rep G f') (C':ℝ) (H:Cash W x μ L Q o C' T R), Nonempty (Loom H A f (V x) χ i) := by
  obtain ⟨n,hN⟩:= Utopia.whittle P Q
  refine ⟨n,fun L hL D hD i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  have hG:= Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f
  obtain ⟨Y,hY⟩:= apical P L D hD o.K o.γ W o.a χ i hV hv hb o.indexPay o.f
  filter_upwards [hχ,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm),hY,hG,paysDia P L D hD _ _ W o.a χ i hV hB hv o.indexPay o.f A ] with x Hx h hx hp hY hG hB c f S T hS hT R C' H
  obtain ⟨Ξ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp; obtain ⟨C',hC,hL⟩:= hB _ _ S T hh hS hθ.access R hy
  let e:= |U x|; have he:0 ≤ e:= abs_nonneg _; let z:= (1+e)^i; have hz:0≤z:=by unfold z; positivity
  refine ⟨⟨hA,hp,|B x|,r x,C,Ξ,|Y x|,abs_nonneg _,?_,z+C',add_nonneg hz hC,k*i,?_⟩⟩
  · intro E _ _ _ F X w β V U z x' s y hX hF hM hψ hA h hζ
    exact hY c _ S T hS hh hθ.access E x' V F X β U w z hX hψ hF (hθ.localP F X hX hF hM) hA h s y hζ
  intro F X hX hF hζ hM E _ _ _ Y y hy' hf
  have hZ := hθ.localP F X hX hF hM
  refine ⟨hG c _ S T hS hh hθ.access F X hF hζ hX hZ E Y y hy' hf, fun z'=>?_⟩
  obtain ⟨hw,hD⟩:= hx _ _ S T F X hX hh hζ R.beta hy.positive z' E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [hX,hh.length_eq]; exact hp)
  refine ⟨hp,fun J=>?_⟩
  have hq := h c _ S T hh hS hθ.access E y Y F X z' R hX hF hζ hZ hy hf hp hw J
  have hL':= hL E y Y F X z' hX hF hζ hZ hf hp J
  let p:= facescale univ z'
  have hp':1≤p:= (Flux.expenses ..).1
  refine ⟨hq.trim|>.climb ?_ le_rfl,hL'.climb (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hz) (by positivity)) le_rfl⟩
  let q:= facescale J z'; have hh:1≤q:=(Flux.expenses ..).1
  have he': 1+e*q^k ≤ (1+e)*p^k := calc
    _ ≤ 1+e*p^k:= add_le_add_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hh) (lo_phi ..) k) he) _
    _ ≤ (1+e)*p^k:= by rw [add_mul,one_mul]; exact add_le_add_left (one_le_pow₀ hp') _
  rw [one_mul]; apply (pow_le_pow_left₀ (show 0≤ 1+e*q^k from (by positivity)) he' i).trans; rw [mul_pow, ← pow_mul]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (by positivity)

open March
-- Clock augments full V.S coupling calendar H. output `Rig` still needs LOOMS that hold for ALL H.
structure Rig (H : Cash W x μ L Q o C T R) (i : ℕ) (v : ℝ) (χ:Chi) where
  birds : ℝ
  spree : ℝ
  veins : Loom H birds spree v χ i
  rays : ℝ
  seat : ℝ
  money : ℝ
  roller : Utopia H i v rays seat money χ
  corps : ℝ
  order : ℕ
  plate : Oboe H i v corps order birds spree roller
  holds : Covers T x H
  mark : ℝ
  rate : 0 ≤ mark
  near : i*mark ≤ v
  groom : Sailor G (Pressure.temp x) mark i
lemma excelsior (P : Teller G) (Q : ConnectedActivityE6.Target G P) : ∃ N:ℕ,∀ L:Side,N≤L.val→∀ (D:Patch), D.Branches P.bind G→∀ (i:ℕ) (χ:Chi) (W μ : ℝ), 0<W→0<μ→ ∀ o:Target.Order G W,∀ᶠ x in atTop, ∃ v:ℝ,0<v∧∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D → Stamp T→∀ (R:RG.Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),Nonempty (Rig H i v χ):= by
  obtain ⟨N,hN⟩:= discover P Q; obtain ⟨M,hM⟩:= Oboe.ell P Q
  refine ⟨N+M,?_⟩; intro L hL D hD i χ W μ hW hμ o
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x:= 2*Pressure.fiery G x L; let v x:= ((i:ℝ)+1)*Z*t x
  have ht : Rate G L (-(1/2)) t:= Rate.flame.mul_left _; have hh : Rate G L (-(1/2)) v:= ht.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  have hv:∀ᶠ x in atTop,0 ≤ v x:=hp.mono fun x h=>by unfold v; positivity
  obtain ⟨C,q,r,p,l,hB,hX⟩:= hM L (by omega) D hD i χ W hW μ hμ o A a hA v hh hv
  filter_upwards [hp,hX,hN L (by omega) D hD i χ W hW μ hμ o A a hA v hh hv, ired P D L hD W o Q] with x hx hX hK hI
  refine ⟨v x,by unfold v; positivity,?_⟩; intro c f S T hS hT R C' H
  obtain ⟨Ξ,he⟩:=hX _ _ S T hS hT R C' H
  refine ⟨A,a,(hK _ _ S T hS hT R C' H).some, q x, r x, C,Ξ,|p x|,l,he,hI _ _ S T hS R μ C' H,Z*t x,mul_nonneg hZ.le hx.le,(by unfold v; nlinarith only [mul_nonneg hZ.le hx.le]),⟨?_⟩⟩ -- hI ..
  intro c e he; apply hq c (t x) hx.le e; apply he.trans; have hp:=H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at hp; exact hp
end YM.PhysicalNext.Repeat.Alabaster
