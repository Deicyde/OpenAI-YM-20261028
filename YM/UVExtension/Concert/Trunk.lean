import YM.UVExtension.Concert.Vines
import YM.UVExtension.Concert.Speakers
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Gas Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
open AnalyticBridge VerifiedReset Collection Quotes Song Extra.Iteration
variable {Y X' : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {T':Opening X' Y}
private def tallT : Songbook c→ Prop := Sum.elim (fun _=>False) (Sum.elim (fun _=>True) (Sum.elim (fun _=>True) (fun _=>False)))
lemma music (R : PathData G) (p:BudgetPoint) (γ:ℝ) (c' : Clip) {σ V Λ:ℝ} (hr:R.Bounds c' σ V Λ) (hP : WilsonStartup.Decent c' p)
    (hv: preExponent p / p.B ≤ σ/2) {b:ℝ}(hb:0<b) (f:X'→ℝ)(g:Y→ℂ)(hp:∀ z,g (T'.call z)=↑(f z)) (ht:Bumps T'.span g)
    {U:ℝ}(he:1≤U)(hy:∀ z∈T'.span,‖g z‖≤U*b):
    (∀ z,smoothP p (strings R p (n:=c)) (sounding R c' (f z) γ))∧ Nonempty (ticketR T' p (strings R p (n:=c)) (preExponent p) (fun z=>sounding R c' (f z) γ) (fun _=>U*octaveNeed G p c' σ V Λ b γ)):=by
  have hm :0≤U:= zero_le_one.trans he
  let X:= strings R p (n:=c)
  let M:= fork p G X (preExponent p)
  choose V hV hW using fun a=> stanzaReady (n:=c) R c' p a γ hr hP hv
  let F a:= sounding R c' a γ (n:=c)
  let v (a:ℝ) (i: Songbook c):ℝ:= if tallT i then a/b else 1
  let Z(z:Y) (i: Songbook c):ℂ:= if tallT i then g z / b else 1
  have hA d i : Z (T'.call d) i=↑(v (f d) i):= by unfold Z v; split <;> simp only [*,Complex.ofReal_div,Complex.ofReal_one]
  have hZ z (hz:z∈T'.span) i : ‖Z z i‖ ≤ U:= by
    unfold Z; split; next => rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hb.le]; exact (div_le_iff₀ hb).mpr (hy z hz)
    rw [norm_one]; exact he
  let G z : M.CSlot := fun i x=> Z z i* (↑(Tap.read (show Tap p G (X i).site (X i).support from x) (F b i)):ℂ)
  have hi a i : F a i = v a i • F b i:= by
    funext x; rcases i with i|i|i|i
    · rw [show v a (.inl i)=1 from if_neg id, one_smul]; rfl
    · rw [show v a (.inr (.inl i))=a/b from if_pos True.intro]; change (VerifiedReset.factor* -a)*_=a/b*((VerifiedReset.factor* -b)*_); field_simp
    · rw [show v a (.inr (.inr (.inl i)))=a/b from if_pos True.intro]; change (VerifiedReset.factor * -a)*_=a/b*((VerifiedReset.factor* -b)*_); field_simp
    rw [show v a (.inr (.inr (.inr i)))=1 from if_neg id,one_smul]; rfl
  refine ⟨fun z i=>(hW _ i).1,⟨⟨G,fun z i w=>?_,fun i w S f h hh ha=>?_,fun z hz=>?_⟩⟩⟩
  · let w':= show Tap p _ _ _ from w
    change Z (T'.call z) i*_ = ↑(leftDerivs (sounding R c' (f z) γ i) w'.poll w'.view)
    rw [show sounding _ _ _ _ i=_ from hi (f z) i]
    rw [show leftDerivs (v (f z) i • F b i) w'.poll w'.view=_ from Local.left_linear (v (f z) i • ContinuousLinearMap.id ℝ ℝ) w'.poll (show Local.Chart p.order (F b i) _ from (hW b i).1.smooth w'.view w'.live) w'.card]
    rw [hA]; exact (Complex.ofReal_mul ..).symm
  · unfold G Z; split; next => exact (((ht S f h hh ha).div_const _).mul_const _)
    exact differentiableOn_const _
  have hg(i):= tap_bound.mp ((hW b i).2)
  have hC:0≤ U:= zero_le_one.trans he
  refine ⟨fun i=> U* V b i,fun i=>⟨mul_nonneg hC (hg i).1,fun k=>?_⟩,(singers _ _).2 (fun o=>?_)⟩
  · unfold G; rw [norm_mul]
    exact mul_le_mul (hZ z hz i) (((Complex.norm_real _).trans_le ((hg i).2 k))) (norm_nonneg _) hC
  simpa only [mul_ite,mul_zero,mul_assoc] using! budget_scale hm (hV b o)

lemma opusE (p:BudgetPoint) (γ:ℝ) {σ Λ : ℝ} (hu:T.down.Bounds T.low σ C Λ) (he: WilsonStartup.Decent T.low p) (hx: preExponent p/p.B≤ σ/2)
    (h:1≤betaF G x L) (hF:Festa Q L H V w g)
    (J:(d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V)) {c':ℝ} (χ:Chi) (hz:∀ d, smoothP p (Beam.dashboard H) (Song.sequence H (fleet d J H) χ))
    (f:ticketR (aperture hF) p (Beam.dashboard H) (preExponent p) (fun d=> Song.sequence H (fleet d J H) χ) (fun _=> c')):
    (∀ d, smoothP p (Beam.marquee H p).reg (Song.plusone H (fleet d J H) χ γ).logRead) ∧ Nonempty (ticketR (aperture hF) p (Beam.marquee H p).reg (preExponent p) (fun d=> (Song.plusone H (fleet d J H) χ γ).logRead)
      (fun _=>4*turnFee p*(c'+4*octaveNeed G p T.low σ C Λ (betaF G x L) γ))) := by
  let D':=Canvas (betaF G x L) w ι; let A d:= Song.sequence H (fleet d J H) χ
  let R' (d:D'):= sounding T.down T.low (d.val none) γ (n:=c) -- d annotate
  let k:= betaF G x L; have hv:0<k:= zero_lt_one.trans_le h
  obtain ⟨hg,⟨g'⟩⟩:= music (c:=c) (T':=aperture hF) T.down p γ T.low hu he hx hv (fun d=> d.val none) (fun z=> z none) (fun d=> rfl) (bumps _ _ (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) none|>.differentiable.differentiableOn)) (by norm_num : (1:ℝ)≤4) (fun z hz=> by
    obtain ⟨⟨hk,hq,hY⟩,hU⟩:= (marching _).1 (show z∈parade (betaF G x L) g from hz)
    have hx:0<(z none).re:= by unfold k at hv; linarith
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [abs_of_pos hx]
    have hu : |(z none).im|≤ k:= hY.le.trans ((Real.rpow_le_rpow_of_exponent_le h (by norm_num : (99/100:ℝ) ≤1)).trans_eq (Real.rpow_one k))
    unfold k at *; linarith)
  obtain ⟨hD⟩:= bundled _ A _ (R':D'→_) f g'
  let f' d:= opus H (fleet d J H) χ γ
  have hP d: smoothP p (Beam.contents H p) (f' d):= fun i=>match i with | .inl i=> hz d i | .inr i=> hg d i
  have hh d : smoothP p (revolve (Beam.contents H p)) (choir (f' d)):= fun i=> CouplingShape.reg_scale (Rim c) (Seat.regular i.1 (hP d i.2))
  refine ⟨fun d i=> hh d (pennant H i),?_⟩
  let t:= c'+ 4*octaveNeed G p T.low σ C Λ k γ
  have hv : 0≤ t:= by
    have he:Nonempty D':= canvas_nonempty hv hF.margin; let i:D':=Classical.choice he; obtain ⟨w,h,hB⟩:= (hD.bounds ((aperture hF).call i) ((aperture hF).within i)).afloat; exact budget_nonneg (hB 0)
  obtain ⟨hD⟩:= revolving (Beam.contents H p) f' hP (show ticketR _ p _ _ _ (fun _=>t) from hD) (fun _ _=> ⟨hv,le_refl _⟩) hv hh
  exact relocated _ _ (pennant H) hD
end YM.UVExtension.Concert
