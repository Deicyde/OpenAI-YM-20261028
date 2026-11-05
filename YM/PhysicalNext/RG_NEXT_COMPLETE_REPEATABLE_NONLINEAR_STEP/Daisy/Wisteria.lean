import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Syllabus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Kin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Profile
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
variable (χ0:Chi) (V:Config G c) (θp:ℝ)(w:ℕ)
local notation "F0" => color M H χ0
@[simp] lemma color0 : F0 V 0= H.spawn χ0 V := by ext i; simp [color]
-- without Champion or Plating API still parameter.F
private lemma color_spin (i : Molecule S) : Measurable (fun V=> F0 V θp i) ∧ UsesFinal (Pressure.temp x) (H.unionP i) (fun V=> F0 V θp i) ∧ GaugeInvariant (fun V=> F0 V θp i):=by
  obtain ⟨hs,hx,hv⟩:= M.spinning T x χ0 H i
  refine ⟨(Match.fees H χ0 i).1.add (measurable_const.mul hv),fun V U h hp=> congr_arg₂ (·+·) (Match.sites H χ0 i V U h hp) (congr_arg _ (hs V U h hp)),fun t U=> congr_arg₂ (·+·) (?_) (congr_arg _ (hx t U))⟩
  unfold Cash.spawn poolA; apply congr_arg likely; funext u; exact H.radiant (prism T x χ0 o.K U (Greenbelt.allot u)) rfl rfl ..
lemma smiling (p:H.Chainbook):
    let g:= fun V=> H.smilesMill V (F0 V θp) p
    Measurable g∧ UsesFinal (Pressure.temp x) (H.library p) g∧ GaugeInvariant g ∧ (g V≠0→ (H.inventory p.1.toLeft).Nonempty∧ H.statesPool V p∧Ac.Spark H.bookFoot p.1):=by
  intro g
  let Z:= fun V i=> H.cologneMill (F0 V θp) i; have hg(i:H.Chapter): Measurable (fun V=> Z V i) ∧ UsesFinal (Pressure.temp x) (H.bookFoot i) (fun V=>Z V i)∧GaugeInvariant (fun V=>Z V i):=by
    rcases i with i|i
    · exact color_spin M H χ0 θp i.val
    let u V j:= H.entriesMill (F0 V θp) (i.2 j); let a:ℝ:=Ursell.coefficient H.seam i.2
    have h(z): H.smallAt (i.2 z)⊆ H.bookFoot (.inr i):= subset_biUnion_of_mem (H.smallAt ∘ i.2) (mem_univ _)
    refine ⟨(Measurable.neg ( (measurable_const (a:=a) |>.mul (Finset.measurable_fun_prod _ fun p _=> show Measurable (fun V=>u V p) from (color_spin M H χ0 θp _).1)).div_const ((i.fst+1).factorial:ℝ))),fun V U hV hb => ?_,fun t U=> ?_⟩
    · exact congr_arg (fun v:ℝ=>-(a*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> inheritance ((color_spin M H χ0 θp _).2.1) (h j) V U hV hb)
    exact congr_arg (fun v:ℝ=>-(a*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> (show u (gauge t U) j=u U j from (color_spin M H χ0 θp _).2.2 t U))
  refine ⟨?_ ,?_,?_,?_⟩
  · by_cases hv:H.Fresh p∧ Ac.Spark H.bookFoot p.1
    · let q(V : Config G c):=RG.flags (Pressure.temp x) V
      unfold g Cash.smilesMill; refine Measurable.ite ?_ (Finset.measurable_fun_prod _ (fun i _=>(( (hg i.val).1).pow_const _).div_const _)) measurable_const
      rw [show {V:Config G c| _}= ⋃ t∈ univ.filter (fun t=> H.inventory p.fst.toLeft=t∩H.library p),{V : Config G c|q V=t} from Set.ext (fun V:Config G c=> by simp [hv.1,hv.2,Cash.statesPool,q])]
      exact MeasurableSet.iUnion fun i=>MeasurableSet.iUnion fun _=>RG.flags_measurable_eq ..
    have ht : g=fun _=>0 := funext fun i=> if_neg (fun hx=>hv ⟨hx.1,hx.2.1⟩)
    rw [ht]; exact measurable_const
  · intro V U hv hl; unfold g Cash.smilesMill; have hu : H.statesPool V p↔ H.statesPool U p:=by unfold Cash.statesPool; rw [inter_comm, hl,inter_comm]
    simp_rw [hu]; split
    · exact prod_congr rfl fun i _=> congr_arg (fun t:ℝ => t^(p.2 i+1)/↑(p.2 i+1).factorial) (inheritance ((hg i.1).2.1) (subset_biUnion_of_mem H.bookFoot i.2) _ _ hv hl)
    rfl
  · intro t V; have hF : H.statesPool (Lattice.gauge t V) p↔H.statesPool V p:= by unfold Cash.statesPool; rw [gauge_flags]
    unfold g Cash.smilesMill; simp_rw [hF]; split
    · exact prod_congr rfl fun i _=> congr_arg (fun t:ℝ=> t^(p.2 i+1)/↑(p.2 i+1).factorial) ((hg i.val).2.2 t V)
    rfl
  intro hc; unfold g Cash.smilesMill at hc; split at hc
  next h=>
    obtain ⟨i,hi⟩:= H.regains p h.2.1 h.1
    exact ⟨Finset.Nonempty.mono (subset_biUnion_of_mem (fun i=> (roster (i:H.ThickP).val).flags) (mem_toLeft.mpr hi)) i.2.2,h.2.2,h.2.1⟩
  next => exact (hc rfl).elim

lemma facing (Y:Site c)(h:Y∈ M.crest.image S.ratio.parent) (p : H.Chainbook)(hx: Y ∉ H.library p): H.smilesMill V (F0 V θp) p= H.smilesPool χ0 V p:=by
  have he (i:Molecule S)(hU:H.unionP i⊆ H.library p): F0 V θp i= H.spawn χ0 V i:=by
    have hh: M.lotus T x χ0 o.K W o.a Q.table Q.halo V i=0:=by
      by_contra hc; apply hx; obtain ⟨x,hz,hh⟩:= mem_image.mp h; subst Y; apply hU; apply (withermore M H V hc).2.2.2.1; apply halo_subset; exact Finset.mem_image_of_mem _ (mem_union_left _ hz)
    unfold color; simp only [hh,mul_zero,add_zero]
  unfold Cash.smilesMill Cash.smilesPool; split
  next hx=>
    refine prod_congr rfl fun i _=> congr_arg (fun t:ℝ=> t^(p.2 i+1)/↑(p.2 i+1).factorial) ?_
    rcases i with ⟨i|i,hv⟩
    · exact he i.val (show H.bookFoot (.inl i) ⊆ _ from subset_biUnion_of_mem H.bookFoot hv)
    exact congr_arg (fun v:ℝ=> -(coefficient H.seam i.2*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> he (i.2 j).val ( Finset.Subset.trans (subset_biUnion_of_mem (H.smallAt ∘ i.2) (mem_univ j)) (subset_biUnion_of_mem H.bookFoot hv)))
  next=>rfl
variable (k : Plating (b₁:=b₁) M H N a t g c₁ u κ' e)(hZeta:|θp| * d0 ≤1)
include k
lemma hot_ovals : Summable (oval M H N):=by
  have he:= ticks M H N k 0; simp only [Nat.zero_le,↓reduceIte] at he; exact everyoneN (fun i=>H.bookFoot (.inr i)) (oval M H N) (oval_pos M H N) he (fun i _=> Refrain.chapter_ne H _) (add_nonneg k.live k.post.le)
omit k
lemma convulse (N: Captain H j q d v Y A b r B C' n χ0) (hhh:Herd H N.conduit A B n)(k : Plating (b₁:=b₁) M H N a t g c₁ u κ' e)(hZeta:|θp| * jewelDebt M Q L x ≤ 1)(O: Forest S.ratio):
    let g:=color M H χ0 V θp; let LV:= H.homesteadMill g
    HasSum (fun p=> overhead (prism T x χ0 o.K V O) R Q.table * LV * H.canopyMill V g p) (S.push R.beta R.eval V+θp*S.push R.beta M.cicada V)∧
      0<LV∧ Real.exp (logSum H.seam (H.entriesMill g))=LV:=by
  intro pF LV
  have hx:= (k.first)
  have hp : Ready H.smallAt (radiusB x) (fun i=> ‖H.entriesMill pF i‖) (a+e) t b₁ g:=
    ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,fun _=>norm_nonneg _,AbsoluteSums.Labels.raise_prices _ _ (fun _=> norm_nonneg _) hx.2.2.2.2.2 (fun i => (warm M H hhh V θp hZeta i).value)⟩
  have he:= H.threshold_logMill pF hp (add_nonneg k.live k.post.le)
  have hz: Summable (H.depositsMill pF) := Summable.of_norm_bounded (everyoneN H.largeAt _ (rides M H n) k.second (fun i _=>i.2.1) (add_nonneg k.live k.post.le)) (fun i=> (cold (n:=n) M H χ0 V θp hZeta i).value)
  exact ⟨H.convoyMill χ0 V pF O (sprouting M H χ0 V θp) (tint M H χ0 V θp O) hp hz (add_nonneg k.live k.post.le), (by unfold LV; rw [← he.2]; exact Real.exp_pos _), he.2⟩
end Charity
end YM.PhysicalNext.Repeat.Daisy
