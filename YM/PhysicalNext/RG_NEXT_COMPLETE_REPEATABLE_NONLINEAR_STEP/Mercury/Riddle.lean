import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Debonaire
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Radio
/-!
 # η power with reserved Mass transfer. small price oracle only Matins.d additional. Arc works both and MARK clocks.C.Struct.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak Greenbelt WardBin.Lies March
open Gas Ursell Trees Daisy Daisy.Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
    {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {W μ x C' : ℝ} {R : Rep G f}
    {p j n m k : ℕ} {L : Side} {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {d A t C w M N z β r η v b Y' q: ℝ}{C₀ : Libretto G n}
-- Macron.Profile D.
def PermitY (Q: ConnectedActivityE6.Target G P)(Bp: Libretto G n) (D : Record)(p:ℕ)(W:ℝ)(o:Target.Order G W)(κ:Chi)(μ x V:ℝ)(L:Side): Prop:= ∀ (c f : Side) (S:StepData c f) (T:Tube G S), Works P L x S T → ∀ (R:Rep G f)(e:ℝ)(_H:Cash W x μ L Q o e T R)(F:Forest S.ratio)(X:Coat T F)(i:ℕ),X.x=x→X.width=o.K→X.χ=Chi.canonical→X.manifest → ∀ B:BudgetPoint,B.B=radiusB x→ B.power=p→Plays Bp D B R.p P T x→∀ (Y : Support c)(I: Type)[Fintype I][DecidableEq I] (a: Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q : Chi)(b:ℝ)(u:Site c),u∈Y→coverNumber B.B Y≤B.B→Healthy B.threshold Y X.V→ Scrim X a→∀ (M:Lotus.Leaf R),M.turn=.logKey i→∀ (L':Config G f→ℝ), R.p.Regular (R.activities.reg i).support L'→ M.ingredient= masked R.p.threshold (R.activities.reg i).support L' →∀ (j:ℕ)(Z: Slab G c j), j≤n→(∀ i,B.dirBound u (Z i))→(∀ i, ‖Z i‖ ≤ canopyW G L p x)→
    Brush n (M.weight*V) 1 (fun y=> M.cinema (vary X (journey X.V j Z y)) {Opacity.key S i} W o.a Q.table Q.halo (podium S G Y X.B)-a.hymn T (gStep R.beta) q b X.k L' (Baffle.magic D R.p R.beta κ) 1 (journey X.V j Z y)) 0
lemma tuned (Q: ConnectedActivityE6.Target G P)(p:ℕ)(B:Libretto G n)(D:Record)(W μ : ℝ)(o:Target.Order G W)(κ: Chi)(L:Side)(hh:2≤n)(h:D.ε ≤ 1/4): ∃ f:ℝ→ℝ, Rate G L (-(1/2)) f ∧ ∀ᶠ x in atTop, PermitY Q B D p W o κ μ x (f x) L:=by
  by_cases he: ∃ H:Patch,H.Branches P.bind G∧ H.L=L∧H.J=P.j
  swap; · exact ⟨(fun _=>0),Rate.power.compare (Eventually.of_forall fun _=>by rw [abs_zero]; exact abs_nonneg _),Eventually.of_forall (fun x c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim)⟩
  obtain ⟨E,hE,hr,hX⟩:=he
  obtain ⟨f,hF,hf⟩:= trove G P L E hE n p B D hh W o Chi.canonical κ h
  refine ⟨(fun x=>2*|f x|),(Brim.absolut hF).mul_left 2,?_⟩
  filter_upwards [hf] with x hx; intro c f S T h R e H F X i hh hp hC hX B' hu hB ht Y I _ _ a q b u hy he hY hP M hM L' hL hL' j Z hj hZ hs
  exact hx _ _ _ T (h.patch hr (by assumption)) h R Q μ _ H F X i rfl hh hp hC hX B' hu hB ht Y I a q b u hy (hu ▸ he) hY hP M hM L' hL hL' j hj Z hZ hs

variable (H : Cash W x μ L Q o C T R) (f' : Lotus.Leaf R) (i : ℕ) (hx:f'.turn= .logKey i)
variable (D : Record)(κ q':Chi)(ε:ℝ)(hN: Captain H p C' d v t A b r M q m Chi.canonical) (hR:Herd H hN.conduit A M m)
variable (L' : Config G f→ℝ)(h':R.p.Regular (R.activities.reg i).support L')(hm:f'.ingredient=masked R.p.threshold (R.activities.reg i).support L')
    (hp:Plays C₀ D B R.p P T x)
    (hv: PermitY Q C₀ D B.power W o κ μ x z L)
    (hB:B.B=radiusB x)(hn:B.order≤p) (hq:Q.halo+5≤k)
    (hh: coverNumber B.B (plate H i).support ≤ B.B)

local notation "g!" => (fun V:Config G c=>groves H i D κ q' ε V L')
local notation "e!" => Charity.matin f' H (icon H i) Chi.canonical
local notation "Y₀" => Brim.plate H i

include hx h' hm hp hB hR hv hh hn
lemma signs (V:Config G c) (hV: Healthy B.threshold (plate H i).support V)
    (l: List (Directions G c))(hl:l.length ≤ B.order)(ha:∀ t∈l,B.dirBound (Y₀).site t)(ht:∀ t∈l,‖t‖ ≤ canopyW G L B.power x): ‖leftDerivs (e!) l V-leftDerivs (g!) l V‖ ≤ f'.weight*z:=by
  let f:= (e!); let g:= (g!); let U:= l.get
  apply silhouette H f' i hx D Chi.canonical κ q' ε hN V hp L' h' hV hR hn _ hl
  have hs:= hp.rehearsed.temp_eq
  have hS:=H.laws.data.funds
  refine swain H f' i D Chi.canonical κ q' ε V L' U (hs ▸ hV) hN ?_
  intro F y; let X:=foyer H i F Chi.canonical V y
  have hz : X.manifest:=planted_valid (prism ..) (head i)
  exact hv _ _ _ _ hS R _ H F X i rfl rfl rfl hz B hB rfl hp (plate H i).support _ (mapcase H i F) q' ε (plate H i).site (plate H i).anchor hh hV (grove H i y F hV hs) f' hx L' h' hm l.length U (hl.trans_eq hp.rehearsed.test) (fun i=> ha _ (List.get_mem l i)) (fun i=>ht _ (List.get_mem l i))

lemma around (hb:0≤ z) {w:ℝ}(hw:0≤w) (hy : ∀ V:Config G c, Healthy B.threshold (plate H i).support V → ∀ F g (l:List (Directions G c)),l.length≤ n → (∀ t∈l,B.dirBound (Y₀).site t)→ ‖leftDerivs (hore H i D κ q' ε L' F g) l V‖ ≤ w): B.supBounds (plate H i).site (plate H i).support e! (w+ f'.weight*z):=by
   refine ⟨add_nonneg hw (mul_nonneg f'.profit hb),fun V hV l hl hz=>?_⟩
   let f:= (e!); let Y:= (Y₀).support
   let Lk(s:Directions G c)(i:Bond c):= if i.1∈Y then s i else 0
   let l' := l.map Lk
   have hf := cornice H f' i hx D Chi.canonical hN hp hR hn
   rw [March.stays hf.sites l Lk (fun v hv j hj=> if_pos hj) V V (fun _ _ _=>rfl)]
   have he := H.laws.data.room; have hQ : B.threshold ≤ 2*fiery G x L := by rw [hp.rehearsed.temp_eq,← H.laws.data.funds.length_eq]; exact he.temperatures
   have hL(t)(hi:t∈l') : B.dirBound (Y₀).site t:=by
      obtain ⟨i,hh,rfl⟩:=List.mem_map.mp hi; intro b; unfold Lk; split; · exact hz _ hh b
      rw [norm_zero]; positivity [B.threshold_pos]
   have hu(t)(hi:t∈l') : ‖t‖ ≤ canopyW G L B.power x:=by
      refine pacing _ Y ?_ B (Y₀).anchor rfl (hL t hi) x L (hB ▸ hh) hQ
      obtain ⟨i,hd,hk⟩:=List.mem_map.mp hi; intro k hk'; rw [← hk]; exact if_neg hk'
   have hJ:l'.length ≤ B.order:=by unfold l'; rw [List.length_map]; exact hl
   have hD:=signs H f' i hx D κ q' ε hN hR _ h' hm hp hv hB hn hh V hV l' hJ hL hu
   let Z:=leftDerivs f l' V; let s:=leftDerivs g! l' V
   have ht : ‖s‖ ≤w:= strums H i D κ q' ε V hp _ h' hV _ (hy _ hV) _ (hJ.trans_eq hp.rehearsed.test) hL
   apply le_trans (show ‖Z‖ ≤ ‖Z-s‖+‖s‖ from by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub Z s 0); exact le_trans (add_le_add hD ht) (le_of_eq (add_comm ..))
end YM.PhysicalNext.Repeat.Mercury
