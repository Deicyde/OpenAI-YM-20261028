import YM.RemainderComparison.Solos.Bodies
/-!
# Loyalty to test address markings
 Needed only for uniform integrability near equality F.B.Flags. For all other uses
 preserve the real rendered leaves. `weight` is before probe restriction.
 Honors support, gauges and flags. Don't require a cost summable over tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
variable (M:ι→Portrait R α) (y:α)
-- place : all tags of leaf (empty if dormant)
variable (M:ι→Portrait R (Audited R₀)) (place :ι→ Finset θ)(Hpc: ∀ (U:Config G f) i, LinearP (place i) (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
-- closed-boundary continuation without differentiating through moving flags
local notation "f₂" => mapWord place
variable (y:Audited R₀)(X:Coat T F) (i:Drums (brand M y) S)
local notation "q₂"=> f₂ i.val.val
variable (N:Captain H j q d v u A b r B e n χ)
variable {E₁:Type}[NormedAddCommGroup E₁][NormedSpace ℝ E₁][FiniteDimensional ℝ E₁]
variable (U:E₁→ Config G c)(p:Molecule S)(a:E₁)(hx:X.x=x)(hk:X.width=o.K)(hF:X.χ=χ)(h:U a=X.V)(hp:Mode U a j v)
variable (hU:Healthy (Pressure.temp x) (H.unionP p) X.V)
local notation "St"=> edgesM S (H.unionP p) (X.B)
set_option quotPrecheck false
local notation "P₀"=> prism T x χ o.K
local notation "I₁"=> podium S G (H.unionP p) X.B
local notation "G↑" u=> (team (V' u) i)
-- Uniform z S.Setup Neighborhood.H Needed all α for recover outside-parameter junk
include H Hpc N h hp hx hk hF -- hU ? needed? no chutes .planted ensure boosts
omit Hpc
omit [∀ i,NormedSpace ℝ (R₀ i)] in
set_option maxHeartbeats 600000 in
lemma rollick (b':S.Choices) :
    let Z := (planted X p).taggedL b'; let K:=(F.order G).prod Z.dice
    ∀ᶠ t in 𝓝 a, ∀ z: Audited R₀,let G₀:=(team (brand M z) i); let f:= G₀.carat (edgesM S (H.unionP p) X.B) Z (U t) A Q.table p W o.a Q.halo
                                            ; Integrable f K ∧ G₀.cinema (vary Z (U t)) p W o.a Q.table Q.halo (podium S G (H.unionP p) X.B)=∫ x,f x ∂K:=by
    intro Z K
    have hQ:=H.laws.data
    have hm : Z.manifest:=planted_valid X p
    have ht:Z.x=x:=hx
    have hh:= N.oboe.flow F Z ht hF hk hm E₁ U a h hp
    have hH:Cash W Z.x μ L Q o C T R:= ht.symm ▸ H
    have hA:8*o.a*Pressure.fiery G Z.x S.patch.L≤ A/2:=by rw [ht,hQ.funds.length_eq]; exact N.oboe.mode
    have hz_b:=congr_arg radiusB ht
    let L' := team (tart H M y) (show Lyric.Drums (tart H M y) S from i)
    have he:= (L'.boosts Z p hH hk hm St hh N.oboe.conduit hA).2
    obtain ⟨s,hs⟩:= hh.sails
    filter_upwards [he,Silica.nearby Z N.oboe.conduit hh.lifts hs] with y' hy hX
    intro z G₀ f'
    have hΖ: ShellAccess S G Z.x W Z.width o.γ:=by rw [ht, show Z.width=o.K from hk]; exact H.laws.data.access
    have hF': Integrable f' K :=by
       let Z' p:=f' p
       have he:Measurable Z':= (team (V' z) i).docks Z (U y') St N.oboe.conduit hX measurable_fst measurable_snd hH.laws.intake hΖ Q.table_exists p
       apply hy.mono he.aestronglyMeasurable (ae_of_all _ (fun v=> Solos.pend H M y Z i z St p (U y') v))
    refine ⟨hF',?_⟩; unfold K; rw [integral_prod _ hF',← chargedU _ X.B]; refine (team (V' z) i).transition Z (U y') St N.oboe.conduit hX p (hQ.localP _ Z ht hk hm).sails.fullC Q.buys (H.unionP p) (show ground R T Q.halo Z.B p ⊆ H.unionP p from ?_) (ht.symm ▸ hQ.room) hH.laws.intake hΖ Q.table_exists rfl
    rw [show Z.B= _ from hz_b]; exact Subset.rfl

include Hpc hU
set_option maxHeartbeats 400000 in
lemma beyond (hv:(roster p).flags=∅) : ∀ᶠ z in 𝓝 a, PaperP q₂ (fun b=> (team (brand M b) i).picture (vary X (U z)) p W o.a Q.table Q.halo):=by
    have hB : X.B=radiusB x:=congr_arg radiusB hx
    filter_upwards [eventually_all.mpr (fun t=> rollick H χ M y X i N U p a hx hk hF h hp t), Team.gathers X p H N.oboe hx hk hF hv hU hp h] with z he hL
    simp_rw [hL]; unfold Team.grove; simp_rw [show (vary X (U z)).B=radiusB x from hB]; split_ifs
    · let f (s:S.Choices)(p':Audited R₀):=(team (brand M p') i).cinema ((preps (vary X (U z)) (roster p)).taggedL s) p W o.a Q.table Q.halo (podium S G (ground R T Q.halo (radiusB x) p) (radiusB x))
      intro hg; apply LinearP.pitch; refine LinearP.seats _ f fun s _=>?_
      let Z:=(planted X p).taggedL s
      have hh(P:Audited R₀): f s P=∫ q, (team (brand M P) i).carat St Z (U z) A Q.table p W o.a Q.halo q ∂((F.order G).prod Z.dice):=by
         refine Eq.trans ((team (brand M P) i).casin X p H hx hv hU s (U z) (U z) (fun _ _ _=> rfl)).symm ?_
         rw [← show X.B=_ from hB]; exact (he s P).2 -- choose occurrence radiusB!
      change LinearP _ (fun z=> f s z)
      simp_rw [hh]; exact LinearP.meal (fun v=> solar M place Hpc y Z i (U z) p St v hg) (fun v=>(he s v).1)
    exact fun h=> LinearP.nil _
omit a hU h hx hF hk hp
local notation "t'" => Pressure.temp x
-- express Mode on neighborhood in field coordinates, not just each direction independently.
variable {V:Config G c}(p':H.ThinP) (hu:Healthy (Pressure.temp x) (H.smallAt p') V)
include hu
omit H N Hpc hu [NormedSpace ℝ E₁] [NormedAddCommGroup E₁] [FiniteDimensional ℝ E₁] in
lemma kick (k:ℕ)(v:ℝ)(hp:0<v) (P:Config G c→ Prop)(V:Config G c) (h:∀ (U:Directions G c→ Config G c), U 0=V → Mode U 0 k v → ∀ᶠ u in 𝓝 0,P (U u)): ∀ᶠ z in 𝓝 V,P z:=by
    -- construction log chart & mode certificate. parallels Hem.charted (Contour)
    obtain ⟨u,hu,hQ⟩:= expCost G k 1
    let a:=1+k.factorial*u; have ha:0<a:=by unfold a; positivity
    let d:= v/(2*a); have hd:0<d:=by unfold d; positivity
    let L:= d • ContinuousLinearMap.id ℝ (Directions G c); have hL: ‖L‖≤1*d:=by unfold L; rw [norm_smul,one_mul,Real.norm_of_nonneg hd.le]; exact mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le
    have hh:= fromLogL L (x:=0) (linearB L (u:=1) (d:=d) (by simp) hL hd.le) 1 zero_lt_one hQ (by intro i; simp only [map_zero, Pi.zero_apply];simp) V
    have he : (1+(k.factorial:ℝ)*u)*((1+1)*d)=v := by change a*_ =_; unfold d; field_simp; ring
    rw [he] at hh
    let f Z:= increment V (L Z); have hg:= h f (show increment V (L 0)=_ from by rw [map_zero]; exact Work.G07.at_zero_increment V) hh
    let L' (t:Config G c) (e:Edge (Site c)):= G.plog (G.mat (t e*(V e)⁻¹)); obtain ⟨(hx:L' V=0), (ht:ContinuousAt L' V),hv⟩:= WardBin.exp_local V id V rfl (fun i=> (continuous_apply i).continuousAt)
    let M:= d⁻¹ • ContinuousLinearMap.id ℝ (Directions G c)
    have hm:Tendsto (M∘ L') (𝓝 V) (𝓝 0):= by
       have he:= M.continuous.continuousAt (x:= L' V); have hh:= he.comp ht; rw [ContinuousAt, show (⇑M ∘ L') V=0 from by rw [Function.comp_apply,hx,map_zero]] at hh; exact hh
    filter_upwards [hm.eventually hg,hv] with y hy hx
    have h₀(x:Directions G c): L (M x)= x:=by simp [L,M,smul_smul,hd.ne']
    change P (increment V (L (M (L' y)))) at hy; rw [h₀,show increment V (L' y)=y from hx] at hy; exact hy
lemma city : ∀ᶠ z in 𝓝 V, PaperP q₂ (fun k=>toe (brand M k) H χ p' i z):=by
    refine kick j v N.position _ V fun U hx hp=> ?_
    filter_upwards [eventually_all.mpr (fun r:Greenbelt.Reserve S=> beyond H χ M place Hpc y (prism T x χ o.K V (allot r)) i N U p'.val 0 rfl rfl rfl hx hp hu p'.prop.2)] with z hz
    intro h; apply LinearP.pitch; exact LinearP.seats _ (fun (a:Greenbelt.Reserve S) b=> (team (brand M b) i).picture (prism T x χ o.K (U z) (allot a)) p'.val W o.a Q.table Q.halo) (fun i _=> hz i h)
end YM.RemainderComparison.Solos
