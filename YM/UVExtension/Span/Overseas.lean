import YM.UVExtension.Span.Opal
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} {M:κ→ Hat G F}
-- states use explicit
variable (he:∀ᶠ i in qq,Mode (Y i) (τ i) k u)(hK:∀ᶠ i in qq,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (qV:StableR v R)
variable (Δ:κ→Directions G f) -- actual held displacement at test. no norm when prices all Compass later
open Silica Flux WithLp MeasureTheory
open Polar Silica Eider
-- arrows.
variable (hx : ∃ r:ℝ,∀ᶠ i in qq, ‖Δ i‖≤ r)
include h p he hK hx
variable (Y':κ→ Config G f)
open Mask
lemma cliffA (i:Bond f): Walt qq τ k (fun n b y=> (vary (Abide s χ U.K T M t n b) (Y n y)).gentry Q.table U.a (mobil A s U.K χ T t Δ M Y n b y) i):=by
   rcases eq_or_ne qq ⊥ with hy|hy
   · exact ⟨by simp [hy],fun i hi=> ⟨⟨0,by simp [hy]⟩,by rw [hy]; exact tendsto_bot⟩⟩
   haveI : NeBot qq:= ⟨hy⟩; obtain ⟨n,hp⟩:=hK.exists; let X:= (M n).order (T (t n false)) s χ U.K; have hp:= (H (t n false)).laws.data
   have hZ := Glass.elevator (j:=k) (a:=U.a) (X:=X) Q.table_exists (mul_pos U.large hp.room.fiery) (show 4*U.a*X.t<Q.table.radius by unfold Coat.t; rw [hp.funds.length_eq]; exact hp.covers)
   exact ((p.windsT h he hK Δ hx).leaf (ContinuousLinearMap.proj i)).plant hZ
section T
omit p h hK hx [FiniteDimensional ℝ E]
attribute [local instance] Gauge.frobInner
lemma ticksB (Z: κ→ Stores S)(a:ℝ)(T:κ→ S.Choices)(i:Bond c): Walt qq τ k (fun n (_:Bool) y=> Mask.noise (Z n) χ i a w (Y' n) (T n) (Y n y)) :=by
   let W n:= S.prediction (Y' n) (T n) i; let L(v:G.Mat):= χ.read ((‖v-1‖/G.colorScale/(w*a))^2)
   have f:ContDiff ℝ (↑k) L:=by
      unfold L; simp_rw [div_pow]; exact (χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp
        ((((contDiff_norm_sq ℝ).comp (f:=fun x:G.Mat=>x-1) (contDiff_id.sub contDiff_const)).div_const _).div_const _)
   have he: Walt qq τ k (fun n (_:Bool) y=> L (G.mat (Y n y i * (W n)⁻¹))):= by
      apply Walt.plant (Z:=L) _ f; apply Walt.twin (royalty G) u; filter_upwards [he] with j hj; refine ⟨?_,rfl⟩; simpa only [one_mul] using! offsetB (hj.atLink i) 1 ((W j)⁻¹) -- parse
   apply (Walt.choose (fun n=> i∈(Z n).aisles) (((Walt.ready 1).minus he).excuse _) (he.excuse _)).same; filter_upwards with n b; filter_upwards with y; unfold noise; dsimp only; split <;> rfl
lemma tickF (Z: κ→ Stores S)(a:ℝ)(i:Cell f): Walt qq τ k (fun n (_:Bool) (_:E)=> Mask.fine (Z n) χ i a (Y' n)) :=by
   exact Walt.stamp ⟨⟨1,Eventually.of_forall (fun n _=> (abs_le.mpr ⟨(by have h:=fine_range (Z n) χ i a (Y' n)|>.1; linarith), (fine_range ..).2⟩: |fine (Z n) χ i a (Y' n)|≤ 1))⟩,(by simp [tendsto_const_nhds])⟩
end T
include qV
lemma moneyA : Walt qq τ k (fun i b (_:E)=> Real.log (Coat.measure_g Q.table (R (t i b)).beta)):=by
    rcases eq_or_ne qq ⊥ with hy|hy; · exact ⟨by simp [hy],fun i hi=> ⟨⟨0,by simp [hy]⟩,by rw [hy]; exact tendsto_bot⟩⟩
    haveI : NeBot qq:= ⟨hy⟩; obtain ⟨n,hm⟩:=hK.exists; have ht:=H (t n true)|>.laws.intake.height; have hp :0< betaF G s S.patch.L / 2:= half_pos (zero_lt_one.trans ht)
    let u x:= Real.log (measure_g Q.table x); apply Walt.stamp; let K : Set ℝ:= Icc (betaF G s S.patch.L/2) (2*betaF G s S.patch.L)
    apply Together.compact (T:=u) (K:=K) isCompact_Icc (qV.pricesBet h) (Eventually.of_forall fun i b=> (H (t i b)).laws.intake.window)
    intro i h; have hx:= hp.trans_le h.1
    refine ContinuousAt.continuousWithinAt (((show ContinuousAt (fun x=> measure_g Q.table x) i from continuousAt_const.mul ((((continuousAt_const.mul (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr hx|>.ne'))).pow _)))).log ?_))
    unfold measure_g; have he:= Q.table_exists.scale; unfold gStep; positivity
lemma speckle (S':Signed)(i:Spot c f)(b:Bool): Walt qq τ k (fun n v y=> rootface (vary (Abide s χ U.K T M t n v) (Y n y)) (mobil A s U.K χ T t Δ M Y n v y) (Y' n) b S' i):= by
    have hh :=p.views.lofty (V:=fun i z=> pull S' 0 (Y i z)) h (he.mono fun i hi=> Blaze.turn hi S') (fun i=> choice S' (M i).tag) (fun n=> pull S' 0 (Y' n)) s i b
    exact hh.minus (p.costsW h he hK S' i (p.windsT h he hK Δ hx))
lemma impression (P: Stores S): Walt qq τ k (fun i b v=> plumeLog (vary (Abide s χ U.K T M t i b) (Y i v)) U.a (R (t i b)) Q.table (mobil A s U.K χ T t Δ M Y i b v) (Y' i) P):=by
   let X i b v:= vary (Abide s χ U.K T M t i b) (Y i v)
   let u' i b y:= mobil A s U.K χ T t Δ M Y i b y; let v:= Q.table
   have hf i b y: (X i b y).pens P= (visit P (10*radiusB s)).filter (fun i=> i∉ F.trunks):=rfl
   let z:κ→ Finset (Bond f):= fun i=> (X i true (τ i)).plaza (P.dome (304*radiusB s)); have hz i b y:(X i b y).plaza (P.dome (304*radiusB s))= z i:=rfl
   have hh: Walt qq τ k (fun i b y=> chalky (X i b y) (u' i b y) (Y' i) P):=(Walt.ready _).pay (Walt.schedule _ _ (fun j _=> Walt.schedule (posted (turnStore j P) (200*radiusB s)) _ (fun k _=> speckle p h he hK qV Δ hx Y' j k false))) -- multiply or smul
   have hv: Walt qq τ k (fun i b y=> crispy (X i b y) P):=(Walt.ready _).pay (Walt.schedule _ _ (fun n _=> Walt.schedule (posted (turnStore n P) (200*radiusB s)) _ (fun k _=> costsW p h he hK n k (p.pulses h he hK))))
   have ht: Walt qq τ k (fun n b y=> ∑ j∈ (X n b y).plaza (P.dome (304*radiusB s)), (X n b y).gentry v U.a (u' n b y) j):=by simp_rw [hz]; exact Walt.cut z _ (fun i=> (Walt.schedule i _ (fun j _=> p.cliffA h he hK Δ hx j)).excuse _)
   unfold plumeLog; refine ((((Walt.stamp ((qV.pricesBet h).continuous continuous_neg)).times (hh.sums hv)).sums ?_).sums ht).minus ?_
   · exact Walt.schedule (visit P (200*radiusB s)) _ (fun i _=> logPins p h he hK i)
   have ht i b y: (vary (Abide s χ U.K T M t i b) (Y i y)).pens P=(visit P (10*radiusB s)).filter (fun i=> i∉ F.trunks):=hf ..
   simp_rw [ht]; exact (Walt.ready _).times (moneyA p h he hK qV Δ hx)
lemma nozzle (Y' : κ→ Config G f)(J:κ→ Finset ℕ)(P:Stores S): Walt qq τ k (fun i b y=> stock (vary (Abide s χ U.K T M t i b) (Y i y)) U.a (R (t i b)) w Q.table (mobil A s U.K χ T t Δ M Y i b y) (Y' i) (J i) P) :=by
   let X i b y:= vary (Abide s χ U.K T M t i b) (Y i y)
   let a:=300*radiusB s; let B i':=P.place⊆(M i').seeds.place ∧ P.flags=∅; let hW i n:= Contract.order (R (t i n)) (J i) (vias S P a) (Y' i)
   have hc: Walt qq τ k (fun i b _=> hW i b):= by
     have hh i b :hW i b=hW i false:=by unfold hW; rw [qV.toKept.chores ..]
     have hp i:|hW i false|≤1:= by unfold hW; rw [abs_of_nonneg (Contract.valid_pay ..|>.1)]; exact (Contract.valid_pay ..).2
     exact Walt.stamp ⟨⟨_, Eventually.of_forall fun i b=> (by rw [hh]; exact hp _: ‖hW i b‖≤1)⟩,(by simp_rw [show ∀ i,hW i true=hW i false from fun i=> hh ..]; simp [tendsto_const_nhds])⟩
   have hg:Walt qq τ k (fun n (_:Bool) (_:E)=> tickets P a (Y' n) (M n).tag):=by
        refine Walt.stamp ⟨⟨Real.exp (tollFee S.patch a * P.shares),Eventually.of_forall fun n b=>?_⟩,?_⟩
        · dsimp only; rw [Real.norm_of_nonneg (ticket_nonneg ..)]; exact tickets_le ..
        simp [tendsto_const_nhds]
   have hp: Walt qq τ k (fun n (_:Bool) y=> profiles P χ a s w (Y' n) (M n).tag (Y n y)):= (caraffa _ _ (fun j _=> tickF he Y' _ _ j)).times (caraffa _ _ (fun j _=> ticksB he Y' _ _ _ j))
   let P' i:=(X i true (τ i)).plaza (P.dome (304*radiusB s))
   apply (Walt.choose B ((((((impression p h he hK qV Δ hx Y' P).exponential.times hc).times hg).times hp).times (parka p h he hK Δ hx U.a P')).excuse _) (Walt.ready 0)).same; filter_upwards with n b; filter_upwards with y; unfold Polar.stock; dsimp only; by_cases he:B n
   · rw [if_pos (show P.place⊆ (vary (Abide s χ U.K T M t n b) (Y n y)).seeds.place ∧ P.flags=∅ from he), if_pos he]; rfl
   rw [if_neg (show ¬(P.place⊆ (vary (Abide s χ U.K T M t n b) (Y n y)).seeds.place ∧ P.flags=∅) from he), if_neg he]
end Score
end YM.UVExtension.Span
