import YM.FullVolume.Florid.Flock
import YM.FullVolume.Panel.Port
import YM.FullVolume.Mark.Booths
/-!
# All-air glints: real prices for mark extraction off interpolation.
These are NOT presumed to realize any Move, density, band at output.
In particular use of the current Bolt in the proof concerns purchase only.
The raw data formula doesn't select another Bolt on this line.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Glitz
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels Jams Cryst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) (H:Chord R N m n l v)
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Θ" => A.B.a.S
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "K" => A.B.a.params m
local notation "wT" => radiusB (A.B.a.clock.hatBeta m)
local notation "k" => Rain.lint R.target A m
local notation "e" => Trio.base k wT
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
variable (x: Chord.Flight A N m n)
local notation "d" => H.pitch x
local notation "hx" => x.property
local notation "W" => H.sight x
local notation "f'" => H.termF x
local notation "Tap0" => H.offerT x
variable (M:Lotus.Leaf x.val) (o:Site (A.B.a.S.side m n))(ho:o∈M.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "V" => veranda M W Chi.canonical W f'
local notation "κ₀" => jewelDebt M Y L y
local notation "D₀" => H.lens x
local notation "T₀" => Collection.shelves (H.listing x) (A.B.kin.path N m) B
set_option quotPrecheck false
local notation "T'" => Collection.branch (H.listing x) (A.B.kin.path N m) (A.B.a.params m|>.clip) B (H.source x) gV
local notation "M₁" => A.B.kin.path N m
local notation "g₂" => tempe (A:=A) (Z:=R.expense) (C:=R.target) (m:=m)
local notation "p" => (Marlin.tithe (2*e) g₂ B (Trio.coverTicket k))
local notation "P!" => (X.p.profile Jp)
variable {b v₁ b₁ t q t₁ t₂ A₁ b₂ w : ℝ}{n':ℕ} (T:Captain (H.sight x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ A₁ b₂ t₂ b₁ b n' Chi.canonical)
variable (hR: Arrives R.shape A.delay) (h:Herd (H.sight x) T.conduit A₁ b₁ n')
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
local notation "z₀" => (Real.exp (-(Y).mark L Cμ y)*(2*Daisy.pledgeQ L Y Cμ y b₁ (P!).order n'))
local notation "Zr"=> H.moment x
lemma snows : (Vapor (D₀) (Tap0) (raiser B) p) ∧ 0≤ p ∧ p ≤ betaF G y L ^ (-(1/8):ℝ):=by
  let F: ℝ→Rep G (A.B.a.S.side (m+1) n) := fun _=>x.val; let s:=Set.Icc (0:ℝ) 0
  have hz: (0:ℝ)∈s:= Set.left_mem_Icc.mpr le_rfl
  have he : ∀ t0∈s, Lives (Roof.spatial A).bake N (m+1) n (F t0)∧(F t0).beta∈band A.B.a (m+1):=fun _ _=>x.property
  have hv:Curve (A.B.a.budget (m+1)) F s:= by rw [← show _= A.B.a.budget (m+1) from x.property.1.point]; exact Rain.unchanged ..
  obtain ⟨U,-⟩:= Rain.verdict R.pledging H.paid hv he hz; let m0:=H.order (listIn (F 0))
  have hh := H.sight_layout U hz hv he; change H.crewD x=_ at hh
  have hu : H.offerT x=tuneT U he H.tone m0 0:= H.sight_graph U hz hv he; rw [Chord.lens,hh, hu]
  have ht (i:Site (A.B.a.S.side m n)):= Rain.earningsF R.pledging H.paid U hv he R.inn (R.settles _ _) H.tone m0 0 i
  have h' (i):=(ht i).1; have hk : 0≤ tempe (A:=A) (Z:=R.expense) (C:=R.target) (m:=m):=(norm_nonneg _).trans ((ht 0).2.2 1)
  let M':= Rain.lens U; let v:= Rain.beams U he H.tone m0 0; let a:=uptick U m0 0; let t:= Rain.nights U he H.tone m0 0
  have hw(i):= estateP U.doors e (2*e) a v t h' i
  have hω:=Marlin.failedP U.doors e (2*e) a v t (fun i=> (ht i).2.1)
  have hf : Vapor M' (Marlin.bison a v t) (raiser B) p:= by
    refine ⟨fun i=> (hw i).uses,fun i U hU=> by by_contra h; exact hω i U h hU,fun i=> (hw i).invariant,fun i=>(hw i).borel, ⟨_,Marlin.caps _ _ _ _ _ hk (fun i=> ?_),Marlin.softly a t _ (fun i=>(ht i).2.2) v⟩⟩
    unfold Trio.coverTicket; apply Nat.cast_le.mpr; apply le_trans (Trio.scaleMeters k wT (B).B_pos i _ le_rfl); rw [two_mul]
  refine ⟨hf, (by obtain ⟨_,hf,-⟩:=hf.funds;exact budget_nonneg (hf.2 0)),?_⟩
  unfold tithe; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact R.inn.terms.allot _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)|>.1
include hp h ho hm hR
omit hm in
lemma stemsY : Season ((D₀).pours Tap0) (raiser B) (V) o κ₀ z₀ ((raiser (B)).supportExponent+1):=by
  have he:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.1.1
  obtain ⟨hr,hq,hE,hcost,hP⟩:= verge M W T h (raiser B) W f' (D₀).reg (Tap0).regular rfl (raindance M W T he hp) ho rfl
  have hf : (Tap0).forced=V 0:=hr.symm
  have hi : ((raiser B).supportExponent+1) ≤ (Ze).earn:= by
    change (B).supportExponent+1+1 ≤ _; have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
  refine ⟨hf.symm,fun i hv=> ?_,hE,hcost,?_⟩
  · have h' := hq i hv; exact ⟨h'.sym,h'.symtest,h'.meas,h'.meas_test,h'.reads,h'.reads_test,h'.permit⟩
  obtain ⟨u,hu,hv,hZ⟩:= hP; refine ⟨u,hu, fun i=> ?_,hZ⟩
  change Ac.Hit (fun i=>(((D₀).pours Tap0).forced i).support) (raiser B).B u (Ze).earn z₀ at hv
  apply budget_mono (hv i)
  · intro i; split; exact mul_nonneg (hu _) (Real.exp_pos _).le; rfl
  intro i; split
  next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hi (by positivity))) (hu _)
  rfl
abbrev overV (t:ℝ):= solid (Marlin.hak (H.lens x)) (A.B.a.budget m) (spice (H.offerT x) (veranda M (H.sight x) Chi.canonical (H.sight x) (H.termF x) t))
lemma doorsY : Season ((T₀).pours T') B (overV H x M) o κ₀ (stems Cμ L G y) ((B).supportExponent+1):=by
  have hi:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.2.1
  obtain ⟨hz,hb,hV⟩:= snows H x
  have hf:= stemsY H x M o ho T hR h hp
  have hp' : z₀ ≤ Real.exp (-(Y).mark L Cμ y):= mul_le_of_le_one_right (Real.exp_pos _).le (by linarith only [hp.gains])
  have hb' : 0 ≤ z₀:=by obtain ⟨-,-,-,hQ,u,hu,hB,hK⟩:=hf; exact budget_nonneg (hB 0)
  obtain ⟨u,hξ⟩:= hi z₀ p hb' hb hV hp'
  obtain ⟨he,hh,hp''⟩:=harvest hf hz hξ (Marlin.hak D₀)
  exact ⟨he,fun t ht=> let hA:=hh t ht; ⟨hA.sym,hA.symtest,hA.meas,hA.meas_test,hA.reads,hA.reads_test,hA.permit⟩,hp''⟩
include g
local notation "f₂" => softNeed G B (K).clip (K).width (K).paths gV (Time.forecastE A.B.a m)
omit hp h ho hR
lemma plantsY : Vapor T₀ T' B f₂:=by
  let F: ℝ→Rep G (A.B.a.S.side (m+1) n) := fun _=>x.val
  let hc := Roof.coating H.earns.conducts H.paid (R:=F) (s:=Set.univ) (fun _ _=> x.property.2)
  exact cools g (Apse.gloss H x) (A.B.support.cap N m hm.le) hc.width hc.decent (Return.enough_room ..)
lemma sols : HasSlots (Zr).p (Zr).activities:=by
  have h:=Apse.savory g H x
  let F: ℝ→Rep G (A.B.a.S.side (m+1) n) := fun _=>x.val
  have hb := Roof.coating H.earns.conducts H.paid (R:=F) (s:=Set.univ) (fun _ _=> x.property.2)
  exact ((Apse.gloss H x).renew g (A.B.support.cap N _ H.paid.le) hb.decent hb.width gV (Return.enough_room _ _ _) (hb.fees 0 (Set.mem_univ 0))).spare_room (A.B.kin.path N m) (A.B.a.params m).clip 0 0
-- camp mismatch Cryst requires SAME c c'
include hp h ho hR
variable (F: Chord R N m n l l)
-- cast until. just require output as U
lemma footprints : Season (H.moment x).activities B (final.frigid T₀ T' (overV H x M) B) o κ₀ (straw Cμ L G y) (B).supportExponent := by
  have hf : (K)=P!:=params_eq A.B.valid m
  have he:=hR _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)|>.2.2
  have hh := UVNext.CouplingReset.within_alpha («B»:=A.B) hm
  have hz : Time.Same (K) (B):= ⟨rfl,rfl,rfl⟩
  set f0:=f₂ with hM
  have hZ:=plantsY g hm H x
  have hS:= he (B) rfl rfl (hf ▸ hz) _ hh
  have hp' : 0 ≤ f0:= by obtain ⟨f,hp,-⟩:= hZ.funds; exact budget_nonneg (hp.2 0)
  have hv:f0= softNeed G B (P!).clip (P!).width (P!).paths gV (Time.credit G P! * δE y):=by rw [hM, ← hf]; rfl
  obtain ⟨u,hU⟩:= hS (hv ▸ hp')
  change Payments.Rates _ _ _ (softNeed G B _ _ _ gV _) _ at hU; rw [← hv] at hU
  rw [Apse.writtenN H x 0]; exact final.slopes (doorsY hm H x M o ho T hR h hp) hZ hU
end YM.PhysicalNext.Repeat.Glitz
