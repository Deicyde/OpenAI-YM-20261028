import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Wall
/-!
# Real all-input (not just the reachable data) allocation.

Use a second type for testing LINEAR spaces to access pre-existing estimates
requiring Lives. This cannot be used for any continuing Move, since the
recipe between levels would be incorrect. Same on ALL the test cells.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {M : Metals G} {D : Rolls M.p} {U : Alloy M D} {bt : Baton G} {v w t : Return.Wages}
    {L : Targets M.p M.K} {p : ℕ→ℕ→JointLoad.Heir.Record} {V : Programs M.p} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {r : ℕ→ℕ→ℕ} {b : ℕ→ℕ→Booth} {E : Expenses L} {H : ℕ→ℕ→Cafe} {Q : ℕ→ℕ→Clockwork.Menu} {a : ℕ→ℝ} {Y : Register D E w a}
    {J : ℕ→ℕ→Folio.Aux} {c c₁ c₂ : ℝ} {E₀ : ℕ→ℕ→Next.Scheduling.Exchange} {η : ℕ→ℝ} {q : UVNext.CouplingReset.ResetPrices}
    (h : Touring (C:=V) (B:=H) U bt v t r b Q p J Y S c E₀ q η)

-- purely extensional input tests at ALL Alloys. Never generates PeriodFuture.
abbrev spatial (U : Alloy M D) : Directed G U.asks M.O M.K U.post :=
  { U.B with bake := {U.B.bake with retain:=fun _ _ _ _=>True}, bases:=U.B.bases }

lemma longs {N m n R} (h:Lives U.B.bake N m n R) : Lives (spatial U).bake N m n R:= ⟨h.path,h.point,h.clip,h.valid,trivial⟩
include h
lemma prepares {N m n} {I : RG.Rep G (U.B.a.S.side (m+1) n)} (hm:m<N) (hq : Lives (spatial U).bake N (m+1) n I) (ht : I.beta∈band U.B.a (m+1)) : ∃ H : Guide U.B Y N m n I, Price U.B Y N m n I H := Opera.feature (spatial U) Y hm h.full h.income hq ht
lemma coating {N m n : ℕ} {R : ℝ → Rep G (U.B.a.S.side (m+1) n)} {s : Set ℝ} (hm:m<N) (he : ∀ x∈s,(R x : RG.Rep G (U.B.a.S.side (m+1) n)).beta∈band U.B.a (m+1)) :
    let a:=U.B.a; Return.Prices U.B N m n q s (fun _=>forecastE a m) (fun x=>forecastK a m S (R x).beta) (fun _=>Time.fraction a m) (fun x=>quoteHard a m F (R x).beta) := by
  intro a; have ht := h.machine.coverage _ _ (step_paid U.B.a m); exact (Time.now U.B hm h.machine.shops ht.1 (params_eq U.B.valid m ▸ ht.2) E₀ h.machine.cubic (p:=n) he).1
local notation "X" => U.B
local notation "W" => U.delay
local notation "P" => M.p
variable (hh : Height.Rich Y c₁ U.delay) (hy : Height.Tenement Y U.delay) (hW : Pew v t V p r Y (wind Q) U.delay c₂)
    (hF : ∀ j i,StepStages j i → (M.p.profile i).supportExponent+3 ≤ (E j i).earn ∧ (M.p.profile i).supportExponent+3 ≤ t j i ∧ (L j i).halo+5 ≤ r j i)
    {N m n : ℕ} (hm : m<N) {I R : RG.Rep G (U.B.a.S.side (m+1) n)}
    (hl : Lives (spatial U).bake N (m+1) n R) (hb : R.beta∈band U.B.a (m+1)) (hc : Guide U.B Y N m n I) (hd : Guide U.B Y N m n R)
    (he : Opera.Price U.B Y N m n R hd) (ha : Alliance hc hd 1 0) (hx : ha.units=Equiv.refl _)
    (hf : I.path=R.path) (hf' : I.activities.reg=R.activities.reg) (hK : I.activities.forced=R.activities.forced)
include h hh hy hW hm hF hl hb he hx hf hf' hK

local notation "a'" => U.B.a

lemma seats :
    Collection.Local (Beam.marquee hc (U.B.a.budget m)) ((a').budget m) (Height.serve hc ha Chi.canonical (Beam.lit hc)) ((c₁+2*c₂)*Time.forecastE U.B.a m) (c*Time.forecastK U.B.a m S R.beta) := by
  let x:=U.B.a.clock.hatBeta m; let B:=U.B.a.budget m; let C:=U.B.a.clock.J m; let u:=U.B.a.clock.J (m+1); let K:=M.p.profile C; let e:=grow G (D.L u) x
  have hi: StepStages u C:= step_paid U.B.a m
  have hk := U.B.valid.pays m
  have hz:=hy u x hk C hi
  let T:= ships X N m n; obtain ⟨Y',d,v',t',A',b',r',B',q',i',z',⟨G',hg'⟩,hC,h₂⟩:= hz.2 _ _ _ T hd.laws.data.funds (protocol X hm h.full) _ hd
  have hR : U.B.a.params m=K:= params_eq U.B.valid m
  have hΨ := hh.large u C hi x hk
  obtain ⟨hH,hKz,hV',hZ⟩:=hΨ; obtain ⟨he',hv',hv⟩:= hZ B' i' z' hC G'.balance h₂
  have hp : B.power=K.power :=congr_arg RG.Stage.power hR
  have hj : B.order=K.order :=congr_arg RG.Stage.order hR
  obtain ⟨hz',ht,hr⟩:=hF u C hi
  have ht':preExponent B= K.supportExponent+3 := congr_arg (fun s:RG.Stage=>s.supportExponent+3) hR
  have hh' := hW _ _ hk _ hi (first_le U.B.valid m) T
  let desk := assigned h.hearing.plan m n X N R
  have he₀:= (Psalm.Stage.directed h.hearing (spatial U) hm hb hl (fun m' h'=> h.full _ _ _ (by simp at h'; omega))).1.enabled
  have hz₀ := he₀.make; obtain ⟨hp₀,hc'⟩:= he₀.pre; have hf₁ := (he₀.clocks R.beta hb).2
  have hh₀ : desk.profile=wind Q u C:= rfl
  rw [← hl.point] at hp₀ hc' hz₀ hf₁
  have hh : U.B.a.S.block m=D.L u:= PriceCompiler.block_eq U.B.valid m
  have he₁ : Houses hd (p u C) desk.broadCut desk.profile Chi.canonical desk.radius B (Solo.raise t u C) (heap G K c₂*δE x) (heap G K c₂*δE x):=
    hh₀.symm ▸ hh' hd.laws.data.funds R _ _ hd B rfl hp hz₀ hr (hh ▸ hp₀) (hp ▸ hc') (hh ▸ hf₁) _ le_rfl _ _ _ _ _ _ _ _ _ _ G' desk.broadCut desk.radius
  have hLx: Collection.Local (Beam.marquee hc B) B _ (turnFee B*(heap G K c₁*δE x+(heap G K c₂*δE x+heap G K c₂*δE x))) _ :=
    Beam.shines hc B _ ha hx hf hf' hK he G' rfl hj.le rfl (ht'.trans_le hz') hp.le (ht'.trans_le (ht.trans (le_add_of_nonneg_right (by norm_num)))) (fun i=> budget_loosen (completed G' hH hg' K.power he' hKz hz.1 hV' hv' i) hv) he₁
  obtain ⟨r,hF',hy⟩:= hLx.expensive
  have he : turnFee B*(heap G K c₁*δE x+(heap G K c₂*δE x+heap G K c₂*δE x))= (c₁+2*c₂)*Time.forecastE U.B.a m := by
    rw [heap,heap, ← show turnFee B=away K from (by unfold turnFee away; rw [hj,hp])]
    change _= (c₁+2*c₂)*(Time.credit G _ * δE x); rw [hR]; field_simp [(turnFee_pos B).ne']; ring
  rw [he] at hLx; exact {hLx with expensive:=⟨r,hF', fun p=> budget_loosen (hy p) (backing X Y h.income hb)⟩}
end YM.PhysicalNext.Repeat.Roof
