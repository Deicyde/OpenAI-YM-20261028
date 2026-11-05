import YM.TraceExtension.Shelves.Route
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
local notation "Fᵣ"=> C.labels.level 4
local notation "Zᵣ"=> C.labels.level 5
variable {X:Axis→ Logs C 5}(hp:∀ i,TravelsC (𝓛:Filter (ℕ×ℕ)) (exhibit t i) (Readout t i) (X i).v (X i).x)
open StressFlux Next.UVStress Margin
variable (Hδ:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u D)(hr:∀ᶠ i in atTop,2 ≤ r i)(hA:auraQ C.path.levels TileNo)
variable {L:PaceBook C}(hL:Rod t none (𝓛:Filter (ℕ×ℕ)) L)
variable {S:Table C.book}{J:Scaling S}{H:(Cells.standard C).Hierarchy}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F H J 𝓛 V Y)
variable (H':S.Hierarchy)(HF:F.PointLimits C S) (hq': StarPath F H J H' 𝓛)
variable {S₁:DiffPlan S}{P₁:DiffPlan (Cells.standard C)} (hJ:S₁.Derivatives S)(hP:P₁.Derivatives (Cells.standard C)) (ho:P₁.Orientation H.spin)
variable {s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne H.spin)} (hY:Spun Z J V H s)
open Asymptotics
local notation "F!"=> Cells.standard C
local notation "P!"=> Stern V
lemma scoutR{E F:Type*}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F](t:ℕ→ E→L[ℝ] F)(f: E→L[ℝ] F)(v:ℕ→ E)(x:E)(h:Tendsto t atTop (𝓝 f))(hp:Tendsto v atTop (𝓝 x)):Tendsto (fun i=>t i (v i)) atTop (𝓝 (f x)):= ((show Continuous (fun z : (E→L[ℝ] F) × E=> z.1 z.2) from continuous_fst.clm_apply continuous_snd)).continuousAt.tendsto.comp (h.prodMk_nhds hp)
-- V pace projection. No assumed Collapsing.
include P hb h hz hq
lemma Vigor {q:ℕ→ S.Field 4}(hp:Fast C.S q)(hv:∀ j,centering S 4 (q j)=q j)(p:ℕ)(he:Tendsto (Moment4 Z J V) atTop (𝓝 (Hill4 C))) (HE:S.Hierarchy): Tendsto (fun i=> (H! (P! i))^p • Hero J V Z 4 i (q (P! i))) atTop (𝓝 0):=by
    let T:=(S.representative 4).restrictScalars ℝ; let r(k):= T (q k); have hr:Fast C.S r:= fast_bill hp T; have hℓ: Tendsto (Stern V) atTop atTop := (Sstar A).comp hq.growth; let y(k):= (H! k)^p
    let f(i):= y i • swale Z 4 i (r i); have hu : Tendsto (f ∘ (P!)) atTop (𝓝 0):= (swiftC (cine P h hb hz hr p)).comp hℓ
    have ht:= Dash.arcing he hu; rw [map_zero] at ht; apply ht.congr'; filter_upwards [hℓ.eventually_ge_atTop (C.ref 4)] with i hi
    let k:= (P! i); let u:= Moment4 Z J V i; change u (y k • (swale _ _ _ _))= y k • _; rw[show ∀ v:C.label 4,u (y k • v)=y k • u v from fun _=> u.toLinearMap.restrictScalars ℝ |>.map_smul (y k) _,show u _=_ from (heroicB P hb hz HE i (r k) hi).symm, show S.project 4 (r k)=q k from S.rep ..,hv]
-- use equivariant real right section on physical frame, then enroll it in actual scaled read maps
omit hz P hb h hq
set_option maxRecDepth 4096
set_option maxHeartbeats 700000 in
def Larch (c:S.RealSpin) (v:TableOne c): Bowl Zᵣ:=
    let x(i):=equivariantSection c (v.val i); (plate Zᵣ).symm (⟨x, fun i=>by rw [show x i=_ from rfl, ← section_color (v.val i) c,show conjQ c _=_ from v.property.1 i],fun b i=> (section_turn b (v.val i) c).trans (by rw [v.property.2,map_smul])⟩: RawOne G)
lemma larch (g:TableOne H'.spin)(i): S.project 5 ((Larch H'.spin g).val i)=g.val i:=by
    change fromPol S (equivariantSection H'.spin (g.val i))=_; exact section_right (g.val i) H'.spin
include hz P hb h hq hY ht
-- H basis V stay.BASE
lemma FrameW (i:ℕ)(hi:C.ref 5 ≤ i)(v:Bowl Zᵣ): (fun d=> swale Z 5 i (v.val d))∈ Bowl Zᵣ:=by
    -- vector map. swale core equiv.S.
    let U:=(swale Z 5 i).restrictScalars ℝ
    exact (vectorMap (K:=reflA Zᵣ) (R:=reflB Zᵣ) (D:=reflA Zᵣ) (T:=reflB Zᵣ) U (fun s x=> stomp P ht hb hz i hi (s,false) x) (fun x=>by
       change swale Z 5 i (star x)=star (swale Z 5 i x); let s:Motion:=(1,true); have he(v): Prism Zᵣ s v=star v:=by unfold Prism Motion.patch; simp[s]; rw [show (Signed.ortho 1)=1 from map_one Signed.inclusionO,Frame.act_one]
       exact he (swale Z 5 i x) ▸ he x ▸ stomp P ht hb hz i hi s x) v).property
include H'
lemma stem_eq(i:ℕ)(hi:C.ref 5 ≤ (P! i))(x:C.label 5)(hx: night Zᵣ x): Hero J V Z 5 i (S.project 5 x)=(J.U i 5).symm (Vault S Z 5 (P! i) (crown Z J (Stern V) 5 i) (swale Z 5 (P! i) x)):= by
    rw [fisc hz P hb ht hi x hx]; let U:=(J.U i 5).symm; exact (U.toLinearMap.restrictScalars ℝ|>.map_smul (crown Z J (Stern V) 5 i) _).symm
lemma ride_vn (b:ℕ → TableOne H'.spin):∃ e:ℕ → Bowl Zᵣ, ∀ k:ℕ,C.ref 5 ≤ k→∀ i,(e k).val i=swale Z 5 k ((Larch H'.spin (b k)).val i):=by
    let Fx (k):=fun d=>swale Z 5 k ((Larch H'.spin (b k)).val d); let e(k):= if hi:Fx k∈ Bowl Zᵣ then (⟨Fx k,hi⟩: Bowl Zᵣ) else 0
    refine ⟨e,fun k hk i=>?_⟩; unfold e; rw[dif_pos (FrameW P h ht hb hz hq hY k hk _)]
lemma Pect(b:ℕ→ TableOne H'.spin)(hb':∀ i:Axis,Fast C.S (fun k=> (b k).val i))(p:ℕ)(e:ℕ→ Bowl Zᵣ)(he:∀ k:ℕ,C.ref 5≤ k→∀ i, (e k).val i=swale Z 5 k ((Larch H'.spin (b k)).val i)) : Tendsto (fun k=> (H! k)^p • e k) atTop (𝓝 0):=by
    let x k:= (H! k)^p
    apply tendsto_subtype_rng.mpr; refine tendsto_pi_nhds.mpr fun i=> ?_
    let q:S.Field 5→ₗ[ℝ] C.label 5:= ((C.labels.level 5).coords.toLinearMap.restrictScalars ℝ).comp (equivariantSection H'.spin)
    have hf:= fast_bill (hb' i) q
    let Q k:= Larch H'.spin (b k); let f k:=(b k).val i
    have hv(k:ℕ): (Q k).val i=q (f k):=rfl
    refine (swiftC (cine P h hb hz hf p)).congr' ?_; filter_upwards[eventually_ge_atTop (C.ref 5)] with k hk; change x k • swale Z 5 k (q (f k))= x k • (e k).val i; exact congr_arg _ (hv k ▸ (he k hk i).symm)
lemma choirB (hs:Prosper V h H s)(y:ℕ→ Bowl Zᵣ)(ht:Tendsto y atTop (𝓝 0)): Tendsto (fun i=>s i (y i)) atTop (𝓝 0):=by
    have he:= scoutR (E:=Bowl Zᵣ) (F:=TableOne H.spin) s (Vbase H.spin).toContinuousLinearMap y 0 hs.alpha ht
    rw[map_zero] at he; exact he
lemma shell_cash {i:ℕ}(x:ℝ)(v:TableOne H'.spin)(w:Bowl Zᵣ)(a:Axis)(hp:C.ref 5 ≤ (P! i)) (hx:(s i w).val a=(J.U i 5).symm (Vault S Z 5 (P! i) (crown Z J (P!) 5 i) (w.val a))) (h:(w.val a)=swale Z 5 (P! i) ((Larch H'.spin v).val a)): (s i (x • w)).val a=x • Hero J V Z 5 i (v.val a):=by
    have hv:(s i w).val a= Hero J V Z 5 i (v.val a):=by
       rw [hx,h]; let W₀:=Larch H'.spin v; let f:= (P! i); let c:= W₀.val a
       rw [show (J.U i 5).symm (Vault S Z 5 (P! i) (crown Z J (P!) 5 i) (swale Z 5 (P! i) ((Larch H'.spin v).val a)))=Hero J V Z 5 i (S.project 5 c) from (stem_eq P ‹_› ht hb hz hq H' hY i hp c (frames_night Zᵣ W₀ a)).symm]; exact congr_arg _ (show S.project 5 c=v.val a from larch H' v a)
    rw [map_smul]; change x • (s i w|>.val a)=_; rw[hv]
lemma syl(b:ℕ→ TableOne H'.spin)(hb':∀ i:Axis,Fast C.S (fun k=> (b k).val i))(p:ℕ)(hs:Prosper V h H s) (c:Axis): Tendsto (fun i=> (H! (P! i))^p • Hero J V Z 5 i ((b (P! i)).val c)) atTop (𝓝 0):=by
    have hC:Tendsto (Stern V) atTop atTop:=(Sstar A).comp hq.growth
    obtain ⟨e,he⟩:= ride_vn P h ht hb hz hq H' hY b
    let Q:= Stern V;let y(i):=(H! (Q i))^p • e (Q i);have he1:= choirB P h ht hb hz hq H' hY hs y ((Pect P h ht hb hz hq H' hY b hb' p e he).comp hC)
    refine (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp he1) c).congr' ?_; filter_upwards[hY.starts,hC.eventually_ge_atTop (C.ref 5)] with i hi hv
    exact shell_cash P h ht hb hz hq H' hY ((H! (Q i))^p) (b _) (e _) c hv (hi (e _) c) (he _ hv c)
end YM.Trace.Shelves
