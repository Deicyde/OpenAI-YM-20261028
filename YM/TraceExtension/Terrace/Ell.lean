import YM.TraceExtension.Terrace.Cor
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes Terrace ProofPorts.GridRealModelsEstimates20261012
open PhysicalNext.Repeat.Legato.Bandage Cells Push.GridApprox YM.MergeProof.Menu
open YM.MergeProof YM.MergeProof.Accent Source Glade Shunt
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}
-- lifted determinant books.Anchor reserves.Size geometry
abbrev canvasR(x:ℝ):ℕ:= Cleft x (wheelQ x)
def Sliver(x:ℝ):= max (canvasR x+ 8) (townD x+1)
lemma slit : ConstMass 0 (fun x:ℝ=> (Sliver x:ℝ)):=by
    let g(x):=(townD x:ℝ); have hg:ConstMass 0 g:=by unfold g townD; push_cast; exact (coasts TileNo).times _ zero_le_two
    let P:=hg.gather (mass zero_le_one); refine ( (campC 60|>.gather (mass (show 0≤ (8:ℝ) by norm_num))) |>.gather P|>.mono ?_); apply Eventually.of_forall; intro x; refine ⟨Nat.cast_nonneg _,?_⟩; apply le_trans (Nat.cast_le.mpr (show Sliver x≤canvasR x +8+(townD x+1) from max_le (by omega) (by omega))); unfold g; push_cast; rfl
lemma allowanceE :∀ᶠ x:ℝ in atTop,(((canvasR x+canvasR x+1:ℕ)^4:ℕ):ℝ) ≤ x^4 ∧ (Shunt.grantS x+(2*x)*wideM x)+x^2 ≤ x^4:=by
    have ht:=campC 60;filter_upwards [(ferry (((ht.gather ht).gather (mass zero_le_one)).crop 4)) 4 (by norm_num), ((quid_fee.spot (b:=2) (by norm_num) |>.plus ((( (board (show (0:ℝ)≤2 from zero_le_two)).prod (sands 1)).prod (ferry (waveM (1/50)))).spot (by norm_num)) ).plus (sands 2)) 4 (by norm_num)] with x hv ht
    constructor
    · push_cast; exact hv.2.trans_eq (Real.rpow_ofNat ..)
    simpa only[Real.rpow_one,Real.rpow_two,Real.rpow_ofNat] using! ht.2
variable {n:Side}{x v t w:ℝ}{F:Labels.Frame G 5}
lemma containA (k:ℕ) : (tower k (n:=n): Set (Site n)) ⊆ Push.GridApprox.window 0 k :=by
    intro i hi; have he: pdist i ≤ k:=by simpa [tower,halo_spec,separation] using! hi
    exact ⟨lift i,FreeResolvent.Lifted.lift_box i k he, by simp⟩
lemma cleave{T:SectionData F}{H:Hol G} (R:Rep G n){f:Film G n}{Z:Coefficient F n}(hp: Proxy T H R (tower (canvasR x)) Z f v t w) : Interior (Push.GridApprox.window 0 (Sliver x)) (Z.exponentialEntry 0 T R):=by
    have hh : Interior (RG.inspected (tower (canvasR x) (n:=n)): Set (Site n)) (Z.exponentialEntry 0 T R):= ⟨hp.symm,hp.pay, UsesFinal.allReads _ _ _ hp.locale, w,hp.all⟩
    have ht : inspected (tower (canvasR x) (n:=n))⊆tower (canvasR x+8):=by
        intro i hi; obtain ⟨v,hv,hQ⟩:=halo_spec.mp (Next.Rank.Thirst.inspect _ hi)
        obtain ⟨x,hx,h⟩:=halo_spec.mp hv; exact halo_spec.mpr ⟨x,hx,(separation_triangle x v i).trans (Nat.add_le_add h hQ)⟩
    exact hh.enlarges ((coe_subset.mpr ht).trans ((containA _).trans (win_inc _ _ _ (le_max_left ..))))
lemma lumen{q:Peat G n}{x v t:ℝ}{R:Rep G n}(hp:ClimateJ R q x v t): Interior (Push.GridApprox.window 0 (Sliver x)) (filmR q):=by
    have ht:= hp.puff.regular; have hg : Interior ((tempQ x (n:=n)): Set (Site n)) (filmR q):=⟨ (Real_regular ht).symmetry, (Real_regular ht).borel, (Real_regular ht).sites,t,fun U=>(Complex.norm_real _).trans_le (hp.price U)⟩
    apply hg.enlarges; exact (containA _).trans (win_inc _ _ _ (le_trans (b:=canvasR x+8) (by unfold canvasR Cleft;omega) (le_max_left ..)))
-- starred ledger. Beam requirement.Day of use.
variable {C:Family G}
set_option quotPrecheck false
local notation "A!"=>C.path.levels
local notation "T!"=> C.path
local notation "H!"=> (A!).clock.hatBeta
local notation "P!"=> C.localSection 5
local notation "V!"=> C.labels.level 5
variable (H:C.Makes)(h:G.Simple)(θ:Terrace.PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {r:ℕ→ℕ}{u:ℕ→ℝ}{W:∀ N p k:ℕ,k<N→GaugeDoor (C.path.rep N p (k+1)) (C.path.rep N p k)}
variable (hp:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) u W)(hr:∀ᶠ i in atTop,2 ≤ r i) (hT: auraQ C.path.levels TileNo)
local notation "G!"=> C.params
-- stash actual surgery choices.assumptions paid later.
structure Hearth (X:Set ℕ) : Type where
  m: ℝ
abbrev DawnU(m:ℕ){n:Side}(R:Rep G n)(x:ℝ)(J:Dart G n)(A:Finset GreenA)(U V:Finset ℕ):Prop:= Merch R x J A U m∧ Drift _ (ochre R x A U) ∧ ∀ b:Axis,let K:= shelves n A U V; let Y:=YCore x J b; let q:=wheelQ x; Depot R x K q m Y (ochre R x A U) (swole x) ∧ ∀ u:Config G n, |hornA R J x m q b u- callX R (cabinet R q K) Y (peace x) m (Bay n x) u| ≤ peace x*Real.exp (-(prism x:ℝ))
lemma dawn {m i:ℕ} {U c:ℝ}{J:Dart G n}{S:Stage}{R:Rep G n} (hp:Wholesome R x J i m (wheelQ x) S U v c)(hx:1≤ x):∀ᶠ A:Finset GreenA in atTop,∀ᶠ V:Finset ℕ in atTop,∀ᶠ W:Finset ℕ in atTop,DawnU m R x J A V W:= hp.crops _ (mul_pos ((pet x hx S).2.1) (Real.exp_pos _))
-- require hp.Scrim seam. cost compare on *actual stencil*.
variable {W':Bid.Worth} {ψ φ δ u':ℕ→ℝ} {ζ:ℕ→ℕ→ℝ}
variable (hν:Scrim C W' u' ψ φ δ ζ r W)
include H h θ K hp hr hT hν
set_option maxHeartbeats 600000 in
lemma crestship (m:ℕ): ∀ᶠ i in atTop,∀ p N,let k:=Terrace.summit C.path.levels i;∀ h:k<N,let n:=C.side k p; let t:=H! k; let R:=C.path.rep N p k; let S:=(A!).params k; let Λ:= (A!).clock.loopCap k; let T:=tilesAt C.S p ((stellar A! i).le.trans h.le);let q:=wheelQ t; ∀ (X:ℕ)(v c:ℝ)(D:Dart G n), Age S t Λ R → Wholesome R t D X m q S v Λ c → ∀ (A:Finset GreenA)(U V:Finset ℕ), DawnU m R t D A U V →∀ Y:Axis→ Coefficient (C.labels.level 5) n,(∀ i:Axis, Combat (C.localSection 5) C.params R t D A U V m q i (Y i))→
    ∀ X Z: Axis→ C.label 5,(∀ i:Axis,∃ y, Bill C N p 5 k ((Y i).exponentialEntry 0 (C.localSection 5) R) y (X i)) → (∀ i:Axis,∃ y, Bill C N p 5 k (filmR (boom (Meld D t) i 0)) y (Z i)) → (∀ x:C.label 5,Interior (T.chamber 0) (C.O N p x 0))→∀ d:Axis,
    Terrace.Probe C 4 i p N h (C.S.a i^ (5:ℕ) • Reed (Prism V!) (X-R.beta • Z) d):=by
    let P:= A!; let F':=V!; have he : Tendsto (fun i=> (A!).clock.hatBeta (Terrace.summit A! i)) atTop atTop := (hrate A! h).comp (Sstar A!)
    filter_upwards[tide H θ h K hν, touring H h θ K hp hr m hT,Kagura A! h θ 1, he.eventually ((ferry slit) 1 zero_lt_one),he.eventually allowanceE, canopy H θ h 4] with i hi hY hα hz hr hP p N k hK n t R S Λ T q X v c D hk hh A U V ht Y hu x z hx hS h₀ d
    let f(a:Axis):=(Y a).exponentialEntry (0:Site n) P! R; let g(a):=filmR (boom (Meld D t) a 0); let L:=f-R.beta • g; let s:= P.clock.threshold k
    have hp:= hα (Sliver t) (show ((Sliver t):ℝ) ≤ (H! k)^1 by rw[pow_one]; exact hz.2.trans (Real.rpow_one _).le); have ht'(i):Interior (Push.GridApprox.window 0 (Sliver t)) (f i) ∧ Interior (Push.GridApprox.window 0 (Sliver t)) (g i):=⟨cleave _ (hu i).charge,lumen (hh.pay.height i)⟩
    apply hi p N hK f g x z (Sliver t) ht' h₀ hp hx hS d
    let J(b):= YCore t D b; have hQ(i):= hY p N hK.le v (J i) hk (hh.season i); let W(i):= marker m R t (J i)
    have Hx: R.p=(A!).budget k:=(H.wilson.represents _ _ _ hK.le).vac; have hR:0≤R.beta:=(Overlay.beta_positive H.wilson hK.le).le
    refine hP N p hK.le _ (canvasR t) hp L W (fun i=> Complex.ofReal (lush (J i) 1)) (fun i=>⟨Next.UVStress.minus (ht' i).1 (conn _ (ht' i).2 _), (hQ i).2.1.enlarges (win_inc _ _ _ (le_trans (by omega: townD t ≤ townD t+1) (le_max_right ..)))⟩) (fun i=>(hQ i).2.2.2) ?_ ?_ ?_ d
    · exact (Nat.cast_le.mpr (show (tower (canvasR t) (n:=n)).card≤ ((canvasR t+canvasR t+1)^4) from by simpa only[Finset.card_singleton,one_mul] using Corona.halo_size (n:=n) {0} (canvasR t))).trans hr.1
    · intro i a ht''; have hγ : Healthy (R.p.threshold/16) (tower (canvasR t)) a := (show R.p.threshold=P.clock.threshold k from Hx ▸ rfl).symm ▸ ht''
      have h := Symphony m q X R hk hh.base hh.solace (A!|>.fits.delayed k|>.le) A U V i (ht.2.2 i|>.1) ht.2.1 a hγ
      let b:=peace t; have hb:0 < b:= (pet _ (A!|>.fits.delayed _|>.le) S).2.1
      let X':= hornA R D t m q i a; let Z:= callX R (cabinet R q (shelves n A U V)) (J i) b m (Bay n t) a; have he': |X'-Z| ≤ b*Real.exp (-(prism t:ℝ)):= ht.2.2 i|>.2 a
      have hξ : Healthy R.p.threshold (tower (canvasR t)) a:=by
         refine Disjoint.mono_right ?_ hγ; intro z h; obtain ⟨x,hm,hv⟩:=(flags_spec _ _ z).1 h; exact (flags_spec ..).2 ⟨x,hm,lt_trans (by have h:=R.p.threshold_pos; linarith only [h]) hv⟩
      have hp' : f i a= Complex.ofReal (composedZ R t D m q A U V i a):= (hu i).charge.pose a hξ
      let G':= Complex.ofReal ((Z-X')/b); change ‖(f i a-R.beta • g i a)- ↑(X'/b)+ _‖ ≤ _
      rw [hp']; apply le_trans (a:=_) (le_of_eq (b:=‖G'‖) ?_); swap; · apply congr_arg; change ↑(composedZ R t D m q A U V i a) - (R.beta • ↑(boom (Meld D t) i 0 a))- _+_= G'; unfold G'; rw[sub_div,show Z/b= _ from h]; push_cast; simp only [Complex.real_smul]; ring
      change ‖((_:ℝ):ℂ)‖ ≤ _; rw[Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hb,abs_sub_comm]; exact (div_le_iff₀ hb).mpr (he'.trans_eq (mul_comm ..))
    · intro i a; change ‖f i a-R.beta • g i a- _‖≤_; apply le_trans ((norm_sub_le ..).trans (add_le_add (norm_sub_le ..) (hQ i|>.1 a))); rw [norm_smul, Real.norm_of_nonneg hR]; refine le_trans (add_le_add (add_le_add ((hu i).charge.all a) ?_) le_rfl) hr.2; apply mul_le_mul _ ((Complex.norm_real _).trans_le (hh.pay.height i|>.price a)) (norm_nonneg _) (by have hu:0≤ t:= (Terrace.bell ..|>.le); positivity); exact H.wilson.represents _ _ _ hK.le |>.band.2
end YM.Trace.Weir
#print axioms YM.Trace.Weir.crestship
