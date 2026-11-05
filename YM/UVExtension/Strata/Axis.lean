import YM.UVExtension.Strata.Valley
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Strata
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
namespace Polish
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
-- provide one Bulb price tight with point domination absolute all measured legs
variable [NeBot v] (he:0 ≤ u)(hp: StableR v R)
structure Crystal (C : Air f G→ℝ)(P:ι→ Molecule S→ℝ): Prop where
     receipt : Swift v P
     employs : Integrable C
     positive (z): 0≤C z
     uv : ∀ᶠ i in v,∀ F (X:Coat (T i) F), X.x=s → X.width=U.K → X.manifest → X.χ=χ→
       ∀ K: Molecule S,(∀ l w',‖shiftV (R:=R) i X (X.body (R i) Q.table w U.a l Q.halo K) w'‖ ≤ P i K*C w'.2) ∧
        ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](τ:E)(V:E→ Config G c),
         V τ=X.V → Healthy (temp X.x) ((H i).unionP K) X.V→ Mode V τ k u →∀ B':Finset (Bond f),
          let f' y:= rhythm B' X (V y) A Q.table K (R i) w U.a Q.halo; ∀ j≤k,∀ z,
           ‖shiftV (R:=R) i X (JetF f' j τ) z‖ ≤ P i K*C z.2
include p he
lemma fareT (v':ℕ): ∃ f':Air f G→ℝ,Integrable f'∧(∀ y,0≤f' y)∧∀ (i:ι)(F:Forest S.ratio)(X:Coat (T i) F),X.x=s→ X.width=U.K → X.manifest →X.χ=χ →∀ x', (quilt (R:=R) i X x')*(1+‖wound (R:=R) i X x'‖)^v' ≤ f' x'.2:=by
    obtain ⟨d,r,H₀,hd,hr,hp,h⟩:= presidents p; obtain ⟨B,hB,hx⟩:=salary p he
    let K:=betaF G s S.patch.L
    obtain ⟨i,hi⟩:= (show ∀ᶠ i in v, True from by simp).exists; have ht:1<K:= H i|>.laws.intake.height
    obtain ⟨f,hF,hg,hv⟩:= sands (J:=Tubular f G) d r B (K/2) (2*K) H₀ (by linarith) hp (by linarith) hd hr hB v'
    exact ⟨f,hF,hg,fun i F X hX hu hM hχ z=> hv _ (h F i X hu hX hM).1 (h F i X hu hX hM).2 _ (H i|>.laws.intake.window) _ (hx F i X hu hX hχ hM z.1) z.2⟩
omit [NeBot v] in lemma sheet_p (i)(F:Forest S.ratio)(X:Coat (T i) F)(hs:X.x=s)(hw:X.width=U.K)(hm:X.manifest)(w:F.Slice G × Air f G):0≤ quilt (R:=R) i X w:= mul_nonneg (Wick.lint_pos (H i|>.laws.intake.positive) _).le (fullFuel _ _|>.le)
-- absorb face powers all stencils
lemma bulbP :∃ z:ℝ,1≤z ∧ ∀ (b : Finset (Bond f)) (w:Air f G),1+B*facescale b w ^ l + 1 ≤ z*(1+‖w‖)^l:=by
   let c:ℝ:=Fintype.card (Bond f); let t:ℝ:= Fintype.card (Tubular f G); let d:= 1+c+t; have hc:0≤c:=Nat.cast_nonneg _; have ht:0≤t:=Nat.cast_nonneg _; have hd: t≤d:=by unfold d; linarith
   have hv:= p.realm.roof; let z:=2+B*d^l; have hZ : 0≤ B*d^l:=by exact mul_nonneg hv (pow_nonneg (ht.trans hd) l)
   refine ⟨z,by unfold z; linarith, ?_⟩
   intro b w; have he : facescale b w ≤ d*(1+‖w‖):=by
       let i:=lensS b G
       have hh:(b.card:ℝ)≤c:= Nat.cast_le.mpr (card_le_univ _)
       have hy:(i.card:ℝ)≤t:= Nat.cast_le.mpr (card_le_univ _)
       have ht' (j:Tubular f G):|w j|≤‖w‖:= (PiLp.norm_apply_le w j)
       have hk:∑ j∈i, |w j|≤ t*‖w‖:=by refine (sum_le_sum (g:=fun _=> ‖w‖) (s:=i) (fun j _=> ht' _)).trans ?_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
       change 1+(b.card:ℝ)+i.card+(∑ j∈i,|w j|) ≤ _; rw [mul_add,mul_one]; unfold d; nlinarith only [hh,hk,hy,mul_le_mul_of_nonneg_right hd (norm_nonneg w)] -- d unfold?
   have hf := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ facescale b w from by unfold facescale; positivity) he l) hv
   rw [mul_pow] at hf
   have hi: 1≤ (1+‖w‖)^l:=one_le_pow₀ (by linarith [norm_nonneg w]); unfold z; linarith -- no associativity
-- supplies absolute budget inside rhythm. `stand` product variant all.
-- factor d(y) may grow exp? already uniform.
section tide
variable {i:ι}{F:Forest S.ratio}{P:Coat (T i) F} (hX:P.x=s)(hV:P.χ=χ)(hD:P.width=U.K)(hm:P.manifest)
include hX hV hD hm
lemma pearl (w':Head S→ℝ)(pw:∀ j,Lodge p i j (w' j))(W:Molecule S)(ph:Healthy (temp P.x) ((H i).unionP W) P.V)(U': Finset (Bond f)) (y: F.Slice G× Air f G)
     (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (τ:E)(Y:E→ Config G c) (Ht:Y τ=P.V)(h: Mode Y τ k u):
     Brush k (1*(∏ i∈W,w' i)) ((B*facescale U' y.2 ^ l)+W.card) (fun z=> rhythm U' P (Y z) A Q.table W (R i) w U.a Q.halo y) τ:=by
    let X:= P.wrapY y.1; let v z:=course X A (R i).beta y.2 (Y z); let t i' := steer X A (worldZ X (R i).beta y.2) (Y i'); have ht:= ((p.realm.granted _ _ S (T i) _ _ (H i) (p.rails i) rfl).2 E Y F X τ hX hV hD hm Ht h).2 y.2
    have hp (j) (hj:j∈W): Brush k (w' j) 1 (fun z=> Polar.ember (vary X (Y z)) U.a (R i) w Q.table (t z) (X.input (worldZ X (R i).beta y.2)) (v z) (Matter.own W) Q.halo j) τ:=
       (pw j).funded E F X Y _ τ _ _ hX hD hV hm h ht.1 (Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H i).supportP hj) ph) _
    have hh : Brush k (∏ i∈W,w' i) (W.card:ℝ) (fun z=> Polar.floating (vary X (Y z)) U.a (R i) w Q.table (v z) (Matter.own W) Q.halo W) τ:=by
       have hf := Brush.all_prod W _ _ _ hp; simp only [sum_const,nsmul_eq_mul,mul_one] at hf; apply hf.shimmy ; filter_upwards [ht.1.patch] with z hz; unfold Polar.floating; rw [show worldZ (vary X (Y z)) _ _= t z from ht.1.moving z]
       let N' := vary X (Y z); let P' :Intake _ _ N'.x (R i) := hX.symm ▸ (H i).laws.intake
       exact Finset.prod_congr rfl fun j _=> (plastic hz ht.1.pulse).reeled (show Room _ _ _ N'.x from hX.symm ▸ (H i).laws.data.room) w Q.table (Matter.own W) Q.halo P' j (v z)
    exact (ht.2.1 U').paints hh
end tide
include hp
lemma entrance : ∃ (f': Air f G→ℝ) (V:ι→ Molecule S→ℝ), Crystal (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=u) (A:=A) f' V :=by
    obtain ⟨f,hf,hV⟩:= opening p hp he; obtain ⟨r,hr⟩:=hf.books; obtain ⟨t,ht,h⟩:= bulbP p he -- inspect
    let P':ℕ:=l*k; obtain ⟨F,hF,hQ,hh⟩:= fareT p he P'; have ht':0≤t:=zero_le_one.trans ht
    -- cost W multiplier 1+# + (both scaled)
    let G' (i:ι)(W: Molecule S):= ∏ j∈W,f i j; let b i W:= G' i W+(W.card:ℝ)^k*G' i W
    let M i W:= (2*t)^k*b i W; refine ⟨F,M,(hf.powerList.plus (hf.flourish k)).scales _ (by positivity),hF,hQ,?_⟩
    filter_upwards [hV,hr] with n h' hX L' X hs hu hM hχ W
    have ht (i):=hh n L' X hs hu hM hχ i; have hx:= sheet_p p he n L' X hs hu hM
    have hw : 0 ≤ G' n W:= prod_nonneg fun _ _=> (hX.1 _)
    have he : G' n W ≤ b n W:= le_add_of_nonneg_right (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hw)
    have hz :1≤ (2*t)^k:= one_le_pow₀ (by linarith : (1:ℝ) ≤ 2*t)
    constructor
    · intro v z; let y:= wound (R:=R) n X z; unfold shiftV; rw [norm_smul,Real.norm_of_nonneg (hx _)]
      have h (j)(hj:j∈W): |(X.wrapY z.1).vertex (R n) Q.table w U.a v Q.halo y j| ≤ f n j:=(h' j).value L' (X.wrapY z.1) hs hu hχ hM y v
      have hP : ‖X.body (R n) Q.table w U.a v Q.halo W (z.1,y)‖ ≤ G' n W:=by unfold Coat.body Coat.term; rw [norm_prod]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) h
      have hS := ((le_mul_of_one_le_right (hx z) (one_le_pow₀ (show 1 ≤ 1+‖y‖ from le_add_of_nonneg_right (norm_nonneg _)) (n:=P'))).trans (ht z))
      calc
           _ ≤ F z.2*(G' n W) := mul_le_mul hS hP (norm_nonneg _) (hQ _)
           _ ≤ _ := by rw [mul_comm (F z.2)]; exact mul_le_mul_of_nonneg_right (he.trans (le_mul_of_one_le_left (hw.trans he) hz)) (hQ _)
    intro E _ _ _ τ V hv hhV hV U' Φ j hj z
    let y:= wound (R:=R) n X z; let b':ℝ:= 1+‖y‖; let c:ℝ:=W.card; have hb':1≤b':=le_add_of_nonneg_right (norm_nonneg _)
    have hy:=pearl p ‹0≤u› hs hχ hu hM _ h' W hhV U' (z.1,y) E τ V hv hV
    have hB:= p.realm.roof
    let Q':=1+(B*facescale U' y^l+c); have hS: B*facescale U' y^l+c≤ Q':= le_add_of_nonneg_left zero_le_one
    have hL: ‖JetF Φ j τ (z.1,y)‖ ≤ G' n W* Q'^k:= by
       apply (hy.order j hj).trans; rw [one_mul]; apply mul_le_mul_of_nonneg_left _ hw; exact (pow_le_pow_left₀ hy.pos hS _).trans (pow_le_pow_right₀ (by unfold Q'; exact le_add_of_nonneg_right hy.pos) hj)
    unfold shiftV; rw [norm_smul,Real.norm_of_nonneg (hx _)]
    let g':= quilt (R:=R) n X z; change g' * _ ≤ _
    obtain he'|he':= W.eq_empty_or_nonempty
    · have hC : c=0 :=by unfold c; simp [he']
      have hK : Q'≤2*t*b'^l:=by unfold Q'; rw [hC,add_zero]; have hh:=h U' y; change _ ≤ t*b'^l at hh; nlinarith only [hh, ht',one_le_pow₀ hb' (n:=l)] -- positivity times
      have hh := (pow_le_pow_left₀ (hy.pos.trans hS) hK k); rw [mul_pow,← pow_mul] at hh
      calc
         _ ≤ g'*(G' n W*((2*t)^k*b'^P')) := mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hh hw)) (hx z)
         _ = (2*t)^k*G' n W*(g'*b'^P'):=by ring
         _ ≤ _ := by exact mul_le_mul (mul_le_mul_of_nonneg_left he (zero_le_one.trans hz))
                                       (ht z) (by exact mul_nonneg (hx _) (pow_nonneg (zero_le_one.trans hb') _)) (mul_nonneg (pow_nonneg (by positivity) _) (hw.trans he))
    have hC:1≤c:=by unfold c; exact_mod_cast show 1 ≤ W.card from Finset.card_pos.mpr he' -- nat pos
    have hK : Q'≤ 2*t*b'^l*c:=by unfold Q'; have hh:=h U' y; change _≤ t*b'^l at hh; nlinarith only [hh,mul_le_mul (show 1≤t from ‹1≤t›) (one_le_pow₀ hb' (n:=l)) zero_le_one ht', hC] -- nlinarith need *c
    have hh := pow_le_pow_left₀ (hy.pos.trans hS) hK k; rw [mul_pow,mul_pow,← pow_mul] at hh
    calc
       _ ≤ g'*(G' n W*((2*t)^k*b'^P' * c^k)):=mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hh hw)) (hx _)
       _ = (2*t)^k*(c^k* G' n W)*(g'*b'^P'):=by ring
       _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hw) (pow_nonneg (by positivity) _)) (ht z) (mul_nonneg (hx _) (pow_nonneg (zero_le_one.trans hb') _)) (mul_nonneg (pow_nonneg (by positivity) _) (hw.trans he))
end Polish
end YM.UVExtension.Strata
#print axioms YM.UVExtension.Strata.Polish.entrance
