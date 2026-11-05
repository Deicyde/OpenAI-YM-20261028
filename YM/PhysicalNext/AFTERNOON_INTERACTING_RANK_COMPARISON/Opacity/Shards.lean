import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Petty
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Palette
/-!
# Log-determinants with sector rents, not extending eigenvalue marks
- Uniform ribbons over ALL (A,key) using Certified. Off-corner data never
  asserted to move across flags; still price each trace at actual support.
- Split prelude from these tails only, scoring in ℝ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Port
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute Physical
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Dictionary Dictionary.Notify Wires  EndpointLoadF16.DetLong Physical
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x W a e v₀ L η C b d : ℝ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S}
local notation "PS"=>Physical.place S (G:=G)
local notation "R"=>radiusB x
local notation "τ"=>currency b (radiusB x)
local notation "N"=>Physical.Key G f
local notation "I"=>Physical.windows S x (G:=G)

def panel (v : Dyed G S) (p:Pilot G S x) := AFull v.things p.key p.park x p.view p.tag
def frame (v : Dyed G S) (p:Pilot G S x) := AFull v.things (voidStore S) p.park x 1 p.tag
def sect (v : Dyed G S) (i:Bond f) (p:Pilot G S x):= EndpointLoadF16.DetLong.prelude x v.things p.key p.park p.tag i p.view
def wager (v : Dyed G S) (z:Letter N 1) (p:Pilot G S x) := -(1/2:ℝ)*(page I (panel v p) z-page I (frame v p) z)

def introTax (v : Dyed G S) (p:Pilot G S x):= ∑' i:Letter N 1,wager v i p
def showTax (v : Dyed G S) (p:Pilot G S x):= ∑' i:Letter N 0,(1/2:ℝ)*errata I (panel v p) i
lemma conducts (v : Dyed G S) (i:Bond f) (p:Pilot G S x): sect v i p= -(1/2:ℝ)*∑ j:G.ColorIndex,(letterBase I (panel v p) (i,j)-letterBase I (frame v p) (i,j)):= by rw [sum_sub_distrib];unfold sect EndpointLoadF16.DetLong.prelude contrast; simp only [Pi.sub_apply,chapters, Sum.elim_inl,bolus_read]; rfl
lemma book_price (h : Chips v P W x) (hc : Certified S v.things x v₀ C η b) (hA : Matched p) (he : 0≤e)
    (h0 : Physical.parcel G S 20 e v₀ C b d R 0) (h1 : Physical.parcel G S 20 e v₀ C b d R 1) : v.keptEarly p= -(Fintype.card (Frozen p.key x p.park):ℝ)*Real.log (spare v.ratio v.source.beta) + (∑ i,sect v i p)+(introTax v p+showTax v p) :=by
  obtain ⟨ht,hb,hv,hM⟩:= Export.receipt hc p.park p.tag _ he (spare v.ratio v.source.beta) h.boost.produced.branched hA h0 h1
  apply Real.exp_injective; rw [← show Export.account _ _ _ _ _ _ _=Real.exp (v.keptEarly p) from hM]; apply congr_arg Real.exp
  unfold introTax showTax; simp_rw [wager,tsum_mul_left,conducts,← Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun i: Physical.Key G f=> letterBase I (panel v p) i-letterBase I (frame v p) i)]; unfold panel frame; ring
lemma inspect (h: Boosted v.things P x) {X : Support c} {g:Matrix N N ℝ→ℝ}
    (hg : ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices),Measurable fun U=>g (Wires.beam v.things k U x A F))
    (hS : ∀ A A',ReadTogether PS X R I I A A' → g A=g A') : Pulled (fun p:Pilot G S x=>g (panel v p)) X ∧ Pulled (fun p:Pilot G S x=>g (frame v p)) X:= by
  have hp (A : Stores S) F k U (hk : Positioned x A U) : Wires.beam v.things k U x A F=AFull v.things A F x U k:= by
    obtain ⟨s,hs⟩:= h.license A F U hk; exact Wires.beam_exact _ _ _ _ _ _ h.produced hs
  have hu:= Export.no_seeds G S x
  constructor
  · refine (Pulled.conforme (z:=fun p:Pilot G S x=>g (Wires.beam v.things p.tag p.view x p.key p.park)) ⟨fun A F k=> ⟨_,(hg A F k).comp measurable_fst,fun _ _ _=>rfl⟩,fun p q _ _ ht=>hS _ _ (Wires.positioned _ h.produced ht.reads)⟩ fun i h=> congr_arg g (hp _ _ _ _ h))
  refine (Pulled.conforme (z:=fun p:Pilot G S x=>g (Wires.beam v.things p.tag 1 x (voidStore S) p.park)) ⟨fun A F k=> ⟨fun _=>g (Wires.beam v.things k 1 x (voidStore S) F),measurable_const,fun _ _ _=>rfl⟩,fun p q _ _ ht=> hS _ _ (Wires.positioned _ h.produced ?_)⟩ fun i h=> congr_arg g (hp _ _ _ _ hu))
  exact ⟨fun _ _ _=>rfl,ht.reads.frame,ht.reads.bond,ht.reads.tree,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩
lemma estate_at (h : Boosted v.things P x) (i:Bond f) (he : Shields X (S.ratio.parent i.1) (20*R)) : Pulled (sect v (x:=x) i) X:= by
  have hl j (k:G.ColorIndex) (hJ : j=(i,k)):= inspect (X:=X) (g:=fun z=> letterBase I z j) h (fun A F t=>Typeset.first _ (fun i j=> beam_meas v.things t x A F i j h.produced.branched) j) (fun _ _ h'=>h'.local_value (by omega : 15≤20) j (by subst j; exact fun u hk=> he u ((lens_spec ..).mp hk)))
  apply Pulled.conforme (z:=fun p:Pilot G S x=>-(1/2:ℝ)*∑ j:G.ColorIndex,(letterBase I (panel v p) (i,j)-letterBase I (frame v p) (i,j))) _ (fun p hp=>(conducts v i p).symm)
  apply Pulled.times (Pulled.fetch _); exact Pulled.sum _ fun j _=> ((hl (i,j) j rfl).1.covers (hl (i,j) j rfl).2).twine (measurable_fst.sub measurable_snd)
lemma gross (p : Pilot G S x) (h:Matched p) (hc : Certified S v.things x v₀ C η b) (i:Bond f) : |sect v i p| ≤ Fintype.card G.ColorIndex*((C+1)*C):= by
  let f:=fun j:G.ColorIndex=> letterBase I (panel v p) (i,j)-letterBase I (frame v p) (i,j)
  let Y:=(C+1)*C; let A:= Fintype.card G.ColorIndex
  have hg j : |f j| ≤ Y+Y:= (abs_sub ..).trans (add_le_add ((hc.writes _ _ h).regular_price _).2 ((hc.writes _ _ (Export.no_seeds G S x)).regular_price _).2)
  rw [conducts,abs_mul,abs_neg,abs_of_nonneg (by norm_num :(0:ℝ)≤1/2)]
  have hw : |∑ j,f j|≤ (∑ _j:G.ColorIndex,(Y+Y)):= ((Finset.abs_sum_le_sum_abs f _).trans (Finset.sum_le_sum fun j _=> hg j)); apply (mul_le_mul_of_nonneg_left hw (show 0≤(1/2:ℝ) by norm_num)).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul]; unfold Y; ring
lemma billIt (h : Chips v P W x) (hc : Certified S v.things x v₀ C η b) (hC : 0≤C) (he : 0≤e)
    (h0 : Physical.parcel G S 20 e v₀ C b d R 0) (h1 : Physical.parcel G S 20 e v₀ C b d R 1) : Petty v W R e (currency d R) (introTax v (x:=x)) ∧ Petty v W R e (currency d R) (showTax v (x:=x)):= by
  let q := (τ); let a1 (n:ℕ) := inventory PS 20 R (n:=n); let l (n:ℕ) := AnalyticBridge.RelativeLogdet.ticket PS R v₀ C q (n:=n)
  have he' n (i : Letter N n): 0≤l n i:= ticket_nn _ _ hC (currency_pos ..).le _
  have hI n (i : Letter N n) : (a1 n i).Nonempty := ⟨PS i.snd.1,(first_lens ..) (lens_root ..)⟩
  let p:= h.boost.produced.branched
  constructor
  · refine Petty.accepts (L:=wager v) (ι:=Letter N 1) (fun i=> ?_) (hI 1) (he' 1) h1 he fun i k hp=> ?_
    · have h := inspect (g:=fun z=>page I z i) (X:=a1 1 i) h.boost (fun A F s=>Typeset.article I (fun i j=> beam_meas v.things s x A F i j p) _) fun _ _ h=>?_ -- proof after h binds
      exact Pulled.times (Pulled.fetch _) ((h.1.covers h.2).twine (measurable_fst.sub measurable_snd))
      unfold AnalyticBridge.RelativeLogdet.page; rw [show _ = AnalyticBridge.RelativeLogdet.scroll I _ _ _ from h.manuscript (l:=20) (by omega) i (Finset.Subset.refl _)] -- order
    · have hP:= ((hc.writes k.park k.tag hp).scrolls (furnished _ k.tag k.view p k.key k.park hc.geometry) i).2.2
      have hQ:= ((hc.writes k.park k.tag (Export.no_seeds G S x)).scrolls (furnished v.things k.tag (1:Config G c) p (voidStore S) k.park hc.geometry) i).2.2
      unfold wager; rw [abs_mul,abs_neg,abs_of_nonneg (by norm_num :(0:ℝ)≤1/2)]
      exact (mul_le_mul_of_nonneg_left ((abs_sub ..).trans (add_le_add hP hQ)) (by norm_num : 0≤(1/2:ℝ))).trans_eq (by unfold l q; ring)
  · refine Petty.accepts (L:=fun i p=>(1/2:ℝ)*errata I (panel v p) i) (fun i=> Pulled.times (Pulled.fetch _) ?_) (hI 0) (he' 0) h0 he fun i k hp=> ?_
    · exact (inspect (X:=a1 0 i) (g:=fun z=>errata I z i) h.boost (fun A F t=>Typeset.printing _ (fun i j=> beam_meas v.things t x A F i j p) _) (fun _ _ h=>h.notices (by omega :17≤20) i (Finset.Subset.refl _))).1
    exact (le_trans (le_of_eq (abs_mul ..)) ((mul_le_of_le_one_left (abs_nonneg _) (by norm_num : |(1/2:ℝ)| ≤ 1)).trans ((hc.writes k.park k.tag hp).erratas (furnished _ k.tag k.view p k.key k.park hc.geometry) i)))
end YM.PhysicalNext.InteractingRank.Pump.Port
