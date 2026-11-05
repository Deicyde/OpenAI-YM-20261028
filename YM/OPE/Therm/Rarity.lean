import YM.OPE.Therm.Law
import YM.Next.RANK.Determinant
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.Vac.Treasury
/-!
# Rare events measured at the coarse effective mesh

No promotion to all sequences of stages yet. Geometry constants picked from the desired entropy
vs boundary-width price. This working core lets us budget also *inside* flags by stopping
at lower-than-actual chord threshold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm
open Function Filter Set MeasureTheory Lattice Wilson RG Next.Rank Push.GridApprox Cells WardBin.Wheels
open scoped ENNReal Topology BigOperators Classical
variable {G:Gauge} {H:History G}(Y:H.Selected){k i m N p:ℕ} {τ g :ℝ}
local notation "n" j => H.S.side j p
local notation "Q" j => H.rep N p j
local notation "η" j => prior G (H.S.side j p)
local notation "ℤ∞" => partition G (H.S.side N p) (H.β N p N)
local notation "μ" j => scene H N p j
local notation "P*" => H.levels
local notation "Ξ" => Vac.treasury H.levels k
local notation "c₀" => H.levels.clock
section spot
variable {v:Side}
def trigger (z:Face (Per v))(τ:ℝ) : Set (Config G v) := {U|τ<G.chord (faceValue U z)}
def fires (z:Face (Per v))(τ:ℝ): Config G v → ℂ:= (trigger z τ).indicator 1
lemma fire_meas (z:Face (Per v))(τ:ℝ): MeasurableSet (trigger (G:=G) z τ):= measurableSet_lt measurable_const (show Continuous (fun U:Config G v=> G.chord (faceValue U z)) from by unfold faceValue; fun_prop).measurable
lemma fire_copy (t:Tiling v) (z:Face (Per v))(τ:ℝ) (i:t.Cell): t.copy i (fires (G:=G) z τ) = fires (Face.send (t.omega i) (t.translateBy i) z) τ := by
   classical
   let f:=t.omega i; let b:=t.translateBy i; funext U; have he : fires z τ (pull f b U)=(fires (Face.send f b z) τ U):=by
      simp [fires,trigger,Set.indicator,Face.send_price U z f b G.chord G.chord_inv (fun x y=>G.chord_conj y x)]
   unfold Tiling.copy; split_ifs; swap; · exact he
   rw [he]; change star (fires (Face.send f b z) τ U) = fires (Face.send f b z) τ U; unfold fires; by_cases h:U∈trigger (Face.send f b z) τ <;> simp [h]
lemma fire_interior (a:Set (Site v))(z:Face (Per v))(τ:ℝ)(hp:(touched z:Set _)⊆a):Interior (G:=G) a (fires z τ):=by
   refine ⟨fun x U=>?_, measurable_const.indicator (fire_meas z τ),fun U V h=>?_,1,fun U=>?_⟩
   · classical unfold fires trigger; simp only [Set.indicator,mem_setOf_eq,face_gauge,G.chord_conj,Pi.one_apply]
   · have ht:faceValue U z=faceValue V z:=by apply travel_local; apply agrees_mono h; exact fun x he=> hp (Finset.mem_coe.mpr (List.mem_toFinset.mpr he))
     unfold fires trigger; classical simp [ht,Set.indicator]
   unfold fires Set.indicator; split <;> simp
lemma fire_mass (ν:Measure (Config G v))[IsFiniteMeasure ν] (z:Face (Per v))(τ:ℝ): ‖∫ U,fires z τ U∂ν‖=ν.real (trigger z τ):=by
   unfold fires; rw [integral_indicator (fire_meas (G:=G) z τ)]; change ‖∫ (_:Config G v) in _, (1:ℂ)∂ ν‖=_; rw [setIntegral_const,norm_smul]; simp [Real.norm_of_nonneg measureReal_nonneg]
lemma window_serves (z:Face (Per v)): (touched z : Set _) ⊆ window z.1 2 := by
   intro i hi; have ht:pdist (i-z.1)≤ 2 := le_trans ((separation_comm i z.1)).le (Work.E01.sep_touched z _ hi)
   refine ⟨lift (i-z.1), ?_, by dsimp only; rw [wrap_lift,sub_add_cancel]⟩; have he (j: Axis):= (component_le (i-z.1) j).trans ht
   change _∈ box 2; rw [box_test]; constructor <;> intro j <;> specialize he j <;> omega
lemma trigger_injective (T:Tiling v)(z:Face (Per v))(h:(touched z : Set _) ⊆ T.chamber 0) : Injective (fun i=> Face.send (T.omega i) (T.translateBy i) z) :=by
   have ht (i:T.Cell): let Z:=Face.send (T.omega i) (T.translateBy i) z; T.which Z.1=i :=by
      intro Z; refine T.which_chamber ?_; have ht:=Work.E01.base_touched Z; unfold Z at ht; rw [Work.H03.touched_send] at ht
      obtain ⟨y,hy,hY⟩:=Finset.mem_image.mp ht; rw [← hY]; exact T.enumerate i (h hy)
   exact fun i j hij=> Eq.trans (ht i).symm ((congr_arg (fun z:Face (Per v)=> T.which z.1) hij).trans (ht j))
local notation "vol0" => (Fintype.card (Site v):ℝ)
local notation "ac" => (Fintype.card PlaqAxes:ℝ)
private lemma poll {R : Rep G v}{σ A Λ δ w:ℝ}(Y:R.Lawful σ A Λ δ w) (hw:w≤1) (hg :0<g) (he:g ≤ R.p.threshold) (hm:R.beta*g^2=1) (T:Tiling v)(z:Face (Per v))(h:(touched z : Set _) ⊆ T.chamber 0) :
    let e:ℝ:= g / strength R.clip
    let a:= τ/e*Fintype.card T.Cell
    ∀ U, ‖(R.eval U:ℂ)* T.fullAt (fun _=>fires z τ) U‖ ≤ Real.exp (R.scalar+vol0*(R.exCost A Λ δ + ac) - a) :=by
   intro e a U; let r(i:Face (Per v))(U:Config G v):= G.chord (faceValue U i)/e; have hx:=trigger_injective T z h
   let g' (j:T.Cell):= Face.send (T.omega j) (T.translateBy j) z; let R₀:=∑ j,r j U
   have hh (j): T.copy j (fires z τ) U = fires (g' j) τ U:= congr_fun (fire_copy T z τ j) U
   unfold Tiling.fullAt; simp_rw [hh]; by_cases hy : ∀ j:T.Cell,U ∈ trigger (g' j) τ; swap
   · push Not at hy; obtain ⟨j,hj⟩:=hy
     rw [Finset.prod_eq_zero (Finset.mem_univ j) (f:=fun j=> fires (g' j) τ U) ?zero]; simp [(Real.exp_pos _).le] -- b not arg
     case zero=> exact indicator_of_notMem hj 1
   have hE : 0<e:= div_pos hg (strength_pos _); have hr(i):0 ≤ r i U:=div_nonneg (G.chord_nonneg _) hE.le
   have hT : a ≤ R₀:=by
      have ht:=Finset.sum_le_sum_of_subset_of_nonneg (f:=fun i=>r i U) (Finset.subset_univ (Finset.univ.image g')) (by intros; apply hr)
      rw [Finset.sum_image hx.injOn] at ht; apply le_trans ?_ ht
      unfold a; rw [mul_comm _ ((Fintype.card T.Cell):ℝ), ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun i _=> div_le_div_of_nonneg_right (show τ ≤ _ from le_of_lt (hy i)) hE.le
   have hv (i): fires (g' i) τ U=1:= indicator_of_mem (hy i) 1; simp_rw [hv]; simp only [Finset.prod_const_one,mul_one,Rep.eval,Complex.norm_real,norm_mul]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact ((mul_le_mul_of_nonneg_left (SectorNext.Vacuum.gas_le_one R.activities hw Y.labels U) (Real.exp_pos _).le).trans_eq (mul_one _)).trans (Real.exp_monotone (le_trans (exponent_retains Y hg he hm U) (sub_le_sub_left hT _))) -- eq trans_eq type
end spot
-- one volume estimate
include Y
set_option maxHeartbeats 650000 in
lemma away (h:i≤ k) (he:k≤N) (z:PlaqAxes) (hp:room P* i k 2) (hg:0<g)(hγ:g≤ (Q k).p.threshold) (hw:(Q k).beta*g^2=1) :
    let a:= ((H.S.toDepth h p).count.val:ℝ)^4
    let b:= strength ((P*).params k).clip
    (μ k).real (trigger (0,z) τ) ≤ Real.exp (a*(Ξ+ Fintype.card PlaqAxes) - τ/(g/b)) :=by
    let t : Face (Per (n k)):= (0,z); let c:= H.levels.clock;let U:= H.levels.params k; let R:= Q k;intro a b; let P:=tilesAt H.S p h
    let C':ℝ:=Fintype.card P.Cell; let W:ℝ:=Fintype.card (Site (n k)); let L:=c.loopCap k; let A:=U.paths; let X:= c.hatCoupling k; let V:=c.allowance k; let WQ:=c.forcedAllowance k; let B:= Fintype.card PlaqAxes; let σ:= R.exCost A L V
    let b1:= R.scalar-W*(σ+R.beta*baseBudget R.clip A X)-(Fintype.card (Edge (Site (n k))):ℝ)*Module.finrank ℝ G.Mat* Real.log (16/X)
    let b2:=R.scalar+ W*(σ+B) - τ/(g/b)*C'; let a0:= a*(Ξ+B) - τ/(g/b)
    have hR:= Y.represents N p k he; have hvac:=hR.vac
    have hn :0<X:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ((P*).fits.delayed _)))
    have hE:X≤ R.p.threshold:= by
       change X≤(Q k).p.threshold; rw [hvac]
       exact le_mul_of_one_le_right hn.le (Real.one_le_exp (sq_nonneg _))
    have hz : 0<R.beta := by
       refine lt_of_lt_of_le ?_ hR.band.1; have h:= (P*).fits.delayed k; linarith only [h]
    have hK : 0<WQ := Real.exp_pos _
    have hΨ : WQ ≤ 1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
    let F:=fires (G:=G) t τ
    letI:= probability (p:=p) Y he
    have hc:P.chamber 0⊇ window (0:Site (n k)) 2:=by
       have hh:=room_fits p (P*) 2 h le_rfl hp 0; rwa [anchor,← Ratio.root_embed,map_zero,begin_radius] at hh
    have ht := fire_interior (window t.1 2) t τ (G:=G) (window_serves t)
    have hi := repeated (p:=p) Y h he F 2 ht hp; change ‖∫ U,fires t τ U∂ μ k‖ ^ Fintype.card P.Cell ≤ _ at hi; rw [fire_mass] at hi
    have hV := Vac.suffices_bill (H:=H) (p:=p) Y he 0 0 0 0 0
    simp only [Overlay.Bands.finalBill, Nat.cast_zero,zero_mul,add_zero] at hV; change W*(2*σ+WQ+ R.beta*baseBudget R.clip A X+4*Module.finrank ℝ G.Mat*Real.log (16/X)) ≤ W*Ξ at hV -- clip
    have hZ : W=C'*a:=by
       unfold W C' a; change (↑(Fintype.card (Site (n k))) : ℝ)= ↑(Fintype.card (Site (n i)))*_; simp_rw [site_card]; rw [(H.S.toDepth h p).exact_size]; push_cast; ring
    have h₀:0≤W:=Nat.cast_nonneg _
    apply le_of_pow_le_pow_left₀ P.cells_positive.ne' (Real.exp_pos _).le; refine hi.trans ?_
    rw [violet Y he,norm_div,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le, div_le_iff₀ (partition_pos _)]
    have hD : Real.exp b1 ≤ ℤ∞:= by
       rw [← H.partition_eq Y N p k he]; exact R.denominator hR.good hz.le X hn hE (fun u=> (gravity Y he u).le)
    let Y'(U:Config G (n k)):=((Q k).eval U:ℂ)* P.fullAt (fun _=> F) U
    have hA(U): ‖Y' U‖ ≤ Real.exp b2:=by
       have htz: strength ((Q k).clip) = b := congr_arg _ hR.clip
       have ht:=poll (τ:=τ) hR.good hΨ hg hγ hw P t ((window_serves t).trans hc) U; rw [htz] at ht; exact ht
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hD (pow_nonneg (Real.exp_pos _).le _)); rw [← Real.exp_nat_mul,← Real.exp_add]
    have hb : ‖∫ U,Y' U∂(η k)‖ ≤ Real.exp b2:= by simpa using norm_integral_le_of_norm_le_const («μ»:=η k) (Eventually.of_forall hA)
    apply hb.trans (Real.exp_monotone ?_); change b2 ≤ C'*a0+b1
    have hh : (Fintype.card (Edge (Site (n k))):ℝ)=4*W:= by unfold W; simp [Edge,Axis,mul_comm]
    unfold b1 b2 a0; rw [hh]; have he' :=mul_nonneg h₀ hK.le; rw [hZ] at he' hV ⊢; linarith
end YM.OPE.Therm
