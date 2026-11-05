import YM.UVExtension.Concert.Aperture

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
variable (N : Wick.Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
variable {X} (hc:X.χ=χ) (hX:X.x=x) (hr:X.width=o.K)
variable {q : Q.rate≤γ} {hh:γ<0} {U v₀ C₀ q'' : ℝ} {k:ℕ} (Y:Outliner N hF γ q hh U v₀ C₀ q'' k)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V':E→ Config G c) (τ:E)
    (hx: V' τ=X.V) (hv:Mode V' τ j u) (J : (d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V))
    (m:H.ThinP)
-- massage priors across planners; flare order from single voucher

def ivy (z:Vines ι) (i:H.ThinP) := if hp:z∈parade (betaF G x L) g then Outliner.paint N hF Y z hp i.val else 0
lemma ivy_nn (z:Vines ι) (u':H.ThinP) : 0≤ ivy N hF Y z u':= by
  unfold ivy; split; next hp => exact (Outliner.jetbook N hF Y z hp).1 _
  exact le_refl _
include hX hx hc hr Y hv hS
set_option maxHeartbeats 250000 in
lemma fringe_ivy (he : Healthy (temp x) (H.unionP m.val) (V' τ)) : ∃ g', Twist (aperture hF) τ j (fun d r=> Stained.fringe (vary X (V' r)) W o.a m.val (freshen d R V) Q.table Q.halo) g' ∧ ∀ z ∈ (aperture hF).span, Brush j (ivy N hF Y z m) 1 (g' z) τ:=by
  have hW : Healthy (temp X.x) (H.unionP m.val) X.V:= by rw [hX,←hx]; exact he
  let A' (i:ℕ) (p:Fin i→ E):= Outliner.badgeP (H:=H) (V:=V) (A:=A) (V':=V') (τ:=τ) m.val p X rfl
  have hi (d:Canvas (betaF G x L) w ι) i (hi:i≤j)(p:Fin i→ E) := Outliner.garnet N hS hF hX hc hr Y hx hv m.val hW m.2.2 p hi d.val d.2
  refine Twist.bloomset (T:=aperture hF) (f:=fun d r=> Stained.fringe (vary X (V' r)) W o.a m.val (freshen d R V) Q.table Q.halo) (t:=τ) (j:=j) ?_ _ A' ?_ ?_ (fun z hz=> ivy_nn N hF Y z m) ?_
  · exact fun i=> (hi i 0 (by omega) (fun _=>0)).1
  · exact fun d i hp v=> (hi d i hp v).2
  · exact fun i hi v=> Outliner.forma N hS hF hX hc hr Y hx hv m.val hW m.2.1 v hi
  intro z hz i hp p; change z∈parade (betaF G x L) g at hz; unfold ivy; rw [dif_pos hz]; exact Outliner.lap N hS hF hX hc hr Y hx hv m.val hW p hp z hz
omit hX hx hr hc
lemma leafy (he : Healthy (temp x) (H.smallAt m) (V' τ)) : ∃ g', Twist (aperture hF) τ j (fun d r=> leaflet (J d) χ (V' r) ((fleet d J H).bearing m)) g' ∧ ∀ z ∈ (aperture hF).span, Brush j (ivy N hF Y z m) 1 (g' z) τ:=by
  letI := Tree.select S.ratio S.patch.odd_side
  let X i:= prism T x χ o.K (V' τ) (Greenbelt.allot i)
  choose f hf hp using fun i : Greenbelt.Reserve S=> fringe_ivy (X:=X i) N hS hF rfl rfl rfl Y V' τ rfl hv m he
  let G':= Greenbelt.Reserve S; let c':ℝ:= (Fintype.card G':ℝ)⁻¹; have hC:0<c':= by unfold c'; positivity
  refine ⟨fun z x' => (c':ℂ)*∑ i,f i z x',?_ , fun z hz=>?_⟩
  · apply (Twist.plus c').times (Twist.crew Finset.univ _ f (fun i _=> hf i)) -- rfl
  have hv:= Brush.spree Finset.univ (fun i=> f i z) (fun _=> ivy N hF Y z m) zero_le_one (fun i _=> hp i z hz)
  refine (scales hv c').climb (le_of_eq ?_) le_rfl
  rw [Complex.norm_real,Real.norm_of_nonneg hC.le,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold c' G'; simp

omit hv hS
def mug (i:H.fragrances) (z:Vines ι) := Ursell.clusters H.seam (fun i=> (2:ℝ)^j * ivy N hF Y z i) i.snd
lemma mug_nn (i:H.fragrances) (z:Vines ι): 0≤ mug N hF Y i z:= clusters_nonneg _ (fun i=> mul_nonneg (by positivity) (ivy_nn N hF Y z i)) _
include hv hS
lemma shells (i:H.fragrances) (he:Healthy (temp x) (Song.perf H i) (V' τ)) : ∃ g', Twist (aperture hF) τ j
      (fun d r=> stream (J d) χ (V' r) ((fleet d J H).furrow i)) g' ∧∀ z∈ (aperture hF).span, Brush j (mug N hF Y i z) 1 (g' z) τ:=by
  choose f hf hp using fun n : Option (Fin i.1)=> leafy N hS hF Y V' τ hv J (i.2 n) (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem (H.smallAt ∘ i.2) (mem_univ _)) he)
  let a':= coefficient H.seam i.2 / (i.1+1).factorial
  let B' d r:= ∏ n, leaflet (J d) χ (V' r) ((fleet d J H).bearing (i.2 n))
  have hE d r:stream (J d) χ (V' r) ((fleet d J H).furrow i)=a' * B' d r:= by
    unfold stream Gas.term; rw [← Match.weighs _ (fleet d J H).sec]; change coefficient H.seam i.2 * B' d r / (↑ ((i.1+1).factorial):ℝ) = _; unfold a'; ring
  simp_rw [hE]; refine ⟨fun z x=> (a':ℂ)*∏ n,f n z x, (Twist.plus a').times (Twist.clues Finset.univ _ _ (fun i _=> hf i)),fun z hz=>?_⟩
  let g w := ivy N hF Y z (i.2 w)
  have hp':= all_thread Finset.univ (fun i=> f i z) g (fun _=>1) (fun i _=> hp i z hz)
  apply (scales hp'.trim a').climb _ le_rfl
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one,Complex.norm_real]
  unfold mug clusters; change ‖a'‖*((∏ i,g i)*(1+((i.fst+1:ℕ):ℝ))^j) ≤ |_| *(∏ n,2^j*g n)/_
  conv_rhs => rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
  have he : (1+((i.fst+1:ℕ):ℝ))^j ≤ (2^j : ℝ)^(i.fst+1) := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=i.fst+1)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (show 0≤∏ i,g i from Finset.prod_nonneg
    fun i _=> ivy_nn N hF Y z _)) (norm_nonneg a')).trans_eq
  unfold a'; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity : 0 ≤ ((i.1+1).factorial:ℝ))]; ring
end YM.UVExtension.Concert
