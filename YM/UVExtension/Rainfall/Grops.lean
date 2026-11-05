import YM.MergeProof.Bouquet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Coasts
/-!
 Fixed-beat linearity, genuine threshold convention. Germs by angular change of
 variables (not claiming Healthy is open or differentiating its indicator).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Rainfall
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Lotus
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Charity Merge
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
   {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
   {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
   {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
-- Sage. data
variable {t:ι→ℝ}{Z:ι→Leaf R}
private lemma sticks (h:Grouped M t Z)(V:Config G c)(d:ℝ)(I:Finset (Bond f))(z:F.Slice G×Air f G) (p:Molecule S): M.carat I X V d Q.table p W o.a Q.halo z= ∑ i,t i*(Z i).carat I X V d Q.table p W o.a Q.halo z:=by
   unfold Leaf.carat Leaf.chimes Leaf.floret; simp_rw [h.turn]; split;next hp =>
     unfold Leaf.paidU Leaf.fond; simp_rw [h.turn]
     rw [← (h.earn _).tsum_eq,tsum_fintype]
     simp_rw [Finset.sum_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; ring
   next hp=> simp
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{V:E→ Config G c}{y:E}
open Itinerary Stained March
include N
private lemma budding (hx:X.x=x) (hχ:X.χ=χ)(hw:X.width=o.K)(h: Healthy (Pressure.temp x) (H.unionP p) X.V)(ht:(roster p).flags=∅)(hs:Grouped M t Z)(he:Mode V y j v)(hp:V y=X.V) : ∀ᶠ z in 𝓝 y,M.picture (vary X (V z)) p W o.a Q.table Q.halo=∑ i,t i*(Z i).picture (vary X (V z)) p W o.a Q.table Q.halo:=by
    let f(z:E)(C:Lotus.Leaf R):= C.grove (vary X (V z)) p W o.a Q.table Q.halo
    have hr(C:Lotus.Leaf R):∀ᶠ z in 𝓝 y,C.picture (vary X (V z)) p W o.a Q.table Q.halo=f z C:=C.arc X p H N.oboe hx hw hχ ht h he hp
    suffices hv: ∀ᶠ z in 𝓝 y,f z M= ∑ i,t i*f z (Z i) by
       filter_upwards [hr M,eventually_all.mpr fun i=>hr (Z i),hv] with z ha hh hc; rw [ha,hc]; simp_rw [hh]
    have hb:X.B=radiusB x:= congr_arg radiusB hx
    unfold f Leaf.grove; simp_rw [show ∀ z:E, (vary X (V z)).B=radiusB x from fun z=> hb]
    split_ifs with hZ; swap; · simp
    let D:= H.unionP p; let I:=podium S G D (radiusB x); let K k (z:E)(C:Leaf R) := C.cinema ((preps (vary X (V z)) (roster p)).taggedL k) p W o.a Q.table Q.halo I
    have hK k:∀ᶠ z in 𝓝 y,K k z M=∑ i,t i*K k z (Z i):=by
       let U:=(planted X p).taggedL k; have hv:U.manifest :=planted_valid X p
       have hr:= N.oboe.flow F U hx hχ hw hv E V y hp he; have hD:8*o.a*Pressure.fiery G U.x S.patch.L≤ A/2:=by rw [show U.x=x from hx,H.laws.data.funds.length_eq]; exact N.oboe.mode
       have H':Cash W U.x μ L Q o C T R:= (show x=U.x from hx.symm) ▸ H
       let I':= edgesM S (H'.unionP p) U.B; let L':=(F.order G).prod U.dice; let u(C: Leaf R)(z:E):=C.carat I' U (V z) A Q.table p W o.a Q.halo -- A or d
       have hZ (C:Leaf R): ∀ᶠ z in 𝓝 y,K k z C=(∫ y,u C z y ∂L')∧ Integrable (u C z) L':=by
          filter_upwards [C.chutes U p H' hw hv hr N.oboe.conduit hD,(C.boosts U p H' hw hv I' hr N.oboe.conduit hD).2] with z hz ht'
          refine ⟨?_,ht'⟩; unfold K I; rw [← C.casin X p H hx ht h k (V z) (V z) (fun _ _ _=>rfl), show podium S G D (radiusB x)= podium S G (H'.unionP p) U.B from ?_];exact hz
          change _=podium S G (ground _ T Q.halo X.B p) X.B; rw [hb]; rfl
       filter_upwards [hZ M,eventually_all.mpr (fun i=> hZ (Z i))] with z hM hz
       rw [hM.1, show u M z=(fun v=>∑ i,t i*u (Z i) z v) from funext fun v=> sticks M U hs (V z) _ _ _ _]; simp_rw [fun i=>(hz i).1]; rw [MeasureTheory.integral_finsetSum]; swap; · intro i hi; exact ((hz i).2).const_mul _
       simp_rw [integral_const_mul]
    filter_upwards [eventually_all.mpr hK] with z hz
    let a:ℝ:= (Fintype.card S.Choices:ℝ)⁻¹; change a*(∑ k,K k z M)= ∑ i,t i*(a*∑ k,K k z (Z i)); simp_rw [hz]; rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ;rw [← Finset.mul_sum]; ring
private lemma portion (h: Healthy (Pressure.temp x) (H.unionP p) (V y))(ht:(roster p).flags=∅)(hs:Grouped M t Z)(he:Mode V y j v): ∀ᶠ z in 𝓝 y, escort M χ Q.table p Q.halo T W x o.K o.a (V z) = ∑ i,t i*escort (Z i) χ Q.table p Q.halo T W x o.K o.a (V z):=by
    let f (C:Leaf R) (i:Greenbelt.Reserve S) z:= C.picture (prism T x χ o.K (V z) (allot i)) p W o.a Q.table Q.halo
    have hf (i: Greenbelt.Reserve S):∀ᶠ z in 𝓝 y,f M i z=∑ j,t j*f (Z j) i z:=budding M (prism T x χ o.K (V y) (allot i)) H N rfl rfl rfl h ht hs he rfl
    filter_upwards [eventually_all.mpr hf] with z hz
    let a:ℝ:=(Fintype.card (Greenbelt.Reserve S):ℝ)⁻¹; change a*∑ i,f M i z= ∑ j,t j*(a*∑ i,f (Z j) i z); simp_rw [hz]; rw [Finset.sum_comm,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ;rw [← Finset.mul_sum]; ring
lemma rind (hs:Grouped M t Z)(p:H.fragrances)(o':Site c)(h:Healthy (Pressure.temp x) (locus M H o' p) (V y))(he:Mode V y j v): ∀ᶠ z in 𝓝 y, matin M H p χ (V z)=∑ i,t i*matin (Z i) H p χ (V z):=by
   by_cases hk:speaks M H p; swap
   · have hr i: ¬speaks (Z i) H p := by unfold speaks; rw [hs.turn]; exact hk
     have heZ i: matin (Z i) H p χ=0:= quiet _ _ _ _ (hr i)
     simp_rw [show matin M H p χ=0 from quiet _ _ _ _ hk, heZ];simp
   rw [locus,if_pos hk] at h
   have hY i: Healthy (Pressure.temp x) (H.smallAt (p.2 i)) (V y):= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ i)) h
   have hh(i):∀ᶠ z in 𝓝 y, libs M H χ (V z) (p.2 i) =∑ j,t j*libs (Z j) H χ (V z) (p.2 i):= portion M H N (hY i) ((p.2 i).property.2) hs he
   filter_upwards [eventually_all.mpr hh] with z hz; unfold matin; simp_rw [hz]; let q:ℝ:= coefficient H.seam p.2/↑(p.1+1).factorial; let g i:=∏ j ∈ univ.erase i, leaflet H χ (V z) (p.2 j)
   change q*(∑ i,g i * ∑ j,t j*libs (Z j) H χ (V z) (p.2 i))=∑ j,t j*(q*∑ i,g i * libs (Z j) H χ (V z) (p.2 i)); simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring
lemma peel (hs:Grouped M t Z)(p:H.fragrances)(o':Site c) {U:Config G c}(hp: Healthy (Pressure.temp x) (locus M H o' p) U): ∀ᶠ z:Directions G c in 𝓝 0, matin M H p χ (increment U z) = ∑ i,t i*matin (Z i) H p χ (increment U z):=by
   obtain ⟨u,hu,h⟩:= expCost G j 1
   let a:=1+j.factorial*u; have ha : 0<a := by unfold a; positivity
   let d:= v/(2*a); have hv:= N.position; have hd : 0<d:= by unfold d; positivity
   let L := d • ContinuousLinearMap.id ℝ (Directions G c)
   have hL : ‖L‖ ≤ 1*d := by unfold L; rw [norm_smul,one_mul,Real.norm_of_nonneg hd.le]; exact mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le
   have hh := fromLogL L (x:=0) (linearB L (u:=1) (d:=d) (by simp) hL hd.le) 1 zero_lt_one h (by intro i; simp only [map_zero, Pi.zero_apply]; simp) U
   have he : (1+(j.factorial:ℝ)*u)*((1+1)*d)=v := by change a*_ =_; unfold d; field_simp; ring
   rw [he] at hh
   let S := d⁻¹ • ContinuousLinearMap.id ℝ (Directions G c); have hx:= S.continuous.tendsto 0; rw [map_zero] at hx
   have hp:= hx.eventually (rind M H N hs p o' (by simpa only [map_zero,Work.G07.at_zero_increment] using hp) hh); filter_upwards [hp] with z hz; simpa [S,L,smul_smul,hd.ne'] using hz
end YM.PhysicalNext.Repeat.Daisy.Rainfall
