import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Affine
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Birthday
import YM.Progress.STATIONARY_SCENES.Thermal


/-!
# The tree tangent hits every orientation of the energetic Ybase rows

No change of reference fields or doing separate rotations of Q. Derivation
from the exact *actual* Step with Comptroller finances (costs
remain). E Eq rowzero. No asserting cancellation at a nonlinear field.
Noise symmetry uses the SAME estimator tags even in limits. Sworn on these
real metric channels required; get from e.g. Stationary Service, not from
existence of unmarked partition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Turn
open Matrix Work.F03 Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations
open Progress.StationaryScenes Filter Bloch
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma flip_energy (s : Signed) (Q V : Config G c) (i : Bond c) :
    ‖Tube.Z S (pull s 0 Q) (pull s 0 V) i‖ = ‖Tube.Z S Q V (edgeP s i)‖ := by
  unfold Tube.Z; rw [step_transport,step_transport]; split
  · let u := V (edgeP s i); let v := Q (edgeP s i)
    have hv : u⁻¹*(v⁻¹)⁻¹ = (u⁻¹*(u*v⁻¹)*(u⁻¹)⁻¹)⁻¹ := by group
    change ‖_ • G.curvature (u⁻¹*(v⁻¹)⁻¹)‖ = _
    rw [hv,G.curvature_inv, G.curvature_conjugate]; simp only [norm_smul, norm_neg,G.norm_adjoint]; rfl
  rfl

def orient (s : Signed) (u : LogField G n) := form (maps s 1 (collect G u))

lemma orient_linear (s : Signed) (u : LogField G n) (t : ℝ) : orient s (t • u) = t • orient s u := by
  unfold orient; rw [show collect G (t • u) = t • collect G u from rfl,map_smul]; rfl

lemma orient_represents (s : Signed) (u : LogField G n) : represent (orient s u) = pull s 0 (represent u) := by
  unfold represent orient; rw [operations_pulled,collect_form]; congr 1
  funext i; simp [pull, Step.read]

lemma orient_pulls (s : Signed) (u : LogField G n) : orient s u=Bid.pulled u s := by
  unfold orient collect form Bid.pulled
  funext i; rw [maps_apply]; simp [edgeP,sendEdge]; -- type second uses axisEquiv

lemma z_energy (s : Signed) (a : LogField G f) (b : LogField G c) (h : S.patch.Branches S.kernel G) :
    ∑ i, ‖zLin S (orient s a) (orient s b) i‖^2 = ∑ i, ‖zLin S a b i‖^2 := by
  let t : S.Choices := Classical.ofNonempty
  let q := choice s t
  have hh i (t : S.Choices) (x : LogField G f) (y : LogField G c) :
      Tendsto (fun r : ℝ => ‖r‖⁻¹ * ‖zTest S t i (r • (x,y))‖) (𝓝[≠] 0) (𝓝 ‖zLin S x y i‖) := by
    have hv := (zTest_deriv (S:=S) h t i (x,y)).tendsto_slope.norm
    simpa only [slope_def_module, sub_zero, zero_smul, zTest_zero h, norm_smul,norm_inv] using hv
  have he i : (fun r : ℝ => ‖zTest S q i (r • (orient s a,orient s b))‖) =
      fun r => ‖zTest S t (edgeP s i) (r • (a,b))‖ := by
    funext r
    change ‖Tube.Z _ (S.prediction (represent (r • orient s a)) q) (represent (r • orient s b)) i‖ = _
    rw [← orient_linear, ← orient_linear, orient_represents,orient_represents,(carry s h t _).2]
    exact flip_energy ..
  calc
    _ = ∑ i, ‖zLin S a b (edgeP s i)‖ ^ 2 := Finset.sum_congr rfl fun i _ => by
      congr 1
      have hv := hh i q (orient s a) (orient s b)
      simp_rw [show ∀ r : ℝ, ‖zTest S q i (r • (orient s a,orient s b))‖ = _ from congr_fun (he i)] at hv
      exact tendsto_nhds_unique hv (hh (edgeP s i) t ..)
    _ = _ := Equiv.sum_comp (StepData.sendBonds s 0) fun i => ‖zLin S a b i‖^2

/-- additional data supplied via StationaryScenes / H.Suffices with
Sworn orientation on both beds. -/
structure Alongside (A B : Bed) (T : Tube G S) : Prop where
  inbound : Attached A T.up
  outbound : Attached B T.down
  together : Towers.Diagonal S A B T.R
  sails : Towers.Roll S A B T.R T.high T.low
  budgets : ∃ a b q r, Floor A T.high f a b ∧ Floor B T.low c q r
  old : Bid.Sworn A f G
  new : Bid.Sworn B c G

-- extend linear function explicitly also to coordinates off chart

def station (T : Tube G S) (F : Forest S.ratio) (b : LogField G c) : LogField G f := fun i =>
  WithLp.toLp 2 fun k => (extracted S F (installed S.ratio T.R.A0) *ᵥ parts G 1 b k) i

def attempt (T : Tube G S) (F : Forest S.ratio) (b : LogField G c) :=
  collect G (station T F b) - linearCopy S.ratio (collect G b)

lemma attempt_root (T : Tube G S) (F : Forest S.ratio) (b : LogField G c) (i : Bond f) (he : i∈F.trunks) :
    attempt T F b i=(0:G.Color) := by
  have hp : linearCopy S.ratio (collect G b) i=0 := by unfold linearCopy; rw [if_pos (F.trunk_internal (by simpa using he))]
  have hs : collect G (station T F b) i=0 := by
    ext k; exact Precision.stays (S:=S) F _ (parts G 1 b k) i he
  simp only [attempt, Pi.sub_apply, hp,hs,sub_zero]



section receipt
variable (T : Tube G S) {P : Teller G} {A B : Bed} (ha : Alongside A B T) (hT : P.Funds S T)
  (b : LogField G c) (F : Forest S.ratio)

def Limage (b : LogField G c) := xLin T.low T.down b

def Fout := zip (flatF T) (Limage T b)
def Qout := zip (flatI T) (Limage T b)

include ha hT
private lemma read_price (s : Co c Layers2) (k) :
    Limage T b ((Work.E03.meshEquiv c).symm s) k = ((B.full T.low c*d 1 c) *ᵥ parts G 1 b k) s := by
  obtain ⟨W,C,hx,hV⟩ := hT.feeds; rw [← hT.low] at hV
  have he := xLin_component T.low T.down B hV ha.outbound b ((Work.E03.meshEquiv c).symm s) k
  rw [show mesh ((Work.E03.meshEquiv c).symm s)=s from (Work.E03.meshEquiv c).apply_symm_apply _] at he; exact he

lemma gain_zero (i) : zip (flatN T) (Limage T b) i = 0 := by
  ext k
  have he := scalar_zip (T.R.o.acts c) (Equiv.refl _) (Work.E03.meshEquiv c) (Limage T b) i k
  simp only [read_price T ha hT b, Equiv.refl_apply] at he
  rw [mulVec_mulVec, ← Matrix.mul_assoc,ha.sails.oPart, zero_mulVec] at he; exact he

lemma row_cost (i) : xLin T.high T.up (station T F b) i = Fout T b i := by
  obtain ⟨W,C,hx,hV⟩ := hT.feeds; rw [← hT.high] at hx
  have he : d 1 f * extracted S F (installed S.ratio T.R.A0)=d 1 f * installed S.ratio T.R.A0 := by
    unfold extracted
    rw [Matrix.mul_add, ← Matrix.mul_assoc _ (d 0 f), Exterior.closed 0,Matrix.zero_mul,add_zero]
  ext k
  rw [xLin_component T.high T.up A hx ha.inbound]
  have hp := scalar_zip (installed S.ratio T.R.mf) (Work.E03.meshEquiv f) (Work.E03.meshEquiv c) (Limage T b) i k
  simp_rw [read_price T ha hT b] at hp; rw [mulVec_mulVec, ← Matrix.mul_assoc, ha.sails.fPart] at hp
  change _ = zip (flatF T) (Limage T b) i k; apply Eq.trans _ hp.symm
  rw [show parts G 1 (station T F b) k=extracted S F (installed S.ratio T.R.A0) *ᵥ parts G 1 b k from rfl,
    mulVec_mulVec, Matrix.mul_assoc, he, ← Matrix.mul_assoc]; rfl

lemma Qidentify (k) (i) : Qout T b i k = (Real.sqrt S.kernel.penalty)⁻¹ •
    ((K (B.metric.acts c) *ᵥ parts G 1 b k) (pole i)) := by
  let h := scalar_zip (T.R.mn.acts c) (Work.E03.poleEquiv c) (Work.E03.meshEquiv c) (Limage T b) i k
  simp_rw [read_price T ha hT b] at h; rw [mulVec_mulVec, ← Matrix.mul_assoc,ha.sails.nPart, Matrix.smul_mulVec] at h
  exact h

lemma bond_cost (i) : zLin S (station T F b) b i = Qout T b i := by
  have hr := (stationed F _ _ _ ha.together.trial).1
  let κ := S.kernel.penalty
  have he : 0 < κ := S.kernel.penalty_pos
  have hi : Real.sqrt κ * κ⁻¹ = (Real.sqrt κ)⁻¹ := by field_simp; exact Real.sq_sqrt he.le
  ext k
  let y := parts G 1 b k; let z := K (B.metric.acts c)
  change Real.sqrt κ * (y (pole i) - (probe S *ᵥ (extracted S F _ *ᵥ y)) _) = _
  rw [mulVec_mulVec,hr,Matrix.sub_mulVec, Matrix.one_mulVec, Qidentify T ha hT b, Matrix.smul_mulVec]
  change Real.sqrt κ * (y _-(y _- κ⁻¹*(z *ᵥ y) _)) = (Real.sqrt κ)⁻¹ * ((z *ᵥ y) _)
  rw [sub_sub_cancel, ← mul_assoc, hi]
end receipt

section squares
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Not Pi norm. -/
def counted (A : X→G.Color) := ∑ i, ‖A i‖^2

private lemma norm_axis (B : Bed) (V : Clip) (W : PathData G) (x : LogField G n)
    {b q s σ C} (hb : W.Bounds V σ C s) (hv : Attached B W) (h : Floor B V n b q) :
    Bid.gaugeFiscal B x x = counted (xLin V W x) := by
  rw [metric_pair B hb hv x x h,counted]; conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  simp only [Fintype.sum_bool,xLin, Bool.false_eq_true, ↓reduceIte, norm_smul,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt V.quadratic_pos.le,
    real_inner_self_eq_norm_sq, add_comm]

theorem one_square (T : Tube G S) (x : LogField G f) (b : LogField G c)
    {P : Teller G} {A B : Bed} (hA : Alongside A B T) (hP : P.Funds S T) :
    let Z := zLin S x b; let L := xLin T.high T.up x
    counted (L-Fout T b) + counted (Z - Qout T b) = counted L + counted Z - counted (Limage T b) := by
  obtain ⟨c₁,e,hc,he⟩ := hP.feeds
  rw [← hP.high] at hc; rw [← hP.low] at he
  intro Z L
  let v := Limage T b
  let I := Fout T b; let O := Qout T b
  let H p (u w : p → G.Color) [Fintype p] := ∑ i, inner ℝ (u i) (w i)
  have hf (u w) : H _ u I + H _ w O = ∑ j,inner ℝ (v j) (unzip (flatF T) u j + unzip (flatI T) w j) := by
    have hj : H _ u I = ∑ i, inner ℝ (I i) (u i) := Finset.sum_congr rfl (fun _ _ => real_inner_comm ..)
    have hk : H _ w O = ∑ i, inner ℝ (O i) (w i) := Finset.sum_congr rfl (fun _ _ => real_inner_comm ..)
    rw [hj,hk,show I = zip (flatF T) v from rfl, show O = zip (flatI T) v from rfl,
      arity (flatF T) u v, arity (flatI T) w v]; simp_rw [inner_add_right, Finset.sum_add_distrib]
  have hx : H _ L I+ H _ Z O=counted v := by
    rw [hf L Z]; unfold counted; refine Finset.sum_congr rfl fun i _ => ?_
    rw [show unzip (flatF T) L i + unzip (flatI T) Z i=v i from
         sub_eq_zero.mp (roll_l T hA.sails hc he hA.inbound hA.outbound x b i), real_inner_self_eq_norm_sq]
  have hi : H _ I I+H _ O O=counted v := by
    rw [hf]; unfold counted; refine Finset.sum_congr rfl fun i _ => ?_
    have hz := sub_eq_zero.mp (roll_d T hA.sails v i)
    have he : zip (flatN T) v=0 := funext (gain_zero T hA hP b)
    have hl : unzip (flatF T) I i + unzip (flatI T) O i = v i := by
      simpa only [he, show unzip (flatN T) (0 : Co c Gain → G.Color) i=0 from by simp [unzip], add_zero] using! hz.symm
    rw [hl,real_inner_self_eq_norm_sq]
  have hr (p : Type) [Fintype p] (a b : p → G.Color) :
      counted (a-b) = counted a + H _ b b - 2*H p a b := by
    unfold counted H
    simp_rw [Pi.sub_apply, norm_sub_sq_real,real_inner_self_eq_norm_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,Finset.mul_sum]; ring
  change counted (L-I)+counted (Z-O) = _ - counted v
  rw [hr,hr]; linarith only [hx,hi]

lemma square_turn (T : Tube G S) (x : LogField G f) (b : LogField G c)
    {P : Teller G} {A B : Bed} (hA : Alongside A B T) (hP : P.Funds S T) (s : Signed) :
    let g := orient s x; let v := orient s b; let f := xLin T.high T.up
    counted (f g-Fout T v) + counted (zLin S g v-Qout T v)=
      counted (f x-Fout T b)+counted (zLin S x b-Qout T b) := by
  obtain ⟨c,e,hc,hv⟩ := hP.feeds
  obtain ⟨a,m,n,w,hx,hy⟩ := hA.budgets
  rw [← hP.high] at hc; rw [← hP.low] at hv
  intro g v f; unfold f
  have hf : counted (zLin S g v)=counted (zLin S x b) := z_energy _ x b (hP.knobs.symm ▸ hP.kernel)
  calc
    _ = counted (f g)+counted (zLin S g v)-counted (Limage T v) := one_square T g v hA hP
    _ = counted (f x)+counted (zLin S x b)-counted (Limage T b) := by
        unfold Limage f
        rw [hf, ← norm_axis A _ _ g hc hA.inbound hx, ← norm_axis A _ _ x hc hA.inbound hx,
          ← norm_axis B _ _ v hv hA.outbound hy, ← norm_axis B _ _ b hv hA.outbound hy,
          show g = Bid.pulled x s from orient_pulls .., show v = Bid.pulled b s from orient_pulls ..,
          hA.old s x x, hA.new s b b]
    _ = _ := (one_square T x b hA hP).symm

/-- All orientation channels on the one field. No taking just one
channel linear term while billing the others. -/
theorem escape {P : Teller G} (T : Tube G S) {A B : Bed} (hA : Alongside A B T) (hP : P.Funds S T)
    (s : Signed) (F : Forest S.ratio) (b : LogField G c) :
    let v := orient s (station T F b); let x := orient s b
    xLin T.high T.up v = Fout T x ∧ zLin S v x = Qout T x := by
  intro v x
  let Z := station T F b
  let f := xLin T.high T.up v - Fout T x; let g := zLin S v x - Qout T x
  have ht : counted f + counted g = 0 := by
    have he := square_turn T Z b hA hP s
    refine he.trans ?_; rw [show xLin T.high T.up Z=Fout T b from funext (row_cost T hA hP b F),
      show zLin S Z b=Qout T b from funext (bond_cost T hA hP b F)]; simp [counted]
  have hn (p : Type) [Fintype p] (a : p → G.Color) : 0 ≤ counted a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hf : counted f≤0 := by linarith [hn _ f,hn _ g]
  have hg : counted g≤0 := by linarith [hn _ f,hn _ g]
  have hx (p : Type) [Fintype p] (a : p → G.Color) (h : counted a ≤ 0) : a=0 := by
    funext i
    have he : ‖a i‖^2 ≤ 0 := le_trans (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg ‖a j‖)
      (Finset.mem_univ i)) h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (a i)])
  exact ⟨sub_eq_zero.mp (hx _ f hf),sub_eq_zero.mp (hx _ g hg)⟩
end squares
end YM.AnalyticNext.ConnectedActivity.Aff
