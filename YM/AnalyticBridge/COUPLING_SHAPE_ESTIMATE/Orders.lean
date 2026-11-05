import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Existing
import YM.Extra.ITERATION_NO_LOSS.TermNorm


/-! # Counterterm on the higher-curvature paths

Necessary even with no forced indicators; not reinterpreting them
as only on unflagged fields. Doesn't affect the affine Hessian. Retain
path lengths in all costs via the existing canonical paid receipts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Wilson PathData Next.Scheduling Next.Scheduling.Wages Precision Push Push.BetaTransport Work
open scoped BigOperators Matrix.Norms.Frobenius ContDiff Topology Classical
variable {G : Gauge} {n : Side} {k : ℕ}

abbrev Post (n : Side) := Around n ℕ
variable (F : ℕ→Atom G k) (b : BudgetPoint)
namespace Post

def park (i : Post n) : RegularAddress n :=
  ⟨i.atPin,i.region ((F i.token).footprint 0), Finset.mem_image.mpr ⟨0,Finset.mem_image.mpr ⟨0,Finset.mem_insert_self ..,by simp⟩,i.pull_home⟩⟩
def fee (i : Post n) := weight • i.read (fun U => (F i.token).unmasked U 0)
def restore (i : Post n) := masked b.threshold (park F i).support (fee F i)

def hairpin (i : ℕ) := weight*(WardBin.Wheels.tariff b*Wages.price b (F i))
lemma active (hh : ∀ i, (F i).Invariant) (i : Post n) : b.Regular (park F i).support (fee F i) ∧
    b.supBounds (park F i).site (park F i).support (fee F i) (hairpin F b i.token) := by
  have hv := Extra.Iteration.Derivs.canonical_regular (F i.token) (0:Site n) b (hh i.token)
  refine ⟨reg_scale weight (WardBin.Wheels.regular_carry i.turns i.atPin hv),?_⟩
  have hb := WardBin.Wheels.carry_bound i.turns i.atPin hv (Wages.total b _ _); rw [i.pull_home] at hb
  have hs := sup_scale weight hb; rw [abs_of_pos weight_pos] at hs; exact hs

lemma sanctuary (s : Signed) (x : Site n) (i : Post n) : let j:=Around.move _ s x i
    (park F j).site = affine s x (park F i).site ∧ (park F j).support=(park F i).support.image (affine s x) ∧
      ∀ U : Config G n, fee F j U=fee F i (pull s x U) :=
  ⟨rfl,Around.carries ..,fun U => congr_arg (fun v : ℝ => weight • v) (i.read_move s x (fun V => (F i.token).unmasked V 0) U)⟩

include b in
lemma wont (F : ℕ→ Atom G (3+k)) (hs : G.Simple) (hh : ∀ i,(F i).Invariant) (i : Post n) :
    fee F i 1=0 ∧ ∀ x y, logHessian (fee F i) x y=0 := by
  have hc := (active F b hh i).1
  let f := fee F i
  have ray (B : Directions G n) : Tendsto (fun t : ℝ => f (increment 1 (t • B))/t^2) (𝓝[≠] 0) (𝓝 0) := by
    let X:= ProjectorNext.Equivariance.pulledDirection i.turns i.atPin 1 B
    let A:=windDir X
    have he (t : ℝ) : f (increment 1 (t • B))=weight*(F i.token).unmasked (represent (t • A)) 0 := by
      unfold f fee; simp only [Pi.smul_apply,Around.read,ProjectorNext.Equivariance.pull_increment,map_smul,pull_empty]
      have hl : represent (t • A)=increment 1 (t • X) := by
        unfold represent; rw [show Exterior.collect G (t • A)=t • Exterior.collect G (windDir X) from rfl,collect_wind]
      rw [hl]; rfl
    have h₀ := F03.atom_limit (F i.token) 0 A
    have h₁ : Tendsto (fun t:ℝ => t^(k+1)) (𝓝[≠] 0) (𝓝 0) := by simpa using (tendsto_id (x:=𝓝 (0:ℝ))).pow (k+1) |>.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
    have hz:= (h₀.mul h₁).const_mul weight; rw [mul_zero,mul_zero] at hz
    apply hz.congr'; filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0,t≠0 from self_mem_nhdsWithin] with t ht
    rw [he]
    rw [show t^(3+k)=t^2*t^(k+1) by rw [←pow_add]; congr 1; omega]; field_simp
  have H₀ (A : Directions G n) : H f A A=0 := by rw [from_ray hs hc (ray A)]; ring
  constructor
  · have hh' := F03.value_slope_of_sq_limit (shrink_smooth _ _ hc _).continuousAt (ray (0:Directions G n)); simpa only [zero_smul,G07.at_zero_increment] using hh'.1
  intro A B; rw [log_eq_H]; have hv := polar hc A B
  change _=H f A A+_*H f A B+H f B B at hv
  rw [H₀ A,H₀ B] at hv; linarith [H₀ (A+B)]

variable {F b}
def full (G : Gauge) (k : ℕ) (b : BudgetPoint) (σ C : ℝ) := Fintype.card Signed*(weight*WardBin.Wheels.tariff b*
    (Wages.fund G b.power b.order k b.supportExponent σ*b.threshold^k*C))
lemma earned {σ C : ℝ} (hp : 0 < σ) (hg : b.supportExponent/b.B ≤ σ/4)
    (h : SumBudget (fun i => (F i).budget σ) C) : Sealed b (park (n:=n) F) (fun i => hairpin F b i.token) (full G k b σ C) := by
  intro x
  apply stamped (x:=x) (w:=fun i : Post n => b.mass (park F i).support (hairpin F b i.token)) (fun o s => ?_)
  have hh := Wages.ticket b σ C hp hg F h (0:Site n)
  have hw := weight_pos; have ht:=WardBin.Wheels.tariff_positive b
  refine AbsoluteSums.budget_mono (AbsoluteSums.budget_scale (show 0 ≤ weight*WardBin.Wheels.tariff b by positivity) hh) ?_ ?_
  · intro i; unfold BudgetPoint.mass hairpin
    have he := (Wages.total b (F i) (0:Site n)).1
    dsimp only [Around.token]; positivity
  intro i
  have he : coverNumber b.B (park F (o,s,i)).support=coverNumber b.B ((F i).footprint (0:Site n)) := Local.cover_map (Local.turnSites s o) (Local.turn_sep s o) b.B _
  unfold BudgetPoint.mass hairpin; simp only [he,Around.token]
  have hv : Wages.price b (F i) ≤ Wages.toll b σ (F i) := le_mul_of_one_le_left ((Wages.total b (F i) (0:Site n)).1) (Real.one_le_exp (by positivity))
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv ht.le) hw.le) (Real.exp_pos _).le)
  apply le_of_eq; ring

variable (F b)
lemma translateAtom (A : Atom G k) (x o : Site n) (U : Config G n) : A.placed b (Lattice.translate o U) x = A.placed b U (x+o) := by
  rw [Atom.placed, ←pull_one]
  have hh (V : Config G n) : expandAt x (pull 1 o V)=expandAt (x+o) V := by funext; simp only [pull_one,expandAt,Lattice.translate,add_assoc]
  have hx : (A.footprint x).image (affine 1 o) = A.footprint (x+o) := by simp [Atom.footprint,Finset.image_image,comp_def,affine,add_assoc]
  rw [← mask_cov b.threshold 1 o U (X:=A.footprint x) (g:=fun V : Config G n => A.unmasked V (x+o)) (by simp only [Atom.unmasked,Slot.atSite,hh]),hx]
  rfl

lemma active_site (s : Signed) (x : Site n) (i : ℕ) (U : Config G n) : restore F b (s.act x,s,i) U=weight*(F i).placed b (pull s 0 U) x := by
  let W := fun V : Config G n => weight*(F i).unmasked V 0; let j:= F i
  rw [restore]; let M := (s.act x,s,i)
  rw [show masked _ (park F M).support _ _=masked b.threshold (j.footprint 0) W (pull s (s.act x) U) from
      mask_cov b.threshold s (s.act x) U (f:=W) (X:=j.footprint 0) (g:=fee F M) rfl, recenter,
    ← show (F i).placed b (Lattice.translate x (pull s 0 U)) 0=(F i).placed b (pull s 0 U) x by rw [translateAtom,zero_add]]
  let V := Lattice.translate x (pull s 0 U)
  change masked b.threshold _ W V=weight*masked b.threshold (j.footprint 0) _ V
  by_cases h : Healthy b.threshold (j.footprint 0) V
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]
  rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero]

lemma income {σ C : ℝ} (h : ∀ i,(F i).Invariant) (hg : b.supportExponent/b.B≤σ/4) (hσ : 0<σ)
    (hh : SumBudget (fun i => (F i).budget σ) C) : Dominated (restore F b (n:=n)) :=
  ⟨_,(totalBooked (fun i : Post n => (active F b h i).2.1) (earned hσ hg hh)).2.1,fun i U => mask_cost (active F b h i).2 U⟩

lemma totals {σ C : ℝ} (h : ∀ i,(F i).Invariant) (hg : b.supportExponent/b.B≤σ/4) (hσ : 0<σ)
    (hh : SumBudget (fun i => (F i).budget σ) C) (U : Config G n) :
    (∑' i, restore F b i U) = weight * ∑ s : Signed,∑ x : Site n,atomSeries F b (pull s 0 U) x := by
  rw [tally ((income F b h hg hσ hh).summable U),Finset.sum_comm,Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Equiv.sum_comp (s.actEquiv (R:=Per n)).toEquiv (fun x => ∑' i:ℕ,restore F b (x,s,i) U),Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _; change (∑' i:ℕ, restore F b (s.act x,s,i) U)=_
  simp_rw [active_site,tsum_mul_left]; rfl
end Post

lemma kin_assembled {R : PathData G} {p : Clip} {b : BudgetPoint} {σ C Λ : ℝ} (h : R.Bounds p σ C Λ)
    (hg : Grace p b σ) (U : Config G n) :
    kinetic R p b U=hub R p b U+(∑' i,Post.restore R.cubic b i U)+(∑' i,Post.restore R.quartic b i U) := by
  rw [Post.totals _ _ (fun i => (h.invariant i).2.1) hg.2 h.width h.three,
    Post.totals _ _ (fun i=>(h.invariant i).2.2) hg.2 h.width h.four]
  simp only [kinetic,hub,Finset.sum_add_distrib,weight]; ring
end YM.AnalyticBridge.CouplingShape
